#include "loopinductionderived.hh"
#include "defusechain.hh"
#include "loopinductionopt.hh"

using namespace std;
using namespace quad;

namespace {

struct AffineCandidate {
    int basicTempNum = -1;
    int coeff = 0;
    int constant = 0;
    int currentTempNum = -1;
    size_t defOrder = static_cast<size_t>(-1);
    int sourceTempNum = -1;
    size_t sourceOrder = static_cast<size_t>(-1);
    QuadStm* defStm = nullptr;
};

int getTempNumFromTerm(QuadTerm* term) {
    if (term == nullptr || term->kind != QuadTermKind::TEMP) {
        return -1;
    }
    QuadTemp* quadTemp = term->get_temp();
    if (quadTemp == nullptr || quadTemp->temp == nullptr) {
        return -1;
    }
    return quadTemp->temp->num;
}

bool getConstFromTerm(QuadTerm* term, int& value) {
    if (term == nullptr || term->kind != QuadTermKind::CONST) {
        return false;
    }
    value = term->get_const();
    return true;
}

int getDefinedTemp(QuadStm* stm) {
    if (stm == nullptr) {
        return -1;
    }
    if (stm->kind == QuadKind::MOVE) {
        QuadMove* move = dynamic_cast<QuadMove*>(stm);
        return (move != nullptr && move->dst != nullptr && move->dst->temp != nullptr) ? move->dst->temp->num : -1;
    }
    if (stm->kind == QuadKind::MOVE_BINOP) {
        QuadMoveBinop* binop = dynamic_cast<QuadMoveBinop*>(stm);
        return (binop != nullptr && binop->dst != nullptr && binop->dst->temp != nullptr) ? binop->dst->temp->num : -1;
    }
    return -1;
}

map<QuadStm*, size_t> buildStatementOrder(QuadFuncDecl* func) {
    map<QuadStm*, size_t> order;
    if (func == nullptr || func->quadblocklist == nullptr) {
        return order;
    }

    size_t nextOrder = 0;
    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (QuadStm* stm : *block->quadlist) {
            order[stm] = nextOrder++;
        }
    }
    return order;
}

AffineCandidate makeBaseCandidate(int basicTempNum, int tempNum, size_t order, QuadStm* defStm) {
    AffineCandidate candidate;
    candidate.basicTempNum = basicTempNum;
    candidate.coeff = 1;
    candidate.constant = 0;
    candidate.currentTempNum = tempNum;
    candidate.defOrder = order;
    candidate.sourceTempNum = tempNum;
    candidate.sourceOrder = order;
    candidate.defStm = defStm;
    return candidate;
}

bool buildAffineFromBinop(
    QuadMoveBinop* binop,
    const map<int, AffineCandidate>& affineByTemp,
    size_t defOrder,
    AffineCandidate& out
) {
    if (binop == nullptr || binop->dst == nullptr || binop->dst->temp == nullptr) {
        return false;
    }

    int leftTemp = getTempNumFromTerm(binop->left);
    int rightTemp = getTempNumFromTerm(binop->right);
    int leftConst = 0;
    int rightConst = 0;
    bool leftIsConst = getConstFromTerm(binop->left, leftConst);
    bool rightIsConst = getConstFromTerm(binop->right, rightConst);

    auto leftIt = affineByTemp.find(leftTemp);
    auto rightIt = affineByTemp.find(rightTemp);

    auto finish = [&](const AffineCandidate& src, int coeff, int constant, int sourceTempNum) {
        out = src;
        out.coeff = coeff;
        out.constant = constant;
        out.currentTempNum = binop->dst->temp->num;
        out.defOrder = defOrder;
        out.sourceTempNum = sourceTempNum;
        out.sourceOrder = src.defOrder;
        out.defStm = binop;
    };

    if (binop->binop == "+") {
        if (leftIt != affineByTemp.end() && rightIsConst) {
            finish(leftIt->second, leftIt->second.coeff, leftIt->second.constant + rightConst, leftTemp);
            return out.coeff != 0;
        }
        if (rightIt != affineByTemp.end() && leftIsConst) {
            finish(rightIt->second, rightIt->second.coeff, rightIt->second.constant + leftConst, rightTemp);
            return out.coeff != 0;
        }
    }

    if (binop->binop == "-") {
        if (leftIt != affineByTemp.end() && rightIsConst) {
            finish(leftIt->second, leftIt->second.coeff, leftIt->second.constant - rightConst, leftTemp);
            return out.coeff != 0;
        }
        if (rightIt != affineByTemp.end() && leftIsConst) {
            finish(rightIt->second, -rightIt->second.coeff, leftConst - rightIt->second.constant, rightTemp);
            return out.coeff != 0;
        }
    }

    if (binop->binop == "*") {
        if (leftIt != affineByTemp.end() && rightIsConst) {
            finish(leftIt->second, leftIt->second.coeff * rightConst, leftIt->second.constant * rightConst, leftTemp);
            return out.coeff != 0;
        }
        if (rightIt != affineByTemp.end() && leftIsConst) {
            finish(rightIt->second, rightIt->second.coeff * leftConst, rightIt->second.constant * leftConst, rightTemp);
            return out.coeff != 0;
        }
    }

    return false;
}

bool isBasicFamilyTemp(const vector<BasicInductionVar>& basics, int tempNum) {
    for (const BasicInductionVar& basic : basics) {
        if (basic.isRelatedTemp(tempNum)) {
            return true;
        }
    }
    return false;
}

}  // namespace

map<int, vector<DerivedInductionVar>> discoverDerivedInductionVars(QuadFuncDecl* func, LoopHeaderMap *loopHeaderMap, 
        const DefUseChain& du, const ControlFlowInfo& cfi) {
    map<int, vector<DerivedInductionVar>> result;
    if (func == nullptr || func->quadblocklist == nullptr || loopHeaderMap == nullptr) {
        return result;
    }
    if (!loopHeaderMap->funcLoopHeaders.count(func)) {
        return result;
    }

    // fill in the code to discover derived induction variables,
    // and populate the result map with header label -> list ofderived IVs in that loop
    // Note to fill in all the necessary information in the DerivedInductionVar objects,
    // including the related temps and their usefulness, and the expression for how the derived IV is computed
    map<int, QuadBlock*> labelToBlock = buildLabelToBlock(func);
    map<QuadStm*, size_t> statementOrder = buildStatementOrder(func);
    map<int, vector<BasicInductionVar>> basicByHeader = discoverBasicInductionVars(func, loopHeaderMap, du, cfi);

    for (LoopHeader* loopHeader : loopHeaderMap->funcLoopHeaders[func]) {
        if (loopHeader == nullptr) {
            continue;
        }

        auto basicIt = basicByHeader.find(loopHeader->headerLabel);
        if (basicIt == basicByHeader.end() || basicIt->second.empty()) {
            continue;
        }

        map<int, AffineCandidate> affineByTemp;
        set<QuadStm*> affineDefStms;

        for (const BasicInductionVar& biv : basicIt->second) {
            size_t phiOrder = statementOrder.count(biv.phiStm) ? statementOrder[biv.phiStm] : static_cast<size_t>(-1);
            size_t updateOrder = statementOrder.count(biv.updateStm) ? statementOrder[biv.updateStm] : static_cast<size_t>(-1);
            affineByTemp[biv.phiTempNum] = makeBaseCandidate(biv.phiTempNum, biv.phiTempNum, phiOrder, biv.phiStm);
            affineByTemp[biv.backedgeTempNum] = makeBaseCandidate(biv.phiTempNum, biv.backedgeTempNum, updateOrder, biv.updateStm);
        }

        for (int blockLabel : loopHeader->bodyBlocks) {
            auto blockIt = labelToBlock.find(blockLabel);
            if (blockIt == labelToBlock.end() || blockIt->second == nullptr || blockIt->second->quadlist == nullptr) {
                continue;
            }

            for (QuadStm* stm : *blockIt->second->quadlist) {
                if (stm == nullptr) {
                    continue;
                }

                int definedTemp = getDefinedTemp(stm);
                if (definedTemp == -1) {
                    continue;
                }

                if (isBasicFamilyTemp(basicIt->second, definedTemp)) {
                    continue;
                }

                if (stm->kind == QuadKind::MOVE) {
                    QuadMove* move = dynamic_cast<QuadMove*>(stm);
                    int srcTemp = (move != nullptr) ? getTempNumFromTerm(move->src) : -1;
                    auto srcIt = affineByTemp.find(srcTemp);
                    if (srcIt != affineByTemp.end()) {
                        AffineCandidate copied = srcIt->second;
                        copied.currentTempNum = definedTemp;
                        copied.defOrder = statementOrder[stm];
                        copied.sourceTempNum = srcTemp;
                        copied.sourceOrder = srcIt->second.defOrder;
                        copied.defStm = stm;
                        affineByTemp[definedTemp] = copied;
                        affineDefStms.insert(stm);
                    }
                    continue;
                }

                if (stm->kind != QuadKind::MOVE_BINOP) {
                    continue;
                }

                AffineCandidate candidate;
                if (buildAffineFromBinop(dynamic_cast<QuadMoveBinop*>(stm), affineByTemp, statementOrder[stm], candidate)) {
                    affineByTemp[definedTemp] = candidate;
                    affineDefStms.insert(stm);
                }
            }
        }

        for (const auto& [tempNum, candidate] : affineByTemp) {
            if (candidate.defStm == nullptr || !affineDefStms.count(candidate.defStm)) {
                continue;
            }

            if (isBasicFamilyTemp(basicIt->second, tempNum)) {
                continue;
            }

            VarDefInfo* defInfo = du.getDef(tempNum);
            if (defInfo == nullptr || defInfo->useSet.empty()) {
                continue;
            }

            bool hasNonAffineUse = false;
            for (const auto& useSite : defInfo->useSet) {
                QuadStm* useStm = useSite.second;
                if (!affineDefStms.count(useStm)) {
                    hasNonAffineUse = true;
                    break;
                }
            }
            if (!hasNonAffineUse) {
                continue;
            }

            AffineIVExpr expr;
            expr.basicTempNum = candidate.basicTempNum;
            expr.basicCoeff = candidate.coeff;
            expr.constant = candidate.constant;
            result[loopHeader->headerLabel].push_back(
                DerivedInductionVar(
                    loopHeader->headerLabel,
                    tempNum,
                    candidate.sourceTempNum,
                    candidate.sourceOrder,
                    expr,
                    candidate.defStm
                )
            );
        }
    }

    return result;
}
