#include "loopinductionbasic.hh"
#include "defusechain.hh"
#include "loopinductionopt.hh"
#include <cstdlib>

using namespace std;
using namespace quad;

namespace {

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

int getBlockLabel(QuadBlock* block) {
    if (block == nullptr || block->entry_label == nullptr) {
        return -1;
    }
    return block->entry_label->num;
}

map<QuadStm*, int> buildStatementOrder(QuadFuncDecl* func) {
    map<QuadStm*, int> order;
    if (func == nullptr || func->quadblocklist == nullptr) {
        return order;
    }

    int nextOrder = 0;
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

bool isLoopInvariantTemp(int tempNum, const DefUseChain& du, const set<int>& bodyBlocks) {
    if (tempNum == -1) {
        return false;
    }
    VarDefInfo* defInfo = du.getDef(tempNum);
    if (defInfo == nullptr) {
        return false;
    }
    return !bodyBlocks.count(getBlockLabel(defInfo->defBlock));
}

bool parseBasicUpdate(
    QuadMoveBinop* update,
    int phiTempNum,
    const DefUseChain& du,
    const set<int>& bodyBlocks,
    int& stepValue,
    int& stepTempNum
) {
    if (update == nullptr) {
        return false;
    }

    int leftTemp = getTempNumFromTerm(update->left);
    int rightTemp = getTempNumFromTerm(update->right);
    int leftConst = 0;
    int rightConst = 0;
    bool leftIsConst = getConstFromTerm(update->left, leftConst);
    bool rightIsConst = getConstFromTerm(update->right, rightConst);

    stepValue = 0;
    stepTempNum = -1;

    if (update->binop == "+") {
        if (leftTemp == phiTempNum && rightIsConst) {
            stepValue = rightConst;
            return true;
        }
        if (rightTemp == phiTempNum && leftIsConst) {
            stepValue = leftConst;
            return true;
        }
        if (leftTemp == phiTempNum && isLoopInvariantTemp(rightTemp, du, bodyBlocks)) {
            stepTempNum = rightTemp;
            return true;
        }
        if (rightTemp == phiTempNum && isLoopInvariantTemp(leftTemp, du, bodyBlocks)) {
            stepTempNum = leftTemp;
            return true;
        }
    }

    if (update->binop == "-") {
        if (leftTemp == phiTempNum && rightIsConst) {
            stepValue = -rightConst;
            return true;
        }
        if (leftTemp == phiTempNum && isLoopInvariantTemp(rightTemp, du, bodyBlocks)) {
            stepTempNum = -rightTemp;
            return true;
        }
    }

    return false;
}

}  // namespace

map<int, vector<BasicInductionVar>> discoverBasicInductionVars(QuadFuncDecl* func, LoopHeaderMap *loopHeaderMap, 
        const DefUseChain& du, const ControlFlowInfo& cfi) {
    map<int, vector<BasicInductionVar>> result;
    if (func == nullptr || func->quadblocklist == nullptr || loopHeaderMap == nullptr) {
        return result;
    }
    if (!loopHeaderMap->funcLoopHeaders.count(func)) {
        return result;
    }
    // fill in the code to discover basic induction variables,
    // and populate the result map with header label -> list of basic IVs in that loop
    // Note to fill in all the necessary information in the BasicInductionVar objects,
    // including the related temps and their usefulness

    map<QuadStm*, int> statementOrder = buildStatementOrder(func);
    map<int, QuadBlock*> labelToBlock = buildLabelToBlock(func);

    for (LoopHeader* loopHeader : loopHeaderMap->funcLoopHeaders[func]) {
        if (loopHeader == nullptr) {
            continue;
        }

        auto blockIt = labelToBlock.find(loopHeader->headerLabel);
        if (blockIt == labelToBlock.end() || blockIt->second == nullptr || blockIt->second->quadlist == nullptr) {
            continue;
        }

        QuadBlock* headerBlock = blockIt->second;
        for (QuadStm* stm : *headerBlock->quadlist) {
            if (stm == nullptr || stm->kind != QuadKind::PHI) {
                continue;
            }

            QuadPhi* phi = dynamic_cast<QuadPhi*>(stm);
            if (phi == nullptr || phi->temp_exp == nullptr || phi->temp_exp->temp == nullptr || phi->args == nullptr) {
                continue;
            }

            int phiTempNum = phi->temp_exp->temp->num;
            int initTempNum = -1;
            int backedgeTempNum = -1;

            for (const auto& arg : *phi->args) {
                if (arg.first == nullptr || arg.second == nullptr) {
                    continue;
                }
                if (loopHeader->bodyBlocks.count(arg.second->num)) {
                    backedgeTempNum = arg.first->num;
                } else {
                    initTempNum = arg.first->num;
                }
            }

            if (initTempNum == -1 || backedgeTempNum == -1) {
                continue;
            }

            VarDefInfo* backedgeDef = du.getDef(backedgeTempNum);
            if (backedgeDef == nullptr || backedgeDef->defStm == nullptr || backedgeDef->defStm->kind != QuadKind::MOVE_BINOP) {
                continue;
            }
            if (!loopHeader->bodyBlocks.count(getBlockLabel(backedgeDef->defBlock))) {
                continue;
            }

            QuadMoveBinop* update = dynamic_cast<QuadMoveBinop*>(backedgeDef->defStm);
            int stepValue = 0;
            int stepTemp = -1;
            if (!parseBasicUpdate(update, phiTempNum, du, loopHeader->bodyBlocks, stepValue, stepTemp)) {
                continue;
            }

            BasicInductionVar biv(
                loopHeader->headerLabel,
                phiTempNum,
                initTempNum,
                backedgeTempNum,
                stepValue,
                stm,
                backedgeDef->defStm
            );
            biv.stepTempNum = stepTemp;

            auto orderIt = statementOrder.find(backedgeDef->defStm);
            if (orderIt != statementOrder.end()) {
                biv.updateOrder = orderIt->second;
            }

            result[loopHeader->headerLabel].push_back(biv);
        }
    }

    return result;
}
//
// Classify related temps as useless (only in backedges) or useful (in computations)

void classifyRelatedTemps(
    QuadFuncDecl* func,
    map<int, vector<BasicInductionVar>>& basicByHeader,
    const DefUseChain& du
) {
    if (func == nullptr || func->quadblocklist == nullptr) {
        return;
    }
    // fill in the code to classify related temps of basic induction variables
    // as useless (only in backedges) or useful (in computations),
    // by analyzing the def-use chains of the related temps, and
    // checking if they are used in any statements other than the backedge updates of the IV family

    for (auto& [headerLabel, bivs] : basicByHeader) {
        (void)headerLabel;
        for (BasicInductionVar& biv : bivs) {
            if (biv.stepTempNum != -1) {
                biv.addRelatedTemp(abs(biv.stepTempNum));
            }

            for (int tempNum : biv.relatedTemps) {
                if (tempNum == biv.phiTempNum || tempNum == biv.initTempNum) {
                    biv.markUseful(tempNum);
                    continue;
                }

                VarDefInfo* defInfo = du.getDef(tempNum);
                if (defInfo == nullptr) {
                    biv.markUseful(tempNum);
                    continue;
                }

                bool usedOutsideIVCycle = false;
                for (const auto& useSite : defInfo->useSet) {
                    QuadStm* useStm = useSite.second;
                    if (useStm == nullptr) {
                        continue;
                    }
                    if (useStm != biv.phiStm && useStm != biv.updateStm) {
                        usedOutsideIVCycle = true;
                        break;
                    }
                }

                if (usedOutsideIVCycle) {
                    biv.markUseful(tempNum);
                } else {
                    biv.markUseless(tempNum);
                }
            }
        }
    }
}