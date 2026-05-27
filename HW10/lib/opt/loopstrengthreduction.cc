#include "loopstrengthreduction.hh"
#include "loopinductionopt.hh"
#include "defusechain.hh"
#include <cstdlib>
#include <algorithm>

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

LoopHeader* findLoopHeader(LoopHeaderMap* loopHeaderMap, QuadFuncDecl* func, int headerLabel) {
    if (loopHeaderMap == nullptr || !loopHeaderMap->funcLoopHeaders.count(func)) {
        return nullptr;
    }
    for (LoopHeader* loopHeader : loopHeaderMap->funcLoopHeaders[func]) {
        if (loopHeader != nullptr && loopHeader->headerLabel == headerLabel) {
            return loopHeader;
        }
    }
    return nullptr;
}

const BasicInductionVar* findBasicIV(const vector<BasicInductionVar>& basics, int basicTempNum) {
    for (const BasicInductionVar& basic : basics) {
        if (basic.phiTempNum == basicTempNum) {
            return &basic;
        }
    }
    return nullptr;
}

set<int> collectAllTemps(QuadFuncDecl* func) {
    set<int> temps;
    if (func == nullptr || func->quadblocklist == nullptr) {
        return temps;
    }

    auto visitTerm = [&](QuadTerm* term) {
        int tempNum = getTempNumFromTerm(term);
        if (tempNum != -1) {
            temps.insert(tempNum);
        }
    };

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (QuadStm* stm : *block->quadlist) {
            if (stm == nullptr) {
                continue;
            }
            switch (stm->kind) {
                case QuadKind::MOVE: {
                    QuadMove* move = dynamic_cast<QuadMove*>(stm);
                    if (move != nullptr && move->dst != nullptr && move->dst->temp != nullptr) {
                        temps.insert(move->dst->temp->num);
                    }
                    if (move != nullptr) {
                        visitTerm(move->src);
                    }
                    break;
                }
                case QuadKind::LOAD: {
                    QuadLoad* load = dynamic_cast<QuadLoad*>(stm);
                    if (load != nullptr && load->dst != nullptr && load->dst->temp != nullptr) {
                        temps.insert(load->dst->temp->num);
                    }
                    if (load != nullptr) {
                        visitTerm(load->src);
                    }
                    break;
                }
                case QuadKind::STORE: {
                    QuadStore* store = dynamic_cast<QuadStore*>(stm);
                    if (store != nullptr) {
                        visitTerm(store->src);
                        visitTerm(store->dst);
                    }
                    break;
                }
                case QuadKind::MOVE_BINOP: {
                    QuadMoveBinop* binop = dynamic_cast<QuadMoveBinop*>(stm);
                    if (binop != nullptr && binop->dst != nullptr && binop->dst->temp != nullptr) {
                        temps.insert(binop->dst->temp->num);
                    }
                    if (binop != nullptr) {
                        visitTerm(binop->left);
                        visitTerm(binop->right);
                    }
                    break;
                }
                case QuadKind::MOVE_CALL: {
                    QuadMoveCall* movecall = dynamic_cast<QuadMoveCall*>(stm);
                    if (movecall != nullptr && movecall->dst != nullptr && movecall->dst->temp != nullptr) {
                        temps.insert(movecall->dst->temp->num);
                    }
                    break;
                }
                case QuadKind::MOVE_EXTCALL: {
                    QuadMoveExtCall* moveextcall = dynamic_cast<QuadMoveExtCall*>(stm);
                    if (moveextcall != nullptr && moveextcall->dst != nullptr && moveextcall->dst->temp != nullptr) {
                        temps.insert(moveextcall->dst->temp->num);
                    }
                    break;
                }
                case QuadKind::CJUMP: {
                    QuadCJump* cjump = dynamic_cast<QuadCJump*>(stm);
                    if (cjump != nullptr) {
                        visitTerm(cjump->left);
                        visitTerm(cjump->right);
                    }
                    break;
                }
                case QuadKind::PHI: {
                    QuadPhi* phi = dynamic_cast<QuadPhi*>(stm);
                    if (phi != nullptr && phi->temp_exp != nullptr && phi->temp_exp->temp != nullptr) {
                        temps.insert(phi->temp_exp->temp->num);
                    }
                    if (phi != nullptr && phi->args != nullptr) {
                        for (const auto& arg : *phi->args) {
                            if (arg.first != nullptr) {
                                temps.insert(arg.first->num);
                            }
                        }
                    }
                    break;
                }
                case QuadKind::RETURN: {
                    QuadReturn* ret = dynamic_cast<QuadReturn*>(stm);
                    if (ret != nullptr) {
                        visitTerm(ret->exp);
                    }
                    break;
                }
                case QuadKind::PTR_CALC: {
                    QuadPtrCalc* ptrcalc = dynamic_cast<QuadPtrCalc*>(stm);
                    if (ptrcalc != nullptr) {
                        visitTerm(ptrcalc->dst);
                        visitTerm(ptrcalc->ptr);
                        visitTerm(ptrcalc->offset);
                    }
                    break;
                }
                default:
                    break;
            }
        }
    }
    return temps;
}

int allocateTemp(set<int>& usedTemps, int& cursor) {
    while (usedTemps.count(cursor)) {
        ++cursor;
    }
    usedTemps.insert(cursor);
    return cursor++;
}

QuadTemp* makeQuadTemp(int tempNum) {
    return new QuadTemp(new Temp(tempNum), QuadType::INT);
}

QuadTerm* makeTempTerm(int tempNum) {
    return new QuadTerm(makeQuadTemp(tempNum));
}

QuadTerm* makeConstTerm(int value) {
    return new QuadTerm(value);
}

QuadMove* makeMove(int dstTempNum, QuadTerm* src) {
    return new QuadMove(makeQuadTemp(dstTempNum), src, nullptr, nullptr);
}

QuadMoveBinop* makeBinop(int dstTempNum, QuadTerm* left, const string& op, QuadTerm* right) {
    return new QuadMoveBinop(makeQuadTemp(dstTempNum), left, op, right, nullptr, nullptr);
}

QuadPhi* makePhi(int phiTempNum, int initTempNum, int initLabel, int backedgeTempNum, int backedgeLabel) {
    auto args = new vector<pair<Temp*, Label*>>();
    args->push_back({new Temp(backedgeTempNum), new Label(backedgeLabel)});
    args->push_back({new Temp(initTempNum), new Label(initLabel)});
    return new QuadPhi(makeQuadTemp(phiTempNum), args, nullptr, nullptr);
}

int findPreheaderLabel(const BasicInductionVar& basic, const LoopHeader& loopHeader) {
    QuadPhi* phi = dynamic_cast<QuadPhi*>(basic.phiStm);
    if (phi == nullptr || phi->args == nullptr) {
        return -1;
    }
    for (const auto& arg : *phi->args) {
        if (arg.second != nullptr && !loopHeader.bodyBlocks.count(arg.second->num)) {
            return arg.second->num;
        }
    }
    return -1;
}

int findBackedgeLabel(const BasicInductionVar& basic, const LoopHeader& loopHeader) {
    QuadPhi* phi = dynamic_cast<QuadPhi*>(basic.phiStm);
    if (phi == nullptr || phi->args == nullptr) {
        return -1;
    }
    for (const auto& arg : *phi->args) {
        if (arg.second != nullptr && loopHeader.bodyBlocks.count(arg.second->num)) {
            return arg.second->num;
        }
    }
    return -1;
}

void replaceTempInTerm(QuadTerm* term, const map<int, int>& replacements) {
    if (term == nullptr || term->kind != QuadTermKind::TEMP) {
        return;
    }
    QuadTemp* quadTemp = term->get_temp();
    if (quadTemp == nullptr || quadTemp->temp == nullptr) {
        return;
    }
    auto it = replacements.find(quadTemp->temp->num);
    if (it != replacements.end()) {
        quadTemp->temp->num = it->second;
    }
}

void replaceTempsInUses(QuadStm* stm, const map<int, int>& replacements) {
    if (stm == nullptr || replacements.empty()) {
        return;
    }
    switch (stm->kind) {
        case QuadKind::MOVE: {
            QuadMove* move = dynamic_cast<QuadMove*>(stm);
            if (move != nullptr) {
                replaceTempInTerm(move->src, replacements);
            }
            break;
        }
        case QuadKind::LOAD: {
            QuadLoad* load = dynamic_cast<QuadLoad*>(stm);
            if (load != nullptr) {
                replaceTempInTerm(load->src, replacements);
            }
            break;
        }
        case QuadKind::STORE: {
            QuadStore* store = dynamic_cast<QuadStore*>(stm);
            if (store != nullptr) {
                replaceTempInTerm(store->src, replacements);
                replaceTempInTerm(store->dst, replacements);
            }
            break;
        }
        case QuadKind::MOVE_BINOP: {
            QuadMoveBinop* binop = dynamic_cast<QuadMoveBinop*>(stm);
            if (binop != nullptr) {
                replaceTempInTerm(binop->left, replacements);
                replaceTempInTerm(binop->right, replacements);
            }
            break;
        }
        case QuadKind::CALL: {
            QuadCall* call = dynamic_cast<QuadCall*>(stm);
            if (call != nullptr) {
                replaceTempInTerm(call->obj_term, replacements);
                if (call->args != nullptr) {
                    for (QuadTerm* arg : *call->args) {
                        replaceTempInTerm(arg, replacements);
                    }
                }
            }
            break;
        }
        case QuadKind::MOVE_CALL: {
            QuadMoveCall* movecall = dynamic_cast<QuadMoveCall*>(stm);
            if (movecall != nullptr && movecall->call != nullptr) {
                replaceTempInTerm(movecall->call->obj_term, replacements);
                if (movecall->call->args != nullptr) {
                    for (QuadTerm* arg : *movecall->call->args) {
                        replaceTempInTerm(arg, replacements);
                    }
                }
            }
            break;
        }
        case QuadKind::EXTCALL: {
            QuadExtCall* extcall = dynamic_cast<QuadExtCall*>(stm);
            if (extcall != nullptr && extcall->args != nullptr) {
                for (QuadTerm* arg : *extcall->args) {
                    replaceTempInTerm(arg, replacements);
                }
            }
            break;
        }
        case QuadKind::MOVE_EXTCALL: {
            QuadMoveExtCall* moveextcall = dynamic_cast<QuadMoveExtCall*>(stm);
            if (moveextcall != nullptr && moveextcall->extcall != nullptr && moveextcall->extcall->args != nullptr) {
                for (QuadTerm* arg : *moveextcall->extcall->args) {
                    replaceTempInTerm(arg, replacements);
                }
            }
            break;
        }
        case QuadKind::CJUMP: {
            QuadCJump* cjump = dynamic_cast<QuadCJump*>(stm);
            if (cjump != nullptr) {
                replaceTempInTerm(cjump->left, replacements);
                replaceTempInTerm(cjump->right, replacements);
            }
            break;
        }
        case QuadKind::PHI: {
            QuadPhi* phi = dynamic_cast<QuadPhi*>(stm);
            if (phi != nullptr && phi->args != nullptr) {
                for (auto& arg : *phi->args) {
                    if (arg.first != nullptr) {
                        auto it = replacements.find(arg.first->num);
                        if (it != replacements.end()) {
                            arg.first->num = it->second;
                        }
                    }
                }
            }
            break;
        }
        case QuadKind::RETURN: {
            QuadReturn* ret = dynamic_cast<QuadReturn*>(stm);
            if (ret != nullptr) {
                replaceTempInTerm(ret->exp, replacements);
            }
            break;
        }
        case QuadKind::PTR_CALC: {
            QuadPtrCalc* ptrcalc = dynamic_cast<QuadPtrCalc*>(stm);
            if (ptrcalc != nullptr) {
                replaceTempInTerm(ptrcalc->ptr, replacements);
                replaceTempInTerm(ptrcalc->offset, replacements);
            }
            break;
        }
        default:
            break;
    }
}

size_t findTerminatorPosition(const vector<QuadStm*>& stms) {
    if (stms.empty()) {
        return 0;
    }
    size_t pos = stms.size();
    while (pos > 0) {
        QuadKind kind = stms[pos - 1]->kind;
        if (kind == QuadKind::JUMP || kind == QuadKind::CJUMP || kind == QuadKind::RETURN) {
            --pos;
        } else {
            break;
        }
    }
    return pos;
}

vector<QuadStm*> buildInitStatements(const StrengthReductionPlan::ReplacementIV& repl) {
    vector<QuadStm*> stms;

    int currentSourceTemp = repl.initExpr.initTempNum;
    if (repl.initExpr.sourceAfterBasicUpdate) {
        if (repl.initExpr.basicStepTempNum != -1) {
            const string op = (repl.initExpr.basicStepTempNum < 0) ? "-" : "+";
            stms.push_back(makeBinop(
                repl.initTemps.newInitAdjustedSourceTemp,
                makeTempTerm(repl.initExpr.initTempNum),
                op,
                makeTempTerm(abs(repl.initExpr.basicStepTempNum))
            ));
        } else if (repl.initExpr.basicStepValue != 0) {
            const string op = (repl.initExpr.basicStepValue < 0) ? "-" : "+";
            stms.push_back(makeBinop(
                repl.initTemps.newInitAdjustedSourceTemp,
                makeTempTerm(repl.initExpr.initTempNum),
                op,
                makeConstTerm(abs(repl.initExpr.basicStepValue))
            ));
        }
        currentSourceTemp = repl.initTemps.newInitAdjustedSourceTemp;
    }

    int coeff = repl.initExpr.basicCoeff;
    int currentValueTemp = currentSourceTemp;
    if (coeff != 1) {
        int mulDst = (repl.initExpr.constant == 0) ? repl.initTemps.newInitTemp : repl.initTemps.newInitIntermediateTemp;
        stms.push_back(makeBinop(
            mulDst,
            makeTempTerm(currentSourceTemp),
            "*",
            makeConstTerm(coeff)
        ));
        currentValueTemp = mulDst;
    }

    if (repl.initExpr.constant != 0) {
        const string op = (repl.initExpr.constant < 0) ? "-" : "+";
        stms.push_back(makeBinop(
            repl.initTemps.newInitTemp,
            makeTempTerm(currentValueTemp),
            op,
            makeConstTerm(abs(repl.initExpr.constant))
        ));
    } else if (currentValueTemp != repl.initTemps.newInitTemp) {
        stms.push_back(makeMove(repl.initTemps.newInitTemp, makeTempTerm(currentValueTemp)));
    }

    if (repl.stepExpr.newStepTemp != -1) {
        stms.push_back(makeBinop(
            repl.stepExpr.newStepTemp,
            makeTempTerm(repl.stepExpr.stepSourceTempNum),
            "*",
            makeConstTerm(repl.stepExpr.stepTempScaleFactor)
        ));
    }

    return stms;
}

QuadStm* buildUpdateStatement(const StrengthReductionPlan::ReplacementIV& repl) {
    if (repl.stepExpr.stepIncrementTempNum != -1) {
        const string op = repl.stepExpr.stepIncrementNegative ? "-" : "+";
        return makeBinop(
            repl.map.newBackedgeTemp,
            makeTempTerm(repl.map.newPhiTemp),
            op,
            makeTempTerm(repl.stepExpr.stepIncrementTempNum)
        );
    }

    int stepValue = repl.stepExpr.stepIncrementValue;
    if (stepValue == 0) {
        return makeMove(repl.map.newBackedgeTemp, makeTempTerm(repl.map.newPhiTemp));
    }
    const string op = (stepValue < 0) ? "-" : "+";
    return makeBinop(
        repl.map.newBackedgeTemp,
        makeTempTerm(repl.map.newPhiTemp),
        op,
        makeConstTerm(abs(stepValue))
    );
}

void rewriteLoopCondition(QuadBlock* headerBlock, const StrengthReductionPlan::ReplacementIV& repl) {
    if (headerBlock == nullptr || headerBlock->quadlist == nullptr) {
        return;
    }

    int newRightConst = repl.initExpr.constant;
    if (repl.initExpr.sourceAfterBasicUpdate && repl.initExpr.basicStepTempNum == -1) {
        newRightConst += repl.initExpr.basicCoeff * repl.initExpr.basicStepValue;
    }

    for (QuadStm* stm : *headerBlock->quadlist) {
        if (stm == nullptr || stm->kind != QuadKind::CJUMP) {
            continue;
        }
        QuadCJump* cjump = dynamic_cast<QuadCJump*>(stm);
        if (cjump == nullptr) {
            continue;
        }
        int leftTemp = getTempNumFromTerm(cjump->left);
        int rightConst = 0;
        if (leftTemp == repl.map.basicTempNum && getConstFromTerm(cjump->right, rightConst)) {
            cjump->left = makeTempTerm(repl.map.newPhiTemp);
            cjump->right = makeConstTerm(newRightConst);
            return;
        }
    }
}

}  // namespace

StrengthReductionPlan generateStrengthReductionPlan(
    QuadFuncDecl* func,
    const map<int, vector<DerivedInductionVar>>& derivedIVsByHeader,
    const map<int, vector<BasicInductionVar>>& basicIVsByHeader,
    LoopHeaderMap* loopHeaderMap
) {
    StrengthReductionPlan plan;
    
    if (func == nullptr || loopHeaderMap == nullptr || derivedIVsByHeader.empty()) {
        return plan;
    }

    // fill in the code to generate a strength reduction plan based on the discovered basic and derived IVs,
    // and the loop structure in loopHeaderMap. The plan should include which derived IVs to replace with new PHI+update
    // how to compute the new PHI and update values, where to place the new statements, and which original statements to remove.
    set<int> usedTemps = collectAllTemps(func);

    for (const auto& [headerLabel, deriveds] : derivedIVsByHeader) {
        auto basicIt = basicIVsByHeader.find(headerLabel);
        if (basicIt == basicIVsByHeader.end()) {
            continue;
        }

        LoopHeader* loopHeader = findLoopHeader(loopHeaderMap, func, headerLabel);
        if (loopHeader == nullptr) {
            continue;
        }

        vector<DerivedInductionVar> orderedDeriveds = deriveds;
        sort(orderedDeriveds.begin(), orderedDeriveds.end(), [](const DerivedInductionVar& lhs, const DerivedInductionVar& rhs) {
            return lhs.tempNum < rhs.tempNum;
        });

        for (const DerivedInductionVar& derived : orderedDeriveds) {
            const BasicInductionVar* basic = findBasicIV(basicIt->second, derived.expr.basicTempNum);
            if (basic == nullptr) {
                continue;
            }

            StrengthReductionPlan::ReplacementIV repl;
            repl.map.headerLabel = headerLabel;
            repl.map.oldTempNum = derived.tempNum;
            repl.map.basicTempNum = basic->phiTempNum;
            repl.sourceOrder = derived.sourceOrder;
            repl.initExpr.initTempNum = basic->initTempNum;
            repl.initExpr.basicCoeff = derived.expr.basicCoeff;
            repl.initExpr.constant = derived.expr.constant;
            repl.initExpr.sourceAfterBasicUpdate =
                derived.sourceTempNum == basic->backedgeTempNum ||
                (basic->updateOrder >= 0 && derived.sourceOrder != static_cast<size_t>(-1) &&
                 derived.sourceOrder >= static_cast<size_t>(basic->updateOrder));

            int cursor = derived.tempNum + 1;
            repl.map.newPhiTemp = allocateTemp(usedTemps, cursor);
            repl.initTemps.newInitTemp = allocateTemp(usedTemps, cursor);
            repl.map.newBackedgeTemp = allocateTemp(usedTemps, cursor);

            if (repl.initExpr.sourceAfterBasicUpdate) {
                repl.initTemps.newInitAdjustedSourceTemp = allocateTemp(usedTemps, cursor);
            }
            if (repl.initExpr.basicCoeff != 1 && repl.initExpr.constant != 0) {
                repl.initTemps.newInitIntermediateTemp = allocateTemp(usedTemps, cursor);
            }

            if (basic->stepTempNum != -1) {
                repl.initExpr.basicStepTempNum = basic->stepTempNum;
                int signedScale = derived.expr.basicCoeff * ((basic->stepTempNum < 0) ? -1 : 1);
                repl.stepExpr.stepIncrementNegative = signedScale < 0;
                repl.stepExpr.stepTempScaleFactor = abs(signedScale);
                repl.stepExpr.stepSourceTempNum = abs(basic->stepTempNum);
                if (repl.stepExpr.stepTempScaleFactor == 1) {
                    repl.stepExpr.stepIncrementTempNum = repl.stepExpr.stepSourceTempNum;
                } else {
                    repl.stepExpr.newStepTemp = allocateTemp(usedTemps, cursor);
                    repl.stepExpr.stepIncrementTempNum = repl.stepExpr.newStepTemp;
                }
            } else {
                repl.initExpr.basicStepValue = basic->step;
                repl.stepExpr.stepIncrementValue = derived.expr.basicCoeff * basic->step;
            }

            repl.placement.initLabel = findPreheaderLabel(*basic, *loopHeader);
            repl.placement.backedgeLabel = findBackedgeLabel(*basic, *loopHeader);

            if (repl.placement.initLabel == -1 || repl.placement.backedgeLabel == -1) {
                continue;
            }

            plan.tempReplacement[derived.tempNum] = repl.map.newPhiTemp;
            plan.stmtsToRemove.insert(derived.defStm);
            plan.replacements.push_back(repl);
        }
    }

    return plan;
}

QuadFuncDecl* applyStrengthReduction(
    QuadFuncDecl* func,
    const StrengthReductionPlan& plan
) {
    if (func == nullptr || func->quadblocklist == nullptr) {
        return func;
    }

    if (plan.tempReplacement.empty()) {
        return func;
    }
    // fill in the code to apply the strength reduction plan to func,
    // by modifying the quads in the func
    map<int, QuadBlock*> labelToBlock = buildLabelToBlock(func);
    map<int, vector<QuadStm*>> initStmtsByLabel;
    map<int, vector<QuadStm*>> updateStmtsByLabel;
    map<int, vector<QuadStm*>> phiStmtsByHeader;

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (QuadStm* stm : *block->quadlist) {
            replaceTempsInUses(stm, plan.tempReplacement);
        }
    }

    for (const StrengthReductionPlan::ReplacementIV& repl : plan.replacements) {
        initStmtsByLabel[repl.placement.initLabel] = initStmtsByLabel[repl.placement.initLabel];
        vector<QuadStm*> initStmts = buildInitStatements(repl);
        initStmtsByLabel[repl.placement.initLabel].insert(
            initStmtsByLabel[repl.placement.initLabel].end(),
            initStmts.begin(),
            initStmts.end()
        );

        phiStmtsByHeader[repl.map.headerLabel].push_back(
            makePhi(
                repl.map.newPhiTemp,
                repl.initTemps.newInitTemp,
                repl.placement.initLabel,
                repl.map.newBackedgeTemp,
                repl.placement.backedgeLabel
            )
        );
        updateStmtsByLabel[repl.placement.backedgeLabel].push_back(buildUpdateStatement(repl));

        auto headerIt = labelToBlock.find(repl.map.headerLabel);
        if (headerIt != labelToBlock.end()) {
            rewriteLoopCondition(headerIt->second, repl);
        }
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }

        int blockLabel = getBlockLabel(block);
        vector<QuadStm*> filtered;
        filtered.reserve(block->quadlist->size() + 8);
        for (QuadStm* stm : *block->quadlist) {
            if (!plan.stmtsToRemove.count(stm)) {
                filtered.push_back(stm);
            }
        }

        if (phiStmtsByHeader.count(blockLabel)) {
            size_t insertPos = 0;
            while (insertPos < filtered.size() &&
                   (filtered[insertPos]->kind == QuadKind::LABEL || filtered[insertPos]->kind == QuadKind::PHI)) {
                ++insertPos;
            }
            filtered.insert(filtered.begin() + insertPos,
                            phiStmtsByHeader[blockLabel].begin(),
                            phiStmtsByHeader[blockLabel].end());
        }

        if (initStmtsByLabel.count(blockLabel)) {
            size_t insertPos = findTerminatorPosition(filtered);
            filtered.insert(filtered.begin() + insertPos,
                            initStmtsByLabel[blockLabel].begin(),
                            initStmtsByLabel[blockLabel].end());
        }

        if (updateStmtsByLabel.count(blockLabel)) {
            size_t insertPos = findTerminatorPosition(filtered);
            filtered.insert(filtered.begin() + insertPos,
                            updateStmtsByLabel[blockLabel].begin(),
                            updateStmtsByLabel[blockLabel].end());
        }

        block->quadlist = new vector<QuadStm*>(filtered);
    }

    return func;
}
