#include "instrSelection.hh"

#include <cstdint>
#include <limits>
#include <set>
#include <queue>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace instr {

static bool isExitCallStmt(const quad::QuadStm *stm) {
    if (stm == nullptr) {
        return false;
    }

    if (stm->kind == quad::QuadKind::EXTCALL) {
        auto *ext = dynamic_cast<const quad::QuadExtCall *>(stm);
        return ext != nullptr && ext->extfun == "exit";
    }
    if (stm->kind == quad::QuadKind::MOVE_EXTCALL) {
        auto *moveExt = dynamic_cast<const quad::QuadMoveExtCall *>(stm);
        return moveExt != nullptr && moveExt->extcall != nullptr && moveExt->extcall->extfun == "exit";
    }
    if (stm->kind == quad::QuadKind::CALL) {
        auto *call = dynamic_cast<const quad::QuadCall *>(stm);
        return call != nullptr && call->name == "exit";
    }
    if (stm->kind == quad::QuadKind::MOVE_CALL) {
        auto *moveCall = dynamic_cast<const quad::QuadMoveCall *>(stm);
        return moveCall != nullptr && moveCall->call != nullptr && moveCall->call->name == "exit";
    }

    return false;
}

static bool handledInSchedule(const quad::QuadStm *stm) {
    if (stm == nullptr) {
        return false;
    }
    return stm->kind == quad::QuadKind::JUMP ||
           stm->kind == quad::QuadKind::CJUMP ||
           stm->kind == quad::QuadKind::RETURN ||
           isExitCallStmt(stm);
}

static tree::Temp *newSyntheticTemp(int &nextTempNum) {
    return new tree::Temp(nextTempNum++);
}

static bool canUseMovImmediate(int value) {
    return value >= 0 && value <= 255;
}

static void emitLoadImmediate(AssemInstrList &out, tree::Temp *dst, int value) {
    if (dst == nullptr) {
        return;
    }

    uint32_t bits = static_cast<uint32_t>(value);
    uint32_t low = bits & 0xffffu;
    uint32_t high = (bits >> 16) & 0xffffu;

    out.append(AssemInstr::Oper("movw `d0, #" + std::to_string(low), {dst}, {}, AssemTargets()));
    if (high != 0u || value < 0) {
        out.append(AssemInstr::Oper("movt `d0, #" + std::to_string(high), {dst}, {}, AssemTargets()));
    }
}

static tree::Temp *materializeTerm(
    const quad::QuadTerm *term,
    AssemInstrList &out,
    int &nextTempNum
) {
    if (term == nullptr) {
        return nullptr;
    }

    if (term->kind == quad::QuadTermKind::TEMP) {
        auto *quadTemp = const_cast<quad::QuadTerm *>(term)->get_temp();
        return quadTemp == nullptr ? nullptr : quadTemp->temp;
    }

    tree::Temp *tmp = newSyntheticTemp(nextTempNum);
    if (term->kind == quad::QuadTermKind::CONST) {
        emitLoadImmediate(out, tmp, const_cast<quad::QuadTerm *>(term)->get_const());
        return tmp;
    }

    out.append(AssemInstr::Oper(
        "ldr `d0, =" + const_cast<quad::QuadTerm *>(term)->get_name(),
        {tmp},
        {},
        AssemTargets()
    ));
    return tmp;
}

static bool isSmallImmediate(int value) {
    return value >= 0 && value <= 255;
}

static int tempNumOf(const tree::Temp *temp) {
    return temp == nullptr ? -1 : temp->num;
}

static int tempNumOfQuadTemp(const quad::QuadTemp *quadTemp) {
    return quadTemp == nullptr || quadTemp->temp == nullptr ? -1 : quadTemp->temp->num;
}

static int tempNumOfTerm(const quad::QuadTerm *term) {
    if (term == nullptr || term->kind != quad::QuadTermKind::TEMP) {
        return -1;
    }
    auto *quadTemp = const_cast<quad::QuadTerm *>(term)->get_temp();
    return tempNumOfQuadTemp(quadTemp);
}

static bool usesTemp(const quad::QuadStm *stm, int tempNum) {
    if (stm == nullptr || tempNum < 0 || stm->use == nullptr) {
        return false;
    }
    for (auto *temp : *stm->use) {
        if (tempNumOf(temp) == tempNum) {
            return true;
        }
    }
    return false;
}

static size_t countUsesInTail(
    const std::vector<quad::QuadStm*> &statements,
    size_t startIndex,
    int tempNum
) {
    size_t useCount = 0;
    for (size_t index = startIndex; index < statements.size(); ++index) {
        if (usesTemp(statements[index], tempNum)) {
            ++useCount;
        }
    }
    return useCount;
}

static const quad::QuadStm *nextLowerableStatement(
    const std::vector<quad::QuadStm*> &statements,
    size_t startIndex,
    size_t *foundIndex = nullptr
) {
    for (size_t index = startIndex; index < statements.size(); ++index) {
        auto *stm = statements[index];
        if (stm == nullptr || stm->kind == quad::QuadKind::LABEL || stm->kind == quad::QuadKind::PHI) {
            continue;
        }
        if (foundIndex != nullptr) {
            *foundIndex = index;
        }
        return stm;
    }
    return nullptr;
}

static const quad::QuadStm *findUniqueMemoryUser(
    const std::vector<quad::QuadStm*> &statements,
    size_t startIndex,
    int tempNum,
    size_t *foundIndex = nullptr
) {
    for (size_t index = startIndex; index < statements.size(); ++index) {
        auto *stm = statements[index];
        if (stm == nullptr || stm->kind == quad::QuadKind::LABEL || stm->kind == quad::QuadKind::PHI) {
            continue;
        }
        if (!usesTemp(stm, tempNum)) {
            continue;
        }

        if (stm->kind == quad::QuadKind::LOAD) {
            auto *load = dynamic_cast<const quad::QuadLoad *>(stm);
            if (load != nullptr && tempNumOfTerm(load->src) == tempNum) {
                if (foundIndex != nullptr) {
                    *foundIndex = index;
                }
                return stm;
            }
            return nullptr;
        }

        if (stm->kind == quad::QuadKind::STORE) {
            auto *store = dynamic_cast<const quad::QuadStore *>(stm);
            if (store != nullptr && tempNumOfTerm(store->dst) == tempNum) {
                if (foundIndex != nullptr) {
                    *foundIndex = index;
                }
                return stm;
            }
            return nullptr;
        }

        return nullptr;
    }

    return nullptr;
}

static bool emitFoldedLoadStore(
    const quad::QuadPtrCalc *ptrCalc,
    const quad::QuadStm *memoryStm,
    preScheduleBlock &schedBlock,
    int &nextTempNum
) {
    if (ptrCalc == nullptr || memoryStm == nullptr || ptrCalc->ptr == nullptr || ptrCalc->offset == nullptr) {
        return false;
    }

    tree::Temp *base = materializeTerm(ptrCalc->ptr, schedBlock.selectedInstructions, nextTempNum);
    if (base == nullptr) {
        return false;
    }

    auto emitLoad = [&](tree::Temp *dst, const std::string &addrSuffix, const std::vector<tree::Temp*> &srcTemps) {
        if (dst == nullptr) {
            return false;
        }
        schedBlock.selectedInstructions.append(
            AssemInstr::Oper("ldr `d0, [" + addrSuffix + "]", {dst}, srcTemps, AssemTargets())
        );
        return true;
    };

    auto emitStore = [&](tree::Temp *src, const std::string &addrSuffix, const std::vector<tree::Temp*> &srcTemps) {
        if (src == nullptr) {
            return false;
        }
        std::vector<tree::Temp*> operands;
        operands.push_back(src);
        operands.insert(operands.end(), srcTemps.begin(), srcTemps.end());
        schedBlock.selectedInstructions.append(
            AssemInstr::Oper("str `s0, [" + addrSuffix + "]", {}, operands, AssemTargets())
        );
        return true;
    };

    if (ptrCalc->offset->kind == quad::QuadTermKind::CONST) {
        int offset = ptrCalc->offset->get_const();
        if (!isSmallImmediate(offset) && offset != 0) {
            return false;
        }

        if (memoryStm->kind == quad::QuadKind::LOAD) {
            std::string addrSuffix = offset == 0 ? "`s0" : "`s0, #" + std::to_string(offset);
            auto *load = dynamic_cast<const quad::QuadLoad *>(memoryStm);
            return load != nullptr && load->dst != nullptr && emitLoad(load->dst->temp, addrSuffix, {base});
        }
        if (memoryStm->kind == quad::QuadKind::STORE) {
            std::string addrSuffix = offset == 0 ? "`s1" : "`s1, #" + std::to_string(offset);
            auto *store = dynamic_cast<const quad::QuadStore *>(memoryStm);
            tree::Temp *src = store == nullptr ? nullptr : materializeTerm(store->src, schedBlock.selectedInstructions, nextTempNum);
            return emitStore(src, addrSuffix, {base});
        }
        return false;
    }

    tree::Temp *offset = materializeTerm(ptrCalc->offset, schedBlock.selectedInstructions, nextTempNum);
    if (offset == nullptr) {
        return false;
    }

    if (memoryStm->kind == quad::QuadKind::LOAD) {
        auto *load = dynamic_cast<const quad::QuadLoad *>(memoryStm);
        return load != nullptr && load->dst != nullptr && emitLoad(load->dst->temp, "`s0, `s1", {base, offset});
    }
    if (memoryStm->kind == quad::QuadKind::STORE) {
        auto *store = dynamic_cast<const quad::QuadStore *>(memoryStm);
        tree::Temp *src = store == nullptr ? nullptr : materializeTerm(store->src, schedBlock.selectedInstructions, nextTempNum);
        return emitStore(src, "`s1, `s2", {base, offset});
    }
    return false;
}

static bool tryFoldPtrCalcMemoryAccess(
    const std::vector<quad::QuadStm*> &statements,
    size_t index,
    preScheduleBlock &schedBlock,
    int &nextTempNum,
    size_t *consumedUntil
) {
    if (index >= statements.size()) {
        return false;
    }

    auto *ptrCalc = dynamic_cast<const quad::QuadPtrCalc *>(statements[index]);
    if (ptrCalc == nullptr) {
        return false;
    }

    int addrTempNum = tempNumOfTerm(ptrCalc->dst);
    if (addrTempNum < 0) {
        return false;
    }

    size_t nextIndex = index + 1;
    const quad::QuadStm *nextStm = findUniqueMemoryUser(statements, index + 1, addrTempNum, &nextIndex);
    if (nextStm == nullptr) {
        return false;
    }

    if (countUsesInTail(statements, index + 1, addrTempNum) != 1) {
        return false;
    }

    if (!emitFoldedLoadStore(ptrCalc, nextStm, schedBlock, nextTempNum)) {
        return false;
    }

    if (consumedUntil != nullptr) {
        *consumedUntil = nextIndex;
    }
    return true;
}

static void emitMoveToArgumentRegister(
    AssemInstrList &out,
    int argIndex,
    tree::Temp *src
) {
    if (src == nullptr || argIndex < 0 || argIndex > 3) {
        return;
    }
    out.append(AssemInstr::Oper(
        "mov r" + std::to_string(argIndex) + ", `s0",
        {},
        {src},
        AssemTargets()
    ));
}

static void lowerCallArguments(
    const std::vector<quad::QuadTerm*> *args,
    AssemInstrList &out,
    int &nextTempNum
) {
    if (args == nullptr) {
        return;
    }

    int argIndex = 0;
    for (auto *arg : *args) {
        if (argIndex >= 4) {
            break;
        }
        tree::Temp *argTemp = materializeTerm(arg, out, nextTempNum);
        emitMoveToArgumentRegister(out, argIndex, argTemp);
        ++argIndex;
    }
}

static void lowerCallLike(
    const quad::QuadCall *call,
    AssemInstrList &out,
    int &nextTempNum,
    tree::Temp *resultDst
) {
    if (call == nullptr) {
        return;
    }

    lowerCallArguments(call->args, out, nextTempNum);

    if (call->obj_term != nullptr) {
        tree::Temp *callee = materializeTerm(call->obj_term, out, nextTempNum);
        out.append(AssemInstr::Oper("blx `s0", {}, {callee}, AssemTargets()));
    } else {
        out.append(AssemInstr::Oper("bl " + call->name, {}, {}, AssemTargets()));
    }

    if (resultDst != nullptr) {
        out.append(AssemInstr::Move("mov `d0, r0", {resultDst}, {}));
    }
}

static void lowerExtCallLike(
    const quad::QuadExtCall *call,
    AssemInstrList &out,
    int &nextTempNum,
    tree::Temp *resultDst
) {
    if (call == nullptr) {
        return;
    }

    lowerCallArguments(call->args, out, nextTempNum);
    out.append(AssemInstr::Oper("bl " + call->extfun, {}, {}, AssemTargets()));

    if (resultDst != nullptr) {
        out.append(AssemInstr::Move("mov `d0, r0", {resultDst}, {}));
    }
}

static void lowerStatement(
    const quad::QuadStm *stm,
    preScheduleBlock &schedBlock,
    int &nextTempNum
) {
    if (stm == nullptr) {
        return;
    }

    auto &out = schedBlock.selectedInstructions;

    switch (stm->kind) {
        case quad::QuadKind::MOVE: {
            auto *move = dynamic_cast<const quad::QuadMove *>(stm);
            if (move == nullptr || move->dst == nullptr || move->dst->temp == nullptr || move->src == nullptr) {
                return;
            }
            if (move->src->kind == quad::QuadTermKind::TEMP) {
                auto *src = move->src->get_temp();
                if (src != nullptr && src->temp != nullptr) {
                    out.append(AssemInstr::Move("mov `d0, `s0", {move->dst->temp}, {src->temp}));
                }
                return;
            }
            if (move->src->kind == quad::QuadTermKind::CONST) {
                int value = move->src->get_const();
                if (canUseMovImmediate(value)) {
                    out.append(AssemInstr::Oper(
                        "mov `d0, #" + std::to_string(value),
                        {move->dst->temp},
                        {},
                        AssemTargets()
                    ));
                } else {
                    emitLoadImmediate(out, move->dst->temp, value);
                }
                return;
            }
            out.append(AssemInstr::Oper(
                "ldr `d0, =" + move->src->get_name(),
                {move->dst->temp},
                {},
                AssemTargets()
            ));
            return;
        }
        case quad::QuadKind::LOAD: {
            auto *load = dynamic_cast<const quad::QuadLoad *>(stm);
            if (load == nullptr || load->dst == nullptr || load->dst->temp == nullptr) {
                return;
            }
            tree::Temp *addr = materializeTerm(load->src, out, nextTempNum);
            if (addr != nullptr) {
                out.append(AssemInstr::Oper("ldr `d0, [`s0]", {load->dst->temp}, {addr}, AssemTargets()));
            }
            return;
        }
        case quad::QuadKind::STORE: {
            auto *store = dynamic_cast<const quad::QuadStore *>(stm);
            if (store == nullptr) {
                return;
            }
            tree::Temp *src = materializeTerm(store->src, out, nextTempNum);
            tree::Temp *dst = materializeTerm(store->dst, out, nextTempNum);
            if (src != nullptr && dst != nullptr) {
                out.append(AssemInstr::Oper("str `s0, [`s1]", {}, {src, dst}, AssemTargets()));
            }
            return;
        }
        case quad::QuadKind::PTR_CALC: {
            auto *ptrCalc = dynamic_cast<const quad::QuadPtrCalc *>(stm);
            if (ptrCalc == nullptr || ptrCalc->dst == nullptr || ptrCalc->ptr == nullptr || ptrCalc->offset == nullptr) {
                return;
            }
            tree::Temp *dst = materializeTerm(ptrCalc->dst, out, nextTempNum);
            tree::Temp *base = materializeTerm(ptrCalc->ptr, out, nextTempNum);
            if (dst == nullptr || base == nullptr) {
                return;
            }

            if (ptrCalc->offset->kind == quad::QuadTermKind::CONST) {
                int offset = ptrCalc->offset->get_const();
                if (offset == 0) {
                    out.append(AssemInstr::Move("mov `d0, `s0", {dst}, {base}));
                } else if (isSmallImmediate(offset)) {
                    out.append(AssemInstr::Oper(
                        "add `d0, `s0, #" + std::to_string(offset),
                        {dst},
                        {base},
                        AssemTargets()
                    ));
                } else {
                    tree::Temp *offsetTemp = newSyntheticTemp(nextTempNum);
                    emitLoadImmediate(out, offsetTemp, offset);
                    out.append(AssemInstr::Oper("add `d0, `s0, `s1", {dst}, {base, offsetTemp}, AssemTargets()));
                }
                return;
            }

            tree::Temp *offset = materializeTerm(ptrCalc->offset, out, nextTempNum);
            if (offset != nullptr) {
                out.append(AssemInstr::Oper("add `d0, `s0, `s1", {dst}, {base, offset}, AssemTargets()));
            }
            return;
        }
        case quad::QuadKind::MOVE_BINOP: {
            auto *binop = dynamic_cast<const quad::QuadMoveBinop *>(stm);
            if (binop == nullptr || binop->dst == nullptr || binop->dst->temp == nullptr ||
                binop->left == nullptr || binop->right == nullptr) {
                return;
            }

            const std::string &op = binop->binop;
            if ((op == "+" || op == "-") && binop->right->kind == quad::QuadTermKind::CONST) {
                tree::Temp *left = materializeTerm(binop->left, out, nextTempNum);
                int imm = binop->right->get_const();
                if (left != nullptr && isSmallImmediate(imm)) {
                    out.append(AssemInstr::Oper(
                        std::string(op == "+" ? "add " : "sub ") + "`d0, `s0, #" + std::to_string(imm),
                        {binop->dst->temp},
                        {left},
                        AssemTargets()
                    ));
                    return;
                }
            }

            tree::Temp *left = materializeTerm(binop->left, out, nextTempNum);
            tree::Temp *right = materializeTerm(binop->right, out, nextTempNum);
            if (left == nullptr || right == nullptr) {
                return;
            }

            std::string opcode;
            if (op == "+") {
                opcode = "add";
            } else if (op == "-") {
                opcode = "sub";
            } else if (op == "*") {
                opcode = "mul";
            } else if (op == "/") {
                opcode = "sdiv";
            } else {
                opcode = "add";
            }

            out.append(AssemInstr::Oper(
                opcode + " `d0, `s0, `s1",
                {binop->dst->temp},
                {left, right},
                AssemTargets()
            ));
            return;
        }
        case quad::QuadKind::CALL: {
            lowerCallLike(dynamic_cast<const quad::QuadCall *>(stm), out, nextTempNum, nullptr);
            return;
        }
        case quad::QuadKind::MOVE_CALL: {
            auto *moveCall = dynamic_cast<const quad::QuadMoveCall *>(stm);
            if (moveCall != nullptr && moveCall->dst != nullptr) {
                lowerCallLike(moveCall->call, out, nextTempNum, moveCall->dst->temp);
            }
            return;
        }
        case quad::QuadKind::EXTCALL: {
            lowerExtCallLike(dynamic_cast<const quad::QuadExtCall *>(stm), out, nextTempNum, nullptr);
            return;
        }
        case quad::QuadKind::MOVE_EXTCALL: {
            auto *moveExtCall = dynamic_cast<const quad::QuadMoveExtCall *>(stm);
            if (moveExtCall != nullptr && moveExtCall->dst != nullptr) {
                lowerExtCallLike(moveExtCall->extcall, out, nextTempNum, moveExtCall->dst->temp);
            }
            return;
        }
        default:
            return;
    }
}

// Main instruction selection for a block
void selectInstructionsForBlock(
    const advDFGblock &blockGraph,
    preScheduleBlock &schedBlock,
    int &nextTempNum
) {
    const auto& graph = blockGraph.graph;
    const auto& nodes = graph.getNodes();
    if (nodes.empty()) {
        return;
    }

    //fill in necessary code 

    if (blockGraph.quadBlock == nullptr || blockGraph.quadBlock->quadlist == nullptr) {
        return;
    }

    const auto &statements = *blockGraph.quadBlock->quadlist;
    for (size_t index = 0; index < statements.size(); ++index) {
        auto *stm = statements[index];
        if (stm == nullptr || stm->kind == quad::QuadKind::LABEL || stm->kind == quad::QuadKind::PHI) {
            continue;
        }
        if (stm == schedBlock.lastInstruction && handledInSchedule(stm)) {
            continue;
        }

        size_t consumedUntil = index;
        if (tryFoldPtrCalcMemoryAccess(statements, index, schedBlock, nextTempNum, &consumedUntil)) {
            index = consumedUntil;
            continue;
        }

        lowerStatement(stm, schedBlock, nextTempNum);
    }

    return;
}

void runInstructionSelectionPass(
    const advDFGprog &graphProgram,
    preScheduleProg &preScheduleProgram
) {
    size_t funcCount = std::min(graphProgram.fungraph.size(), preScheduleProgram.funcSchedules.size());
    for (size_t funcIndex = 0; funcIndex < funcCount; ++funcIndex) {
        auto *funcGraph = graphProgram.fungraph[funcIndex];
        auto *funcSchedule = preScheduleProgram.funcSchedules[funcIndex];
        if (funcGraph == nullptr || funcSchedule == nullptr || funcSchedule->quadFunc == nullptr) {
            continue;
        }

        int nextTempNum = funcSchedule->quadFunc->last_temp_num + 1;
        size_t blockCount = std::min(funcGraph->blockgraph.size(), funcSchedule->blockSchedules.size());
        for (size_t blockIndex = 0; blockIndex < blockCount; ++blockIndex) {
            auto *blockGraph = funcGraph->blockgraph[blockIndex];
            auto *blockSchedule = funcSchedule->blockSchedules[blockIndex];
            if (blockGraph == nullptr || blockSchedule == nullptr) {
                continue;
            }

            selectInstructionsForBlock(*blockGraph, *blockSchedule, nextTempNum);
        }

        auto *mutableFunc = const_cast<quad::QuadFuncDecl*>(funcSchedule->quadFunc);
        mutableFunc->last_temp_num = nextTempNum - 1;
    }
}

} // namespace instr
