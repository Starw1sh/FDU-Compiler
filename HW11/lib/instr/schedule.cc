#include "schedule.hh"

#include "advDFG.hh"
#include "instrSelection.hh"

#include <algorithm>
#include <functional>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace instr {

static bool sameLabel(const tree::Label *lhs, const tree::Label *rhs) {
    return lhs != nullptr && rhs != nullptr && lhs->num == rhs->num;
}

static bool sameTemp(const tree::Temp *lhs, const tree::Temp *rhs) {
    return lhs != nullptr && rhs != nullptr && lhs->num == rhs->num;
}

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

static tree::Temp *newSyntheticTemp(int &nextTempNum) {
    return new tree::Temp(nextTempNum++);
}

static tree::Label *newSyntheticLabel(int &nextLabelNum) {
    return new tree::Label(nextLabelNum++);
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

static std::string condForRelop(const std::string &relop) {
    if (relop == "==") return "eq";
    if (relop == "!=") return "ne";
    if (relop == ">") return "gt";
    if (relop == "<") return "lt";
    if (relop == ">=") return "ge";
    if (relop == "<=") return "le";
    return "eq";
}

static std::string inverseCond(const std::string &cond) {
    if (cond == "eq") return "ne";
    if (cond == "ne") return "eq";
    if (cond == "gt") return "le";
    if (cond == "lt") return "ge";
    if (cond == "ge") return "lt";
    if (cond == "le") return "gt";
    return "ne";
}

static void emitArgumentMoves(
    const std::vector<quad::QuadTerm*> *args,
    AssemInstrList &out,
    int &nextTempNum
) {
    if (args == nullptr) {
        return;
    }

    for (size_t index = 0; index < args->size() && index < 4; ++index) {
        tree::Temp *tmp = materializeTerm((*args)[index], out, nextTempNum);
        if (tmp != nullptr) {
            out.append(AssemInstr::Oper(
                "mov r" + std::to_string(index) + ", `s0",
                {},
                {tmp},
                AssemTargets()
            ));
        }
    }
}

static void emitCallLike(
    const quad::QuadCall *call,
    AssemInstrList &out,
    int &nextTempNum,
    tree::Temp *resultDst
) {
    if (call == nullptr) {
        return;
    }
    emitArgumentMoves(call->args, out, nextTempNum);
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

static void emitExtCallLike(
    const quad::QuadExtCall *call,
    AssemInstrList &out,
    int &nextTempNum,
    tree::Temp *resultDst
) {
    if (call == nullptr) {
        return;
    }
    emitArgumentMoves(call->args, out, nextTempNum);
    out.append(AssemInstr::Oper("bl " + call->extfun, {}, {}, AssemTargets()));
    if (resultDst != nullptr) {
        out.append(AssemInstr::Move("mov `d0, r0", {resultDst}, {}));
    }
}

static void emitEpilogue(AssemInstrList &out) {
    out.append(AssemInstr::Oper("sub sp, fp, #36", {}, {}, AssemTargets()));
    out.append(AssemInstr::Oper("add sp, sp, #4", {}, {}, AssemTargets()));
    out.append(AssemInstr::Oper("pop {r4-r10, fp, lr}", {}, {}, AssemTargets()));
    out.append(AssemInstr::Oper("bx lr", {}, {}, AssemTargets()));
}

static void emitParallelMoves(
    const std::vector<std::pair<tree::Temp*, tree::Temp*>> &copies,
    AssemInstrList &out,
    int &nextTempNum
) {
    std::vector<std::pair<tree::Temp*, tree::Temp*>> pending;
    pending.reserve(copies.size());
    for (const auto &copy : copies) {
        if (copy.first == nullptr || copy.second == nullptr || sameTemp(copy.first, copy.second)) {
            continue;
        }
        pending.push_back(copy);
    }

    while (!pending.empty()) {
        bool progressed = false;
        for (size_t index = 0; index < pending.size(); ++index) {
            tree::Temp *dst = pending[index].first;
            bool dstUsedAsSrc = false;
            for (size_t other = 0; other < pending.size(); ++other) {
                if (index != other && sameTemp(dst, pending[other].second)) {
                    dstUsedAsSrc = true;
                    break;
                }
            }
            if (dstUsedAsSrc) {
                continue;
            }

            out.append(AssemInstr::Move("mov `d0, `s0", {pending[index].first}, {pending[index].second}));
            pending.erase(pending.begin() + static_cast<long>(index));
            progressed = true;
            break;
        }

        if (progressed) {
            continue;
        }

        tree::Temp *scratch = newSyntheticTemp(nextTempNum);
        tree::Temp *savedSrc = pending.front().second;
        out.append(AssemInstr::Move("mov `d0, `s0", {scratch}, {savedSrc}));
        for (auto &copy : pending) {
            if (sameTemp(copy.second, savedSrc)) {
                copy.second = scratch;
            }
        }
    }
}

static void emitPhiMovesForEdge(
    const preScheduleBlock *targetBlock,
    const tree::Label *fromLabel,
    AssemInstrList &out,
    int &nextTempNum
) {
    if (targetBlock == nullptr || fromLabel == nullptr) {
        return;
    }

    std::vector<std::pair<tree::Temp*, tree::Temp*>> copies;
    for (auto *phi : targetBlock->phiFunctions) {
        if (phi == nullptr || phi->temp_exp == nullptr || phi->temp_exp->temp == nullptr || phi->args == nullptr) {
            continue;
        }

        for (const auto &arg : *phi->args) {
            if (arg.second != nullptr && arg.second->num == fromLabel->num && arg.first != nullptr) {
                copies.push_back({phi->temp_exp->temp, arg.first});
                break;
            }
        }
    }

    emitParallelMoves(copies, out, nextTempNum);
}

static std::vector<preScheduleBlock*> orderBlocks(const preScheduleFunc *funcSchedule) {
    std::vector<preScheduleBlock*> order;
    if (funcSchedule == nullptr) {
        return order;
    }

    std::unordered_map<int, preScheduleBlock*> byLabel;
    for (auto *block : funcSchedule->blockSchedules) {
        if (block != nullptr && block->entryLabel != nullptr) {
            byLabel[block->entryLabel->num] = block;
        }
    }

    std::unordered_set<int> visited;
    std::function<void(preScheduleBlock*)> dfs = [&](preScheduleBlock *block) {
        if (block == nullptr || block->entryLabel == nullptr || visited.count(block->entryLabel->num) != 0) {
            return;
        }
        visited.insert(block->entryLabel->num);
        order.push_back(block);

        const quad::QuadStm *last = block->lastInstruction;
        if (last != nullptr && last->kind == quad::QuadKind::CJUMP) {
            auto *cjump = dynamic_cast<const quad::QuadCJump *>(last);
            if (cjump != nullptr) {
                dfs(byLabel[cjump->f == nullptr ? -1 : cjump->f->num]);
                dfs(byLabel[cjump->t == nullptr ? -1 : cjump->t->num]);
                return;
            }
        }
        if (last != nullptr && last->kind == quad::QuadKind::JUMP) {
            auto *jump = dynamic_cast<const quad::QuadJump *>(last);
            if (jump != nullptr) {
                dfs(byLabel[jump->label == nullptr ? -1 : jump->label->num]);
                return;
            }
        }
        if (block->quadBlock != nullptr && block->quadBlock->exit_labels != nullptr) {
            for (auto *label : *block->quadBlock->exit_labels) {
                dfs(byLabel[label == nullptr ? -1 : label->num]);
            }
        }
    };

    if (!funcSchedule->blockSchedules.empty()) {
        dfs(funcSchedule->blockSchedules.front());
    }
    for (auto *block : funcSchedule->blockSchedules) {
        dfs(block);
    }

    return order;
}

ScheduleProg *scheduleProg(preScheduleProg *preScheduleProgram) {
    if (preScheduleProgram == nullptr) {
        return nullptr;
    }

    auto *out = new ScheduleProg(preScheduleProgram->quadProgram);

    // fill in the code ... 

    for (auto *funcSchedule : preScheduleProgram->funcSchedules) {
        if (funcSchedule == nullptr || funcSchedule->quadFunc == nullptr) {
            continue;
        }

        auto *scheduledFunc = new ScheduleFunc(funcSchedule->quadFunc);
        out->addFunc(scheduledFunc);

        std::vector<preScheduleBlock*> orderedBlocks = orderBlocks(funcSchedule);
        std::unordered_map<int, preScheduleBlock*> byLabel;
        for (auto *block : funcSchedule->blockSchedules) {
            if (block != nullptr && block->entryLabel != nullptr) {
                byLabel[block->entryLabel->num] = block;
            }
        }

        int nextTempNum = funcSchedule->quadFunc->last_temp_num + 1;
        int nextLabelNum = std::max(
            preScheduleProgram->quadProgram == nullptr ? -1 : preScheduleProgram->quadProgram->last_label_num,
            funcSchedule->quadFunc->last_label_num
        ) + 1;

        for (size_t blockIndex = 0; blockIndex < orderedBlocks.size(); ++blockIndex) {
            preScheduleBlock *block = orderedBlocks[blockIndex];
            if (block == nullptr || block->entryLabel == nullptr) {
                continue;
            }

            tree::Label *nextLabel = nullptr;
            if (blockIndex + 1 < orderedBlocks.size() && orderedBlocks[blockIndex + 1] != nullptr) {
                nextLabel = orderedBlocks[blockIndex + 1]->entryLabel;
            }

            scheduledFunc->addLinearizedInstruction(
                AssemInstr::Label(block->entryLabel->str() + ":", block->entryLabel)
            );

            if (blockIndex == 0) {
                scheduledFunc->addLinearizedInstruction(AssemInstr::Oper("push {r4-r10, fp, lr}", {}, {}, AssemTargets()));
                scheduledFunc->addLinearizedInstruction(AssemInstr::Oper("sub sp, sp, #4", {}, {}, AssemTargets()));
                scheduledFunc->addLinearizedInstruction(AssemInstr::Oper("add fp, sp, #36", {}, {}, AssemTargets()));

                if (funcSchedule->quadFunc->params != nullptr) {
                    for (size_t paramIndex = 0; paramIndex < funcSchedule->quadFunc->params->size() && paramIndex < 4; ++paramIndex) {
                        tree::Temp *param = (*funcSchedule->quadFunc->params)[paramIndex];
                        if (param != nullptr) {
                            scheduledFunc->addLinearizedInstruction(
                                AssemInstr::Move(
                                    "mov `d0, r" + std::to_string(paramIndex),
                                    {param},
                                    {}
                                )
                            );
                        }
                    }
                }
            }

            scheduledFunc->linearizedInstructions.extend(block->selectedInstructions);

            const quad::QuadStm *last = block->lastInstruction;
            if (last == nullptr) {
                continue;
            }

            if (last->kind == quad::QuadKind::RETURN) {
                auto *ret = dynamic_cast<const quad::QuadReturn *>(last);
                tree::Temp *retTemp = materializeTerm(ret == nullptr ? nullptr : ret->exp, scheduledFunc->linearizedInstructions, nextTempNum);
                if (retTemp != nullptr) {
                    scheduledFunc->addLinearizedInstruction(AssemInstr::Oper("mov r0, `s0", {}, {retTemp}, AssemTargets()));
                }
                emitEpilogue(scheduledFunc->linearizedInstructions);
                continue;
            }

            if (last->kind == quad::QuadKind::JUMP) {
                auto *jump = dynamic_cast<const quad::QuadJump *>(last);
                preScheduleBlock *targetBlock = jump == nullptr || jump->label == nullptr ? nullptr : byLabel[jump->label->num];
                emitPhiMovesForEdge(targetBlock, block->entryLabel, scheduledFunc->linearizedInstructions, nextTempNum);
                if (jump != nullptr && jump->label != nullptr && !sameLabel(jump->label, nextLabel)) {
                    scheduledFunc->addLinearizedInstruction(
                        AssemInstr::Oper(
                            "b `j0",
                            {},
                            {},
                            AssemTargets({jump->label})
                        )
                    );
                }
                continue;
            }

            if (last->kind == quad::QuadKind::CJUMP) {
                auto *cjump = dynamic_cast<const quad::QuadCJump *>(last);
                if (cjump == nullptr) {
                    continue;
                }

                tree::Temp *left = materializeTerm(cjump->left, scheduledFunc->linearizedInstructions, nextTempNum);
                tree::Temp *right = materializeTerm(cjump->right, scheduledFunc->linearizedInstructions, nextTempNum);
                if (left != nullptr && right != nullptr) {
                    scheduledFunc->addLinearizedInstruction(AssemInstr::Oper("cmp `s0, `s1", {}, {left, right}, AssemTargets()));
                }

                preScheduleBlock *trueBlock = cjump->t == nullptr ? nullptr : byLabel[cjump->t->num];
                preScheduleBlock *falseBlock = cjump->f == nullptr ? nullptr : byLabel[cjump->f->num];
                std::string cond = condForRelop(cjump->relop);

                if (sameLabel(nextLabel, cjump->f)) {
                    scheduledFunc->addLinearizedInstruction(
                        AssemInstr::Oper(
                            "b" + cond + " `j0",
                            {},
                            {},
                            AssemTargets({cjump->t})
                        )
                    );
                    emitPhiMovesForEdge(falseBlock, block->entryLabel, scheduledFunc->linearizedInstructions, nextTempNum);
                    continue;
                }

                if (sameLabel(nextLabel, cjump->t)) {
                    scheduledFunc->addLinearizedInstruction(
                        AssemInstr::Oper(
                            "b" + inverseCond(cond) + " `j0",
                            {},
                            {},
                            AssemTargets({cjump->f})
                        )
                    );
                    emitPhiMovesForEdge(trueBlock, block->entryLabel, scheduledFunc->linearizedInstructions, nextTempNum);
                    continue;
                }

                tree::Label *trueBridge = newSyntheticLabel(nextLabelNum);
                scheduledFunc->addLinearizedInstruction(
                    AssemInstr::Oper(
                        "b" + cond + " `j0",
                        {},
                        {},
                        AssemTargets({trueBridge})
                    )
                );
                emitPhiMovesForEdge(falseBlock, block->entryLabel, scheduledFunc->linearizedInstructions, nextTempNum);
                if (cjump->f != nullptr) {
                    scheduledFunc->addLinearizedInstruction(
                        AssemInstr::Oper("b `j0", {}, {}, AssemTargets({cjump->f}))
                    );
                }
                scheduledFunc->addLinearizedInstruction(AssemInstr::Label(trueBridge->str() + ":", trueBridge));
                emitPhiMovesForEdge(trueBlock, block->entryLabel, scheduledFunc->linearizedInstructions, nextTempNum);
                if (cjump->t != nullptr) {
                    scheduledFunc->addLinearizedInstruction(
                        AssemInstr::Oper("b `j0", {}, {}, AssemTargets({cjump->t}))
                    );
                }
                continue;
            }

            if (isExitCallStmt(last)) {
                if (last->kind == quad::QuadKind::EXTCALL) {
                    emitExtCallLike(dynamic_cast<const quad::QuadExtCall *>(last), scheduledFunc->linearizedInstructions, nextTempNum, nullptr);
                } else if (last->kind == quad::QuadKind::MOVE_EXTCALL) {
                    auto *moveExt = dynamic_cast<const quad::QuadMoveExtCall *>(last);
                    emitExtCallLike(moveExt == nullptr ? nullptr : moveExt->extcall, scheduledFunc->linearizedInstructions, nextTempNum, nullptr);
                } else if (last->kind == quad::QuadKind::CALL) {
                    emitCallLike(dynamic_cast<const quad::QuadCall *>(last), scheduledFunc->linearizedInstructions, nextTempNum, nullptr);
                } else if (last->kind == quad::QuadKind::MOVE_CALL) {
                    auto *moveCall = dynamic_cast<const quad::QuadMoveCall *>(last);
                    emitCallLike(moveCall == nullptr ? nullptr : moveCall->call, scheduledFunc->linearizedInstructions, nextTempNum, nullptr);
                }
            }
        }
    }

    return out;
}

} // namespace instr
