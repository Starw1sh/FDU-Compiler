#include "loopinductionopt.hh"
#include "defusechain.hh"
#include <queue>
#include <set>

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

int getDefinedTemp(QuadStm* stm) {
    if (stm == nullptr) {
        return -1;
    }
    switch (stm->kind) {
        case QuadKind::MOVE: {
            QuadMove* move = dynamic_cast<QuadMove*>(stm);
            return (move != nullptr && move->dst != nullptr && move->dst->temp != nullptr) ? move->dst->temp->num : -1;
        }
        case QuadKind::LOAD: {
            QuadLoad* load = dynamic_cast<QuadLoad*>(stm);
            return (load != nullptr && load->dst != nullptr && load->dst->temp != nullptr) ? load->dst->temp->num : -1;
        }
        case QuadKind::MOVE_BINOP: {
            QuadMoveBinop* binop = dynamic_cast<QuadMoveBinop*>(stm);
            return (binop != nullptr && binop->dst != nullptr && binop->dst->temp != nullptr) ? binop->dst->temp->num : -1;
        }
        case QuadKind::PHI: {
            QuadPhi* phi = dynamic_cast<QuadPhi*>(stm);
            return (phi != nullptr && phi->temp_exp != nullptr && phi->temp_exp->temp != nullptr) ? phi->temp_exp->temp->num : -1;
        }
        case QuadKind::PTR_CALC: {
            QuadPtrCalc* ptrcalc = dynamic_cast<QuadPtrCalc*>(stm);
            return (ptrcalc != nullptr && ptrcalc->dst != nullptr) ? getTempNumFromTerm(ptrcalc->dst) : -1;
        }
        default:
            return -1;
    }
}

set<int> getUsedTemps(QuadStm* stm) {
    set<int> usedTemps;
    auto addTerm = [&](QuadTerm* term) {
        int tempNum = getTempNumFromTerm(term);
        if (tempNum != -1) {
            usedTemps.insert(tempNum);
        }
    };

    if (stm == nullptr) {
        return usedTemps;
    }

    switch (stm->kind) {
        case QuadKind::MOVE: {
            QuadMove* move = dynamic_cast<QuadMove*>(stm);
            if (move != nullptr) {
                addTerm(move->src);
            }
            break;
        }
        case QuadKind::LOAD: {
            QuadLoad* load = dynamic_cast<QuadLoad*>(stm);
            if (load != nullptr) {
                addTerm(load->src);
            }
            break;
        }
        case QuadKind::STORE: {
            QuadStore* store = dynamic_cast<QuadStore*>(stm);
            if (store != nullptr) {
                addTerm(store->src);
                addTerm(store->dst);
            }
            break;
        }
        case QuadKind::MOVE_BINOP: {
            QuadMoveBinop* binop = dynamic_cast<QuadMoveBinop*>(stm);
            if (binop != nullptr) {
                addTerm(binop->left);
                addTerm(binop->right);
            }
            break;
        }
        case QuadKind::CALL: {
            QuadCall* call = dynamic_cast<QuadCall*>(stm);
            if (call != nullptr) {
                addTerm(call->obj_term);
                if (call->args != nullptr) {
                    for (QuadTerm* arg : *call->args) {
                        addTerm(arg);
                    }
                }
            }
            break;
        }
        case QuadKind::MOVE_CALL: {
            QuadMoveCall* movecall = dynamic_cast<QuadMoveCall*>(stm);
            if (movecall != nullptr && movecall->call != nullptr) {
                addTerm(movecall->call->obj_term);
                if (movecall->call->args != nullptr) {
                    for (QuadTerm* arg : *movecall->call->args) {
                        addTerm(arg);
                    }
                }
            }
            break;
        }
        case QuadKind::EXTCALL: {
            QuadExtCall* extcall = dynamic_cast<QuadExtCall*>(stm);
            if (extcall != nullptr && extcall->args != nullptr) {
                for (QuadTerm* arg : *extcall->args) {
                    addTerm(arg);
                }
            }
            break;
        }
        case QuadKind::MOVE_EXTCALL: {
            QuadMoveExtCall* moveextcall = dynamic_cast<QuadMoveExtCall*>(stm);
            if (moveextcall != nullptr && moveextcall->extcall != nullptr && moveextcall->extcall->args != nullptr) {
                for (QuadTerm* arg : *moveextcall->extcall->args) {
                    addTerm(arg);
                }
            }
            break;
        }
        case QuadKind::CJUMP: {
            QuadCJump* cjump = dynamic_cast<QuadCJump*>(stm);
            if (cjump != nullptr) {
                addTerm(cjump->left);
                addTerm(cjump->right);
            }
            break;
        }
        case QuadKind::PHI: {
            QuadPhi* phi = dynamic_cast<QuadPhi*>(stm);
            if (phi != nullptr && phi->args != nullptr) {
                for (const auto& arg : *phi->args) {
                    if (arg.first != nullptr) {
                        usedTemps.insert(arg.first->num);
                    }
                }
            }
            break;
        }
        case QuadKind::RETURN: {
            QuadReturn* ret = dynamic_cast<QuadReturn*>(stm);
            if (ret != nullptr) {
                addTerm(ret->exp);
            }
            break;
        }
        case QuadKind::PTR_CALC: {
            QuadPtrCalc* ptrcalc = dynamic_cast<QuadPtrCalc*>(stm);
            if (ptrcalc != nullptr) {
                addTerm(ptrcalc->ptr);
                addTerm(ptrcalc->offset);
            }
            break;
        }
        default:
            break;
    }

    return usedTemps;
}

bool isPureDefStm(QuadStm* stm) {
    if (stm == nullptr) {
        return false;
    }
    switch (stm->kind) {
        case QuadKind::MOVE:
        case QuadKind::LOAD:
        case QuadKind::MOVE_BINOP:
        case QuadKind::PHI:
        case QuadKind::PTR_CALC:
            return true;
        default:
            return false;
    }
}

}  // namespace

QuadFuncDecl* eliminateUnusedInductionVars(QuadFuncDecl* func) {
    if (func == nullptr || func->quadblocklist == nullptr) {
        return func;
    }

    // fill in the code to eliminate unused basic and derived induction variables,
    // by modifying the quads in func->quadblocklist, and also update the related
    // def-use chains and control flow info as necessary
    map<int, QuadStm*> pureDefs;
    map<int, set<int>> pureDeps;
    set<int> liveTemps;

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (QuadStm* stm : *block->quadlist) {
            if (stm == nullptr) {
                continue;
            }

            int definedTemp = getDefinedTemp(stm);
            set<int> usedTemps = getUsedTemps(stm);

            if (isPureDefStm(stm) && definedTemp != -1) {
                pureDefs[definedTemp] = stm;
                pureDeps[definedTemp] = usedTemps;
            } else {
                liveTemps.insert(usedTemps.begin(), usedTemps.end());
            }
        }
    }

    queue<int> worklist;
    for (int tempNum : liveTemps) {
        worklist.push(tempNum);
    }

    set<int> visited;
    while (!worklist.empty()) {
        int tempNum = worklist.front();
        worklist.pop();
        if (!visited.insert(tempNum).second) {
            continue;
        }

        auto depIt = pureDeps.find(tempNum);
        if (depIt == pureDeps.end()) {
            continue;
        }
        for (int usedTemp : depIt->second) {
            if (!liveTemps.count(usedTemp)) {
                liveTemps.insert(usedTemp);
                worklist.push(usedTemp);
            }
        }
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }

        vector<QuadStm*> kept;
        kept.reserve(block->quadlist->size());
        for (QuadStm* stm : *block->quadlist) {
            int definedTemp = getDefinedTemp(stm);
            if (isPureDefStm(stm) && definedTemp != -1 && !liveTemps.count(definedTemp)) {
                continue;
            }
            kept.push_back(stm);
        }
        block->quadlist = new vector<QuadStm*>(kept);
    }

    return func;
}
