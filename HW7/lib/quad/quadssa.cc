#define DEBUG
#undef DEBUG

#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <queue>
#include <algorithm>
#include <functional>
#include <utility>
#include "quad.hh"
#include "flowinfo.hh"
#include "quadssa.hh"
#include "temp.hh"
#include "quadssa_diag.hh"

using namespace std;
using namespace quad;

// Forward declarations for internal functions
static void placePhi(QuadFuncDecl* func, ControlFlowInfo* domInfo, DataFlowInfo* liveness);
static void renameVariables(QuadFuncDecl* func, ControlFlowInfo* domInfo);
static void cleanupUnusedPhi(QuadFuncDecl* func);

SsaDiagState diag;

namespace {

static Temp* getCanonicalTemp(map<int, Temp*>& tempPool, int tempNum) {
    auto it = tempPool.find(tempNum);
    if (it != tempPool.end()) {
        return it->second;
    }
    Temp* temp = new Temp(tempNum);
    tempPool[tempNum] = temp;
    return temp;
}

static Label* getCanonicalLabel(map<int, Label*>& labelPool, ControlFlowInfo* domInfo, int blockNum) {
    if (domInfo != nullptr) {
        auto it = domInfo->labelToBlock.find(blockNum);
        if (it != domInfo->labelToBlock.end() && it->second != nullptr && it->second->entry_label != nullptr) {
            return it->second->entry_label;
        }
    }

    auto it = labelPool.find(blockNum);
    if (it != labelPool.end()) {
        return it->second;
    }
    Label* label = new Label(blockNum);
    labelPool[blockNum] = label;
    return label;
}

static int originalTempNum(int tempNum, int originalLastTemp) {
    if (tempNum > originalLastTemp) {
        return VersionedTemp::origTempNum(tempNum);
    }
    return tempNum;
}

static void recordQuadTempType(map<int, QuadType>& tempTypes, QuadTemp* quadTemp) {
    if (quadTemp == nullptr || quadTemp->temp == nullptr) {
        return;
    }
    tempTypes[quadTemp->temp->num] = quadTemp->type;
}

static void recordQuadTermType(map<int, QuadType>& tempTypes, QuadTerm* term) {
    if (term == nullptr || term->kind != QuadTermKind::TEMP) {
        return;
    }
    recordQuadTempType(tempTypes, term->get_temp());
}

static void collectTempTypes(QuadFuncDecl* func, map<int, QuadType>& tempTypes) {
    if (func == nullptr || func->quadblocklist == nullptr) {
        return;
    }

    for (auto* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (auto* stmt : *block->quadlist) {
            if (stmt == nullptr) {
                continue;
            }
            switch (stmt->kind) {
                case QuadKind::MOVE: {
                    auto* move = static_cast<QuadMove*>(stmt);
                    recordQuadTempType(tempTypes, move->dst);
                    recordQuadTermType(tempTypes, move->src);
                    break;
                }
                case QuadKind::LOAD: {
                    auto* load = static_cast<QuadLoad*>(stmt);
                    recordQuadTempType(tempTypes, load->dst);
                    recordQuadTermType(tempTypes, load->src);
                    break;
                }
                case QuadKind::STORE: {
                    auto* store = static_cast<QuadStore*>(stmt);
                    recordQuadTermType(tempTypes, store->src);
                    recordQuadTermType(tempTypes, store->dst);
                    break;
                }
                case QuadKind::MOVE_BINOP: {
                    auto* binop = static_cast<QuadMoveBinop*>(stmt);
                    recordQuadTempType(tempTypes, binop->dst);
                    recordQuadTermType(tempTypes, binop->left);
                    recordQuadTermType(tempTypes, binop->right);
                    break;
                }
                case QuadKind::CALL: {
                    auto* call = static_cast<QuadCall*>(stmt);
                    recordQuadTermType(tempTypes, call->obj_term);
                    if (call->args != nullptr) {
                        for (auto* arg : *call->args) {
                            recordQuadTermType(tempTypes, arg);
                        }
                    }
                    break;
                }
                case QuadKind::MOVE_CALL: {
                    auto* moveCall = static_cast<QuadMoveCall*>(stmt);
                    recordQuadTempType(tempTypes, moveCall->dst);
                    if (moveCall->call != nullptr) {
                        recordQuadTermType(tempTypes, moveCall->call->obj_term);
                        if (moveCall->call->args != nullptr) {
                            for (auto* arg : *moveCall->call->args) {
                                recordQuadTermType(tempTypes, arg);
                            }
                        }
                    }
                    break;
                }
                case QuadKind::EXTCALL: {
                    auto* extCall = static_cast<QuadExtCall*>(stmt);
                    if (extCall->args != nullptr) {
                        for (auto* arg : *extCall->args) {
                            recordQuadTermType(tempTypes, arg);
                        }
                    }
                    break;
                }
                case QuadKind::MOVE_EXTCALL: {
                    auto* moveExtCall = static_cast<QuadMoveExtCall*>(stmt);
                    recordQuadTempType(tempTypes, moveExtCall->dst);
                    if (moveExtCall->extcall != nullptr && moveExtCall->extcall->args != nullptr) {
                        for (auto* arg : *moveExtCall->extcall->args) {
                            recordQuadTermType(tempTypes, arg);
                        }
                    }
                    break;
                }
                case QuadKind::CJUMP: {
                    auto* cjump = static_cast<QuadCJump*>(stmt);
                    recordQuadTermType(tempTypes, cjump->left);
                    recordQuadTermType(tempTypes, cjump->right);
                    break;
                }
                case QuadKind::PHI: {
                    auto* phi = static_cast<QuadPhi*>(stmt);
                    recordQuadTempType(tempTypes, phi->temp_exp);
                    break;
                }
                case QuadKind::RETURN: {
                    auto* ret = static_cast<QuadReturn*>(stmt);
                    recordQuadTermType(tempTypes, ret->exp);
                    break;
                }
                case QuadKind::PTR_CALC: {
                    auto* ptrCalc = static_cast<QuadPtrCalc*>(stmt);
                    recordQuadTermType(tempTypes, ptrCalc->dst);
                    recordQuadTermType(tempTypes, ptrCalc->ptr);
                    recordQuadTermType(tempTypes, ptrCalc->offset);
                    break;
                }
                default:
                    break;
            }
        }
    }
}

static void collectDefinedVars(QuadFuncDecl* func, ControlFlowInfo* domInfo, map<int, set<int>>& defBlocks) {
    if (func == nullptr) {
        return;
    }

    int entryBlock = -1;
    if (domInfo != nullptr) {
        entryBlock = domInfo->entryBlock;
    } else if (func->quadblocklist != nullptr && !func->quadblocklist->empty() && func->quadblocklist->at(0) != nullptr && func->quadblocklist->at(0)->entry_label != nullptr) {
        entryBlock = func->quadblocklist->at(0)->entry_label->num;
    }

    if (func->params != nullptr && entryBlock != -1) {
        for (auto* param : *func->params) {
            if (param != nullptr) {
                defBlocks[param->num].insert(entryBlock);
            }
        }
    }

    if (func->quadblocklist == nullptr) {
        return;
    }

    for (auto* block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || block->quadlist == nullptr) {
            continue;
        }
        int blockNum = block->entry_label->num;
        for (auto* stmt : *block->quadlist) {
            if (stmt == nullptr) {
                continue;
            }
            switch (stmt->kind) {
                case QuadKind::MOVE:
                    defBlocks[static_cast<QuadMove*>(stmt)->dst->temp->num].insert(blockNum);
                    break;
                case QuadKind::LOAD:
                    defBlocks[static_cast<QuadLoad*>(stmt)->dst->temp->num].insert(blockNum);
                    break;
                case QuadKind::MOVE_BINOP:
                    defBlocks[static_cast<QuadMoveBinop*>(stmt)->dst->temp->num].insert(blockNum);
                    break;
                case QuadKind::MOVE_CALL:
                    defBlocks[static_cast<QuadMoveCall*>(stmt)->dst->temp->num].insert(blockNum);
                    break;
                case QuadKind::MOVE_EXTCALL:
                    defBlocks[static_cast<QuadMoveExtCall*>(stmt)->dst->temp->num].insert(blockNum);
                    break;
                case QuadKind::PTR_CALC: {
                    auto* ptrCalc = static_cast<QuadPtrCalc*>(stmt);
                    if (ptrCalc->dst != nullptr && ptrCalc->dst->kind == QuadTermKind::TEMP) {
                        defBlocks[ptrCalc->dst->get_temp()->temp->num].insert(blockNum);
                    }
                    break;
                }
                default:
                    break;
            }
        }
    }
}

static set<int> getBlockLiveIn(QuadBlock* block, DataFlowInfo* liveness) {
    if (block == nullptr || block->quadlist == nullptr || liveness == nullptr || liveness->livein == nullptr) {
        return set<int>();
    }
    if (block->quadlist->empty()) {
        return set<int>();
    }
    QuadStm* firstStmt = block->quadlist->front();
    auto it = liveness->livein->find(firstStmt);
    if (it == liveness->livein->end()) {
        return set<int>();
    }
    return it->second;
}

static void resetDefUseSet(set<Temp*>*& tempSet) {
    if (tempSet == nullptr) {
        tempSet = new set<Temp*>();
    } else {
        tempSet->clear();
    }
}

static void addTermUse(set<Temp*>* uses, QuadTerm* term) {
    if (uses == nullptr || term == nullptr || term->kind != QuadTermKind::TEMP) {
        return;
    }
    QuadTemp* quadTemp = term->get_temp();
    if (quadTemp != nullptr && quadTemp->temp != nullptr) {
        uses->insert(quadTemp->temp);
    }
}

static void recomputeDefUse(QuadStm* stmt) {
    if (stmt == nullptr) {
        return;
    }

    resetDefUseSet(stmt->def);
    resetDefUseSet(stmt->use);

    switch (stmt->kind) {
        case QuadKind::MOVE: {
            auto* move = static_cast<QuadMove*>(stmt);
            if (move->dst != nullptr && move->dst->temp != nullptr) {
                stmt->def->insert(move->dst->temp);
            }
            addTermUse(stmt->use, move->src);
            break;
        }
        case QuadKind::LOAD: {
            auto* load = static_cast<QuadLoad*>(stmt);
            if (load->dst != nullptr && load->dst->temp != nullptr) {
                stmt->def->insert(load->dst->temp);
            }
            addTermUse(stmt->use, load->src);
            break;
        }
        case QuadKind::STORE: {
            auto* store = static_cast<QuadStore*>(stmt);
            addTermUse(stmt->use, store->src);
            addTermUse(stmt->use, store->dst);
            break;
        }
        case QuadKind::MOVE_BINOP: {
            auto* binop = static_cast<QuadMoveBinop*>(stmt);
            if (binop->dst != nullptr && binop->dst->temp != nullptr) {
                stmt->def->insert(binop->dst->temp);
            }
            addTermUse(stmt->use, binop->left);
            addTermUse(stmt->use, binop->right);
            break;
        }
        case QuadKind::CALL: {
            auto* call = static_cast<QuadCall*>(stmt);
            addTermUse(stmt->use, call->obj_term);
            if (call->args != nullptr) {
                for (auto* arg : *call->args) {
                    addTermUse(stmt->use, arg);
                }
            }
            break;
        }
        case QuadKind::MOVE_CALL: {
            auto* moveCall = static_cast<QuadMoveCall*>(stmt);
            if (moveCall->dst != nullptr && moveCall->dst->temp != nullptr) {
                stmt->def->insert(moveCall->dst->temp);
            }
            if (moveCall->call != nullptr) {
                addTermUse(stmt->use, moveCall->call->obj_term);
                if (moveCall->call->args != nullptr) {
                    for (auto* arg : *moveCall->call->args) {
                        addTermUse(stmt->use, arg);
                    }
                }
            }
            break;
        }
        case QuadKind::EXTCALL: {
            auto* extCall = static_cast<QuadExtCall*>(stmt);
            if (extCall->args != nullptr) {
                for (auto* arg : *extCall->args) {
                    addTermUse(stmt->use, arg);
                }
            }
            break;
        }
        case QuadKind::MOVE_EXTCALL: {
            auto* moveExtCall = static_cast<QuadMoveExtCall*>(stmt);
            if (moveExtCall->dst != nullptr && moveExtCall->dst->temp != nullptr) {
                stmt->def->insert(moveExtCall->dst->temp);
            }
            if (moveExtCall->extcall != nullptr && moveExtCall->extcall->args != nullptr) {
                for (auto* arg : *moveExtCall->extcall->args) {
                    addTermUse(stmt->use, arg);
                }
            }
            break;
        }
        case QuadKind::CJUMP: {
            auto* cjump = static_cast<QuadCJump*>(stmt);
            addTermUse(stmt->use, cjump->left);
            addTermUse(stmt->use, cjump->right);
            break;
        }
        case QuadKind::PHI: {
            auto* phi = static_cast<QuadPhi*>(stmt);
            if (phi->temp_exp != nullptr && phi->temp_exp->temp != nullptr) {
                stmt->def->insert(phi->temp_exp->temp);
            }
            if (phi->args != nullptr) {
                for (const auto& arg : *phi->args) {
                    if (arg.first != nullptr) {
                        stmt->use->insert(arg.first);
                    }
                }
            }
            break;
        }
        case QuadKind::RETURN: {
            auto* ret = static_cast<QuadReturn*>(stmt);
            addTermUse(stmt->use, ret->exp);
            break;
        }
        case QuadKind::PTR_CALC: {
            auto* ptrCalc = static_cast<QuadPtrCalc*>(stmt);
            if (ptrCalc->dst != nullptr && ptrCalc->dst->kind == QuadTermKind::TEMP) {
                stmt->def->insert(ptrCalc->dst->get_temp()->temp);
            }
            addTermUse(stmt->use, ptrCalc->ptr);
            addTermUse(stmt->use, ptrCalc->offset);
            break;
        }
        default:
            break;
    }
}

static void recomputeAllDefUse(QuadFuncDecl* func) {
    if (func == nullptr || func->quadblocklist == nullptr) {
        return;
    }

    for (auto* block : *func->quadblocklist) {
        if (block == nullptr || block->quadlist == nullptr) {
            continue;
        }
        for (auto* stmt : *block->quadlist) {
            recomputeDefUse(stmt);
        }
    }
}

struct RenameContext {
    QuadFuncDecl* func;
    ControlFlowInfo* domInfo;
    int originalLastTemp;
    map<int, QuadType> tempTypes;
    map<int, vector<Temp*>> versionStacks;
    map<int, int> versionCounters;
    map<int, Temp*> tempPool;
    map<int, Label*> labelPool;
    set<int> visitedBlocks;

    RenameContext(QuadFuncDecl* func, ControlFlowInfo* domInfo)
                : func(func), domInfo(domInfo), originalLastTemp(func == nullptr ? -1 : func->last_temp_num) {
        collectTempTypes(func, tempTypes);
    }

    QuadType typeOf(int tempNum) {
        auto it = tempTypes.find(tempNum);
        if (it != tempTypes.end()) {
            return it->second;
        }
        return QuadType::INT;
    }

    Temp* ensureCurrentVersion(int origNum, QuadType type) {
        vector<Temp*>& stack = versionStacks[origNum];
        if (!stack.empty()) {
            return stack.back();
        }

        auto counterIt = versionCounters.find(origNum);
        int version = (counterIt == versionCounters.end()) ? 0 : max(0, counterIt->second);
        versionCounters[origNum] = version;

        int versionedNum = VersionedTemp::versionedTempNum(origNum, version);
        tempTypes[origNum] = type;
        Temp* temp = getCanonicalTemp(tempPool, versionedNum);
        stack.push_back(temp);
        return temp;
    }

    Temp* pushNewVersion(int origNum, QuadType type, int blockNum) {
        int nextVersion = 0;
        auto counterIt = versionCounters.find(origNum);
        if (counterIt != versionCounters.end()) {
            nextVersion = counterIt->second + 1;
        }
        versionCounters[origNum] = nextVersion;
        tempTypes[origNum] = type;

        int versionedNum = VersionedTemp::versionedTempNum(origNum, nextVersion);
        Temp* temp = getCanonicalTemp(tempPool, versionedNum);
        diag.createdVersionBlocksByVar[origNum][nextVersion].insert(blockNum);
        versionStacks[origNum].push_back(temp);
        return temp;
    }

    QuadTerm* renameTerm(QuadTerm* term) {
        if (term == nullptr || term->kind != QuadTermKind::TEMP) {
            return term;
        }

        QuadTemp* oldTemp = term->get_temp();
        if (oldTemp == nullptr || oldTemp->temp == nullptr) {
            return term;
        }

        int origNum = originalTempNum(oldTemp->temp->num, originalLastTemp);
        Temp* currentTemp = ensureCurrentVersion(origNum, oldTemp->type);
        return new QuadTerm(new QuadTemp(currentTemp, oldTemp->type));
    }

    void renameCallArgs(QuadCall* call) {
        if (call == nullptr) {
            return;
        }
        call->obj_term = renameTerm(call->obj_term);
        if (call->args != nullptr) {
            for (auto*& arg : *call->args) {
                arg = renameTerm(arg);
            }
        }
    }

    void renameExtCallArgs(QuadExtCall* extCall) {
        if (extCall == nullptr || extCall->args == nullptr) {
            return;
        }
        for (auto*& arg : *extCall->args) {
            arg = renameTerm(arg);
        }
    }

    void renameSuccessorPhiArgs(int blockNum) {
        if (domInfo == nullptr) {
            return;
        }

        auto succIt = domInfo->successors.find(blockNum);
        if (succIt == domInfo->successors.end()) {
            return;
        }

        for (int succNum : succIt->second) {
            auto blockIt = domInfo->labelToBlock.find(succNum);
            if (blockIt == domInfo->labelToBlock.end() || blockIt->second == nullptr || blockIt->second->quadlist == nullptr) {
                continue;
            }

            QuadBlock* succBlock = blockIt->second;
            bool skippedLabel = false;
            for (auto* stmt : *succBlock->quadlist) {
                if (!skippedLabel && stmt != nullptr && stmt->kind == QuadKind::LABEL) {
                    skippedLabel = true;
                    continue;
                }
                if (stmt == nullptr || stmt->kind != QuadKind::PHI) {
                    break;
                }
                auto* phi = static_cast<QuadPhi*>(stmt);
                if (phi->temp_exp == nullptr || phi->temp_exp->temp == nullptr) {
                    continue;
                }

                int origNum = originalTempNum(phi->temp_exp->temp->num, originalLastTemp);
                Temp* incoming = ensureCurrentVersion(origNum, phi->temp_exp->type);

                bool updated = false;
                if (phi->args != nullptr) {
                    for (auto& arg : *phi->args) {
                        if (arg.second != nullptr && arg.second->num == blockNum) {
                            arg.first = incoming;
                            updated = true;
                            break;
                        }
                    }
                }
                if (!updated) {
                    if (phi->args == nullptr) {
                        phi->args = new vector<pair<Temp*, Label*>>();
                    }
                    phi->args->push_back(make_pair(incoming, getCanonicalLabel(labelPool, domInfo, blockNum)));
                }
            }
        }
    }

    void renameBlock(int blockNum) {
        if (visitedBlocks.count(blockNum) != 0 || domInfo == nullptr) {
            return;
        }
        auto blockIt = domInfo->labelToBlock.find(blockNum);
        if (blockIt == domInfo->labelToBlock.end() || blockIt->second == nullptr) {
            return;
        }

        visitedBlocks.insert(blockNum);
        QuadBlock* block = blockIt->second;
        vector<int> pushedTemps;

        if (block->quadlist != nullptr) {
            bool skippedLabel = false;
            for (auto* stmt : *block->quadlist) {
                if (!skippedLabel && stmt != nullptr && stmt->kind == QuadKind::LABEL) {
                    skippedLabel = true;
                    continue;
                }
                if (stmt == nullptr || stmt->kind != QuadKind::PHI) {
                    break;
                }

                auto* phi = static_cast<QuadPhi*>(stmt);
                if (phi->temp_exp == nullptr || phi->temp_exp->temp == nullptr) {
                    continue;
                }

                int origNum = originalTempNum(phi->temp_exp->temp->num, originalLastTemp);
                Temp* renamed = pushNewVersion(origNum, phi->temp_exp->type,blockNum);
                phi->temp_exp = new QuadTemp(renamed, phi->temp_exp->type);
                pushedTemps.push_back(origNum);
            }

            for (auto* stmt : *block->quadlist) {
                if (stmt == nullptr || stmt->kind == QuadKind::PHI) {
                    continue;
                }

                switch (stmt->kind) {
                    case QuadKind::MOVE: {
                        auto* move = static_cast<QuadMove*>(stmt);
                        move->src = renameTerm(move->src);
                        int origNum = originalTempNum(move->dst->temp->num, originalLastTemp);
                        move->dst = new QuadTemp(pushNewVersion(origNum, move->dst->type, blockNum), move->dst->type);
                        pushedTemps.push_back(origNum);
                        break;
                    }
                    case QuadKind::LOAD: {
                        auto* load = static_cast<QuadLoad*>(stmt);
                        load->src = renameTerm(load->src);
                        int origNum = originalTempNum(load->dst->temp->num, originalLastTemp);
                        load->dst = new QuadTemp(pushNewVersion(origNum, load->dst->type, blockNum), load->dst->type);
                        pushedTemps.push_back(origNum);
                        break;
                    }
                    case QuadKind::STORE: {
                        auto* store = static_cast<QuadStore*>(stmt);
                        store->src = renameTerm(store->src);
                        store->dst = renameTerm(store->dst);
                        break;
                    }
                    case QuadKind::MOVE_BINOP: {
                        auto* binop = static_cast<QuadMoveBinop*>(stmt);
                        binop->left = renameTerm(binop->left);
                        binop->right = renameTerm(binop->right);
                        int origNum = originalTempNum(binop->dst->temp->num, originalLastTemp);
                        binop->dst = new QuadTemp(pushNewVersion(origNum, binop->dst->type, blockNum), binop->dst->type);
                        pushedTemps.push_back(origNum);
                        break;
                    }
                    case QuadKind::CALL:
                        renameCallArgs(static_cast<QuadCall*>(stmt));
                        break;
                    case QuadKind::MOVE_CALL: {
                        auto* moveCall = static_cast<QuadMoveCall*>(stmt);
                        renameCallArgs(moveCall->call);
                        int origNum = originalTempNum(moveCall->dst->temp->num, originalLastTemp);
                        moveCall->dst = new QuadTemp(pushNewVersion(origNum, moveCall->dst->type, blockNum), moveCall->dst->type);
                        pushedTemps.push_back(origNum);
                        break;
                    }
                    case QuadKind::EXTCALL:
                        renameExtCallArgs(static_cast<QuadExtCall*>(stmt));
                        break;
                    case QuadKind::MOVE_EXTCALL: {
                        auto* moveExtCall = static_cast<QuadMoveExtCall*>(stmt);
                        renameExtCallArgs(moveExtCall->extcall);
                        int origNum = originalTempNum(moveExtCall->dst->temp->num, originalLastTemp);
                        moveExtCall->dst = new QuadTemp(pushNewVersion(origNum, moveExtCall->dst->type, blockNum), moveExtCall->dst->type);
                        pushedTemps.push_back(origNum);
                        break;
                    }
                    case QuadKind::CJUMP: {
                        auto* cjump = static_cast<QuadCJump*>(stmt);
                        cjump->left = renameTerm(cjump->left);
                        cjump->right = renameTerm(cjump->right);
                        break;
                    }
                    case QuadKind::RETURN: {
                        auto* ret = static_cast<QuadReturn*>(stmt);
                        ret->exp = renameTerm(ret->exp);
                        break;
                    }
                    case QuadKind::PTR_CALC: {
                        auto* ptrCalc = static_cast<QuadPtrCalc*>(stmt);
                        ptrCalc->ptr = renameTerm(ptrCalc->ptr);
                        ptrCalc->offset = renameTerm(ptrCalc->offset);
                        if (ptrCalc->dst != nullptr && ptrCalc->dst->kind == QuadTermKind::TEMP) {
                            QuadTemp* dst = ptrCalc->dst->get_temp();
                            int origNum = originalTempNum(dst->temp->num, originalLastTemp);
                            ptrCalc->dst = new QuadTerm(new QuadTemp(pushNewVersion(origNum, dst->type, blockNum), dst->type));
                            pushedTemps.push_back(origNum);
                        }
                        break;
                    }
                    default:
                        break;
                }
            }
        }

        renameSuccessorPhiArgs(blockNum);

        auto childIt = domInfo->domTree.find(blockNum);
        if (childIt != domInfo->domTree.end()) {
            for (int child : childIt->second) {
                renameBlock(child);
            }
        }

        for (auto it = pushedTemps.rbegin(); it != pushedTemps.rend(); ++it) {
            auto stackIt = versionStacks.find(*it);
            if (stackIt != versionStacks.end() && !stackIt->second.empty()) {
                stackIt->second.pop_back();
            }
        }
    }
};

} // namespace

// Place Phi functions at appropriate locations
// HW7: You need to write this part!!
static void placePhi(QuadFuncDecl* func, ControlFlowInfo* domInfo, DataFlowInfo* liveness) {
#ifdef DEBUG
    cout << "Placing phi functions for function: " << func->funcname << endl;
#endif
    if (func == nullptr || func->quadblocklist == nullptr || domInfo == nullptr) {
        return;
    }
    map<int, QuadType> tempTypes;
    collectTempTypes(func, tempTypes);

    map<int, set<int>> defBlocks;
    collectDefinedVars(func, domInfo, defBlocks);

    map<int, set<int>> placedVarsByBlock;
    map<int, vector<QuadPhi*>> pendingPhis;
    map<int, Temp*> tempPool;
    map<int, Label*> labelPool;

    for (const auto& defEntry : defBlocks) {
        int varNum = defEntry.first;
        queue<int> worklist;
        set<int> enqueued = defEntry.second;

        for (int blockNum : defEntry.second) {
            worklist.push(blockNum);
        }

        while (!worklist.empty()) {
            int blockNum = worklist.front();
            worklist.pop();

            auto frontierIt = domInfo->dominanceFrontiers.find(blockNum);
            if (frontierIt == domInfo->dominanceFrontiers.end()) {
                continue;
            }

            for (int frontierBlockNum : frontierIt->second) {
                auto blockIt = domInfo->labelToBlock.find(frontierBlockNum);
                if (blockIt == domInfo->labelToBlock.end() || blockIt->second == nullptr) {
                    continue;
                }

                set<int> liveIn = getBlockLiveIn(blockIt->second, liveness);
                if (!liveIn.empty() && liveIn.count(varNum) == 0) {
                    continue;
                }

                if (placedVarsByBlock[frontierBlockNum].count(varNum) != 0) {
                    continue;
                }

                placedVarsByBlock[frontierBlockNum].insert(varNum);
                // diag.candidatePhiBlocksByVar[varNum].insert(frontierBlockNum);

                vector<pair<Temp*, Label*>>* args = new vector<pair<Temp*, Label*>>();
                auto predIt = domInfo->predecessors.find(frontierBlockNum);
                if (predIt != domInfo->predecessors.end()) {
                    for (int predNum : predIt->second) {
                        args->push_back(make_pair(getCanonicalTemp(tempPool, varNum), getCanonicalLabel(labelPool, domInfo, predNum)));
                    }
                }

                QuadType tempType = QuadType::INT;
                auto typeIt = tempTypes.find(varNum);
                if (typeIt != tempTypes.end()) {
                    tempType = typeIt->second;
                }

                set<Temp*>* def = new set<Temp*>();
                def->insert(getCanonicalTemp(tempPool, varNum));
                pendingPhis[frontierBlockNum].push_back(
                    new QuadPhi(new QuadTemp(getCanonicalTemp(tempPool, varNum), tempType), args, def, new set<Temp*>())
                );
                diag.candidatePhiBlocksByVar[varNum].insert(frontierBlockNum);

                if (enqueued.insert(frontierBlockNum).second) {
                    worklist.push(frontierBlockNum);
                }
            }
        }
    }

    for (auto* block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || block->quadlist == nullptr) {
            continue;
        }

        auto pendingIt = pendingPhis.find(block->entry_label->num);
        if (pendingIt == pendingPhis.end() || pendingIt->second.empty()) {
            continue;
        }

        vector<QuadStm*>* newQuadList = new vector<QuadStm*>();
        newQuadList->reserve(pendingIt->second.size() + block->quadlist->size());

        auto stmtIt = block->quadlist->begin();
        if (stmtIt != block->quadlist->end() && *stmtIt != nullptr && (*stmtIt)->kind == QuadKind::LABEL) {
            newQuadList->push_back(*stmtIt);
            ++stmtIt;
        }

        for (auto* phi : pendingIt->second) {
            newQuadList->push_back(phi);
        }

        for (; stmtIt != block->quadlist->end(); ++stmtIt) {
            auto* stmt = *stmtIt;
            newQuadList->push_back(stmt);
        }
        block->quadlist = newQuadList;
    }
}

// Rename variables to ensure SSA property
// HW7: You need to write this part!!
static void renameVariables(QuadFuncDecl* func, ControlFlowInfo* domInfo) {
#ifdef DEBUG
    cout << "Entering renaming variables for function: " << func->funcname << endl;
#endif
    if (func == nullptr || func->quadblocklist == nullptr || domInfo == nullptr) {
        return;
    }

    RenameContext ctx(func, domInfo);

    if (func->params != nullptr) {
        for (auto* param : *func->params) {
            if (param == nullptr) {
                continue;
            }
            ctx.versionStacks[param->num].push_back(param);
            ctx.versionCounters[param->num] = -1;
        }
    }

    if (domInfo->entryBlock != -1) {
        ctx.renameBlock(domInfo->entryBlock);
    }

    for (auto* block : *func->quadblocklist) {
        if (block != nullptr && block->entry_label != nullptr) {
            ctx.renameBlock(block->entry_label->num);
        }
    }
    recomputeAllDefUse(func);
}

// Remove unnecessary phi functions
// HW7: You need to write this part!!
static void cleanupUnusedPhi(QuadFuncDecl* func) {
#ifdef DEBUG
    cout << "Cleaning up unused phi functions for function: " << func->funcname << endl;
#endif
    if (func == nullptr || func->quadblocklist == nullptr) {
        return;
    }

    bool changed = true;
    while (changed) {
        changed = false;
        recomputeAllDefUse(func);

        map<int, set<QuadStm*>> useSites;
        for (auto* block : *func->quadblocklist) {
            if (block == nullptr || block->quadlist == nullptr) {
                continue;
            }
            for (auto* stmt : *block->quadlist) {
                if (stmt == nullptr || stmt->use == nullptr) {
                    continue;
                }
                for (auto* temp : *stmt->use) {
                    if (temp != nullptr) {
                        useSites[temp->num].insert(stmt);
                    }
                }
            }
        }

        for (auto* block : *func->quadblocklist) {
            if (block == nullptr || block->quadlist == nullptr) {
                continue;
            }

            vector<QuadStm*>* kept = new vector<QuadStm*>();
            kept->reserve(block->quadlist->size());

            for (auto* stmt : *block->quadlist) {
                bool dropPhi = false;
                if (stmt != nullptr && stmt->kind == QuadKind::PHI) {
                    auto* phi = static_cast<QuadPhi*>(stmt);
                    if (phi->temp_exp != nullptr && phi->temp_exp->temp != nullptr) {
                        auto useIt = useSites.find(phi->temp_exp->temp->num);
                        dropPhi = true;
                        if (useIt != useSites.end()) {
                            for (auto* useStmt : useIt->second) {
                                if (useStmt != phi) {
                                    dropPhi = false;
                                    break;
                                }
                            }
                        }
                    }
                }

                if (dropPhi) {
                    changed = true;
                    auto* phi = static_cast<QuadPhi*>(stmt);
                    int versionedTemp=phi->temp_exp->temp->num;
                    diag.eliminatedVersionBlocksByVar[versionedTemp/100][versionedTemp%100].insert(block->entry_label->num);
                } else {
                    kept->push_back(stmt);
                }
            }

            block->quadlist = kept;
        }
    }

    recomputeAllDefUse(func);
}

// Convert blocked Quad with precomputed flow info to SSA form
quad::QuadProgram *quad2ssa(set<FuncFlowInfo*>* allFuncFlow) {
    if (!allFuncFlow || allFuncFlow->empty()) {
        return nullptr; // Invalid program
    }

    vector<QuadFuncDecl*>* funcs = new vector<QuadFuncDecl*>();
    funcs->reserve(allFuncFlow->size());
    int prog_last_label_num = -1;
    int prog_last_temp_num = -1;

    for (auto* ffi : *allFuncFlow) {
        if (!ffi || !ffi->cfi || !ffi->cfi->func) {
            continue;
        }
        QuadFuncDecl* funcdecl = ffi->cfi->func;
        diag.funcName=funcdecl->funcname;
        diag.candidatePhiBlocksByVar.clear();
        diag.actualPhiBlocksByVar.clear();
        diag.createdVersionBlocksByVar.clear();
        diag.eliminatedVersionBlocksByVar.clear();
        int maxLastLabelNum = funcdecl->last_label_num;
        int maxLastTempNum = funcdecl->last_temp_num;

        ControlFlowInfo* domInfo = ffi->cfi;
        DataFlowInfo* liveness = ffi->dfi;

        // Now Place Phi functions at join points
        placePhi(funcdecl, domInfo, liveness);
        // Rename variables to ensure SSA property
        renameVariables(funcdecl, domInfo);
        // Clean up unnecessary phi nodes
        cleanupUnusedPhi(funcdecl);

        funcs->push_back(funcdecl);
        if (prog_last_label_num < funcdecl->last_label_num) {
            prog_last_label_num = funcdecl->last_label_num;
        }
        if (prog_last_temp_num < funcdecl->last_temp_num) {
            prog_last_temp_num = funcdecl->last_temp_num;
        }
        printSsaDiagSummary(funcdecl, diag);
    }
    return new QuadProgram(funcs, prog_last_label_num, prog_last_temp_num);
}