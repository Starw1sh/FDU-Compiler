#define DEBUG
#undef DEBUG

#include <string>
#include <stack>
#include <variant>
#include <vector>
#include <map>
#include <algorithm>
#include <set>
#include "quad.hh"
#include "flowinfo.hh"
#include "loopopt.hh"

using namespace std;
using namespace quad;

static bool isTerminator(QuadStm* stmt) {
    if (stmt == nullptr) {
        return false;
    }

    return stmt->kind == QuadKind::JUMP ||
           stmt->kind == QuadKind::CJUMP ||
           stmt->kind == QuadKind::RETURN;
}

static bool isHoistableStmt(QuadStm* stmt) {
    if (stmt == nullptr) {
        return false;
    }

    return stmt->kind == QuadKind::MOVE ||
           stmt->kind == QuadKind::MOVE_BINOP ||
           stmt->kind == QuadKind::PTR_CALC;
}

static int getSingleDefTemp(QuadStm* stmt) {
    if (stmt == nullptr || stmt->def == nullptr || stmt->def->size() != 1) {
        return -1;
    }

    Temp* temp = *stmt->def->begin();
    return temp == nullptr ? -1 : temp->num;
}

static map<int, QuadBlock*> buildLabelToBlock(QuadFuncDecl* func) {
    map<int, QuadBlock*> labelToBlock;

    if (func == nullptr || func->quadblocklist == nullptr) {
        return labelToBlock;
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (block != nullptr && block->entry_label != nullptr) {
            labelToBlock[block->entry_label->num] = block;
        }
    }

    return labelToBlock;
}

static map<int, set<int>> buildPredecessors(QuadFuncDecl* func) {
    map<int, set<int>> predecessors;

    if (func == nullptr || func->quadblocklist == nullptr) {
        return predecessors;
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || block->exit_labels == nullptr) {
            continue;
        }

        int sourceLabel = block->entry_label->num;
        for (Label* exitLabel : *block->exit_labels) {
            if (exitLabel != nullptr) {
                predecessors[exitLabel->num].insert(sourceLabel);
            }
        }
    }

    return predecessors;
}

static map<int, int> buildDefBlockMap(QuadFuncDecl* func) {
    map<int, int> defBlockByTemp;

    if (func == nullptr || func->quadblocklist == nullptr) {
        return defBlockByTemp;
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || block->quadlist == nullptr) {
            continue;
        }

        int blockLabel = block->entry_label->num;
        for (QuadStm* stmt : *block->quadlist) {
            if (stmt == nullptr || stmt->def == nullptr) {
                continue;
            }

            for (Temp* temp : *stmt->def) {
                if (temp != nullptr) {
                    defBlockByTemp[temp->num] = blockLabel;
                }
            }
        }
    }

    return defBlockByTemp;
}

static bool usesOnlyInvariantValues(
    QuadStm* stmt,
    const set<int>& loopBlocks,
    const map<int, int>& defBlockByTemp,
    const set<int>& invariantTemps
) {
    if (stmt == nullptr || stmt->use == nullptr) {
        return true;
    }

    for (Temp* temp : *stmt->use) {
        if (temp == nullptr) {
            continue;
        }

        auto defIt = defBlockByTemp.find(temp->num);
        if (defIt == defBlockByTemp.end()) {
            continue;
        }

        if (loopBlocks.count(defIt->second) && !invariantTemps.count(temp->num)) {
            return false;
        }
    }

    return true;
}

static void insertIntoPreheader(QuadBlock* preheader, QuadStm* stmt) {
    if (preheader == nullptr || preheader->quadlist == nullptr || stmt == nullptr) {
        return;
    }

    vector<QuadStm*>* preheaderStmts = preheader->quadlist;
    size_t insertPos = preheaderStmts->size();
    if (insertPos > 0 && isTerminator(preheaderStmts->back())) {
        --insertPos;
    }
    preheaderStmts->insert(preheaderStmts->begin() + static_cast<long>(insertPos), stmt);
}

// Main entry point for loop optimization
// Complete the function!!

QuadFuncDecl* loopHoistFunc(QuadFuncDecl* func, LoopHeaderMap *loopHeaderMap) {
    if (func == nullptr || func->quadblocklist == nullptr || loopHeaderMap == nullptr) {
        return func;
    }
    // Fill in the loop hoisting logic here
    auto funcIt = loopHeaderMap->funcLoopHeaders.find(func);
    if (funcIt == loopHeaderMap->funcLoopHeaders.end() || funcIt->second.empty()) {
        return func;
    }

    vector<LoopHeader*> loopHeaders(funcIt->second.begin(), funcIt->second.end());
    sort(loopHeaders.begin(), loopHeaders.end(), [](LoopHeader* lhs, LoopHeader* rhs) {
        if (lhs == nullptr || rhs == nullptr) {
            return lhs < rhs;
        }
        if (lhs->bodyBlocks.size() != rhs->bodyBlocks.size()) {
            return lhs->bodyBlocks.size() < rhs->bodyBlocks.size();
        }
        return lhs->headerLabel < rhs->headerLabel;
    });

    for (LoopHeader* loopHeader : loopHeaders) {
        if (loopHeader == nullptr) {
            continue;
        }

        const set<int>& loopBlocks = loopHeader->bodyBlocks;
        int headerLabel = loopHeader->headerLabel;

        map<int, set<int>> predecessors = buildPredecessors(func);
        map<int, QuadBlock*> labelToBlock = buildLabelToBlock(func);

        auto predIt = predecessors.find(headerLabel);
        if (predIt == predecessors.end()) {
            continue;
        }

        vector<int> outsidePreds;
        for (int predLabel : predIt->second) {
            if (!loopBlocks.count(predLabel)) {
                outsidePreds.push_back(predLabel);
            }
        }

        if (outsidePreds.size() != 1) {
            continue;
        }

        auto preheaderIt = labelToBlock.find(outsidePreds.front());
        if (preheaderIt == labelToBlock.end()) {
            continue;
        }

        QuadBlock* preheader = preheaderIt->second;
        set<int> invariantTemps;
        bool changed = true;

        while (changed) {
            changed = false;
            map<int, int> defBlockByTemp = buildDefBlockMap(func);

            for (QuadBlock* block : *func->quadblocklist) {
                if (block == nullptr || block->entry_label == nullptr || block->quadlist == nullptr) {
                    continue;
                }
                if (!loopBlocks.count(block->entry_label->num)) {
                    continue;
                }

                for (size_t index = 0; index < block->quadlist->size();) {
                    QuadStm* stmt = block->quadlist->at(index);
                    int defTemp = getSingleDefTemp(stmt);

                    if (!isHoistableStmt(stmt) || defTemp == -1 ||
                        !usesOnlyInvariantValues(stmt, loopBlocks, defBlockByTemp, invariantTemps)) {
                        ++index;
                        continue;
                    }

                    insertIntoPreheader(preheader, stmt);
                    block->quadlist->erase(block->quadlist->begin() + static_cast<long>(index));
                    invariantTemps.insert(defTemp);
                    changed = true;
                }
            }
        }
    }

    return func;
}