#define DEBUG
#undef DEBUG

#include <iostream>
#include <queue>
#include <algorithm>
#include <map>
#include <new>
#include "quad.hh"
#include "flowinfo.hh"

using namespace std;
using namespace quad;
// Find all variables used or defined in the function
void DataFlowInfo::findAllVars() {
#ifdef DEBUG
    cout << "Finding all variables in function: " << func->funcname << endl;
#endif
    //FILE IN THE CODE HERE TO FIND ALL VARIABLES used or defined in the function,
    //and filling in the allVars set, defs map and uses map 
    allVars.clear();
    defs->clear();
    uses->clear();

    if (!func || !func->quadblocklist) {
        return;
    }

    for (QuadBlock* block : *func->quadblocklist) {
        if (!block || !block->quadlist) {
            continue;
        }
        for (QuadStm* stmt : *block->quadlist) {
            if (!stmt) {
                continue;
            }

            if (stmt->def) {
                for (Temp* t : *stmt->def) {
                    if (!t) {
                        continue;
                    }
                    int var = t->num;
                    allVars.insert(var);
                    (*defs)[var].insert({block, stmt});
                }
            }

            if (stmt->use) {
                for (Temp* t : *stmt->use) {
                    if (!t) {
                        continue;
                    }
                    int var = t->num;
                    allVars.insert(var);
                    (*uses)[var].insert({block, stmt});
                }
            }
        }
    }
}

// Calculate both live-in and live-out sets for all statements
void DataFlowInfo::computeLiveness() {
#ifdef DEBUG
    cout << "Computing liveness for function: " << func->funcname << endl;
#endif
    //FILE IN THE CODE HERE TO CALCULATE BOTH LIVE-IN AND LIVE-OUT SETS for all statements in the function,
    livein->clear();
    liveout->clear();

    if (!func || !func->quadblocklist) {
        return;
    }

    map<int, QuadBlock*> labelToBlock;
    for (QuadBlock* block : *func->quadblocklist) {
        if (block && block->entry_label) {
            labelToBlock[block->entry_label->num] = block;
        }
    }

    // Initialize all statement live-in/live-out sets.
    for (QuadBlock* block : *func->quadblocklist) {
        if (!block || !block->quadlist) {
            continue;
        }
        for (QuadStm* stmt : *block->quadlist) {
            if (!stmt) {
                continue;
            }
            (*livein)[stmt] = set<int>();
            (*liveout)[stmt] = set<int>();
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;

        for (auto bIt = func->quadblocklist->rbegin(); bIt != func->quadblocklist->rend(); ++bIt) {
            QuadBlock* block = *bIt;
            if (!block || !block->quadlist) {
                continue;
            }

            vector<QuadStm*>& stmts = *block->quadlist;
            for (int i = static_cast<int>(stmts.size()) - 1; i >= 0; --i) {
                QuadStm* stmt = stmts[i];
                if (!stmt) {
                    continue;
                }

                set<int> newOut;
                if (i + 1 < static_cast<int>(stmts.size())) {
                    QuadStm* nextStmt = stmts[i + 1];
                    if (nextStmt) {
                        newOut.insert((*livein)[nextStmt].begin(), (*livein)[nextStmt].end());
                    }
                } else if (block->exit_labels) {
                    for (Label* succLabel : *block->exit_labels) {
                        if (!succLabel) {
                            continue;
                        }
                        auto succIt = labelToBlock.find(succLabel->num);
                        if (succIt == labelToBlock.end() || !succIt->second || !succIt->second->quadlist || succIt->second->quadlist->empty()) {
                            continue;
                        }
                        QuadStm* firstSuccStmt = succIt->second->quadlist->front();
                        if (firstSuccStmt) {
                            newOut.insert((*livein)[firstSuccStmt].begin(), (*livein)[firstSuccStmt].end());
                        }
                    }
                }

                set<int> newIn;
                if (stmt->use) {
                    for (Temp* t : *stmt->use) {
                        if (t) {
                            newIn.insert(t->num);
                        }
                    }
                }

                set<int> outMinusDef = newOut;
                if (stmt->def) {
                    for (Temp* t : *stmt->def) {
                        if (t) {
                            outMinusDef.erase(t->num);
                        }
                    }
                }
                newIn.insert(outMinusDef.begin(), outMinusDef.end());

                if (newOut != (*liveout)[stmt] || newIn != (*livein)[stmt]) {
                    (*liveout)[stmt] = newOut;
                    (*livein)[stmt] = newIn;
                    changed = true;
                }
            }
        }
    }
}

set<DataFlowInfo*>* dataFLowProg(QuadProgram* prog) {
    //THIS ONE IS DONE FOR YOU!
    // For each function in the program, compute its data flow information and 
    // return a set of DataFlowInfo for all functions
    if (!prog || !prog->quadFuncDeclList) return nullptr;
    set<DataFlowInfo*>* allDataFlows = new set<DataFlowInfo*>();

    size_t validFuncCnt = 0;
    for (auto func : *prog->quadFuncDeclList) {
        if (func && func->quadblocklist) {
            ++validFuncCnt;
        }
    }

    void* pool = nullptr;
    size_t poolIndex = 0;
    if (validFuncCnt > 0) {
        pool = ::operator new(sizeof(DataFlowInfo) * validFuncCnt);
    }

    for (auto func : *prog->quadFuncDeclList) {
        if (!func || !func->quadblocklist) continue;

        void* slot = static_cast<char*>(pool) + poolIndex * sizeof(DataFlowInfo);
        DataFlowInfo* dfInfo = new (slot) DataFlowInfo(func);
        ++poolIndex;
        dfInfo->findAllVars();
        dfInfo->computeLiveness();
#ifdef DEBUG
        cout << "Liveness information for function: " << func->funcname << endl;
        cout << dfInfo->printLiveness() << endl;
#endif
        allDataFlows->insert(dfInfo);
    }
    return allDataFlows;
}
