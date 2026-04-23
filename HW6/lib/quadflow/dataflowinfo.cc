#define DEBUG
#undef DEBUG

#include <iostream>
#include <queue>
#include <algorithm>
#include <map>
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
    if (!func || !func->quadblocklist) return;
    for (auto block : *func->quadblocklist) {
        if (!block || !block->quadlist) continue;
        for (auto stm : *block->quadlist) {
            if (!stm) continue;
            // def/use 是 Temp* 集合
            if (stm->def) {
                for (auto t : *stm->def) {
                    if (!t) continue;
                    allVars.insert(t->num);
                    (*defs)[t->num].insert({block, stm});
                }
            }
            if (stm->use) {
                for (auto t : *stm->use) {
                    if (!t) continue;
                    allVars.insert(t->num);
                    (*uses)[t->num].insert({block, stm});
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
    if (!func || !func->quadblocklist) return;
    // 收集所有语句
    vector<quad::QuadStm*> stmts;
    map<quad::QuadStm*, set<quad::QuadStm*>> succs;
    map<quad::QuadStm*, set<int>> defmap, usemap;
    map<quad::QuadStm*, quad::QuadBlock*> stmt2block;
    for (auto block : *func->quadblocklist) {
        if (!block || !block->quadlist) continue;
        for (size_t i = 0; i < block->quadlist->size(); ++i) {
            quad::QuadStm* stm = block->quadlist->at(i);
            if (!stm) continue;
            stmts.push_back(stm);
            stmt2block[stm] = block;
            if (stm->def) {
                set<int> defnums;
                for (auto t : *stm->def) if (t) defnums.insert(t->num);
                defmap[stm] = defnums;
            }
            if (stm->use) {
                set<int> usenums;
                for (auto t : *stm->use) if (t) usenums.insert(t->num);
                usemap[stm] = usenums;
            }
        }
    }
    // 构建语句级后继关系
    for (auto block : *func->quadblocklist) {
        if (!block || !block->quadlist || block->quadlist->empty()) continue;
        for (size_t i = 0; i < block->quadlist->size(); ++i) {
            quad::QuadStm* stm = block->quadlist->at(i);
            if (!stm) continue;
            set<quad::QuadStm*> sset;
            if (i + 1 < block->quadlist->size()) {
                sset.insert(block->quadlist->at(i + 1));
            } else {
                // 最后一条语句，后继是本块所有出口块的第一条语句
                if (block->exit_labels) {
                    for (auto lbl : *block->exit_labels) {
                        for (auto b2 : *func->quadblocklist) {
                            if (b2 && b2->entry_label && lbl && b2->entry_label->num == lbl->num && b2->quadlist && !b2->quadlist->empty()) {
                                sset.insert(b2->quadlist->at(0));
                            }
                        }
                    }
                }
            }
            succs[stm] = sset;
        }
    }
    // 迭代求解
    map<quad::QuadStm*, set<int>> in, out;
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto stm : stmts) {
            set<int> old_in = in[stm], old_out = out[stm];
            // out = 所有后继的 in
            set<int> new_out;
            for (auto s : succs[stm]) {
                new_out.insert(in[s].begin(), in[s].end());
            }
            out[stm] = new_out;
            // in = use ∪ (out - def)
            set<int> new_in = usemap[stm];
            set<int> out_minus_def;
            set_difference(out[stm].begin(), out[stm].end(), defmap[stm].begin(), defmap[stm].end(), inserter(out_minus_def, out_minus_def.begin()));
            new_in.insert(out_minus_def.begin(), out_minus_def.end());
            in[stm] = new_in;
            if (in[stm] != old_in || out[stm] != old_out) changed = true;
        }
    }
    // 写回
    for (auto stm : stmts) {
        (*livein)[stm] = in[stm];
        (*liveout)[stm] = out[stm];
    }
}

set<DataFlowInfo*>* dataFLowProg(QuadProgram* prog) {
    //THIS ONE IS DONE FOR YOU!
    // For each function in the program, compute its data flow information and 
    // return a set of DataFlowInfo for all functions
    if (!prog || !prog->quadFuncDeclList) return nullptr;
    set<DataFlowInfo*>* allDataFlows = new set<DataFlowInfo*>();
    for (auto func : *prog->quadFuncDeclList) {
        if (!func || !func->quadblocklist) continue;
        
        DataFlowInfo* dfInfo = new DataFlowInfo(func);
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
