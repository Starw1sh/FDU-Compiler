// #define DEBUG
#undef DEBUG

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include "temp.hh"
#include "ig.hh"
#include "asmdataflow.hh"
#include "asmprog.hh"

using namespace std;

// Build interference graphs for all functions in AsmProg

namespace {
void addConflictEdge(map<int, set<int>>& graph, int a, int b) {
    if (a == b) {
        return;
    }
    graph[a].insert(b);
    graph[b].insert(a);
}
}

InterferenceGraph *buildIg(instr::AsmFunction* asmFunc, instr::AsmDataFlowInfo* flowInfo) {
    map<int, set<int>> graph;
    set<pair<int, int>> movePairs;

    if (asmFunc == nullptr || flowInfo == nullptr) {
        return new InterferenceGraph(graph, movePairs);
    }

    for (size_t i = 0; i < asmFunc->instructions.size(); ++i) {
        const instr::AssemInstr& instr = asmFunc->instructions[i];
        set<int> use = flowInfo->getUse(i);
        set<int> def = flowInfo->getDef(i);
        set<int> liveout = flowInfo->liveout[i];

        for (int t : use) {
            graph[t];
        }
        for (int t : def) {
            graph[t];
        }
        for (int t : liveout) {
            graph[t];
        }

        // Temps simultaneously used in one instruction must not share a register.
        vector<int> useVec(use.begin(), use.end());
        for (size_t ui = 0; ui < useVec.size(); ++ui) {
            for (size_t uj = ui + 1; uj < useVec.size(); ++uj) {
                addConflictEdge(graph, useVec[ui], useVec[uj]);
            }
        }

        // Multiple defs in one instruction must also be distinct.
        vector<int> defVec(def.begin(), def.end());
        for (size_t di = 0; di < defVec.size(); ++di) {
            for (size_t dj = di + 1; dj < defVec.size(); ++dj) {
                addConflictEdge(graph, defVec[di], defVec[dj]);
            }
        }

        // For move instructions, do not add interference between dst and src directly.
        set<int> conflictSet = liveout;
        if (instr.kind == instr::AssemInstr::I_MOVE) {
            for (int t : use) {
                conflictSet.erase(t);
            }
            if (!instr.dst.empty() && !instr.src.empty() &&
                instr.dst[0] != nullptr && instr.src[0] != nullptr &&
                instr.dst[0]->num != instr.src[0]->num) {
                movePairs.insert({instr.dst[0]->num, instr.src[0]->num});
            }
        }

        for (int d : def) {
            for (int l : conflictSet) {
                addConflictEdge(graph, d, l);
            }
        }
    }

    return new InterferenceGraph(graph, movePairs);
}

vector<InterferenceGraph*> buildIgProg(instr::AsmProg* program) {
    vector<InterferenceGraph*> graphs;
    
    if (program == nullptr || program->functions.empty()) {
        return graphs;
    }

#ifdef DEBUG
    cout << "Building interference graphs for program with " << program->functions.size() << " functions" << endl;
#endif

    //fill the code. Build Ig for each function.
    for (auto& func : program->functions) {
        instr::AsmDataFlowInfo flowInfo(&func);
        flowInfo.computeLiveness();
        graphs.push_back(buildIg(&func, &flowInfo));
    }

    return graphs;
}