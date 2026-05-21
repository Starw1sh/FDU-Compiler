#include <stack>
#include <map>
#include <set>
#include <vector>
#include "loopopt.hh"
#include "flowinfo.hh"
#include "quad.hh"

// Function to find loop headers in a function and populate the LoopHeaderMap
// Complete the function!!

LoopHeaderMap *findLoopHeaders(QuadFuncDecl* func, FuncFlowInfo *ffi) {
    LoopHeaderMap *loopHeaderMap = new LoopHeaderMap();
    loopHeaderMap->initFunc(func);

    if (func == nullptr || ffi == nullptr || ffi->cfi == nullptr) {
        return loopHeaderMap;
    }

    ControlFlowInfo *cfi = ffi->cfi;
    // Fill in the loop header map for the function
    map<int, set<int>> headerToBody;

    for (const auto& [sourceLabel, succs] : cfi->successors) {
        auto domIt = cfi->dominators.find(sourceLabel);
        if (domIt == cfi->dominators.end()) {
            continue;
        }

        for (int targetLabel : succs) {
            if (!domIt->second.count(targetLabel)) {
                continue;
            }

            set<int>& loopBody = headerToBody[targetLabel];
            loopBody.insert(targetLabel);

            vector<int> worklist = {sourceLabel};
            while (!worklist.empty()) {
                int currentLabel = worklist.back();
                worklist.pop_back();

                if (!loopBody.insert(currentLabel).second) {
                    continue;
                }

                auto predIt = cfi->predecessors.find(currentLabel);
                if (predIt == cfi->predecessors.end()) {
                    continue;
                }

                for (int predLabel : predIt->second) {
                    if (!loopBody.count(predLabel)) {
                        worklist.push_back(predLabel);
                    }
                }
            }
        }
    }

    set<LoopHeader*> loopHeaders;
    for (const auto& [headerLabel, bodyBlocks] : headerToBody) {
        loopHeaders.insert(new LoopHeader(headerLabel, bodyBlocks));
    }

    loopHeaderMap->addLoopHeader(func, loopHeaders);

    return loopHeaderMap;
}