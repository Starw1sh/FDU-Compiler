#include <stack>
#include <map>
#include <set>
#include <algorithm>
#include <vector>
#include "loopheader.hh"
#include "flowinfo.hh"
#include "quad.hh"

using namespace std;
using namespace quad;

LoopHeaderMap* findLoopHeadersWithFlow(QuadFuncDecl* func, ControlFlowInfo* flowInfo) {
    if (func == nullptr || flowInfo == nullptr) {
        return new LoopHeaderMap();  // Return empty map if missing required info
    }

    LoopHeaderMap* loopHeaderMap = new LoopHeaderMap();
    loopHeaderMap->initFunc(func);

    map<int, set<int>> headerToBody;

    for (const auto& [sourceLabel, succs] : flowInfo->successors) {
        auto domIt = flowInfo->dominators.find(sourceLabel);
        if (domIt == flowInfo->dominators.end()) {
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

                auto predIt = flowInfo->predecessors.find(currentLabel);
                if (predIt == flowInfo->predecessors.end()) {
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