#define DEBUG
#undef DEBUG

#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <queue>
#include <algorithm>
#include "temp.hh"
#include "quad.hh"
#include "flowinfo.hh"

using namespace std;
using namespace quad;

void ControlFlowInfo::computeAllBlocks() {
    // This one is done for you!
#ifdef DEBUG
    cout << "Computing all blocks in function: " << func->funcname << endl;
    cout << "#blocks = " << func->quadblocklist->size() << endl;
#endif
    // Compute all blocks in the function
    if (func == nullptr || func->quadblocklist == nullptr) {
        return ; // Nothing to do
    }
    //Collect block information
    allBlocks = set<int>(); //empty set
    labelToBlock = map<int, QuadBlock*>(); //empty map

    for (auto block : *func->quadblocklist) {
        if (block->entry_label) {
            allBlocks.insert(block->entry_label->num);
            labelToBlock[block->entry_label->num] = block;
        }
    }
#ifdef DEBUG
    cout << "All blocks in function: " << func->funcname << endl;
    for (auto block : allBlocks) {
        cout << block << " " << labelToBlock[block]->entry_label->str() << endl;
    }
    cout << endl;
#endif
}

void ControlFlowInfo::computeUnreachableBlocks() {
#ifdef DEBUG
    cout << "Computing unreachable blocks in function: " << func->funcname << endl;
#endif
    // FILE IN THE CODE HERE TO COMPUTE UNREACHABLE BLOCKS
    unreachableBlocks.clear();
    if (!func || !func->quadblocklist || allBlocks.empty() || entryBlock == -1) {
        return;
    }

    set<int> reachable;
    queue<int> work;
    reachable.insert(entryBlock);
    work.push(entryBlock);

    while (!work.empty()) {
        int b = work.front();
        work.pop();

        auto blockIt = labelToBlock.find(b);
        if (blockIt == labelToBlock.end() || !blockIt->second || !blockIt->second->exit_labels) {
            continue;
        }

        for (Label* succLabel : *blockIt->second->exit_labels) {
            if (!succLabel) {
                continue;
            }
            int succ = succLabel->num;
            if (allBlocks.find(succ) == allBlocks.end()) {
                continue;
            }
            if (reachable.insert(succ).second) {
                work.push(succ);
            }
        }
    }

    for (int b : allBlocks) {
        if (reachable.find(b) == reachable.end()) {
            unreachableBlocks.insert(b);
        }
    }
}

void ControlFlowInfo::eliminateUnreachableBlocks() {
#ifdef DEBUG
    cout << "Eliminating unreachable blocks in function: " << func->funcname << endl;
#endif
    // FILE IN THE CODE HERE TO ELIMINATE UNREACHABLE BLOCKS from the function,
    // and emptying all the sets and maps above since everything may need to be recomputed!
    if (!func || !func->quadblocklist || unreachableBlocks.empty()) {
        predecessors.clear();
        successors.clear();
        dominators.clear();
        immediateDominator.clear();
        dominanceFrontiers.clear();
        domTree.clear();
        computeAllBlocks();
        return;
    }

    vector<QuadBlock*>* newBlocks = new vector<QuadBlock*>();
    newBlocks->reserve(func->quadblocklist->size());
    for (QuadBlock* block : *func->quadblocklist) {
        if (!block || !block->entry_label) {
            continue;
        }
        if (unreachableBlocks.find(block->entry_label->num) == unreachableBlocks.end()) {
            newBlocks->push_back(block);
        }
    }
    func->quadblocklist = newBlocks;

    allBlocks.clear();
    unreachableBlocks.clear();
    labelToBlock.clear();
    predecessors.clear();
    successors.clear();
    dominators.clear();
    immediateDominator.clear();
    dominanceFrontiers.clear();
    domTree.clear();

    computeAllBlocks();
}

void ControlFlowInfo::computePredecessors() {
    // Compute predecessors for each block
    // FILE IN THE CODE HERE TO COMPUTE PREDECESSORS for each block
    predecessors.clear();
    if (!func || !func->quadblocklist) {
        return;
    }

    for (int b : allBlocks) {
        predecessors[b] = set<int>();
    }

    for (int b : allBlocks) {
        auto blockIt = labelToBlock.find(b);
        if (blockIt == labelToBlock.end() || !blockIt->second || !blockIt->second->exit_labels) {
            continue;
        }
        for (Label* succLabel : *blockIt->second->exit_labels) {
            if (!succLabel) {
                continue;
            }
            int succ = succLabel->num;
            if (allBlocks.find(succ) != allBlocks.end()) {
                predecessors[succ].insert(b);
            }
        }
    }
}

void ControlFlowInfo::computeSuccessors() {
    // Compute successors for each block
    // FILE IN THE CODE HERE TO COMPUTE SUCCESSORS for each block
    successors.clear();
    if (!func || !func->quadblocklist) {
        return;
    }

    for (int b : allBlocks) {
        successors[b] = set<int>();
    }

    for (int b : allBlocks) {
        auto blockIt = labelToBlock.find(b);
        if (blockIt == labelToBlock.end() || !blockIt->second || !blockIt->second->exit_labels) {
            continue;
        }
        for (Label* succLabel : *blockIt->second->exit_labels) {
            if (!succLabel) {
                continue;
            }
            int succ = succLabel->num;
            if (allBlocks.find(succ) != allBlocks.end()) {
                successors[b].insert(succ);
            }
        }
    }
}

void ControlFlowInfo::computeDominators() {
#ifdef DEBUG
    std::cout << "Computing dominators for: " << func->funcname << endl;
#endif
    // Compute dominators for each block
    // FILE IN THE CODE HERE TO COMPUTE DOMINATORS for each block
    dominators.clear();
    if (!func || !func->quadblocklist || allBlocks.empty() || entryBlock == -1) {
        return;
    }

    for (int b : allBlocks) {
        if (b == entryBlock) {
            dominators[b] = {entryBlock};
        } else {
            dominators[b] = allBlocks;
        }
    }

    bool changed = true;
    while (changed) {
        changed = false;
        for (int b : allBlocks) {
            if (b == entryBlock) {
                continue;
            }

            set<int> newDom;
            auto predIt = predecessors.find(b);
            if (predIt == predecessors.end() || predIt->second.empty()) {
                newDom.insert(b);
            } else {
                bool first = true;
                for (int p : predIt->second) {
                    if (first) {
                        newDom = dominators[p];
                        first = false;
                    } else {
                        set<int> inter;
                        set_intersection(newDom.begin(), newDom.end(),
                                         dominators[p].begin(), dominators[p].end(),
                                         inserter(inter, inter.begin()));
                        newDom = inter;
                    }
                }
                newDom.insert(b);
            }

            if (newDom != dominators[b]) {
                dominators[b] = newDom;
                changed = true;
            }
        }
    }
}

void ControlFlowInfo::computeImmediateDominator() {
#ifdef DEBUG
    std::cout << "Start to find immediate dominators for: " << func->funcname << endl;
#endif
    //FILE IN THE CODE HERE TO COMPUTE IMMEDIATE DOMINATOR for each block, using the dominators information computed above
    immediateDominator.clear();
    if (!func || !func->quadblocklist || allBlocks.empty()) {
        return;
    }

    for (int b : allBlocks) {
        if (b == entryBlock) {
            immediateDominator[b] = -1;
            continue;
        }

        set<int> strictDom = dominators[b];
        strictDom.erase(b);

        int idom = -1;
        for (int d : strictDom) {
            bool isImmediate = true;
            for (int other : strictDom) {
                if (other == d) {
                    continue;
                }
                if (dominators[other].find(d) != dominators[other].end()) {
                    isImmediate = false;
                    break;
                }
            }
            if (isImmediate) {
                idom = d;
                break;
            }
        }
        immediateDominator[b] = idom;
    }
}

void ControlFlowInfo::computeDomTree() {
    #ifdef DEBUG
        std::cout << "Computing dominator tree for: " << func->funcname << endl;
    #endif
    // FILE IN THE CODE HERE TO COMPUTE DOMINATOR TREE using immediate dominators
    domTree.clear();
    if (!func || !func->quadblocklist) {
        return;
    }

    for (int b : allBlocks) {
        domTree[b] = set<int>();
    }

    for (const auto& kv : immediateDominator) {
        int b = kv.first;
        int idom = kv.second;
        if (idom != -1) {
            domTree[idom].insert(b);
        }
    }
}

void ControlFlowInfo::computeDominanceFrontiers() {
#ifdef DEBUG
    std::cout << "Computing dominance frontier for: " << func->funcname << endl;
#endif

    //FILE IN THE CODE HERE TO COMPUTE DOMINANCE FRONTIER for each block, using the successors, dominators, immediate dominator, and domTree information computed above

    dominanceFrontiers.clear();
    if (!func || !func->quadblocklist) {
        return;
    }

    for (int b : allBlocks) {
        dominanceFrontiers[b] = set<int>();
    }

    for (int b : allBlocks) {
        auto predIt = predecessors.find(b);
        if (predIt == predecessors.end() || predIt->second.size() < 2) {
            continue;
        }

        int idomB = -1;
        auto idomIt = immediateDominator.find(b);
        if (idomIt != immediateDominator.end()) {
            idomB = idomIt->second;
        }

        for (int p : predIt->second) {
            int runner = p;
            while (runner != -1 && runner != idomB) {
                dominanceFrontiers[runner].insert(b);
                auto runnerIdomIt = immediateDominator.find(runner);
                if (runnerIdomIt == immediateDominator.end()) {
                    break;
                }
                runner = runnerIdomIt->second;
            }
        }
    }

}
