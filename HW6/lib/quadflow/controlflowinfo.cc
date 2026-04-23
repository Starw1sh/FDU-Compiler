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
    // 使用BFS/DFS从入口块遍历所有可达块，剩下的就是不可达块
    unreachableBlocks.clear();
    if (entryBlock == -1) return;
    set<int> visited;
    queue<int> q;
    q.push(entryBlock);
    visited.insert(entryBlock);
    while (!q.empty()) {
        int cur = q.front(); q.pop();
        if (successors.count(cur)) {
            for (int succ : successors[cur]) {
                if (!visited.count(succ)) {
                    visited.insert(succ);
                    q.push(succ);
                }
            }
        }
    }
    for (int b : allBlocks) {
        if (!visited.count(b)) unreachableBlocks.insert(b);
    }
}

void ControlFlowInfo::eliminateUnreachableBlocks() {
#ifdef DEBUG
    cout << "Eliminating unreachable blocks in function: " << func->funcname << endl;
#endif
    // FILE IN THE CODE HERE TO ELIMINATE UNREACHABLE BLOCKS from the function,
    // and emptying all the sets and maps above since everything may need to be recomputed!
    // 先移除不可达块
    if (unreachableBlocks.empty()) return;
    // 移除func->quadblocklist中对应的block
    auto &blocks = *func->quadblocklist;
    blocks.erase(
        remove_if(blocks.begin(), blocks.end(), [&](quad::QuadBlock* blk) {
            return blk && blk->entry_label && unreachableBlocks.count(blk->entry_label->num);
        }),
        blocks.end()
    );
    // 清空所有分析结果
    allBlocks.clear();
    labelToBlock.clear();
    predecessors.clear();
    successors.clear();
    dominators.clear();
    immediateDominator.clear();
    dominanceFrontiers.clear();
    domTree.clear();
    unreachableBlocks.clear();
}

void ControlFlowInfo::computePredecessors() {
    // Compute predecessors for each block
    // FILE IN THE CODE HERE TO COMPUTE PREDECESSORS for each block
    predecessors.clear();
    for (int b : allBlocks) predecessors[b] = set<int>();
    for (int b : allBlocks) {
        if (!labelToBlock.count(b)) continue;
        quad::QuadBlock* blk = labelToBlock[b];
        if (!blk->exit_labels) continue;
        for (auto lbl : *blk->exit_labels) {
            if (lbl && allBlocks.count(lbl->num)) {
                predecessors[lbl->num].insert(b);
            }
        }
    }
}

void ControlFlowInfo::computeSuccessors() {
    // Compute successors for each block
    // FILE IN THE CODE HERE TO COMPUTE SUCCESSORS for each block
    successors.clear();
    for (int b : allBlocks) successors[b] = set<int>();
    for (int b : allBlocks) {
        if (!labelToBlock.count(b)) continue;
        quad::QuadBlock* blk = labelToBlock[b];
        if (!blk->exit_labels) continue;
        for (auto lbl : *blk->exit_labels) {
            if (lbl && allBlocks.count(lbl->num)) {
                successors[b].insert(lbl->num);
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
    // 经典迭代算法
    dominators.clear();
    for (int b : allBlocks) {
        if (b == entryBlock) dominators[b] = {b};
        else dominators[b] = allBlocks;
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int b : allBlocks) {
            if (b == entryBlock) continue;
            set<int> newDom = allBlocks;
            for (int p : predecessors[b]) {
                set<int> tmp;
                set_intersection(newDom.begin(), newDom.end(), dominators[p].begin(), dominators[p].end(), inserter(tmp, tmp.begin()));
                newDom = tmp;
            }
            newDom.insert(b);
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
    for (int b : allBlocks) {
        if (b == entryBlock) continue;
        set<int> doms = dominators[b];
        doms.erase(b);
        int idom = -1;
        for (int d : doms) {
            bool isImm = true;
            for (int d2 : doms) {
                if (d == d2) continue;
                if (dominators[d2].count(d)) {
                    isImm = false;
                    break;
                }
            }
            if (isImm) { idom = d; break; }
        }
        if (idom != -1) immediateDominator[b] = idom;
    }
}

void ControlFlowInfo::computeDomTree() {
    #ifdef DEBUG
        std::cout << "Computing dominator tree for: " << func->funcname << endl;
    #endif
    // FILE IN THE CODE HERE TO COMPUTE DOMINATOR TREE using immediate dominators
    domTree.clear();
    for (int b : allBlocks) {
        if (immediateDominator.count(b)) {
            int idom = immediateDominator[b];
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
    for (int b : allBlocks) {
        set<int> df;
        if (!successors.count(b)) continue;
        for (int s : successors[b]) {
            if (immediateDominator.count(s) && immediateDominator[s] != b) {
                df.insert(s);
            }
        }
        for (int c : domTree[b]) {
            for (int w : dominanceFrontiers[c]) {
                if (!dominators[b].count(w) || b == w) {
                    df.insert(w);
                }
            }
        }
        dominanceFrontiers[b] = df;
    }

}
