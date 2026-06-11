#define DEBUG
#undef DEBUG

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include "ig.hh"
#include "coloring.hh"

//return true if any node is removed
bool Coloring::simplify() {
#ifdef DEBUG
    cout << "Simplifying..." << endl;
#endif
    bool changed = false;
    
    // fill in the code.
    while (true) {
        int pick = -1;
        for (const auto& it : graph) {
            int node = it.first;
            if (isMachineReg(node)) continue;
            if ((int)it.second.size() < k && !isMove(node)) {
                pick = node;
                break;
            }
        }
        if (pick == -1) break;
        simplifiedNodes.push(pick);
        eraseNode(pick);
        changed = true;
    }

#ifdef DEBUG
    cout << "Simplifying done. Changed=" << changed << endl;
#endif
    return changed;
}

//return true if changed anything, false otherwise
bool Coloring::coalesce() {
#ifdef DEBUG
    cout << "Coalescing..." << endl;
#endif
    if (ig == nullptr) return false;
    bool changed = false;
    
    // fill in the code.
    auto degree = [&](int n) -> int {
        auto it = graph.find(n);
        if (it == graph.end()) return 0;
        return (int)it->second.size();
    };

    vector<pair<int, int>> moves(movePairs.begin(), movePairs.end());
    for (const auto& mv : moves) {
        int u = mv.first;
        int v = mv.second;

        if (u == v) {
            movePairs.erase(mv);
            changed = true;
            continue;
        }

        if (graph.find(u) == graph.end() || graph.find(v) == graph.end()) {
            movePairs.erase(mv);
            changed = true;
            continue;
        }

        // Distinct machine registers are precolored and should not be merged.
        if (isMachineReg(u) && isMachineReg(v)) {
            movePairs.erase(mv);
            changed = true;
            continue;
        }

        // Already interfering: constrained move, remove from move set.
        if (getNeighbors(u).find(v) != getNeighbors(u).end()) {
            movePairs.erase(mv);
            changed = true;
            continue;
        }

        // We try to coalesce x into y.
        int x = u;
        int y = v;

        // If exactly one side is precolored, make it y and use George's rule.
        if (isMachineReg(x) && !isMachineReg(y)) {
            std::swap(x, y);
        }

        bool canCoalesce = false;
        if (isMachineReg(y)) {
            // George's strategy:
            // for every t in Adj(x), either t adjacent to y, or degree(t) < k.
            canCoalesce = true;
            for (int t : getNeighbors(x)) {
                if (t == y) continue;
                bool adjacentToY = (getNeighbors(y).find(t) != getNeighbors(y).end());
                if (!adjacentToY && degree(t) >= k) {
                    canCoalesce = false;
                    break;
                }
            }
        } else {
            // Briggs' strategy:
            // Adj(x) U Adj(y) has fewer than k nodes with degree >= k.
            set<int> combined = getNeighbors(x);
            set<int> yNeighbors = getNeighbors(y);
            combined.insert(yNeighbors.begin(), yNeighbors.end());
            combined.erase(x);
            combined.erase(y);

            int highDegreeCnt = 0;
            for (int t : combined) {
                if (degree(t) >= k) {
                    ++highDegreeCnt;
                }
            }
            canCoalesce = highDegreeCnt < k;
        }

        if (!canCoalesce) {
            continue;
        }

        // Merge x into y.
        set<int> xNeighbors = getNeighbors(x);
        for (int n : xNeighbors) {
            if (n == y) continue;
            addEdge(y, n);
        }

        // Keep track of transitive coalescing for final color propagation.
        if (coalescedMoves.find(x) != coalescedMoves.end()) {
            coalescedMoves[y].insert(coalescedMoves[x].begin(), coalescedMoves[x].end());
            coalescedMoves.erase(x);
        }
        coalescedMoves[y].insert(x);

        eraseNode(x);

        // Rewrite move pairs to the representative y.
        set<pair<int, int>> rewrittenMoves;
        for (const auto& p : movePairs) {
            int a = p.first;
            int b = p.second;
            if (a == x) a = y;
            if (b == x) b = y;
            if (a != b) rewrittenMoves.insert({a, b});
        }
        movePairs.swap(rewrittenMoves);
        changed = true;
    }

    return changed;
}

//freeze the moves that are not coalesced
//return true if changed anything, false otherwise
bool Coloring::freeze() {
#ifdef DEBUG
    cout << "Freezing..." << endl;
#endif
    bool changed = false;

    // fill in the code.
    int pick = -1;
    for (const auto& it : graph) {
        int node = it.first;
        if (isMachineReg(node)) continue;
        if ((int)it.second.size() < k && isMove(node)) {
            pick = node;
            break;
        }
    }
    if (pick != -1) {
        vector<pair<int, int>> eraseList;
        for (const auto& p : movePairs) {
            if (p.first == pick || p.second == pick) {
                eraseList.push_back(p);
            }
        }
        for (const auto& p : eraseList) {
            movePairs.erase(p);
        }
        changed = !eraseList.empty();
    }

    return changed;
}

//This is a soft spill: we just remove the node from the graph and add it to the simplified nodes
//as if nothing happened. The actual spill happens when select&coloring
bool Coloring::spill() {
#ifdef DEBUG
    cout << "Spilling..." << endl;
#endif

    bool changed = false;
    
    //fill in the code.
    int candidate = -1;
    int bestDegree = -1;
    for (const auto& it : graph) {
        int node = it.first;
        if (isMachineReg(node)) continue;
        int deg = (int)it.second.size();
        if (deg >= k && deg > bestDegree) {
            bestDegree = deg;
            candidate = node;
        }
    }
    if (candidate != -1) {
        simplifiedNodes.push(candidate);
        eraseNode(candidate);
        changed = true;
    }

    return changed;
}

//now try to select the registers for the nodes
bool Coloring::select() {
#ifdef DEBUG
    cout << "Selecting..." << endl;
#endif

    bool all_covered = false;

    // fill in the code.
    // Precolored machine regs keep their own color number.
    for (const auto& it : ig->graph) {
        if (isMachineReg(it.first)) {
            colors[it.first] = it.first;
        }
    }

    while (!simplifiedNodes.empty()) {
        int node = simplifiedNodes.top();
        simplifiedNodes.pop();

        if (isMachineReg(node)) {
            colors[node] = node;
            continue;
        }

        set<int> forbidden;
        auto it = ig->graph.find(node);
        if (it != ig->graph.end()) {
            for (int nb : it->second) {
                auto cIt = colors.find(nb);
                if (cIt != colors.end() && cIt->second >= 0 && cIt->second < k) {
                    forbidden.insert(cIt->second);
                }
            }
        }

        int chosen = -1;
        for (int c = 0; c < k; ++c) {
            if (forbidden.find(c) == forbidden.end()) {
                chosen = c;
                break;
            }
        }

        if (chosen == -1) {
            spilled.insert(node);
        } else {
            colors[node] = chosen;
        }
    }

    for (const auto& mv : coalescedMoves) {
        int rep = mv.first;
        if (spilled.find(rep) != spilled.end()) {
            spilled.insert(mv.second.begin(), mv.second.end());
            continue;
        }
        if (colors.find(rep) != colors.end()) {
            for (int n : mv.second) {
                colors[n] = colors[rep];
            }
        }
    }

    all_covered = true;
    for (const auto& it : ig->graph) {
        int node = it.first;
        if (spilled.find(node) == spilled.end() && colors.find(node) == colors.end()) {
            all_covered = false;
            break;
        }
    }

    return all_covered; //return true if all nodes are colored, false otherwise
}
