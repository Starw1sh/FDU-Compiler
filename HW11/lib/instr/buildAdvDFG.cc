#include "advDFG.hh"

#include <algorithm>
#include <unordered_map>
#include <vector>

namespace instr {

static int tempNumOf(const tree::Temp *temp) {
    return temp == nullptr ? -1 : temp->num;
}

static int firstDefinedTemp(const quad::QuadStm *stm) {
    if (stm == nullptr || stm->def == nullptr || stm->def->empty()) {
        return -1;
    }

    int out = -1;
    for (auto *temp : *stm->def) {
        int num = tempNumOf(temp);
        if (num < 0) {
            continue;
        }
        if (out < 0 || num < out) {
            out = num;
        }
    }
    return out;
}

static std::set<int> usedTemps(const quad::QuadStm *stm) {
    std::set<int> out;
    if (stm == nullptr || stm->use == nullptr) {
        return out;
    }

    for (auto *temp : *stm->use) {
        int num = tempNumOf(temp);
        if (num >= 0) {
            out.insert(num);
        }
    }
    return out;
}

static bool isExitLike(const quad::QuadStm *stm) {
    if (stm == nullptr) {
        return false;
    }
    return stm->kind == quad::QuadKind::JUMP ||
           stm->kind == quad::QuadKind::CJUMP ||
           stm->kind == quad::QuadKind::RETURN;
}

advDFGprog *buildAdvDFGprog(const quad::QuadProgram *program) {
    auto *out = new advDFGprog(program);
    if (program == nullptr || program->quadFuncDeclList == nullptr) {
        return out;
    }

    /// fill in the code ...

    for (auto *func : *program->quadFuncDeclList) {
        if (func == nullptr) {
            continue;
        }

        auto *funcGraph = new advDFGfunc(func);
        out->addFunc(funcGraph);

        if (func->quadblocklist == nullptr) {
            continue;
        }

        for (auto *block : *func->quadblocklist) {
            if (block == nullptr) {
                continue;
            }

            auto *blockGraph = new advDFGblock(block);
            funcGraph->addBlock(blockGraph);

            auto *entryNode = new advDFGNode(NodeType::EntryLabel, nullptr);
            blockGraph->graph.addNode(entryNode);

            std::unordered_map<int, advDFGNode*> lastTempDef;
            advDFGNode *previousNode = entryNode;
            int chainIndex = 0;

            if (block->quadlist == nullptr) {
                continue;
            }

            for (auto *stm : *block->quadlist) {
                if (stm == nullptr || stm->kind == quad::QuadKind::LABEL) {
                    continue;
                }

                NodeType nodeType = isExitLike(stm) ? NodeType::ExitStatement : NodeType::Statement;
                auto *node = new advDFGNode(nodeType, stm);
                node->tempDefined = firstDefinedTemp(stm);
                node->tempsUsed = usedTemps(stm);
                node->chainDefined = chainIndex;
                node->chainUsed = previousNode == entryNode ? -1 : previousNode->chainDefined;

                blockGraph->graph.addNode(node);
                blockGraph->graph.addEdge(previousNode, node);

                for (int tempNum : node->tempsUsed) {
                    auto it = lastTempDef.find(tempNum);
                    if (it != lastTempDef.end() && it->second != nullptr && it->second != previousNode) {
                        blockGraph->graph.addEdge(it->second, node);
                    }
                }

                if (node->tempDefined >= 0) {
                    lastTempDef[node->tempDefined] = node;
                }

                previousNode = node;
                ++chainIndex;
            }
        }
    }

    return out;

}

} // namespace instr
