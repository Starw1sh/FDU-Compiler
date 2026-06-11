#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <regex>
#include <sstream>
#include "asmprogpass.hh"
#include "temp.hh"

using namespace std;
using namespace tree;

namespace instr {

string getRegName(int colorNum) {
    return "r" + to_string(colorNum);
}

string getTempRegName(int tempNum, const Coloring* coloring) {
    if (tempNum < 100) {
        return getRegName(tempNum);
    }
    if (coloring == nullptr) {
        return "";
    }
    auto it = coloring->colors.find(tempNum);
    if (it == coloring->colors.end()) {
        return "";
    }
    return getRegName(it->second);
}

namespace {

tree::Temp* regTemp(int regNum) {
    return new tree::Temp(regNum);
}

AssemInstr makeLoadSpill(const string& reg, int offset) {
    return AssemInstr::Oper("ldr " + reg + ", [fp, #-" + to_string(offset) + "]", {}, {}, AssemTargets());
}

AssemInstr makeStoreSpill(const string& reg, int offset) {
    return AssemInstr::Oper("str " + reg + ", [fp, #-" + to_string(offset) + "]", {}, {}, AssemTargets());
}

int parseImmediate(const string& assem, const string& prefix) {
    smatch m;
    regex r("^" + prefix + R"(\s*#([0-9]+)\s*$)");
    if (regex_match(assem, m, r)) {
        return stoi(m[1].str());
    }
    return -1;
}

} // namespace

AsmProg* asmprog2colored(AsmProg* program, const vector<Coloring*>& colorings) {
    AsmProg* colored = new AsmProg();
    
    // fill in the code.
    if (program == nullptr) {
        return colored;
    }

    colored->functions.reserve(program->functions.size());
    for (size_t i = 0; i < program->functions.size(); ++i) {
        const AsmFunction& func = program->functions[i];
        const Coloring* coloring = (i < colorings.size()) ? colorings[i] : nullptr;

        AsmFunction outFunc(func.name);
        const int spillCount = (coloring == nullptr) ? 0 : (int)coloring->spilled.size();
        map<int, int> spillOffset;
        int slot = 0;
        if (coloring != nullptr) {
            for (int t : coloring->spilled) {
                spillOffset[t] = 40 + slot * 4;
                ++slot;
            }
        }

        for (const AssemInstr& instr : func.instructions) {
            // Patch stack-frame constants to reserve spill slots.
            if (spillCount > 0 && instr.assem.rfind("sub sp, sp, #", 0) == 0) {
                int imm = parseImmediate(instr.assem, "sub sp, sp,");
                if (imm >= 0) {
                    AssemInstr patched = instr;
                    patched.assem = "sub sp, sp, #" + to_string(imm + spillCount * 4);
                    outFunc.instructions.push_back(patched);
                    continue;
                }
            }
            if (spillCount > 0 && instr.assem.rfind("add fp, sp, #", 0) == 0) {
                int imm = parseImmediate(instr.assem, "add fp, sp,");
                if (imm >= 0) {
                    AssemInstr patched = instr;
                    patched.assem = "add fp, sp, #" + to_string(imm + spillCount * 4);
                    outFunc.instructions.push_back(patched);
                    continue;
                }
            }
            if (spillCount > 0 && instr.assem.rfind("sub sp, fp, #", 0) == 0) {
                int imm = parseImmediate(instr.assem, "sub sp, fp,");
                if (imm >= 0) {
                    AssemInstr patched = instr;
                    patched.assem = "sub sp, fp, #" + to_string(imm + spillCount * 4);
                    outFunc.instructions.push_back(patched);
                    continue;
                }
            }
            if (spillCount > 0 && instr.assem.rfind("add sp, sp, #", 0) == 0) {
                int imm = parseImmediate(instr.assem, "add sp, sp,");
                if (imm >= 0) {
                    AssemInstr patched = instr;
                    patched.assem = "add sp, sp, #" + to_string(imm + spillCount * 4);
                    outFunc.instructions.push_back(patched);
                    continue;
                }
            }

            if (instr.kind == AssemInstr::I_LABEL) {
                outFunc.instructions.push_back(instr);
                continue;
            }

            vector<AssemInstr> prologueLoads;
            vector<AssemInstr> epilogueStores;
            AssemInstr patched = instr;
            patched.src.clear();
            patched.dst.clear();

            // Replace source temps with colored registers or reload from spills.
            int srcSpillScratch = 0;
            for (size_t si = 0; si < instr.src.size(); ++si) {
                tree::Temp* t = instr.src[si];
                if (t == nullptr) {
                    continue;
                }
                int num = t->num;
                if (num < 100) {
                    patched.src.push_back(regTemp(num));
                    continue;
                }

                bool isSpilled = (coloring != nullptr && coloring->spilled.find(num) != coloring->spilled.end());
                if (isSpilled) {
                    string scratch = (srcSpillScratch % 2 == 0) ? "r9" : "r10";
                    int scratchNum = (srcSpillScratch % 2 == 0) ? 9 : 10;
                    ++srcSpillScratch;
                    prologueLoads.push_back(makeLoadSpill(scratch, spillOffset[num]));
                    patched.src.push_back(regTemp(scratchNum));
                } else {
                    auto cIt = (coloring == nullptr) ? map<int, int>::const_iterator() : coloring->colors.find(num);
                    int reg = (cIt == coloring->colors.end()) ? 0 : cIt->second;
                    patched.src.push_back(regTemp(reg));
                }
            }

            // Replace destination temps with colored registers; spill results back to stack slots.
            int dstSpillScratch = 0;
            for (size_t di = 0; di < instr.dst.size(); ++di) {
                tree::Temp* t = instr.dst[di];
                if (t == nullptr) {
                    continue;
                }
                int num = t->num;
                if (num < 100) {
                    patched.dst.push_back(regTemp(num));
                    continue;
                }

                bool isSpilled = (coloring != nullptr && coloring->spilled.find(num) != coloring->spilled.end());
                if (isSpilled) {
                    string scratch = (dstSpillScratch % 2 == 0) ? "r9" : "r10";
                    int scratchNum = (dstSpillScratch % 2 == 0) ? 9 : 10;
                    ++dstSpillScratch;
                    patched.dst.push_back(regTemp(scratchNum));
                    epilogueStores.push_back(makeStoreSpill(scratch, spillOffset[num]));
                } else {
                    auto cIt = (coloring == nullptr) ? map<int, int>::const_iterator() : coloring->colors.find(num);
                    int reg = (cIt == coloring->colors.end()) ? 0 : cIt->second;
                    patched.dst.push_back(regTemp(reg));
                }
            }

            for (const auto& ld : prologueLoads) {
                outFunc.instructions.push_back(ld);
            }

            bool skipPatched = false;
            if (patched.kind == AssemInstr::I_MOVE && patched.dst.size() == 1 && patched.src.size() == 1 &&
                patched.dst[0] != nullptr && patched.src[0] != nullptr &&
                patched.dst[0]->num == patched.src[0]->num) {
                skipPatched = true;
            }

            if (!skipPatched) {
                outFunc.instructions.push_back(patched);
            }
            for (const auto& st : epilogueStores) {
                outFunc.instructions.push_back(st);
            }
        }

        colored->functions.push_back(outFunc);
    }
    
    return colored;
}

} // namespace instr
