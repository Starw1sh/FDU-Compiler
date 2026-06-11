#include "asmprogpass.hh"
#include "temp.hh"
#include <set>
#include <string>

namespace instr {

void preDataFlowPass(AsmProg* prog) {
    // fill in the code.
    if (prog == nullptr) {
        return;
    }

    for (auto& func : prog->functions) {
        for (auto& instr : func.instructions) {
            // bl/blx clobber caller-saved r0-r3; add them to dst for liveness/IG.
            const bool isCall = instr.assem.rfind("bl ", 0) == 0 || instr.assem.rfind("blx ", 0) == 0;
            if (!isCall) {
                continue;
            }

            std::set<int> existing;
            for (auto* t : instr.dst) {
                if (t != nullptr) {
                    existing.insert(t->num);
                }
            }
            for (int r = 0; r <= 3; ++r) {
                if (existing.find(r) == existing.end()) {
                    instr.dst.push_back(new tree::Temp(r));
                }
            }
        }
    }
}

} // namespace instr
