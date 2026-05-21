#define DEBUG
#undef DEBUG

#include <string>
#include <stack>
#include <variant>
#include <vector>
#include <map>
#include <set>
#include <utility>
#include "quad.hh"
#include "opt.hh"

namespace {

map<Opt*, set<pair<int, int>>> executable_edges;

bool sameRtValue(RtValue left, RtValue right) {
    if (left.getType() != right.getType()) return false;
    if (left.getType() == ValueType::ONE_VALUE) {
        return left.getIntValue() == right.getIntValue();
    }
    return true;
}

RtValue meetRtValue(RtValue old_value, RtValue new_value) {
    if (old_value.getType() == ValueType::MANY_VALUES ||
        new_value.getType() == ValueType::MANY_VALUES) {
        return RtValue(ValueType::MANY_VALUES);
    }
    if (old_value.getType() == ValueType::NO_VALUE) return new_value;
    if (new_value.getType() == ValueType::NO_VALUE) return old_value;
    if (old_value.getIntValue() == new_value.getIntValue()) return old_value;
    return RtValue(ValueType::MANY_VALUES);
}

bool updateTempValue(Opt *opt, int temp_num, RtValue value) {
    RtValue old_value = opt->getRtValue(temp_num);
    RtValue new_value = meetRtValue(old_value, value);
    if (!sameRtValue(old_value, new_value)) {
        opt->temp_value[temp_num] = new_value;
        return true;
    }
    return false;
}

bool markExecutableBlock(Opt *opt, int label_num) {
    if (opt->label2block.find(label_num) == opt->label2block.end()) return false;
    if (!opt->block_executable[label_num]) {
        opt->block_executable[label_num] = true;
        return true;
    }
    return false;
}

bool markExecutableEdge(Opt *opt, int from, int to) {
    bool changed = false;
    pair<int, int> edge = make_pair(from, to);
    if (executable_edges[opt].find(edge) == executable_edges[opt].end()) {
        executable_edges[opt].insert(edge);
        changed = true;
    }
    if (markExecutableBlock(opt, to)) changed = true;
    return changed;
}

int tempNum(QuadTemp *temp) {
    return temp == nullptr || temp->temp == nullptr ? -1 : temp->temp->num;
}

bool tempMayStillBeDefined(int temp_num, const map<int, int> &temp_def_label,
                           const map<int, bool> &block_executable) {
    auto def_it = temp_def_label.find(temp_num);
    if (def_it == temp_def_label.end()) return false;
    auto block_it = block_executable.find(def_it->second);
    return block_it != block_executable.end() && block_it->second;
}

RtValue termValue(Opt *opt, QuadTerm *term, bool promote_undefined,
                  const map<int, int> &temp_def_label) {
    if (term == nullptr) return RtValue(ValueType::MANY_VALUES);
    if (term->kind == QuadTermKind::CONST) return RtValue(term->get_const());
    if (term->kind == QuadTermKind::NAME) return RtValue(ValueType::MANY_VALUES);

    QuadTemp *quad_temp = term->get_temp();
    if (quad_temp == nullptr || quad_temp->temp == nullptr) {
        return RtValue(ValueType::MANY_VALUES);
    }

    int num = quad_temp->temp->num;
    RtValue value = opt->getRtValue(num);
    if (promote_undefined && value.getType() == ValueType::NO_VALUE &&
        !tempMayStillBeDefined(num, temp_def_label, opt->block_executable)) {
        opt->temp_value[num] = RtValue(ValueType::MANY_VALUES);
        return opt->temp_value[num];
    }
    return value;
}

bool evalBinop(const string &op, int left, int right, int &result) {
    if (op == "+") result = left + right;
    else if (op == "-") result = left - right;
    else if (op == "*") result = left * right;
    else if (op == "/") {
        if (right == 0) return false;
        result = left / right;
    }
    else if (op == "%") {
        if (right == 0) return false;
        result = left % right;
    }
    else if (op == "&&") result = (left != 0 && right != 0) ? 1 : 0;
    else if (op == "||") result = (left != 0 || right != 0) ? 1 : 0;
    else return false;
    return true;
}

bool evalRelop(const string &op, int left, int right, bool &result) {
    if (op == "==" || op == "=") result = left == right;
    else if (op == "!=") result = left != right;
    else if (op == "<") result = left < right;
    else if (op == ">") result = left > right;
    else if (op == "<=") result = left <= right;
    else if (op == ">=") result = left >= right;
    else return false;
    return true;
}

bool edgeExecutable(Opt *opt, int from, int to) {
    return executable_edges[opt].find(make_pair(from, to)) != executable_edges[opt].end();
}

QuadTerm* replaceConstTerm(Opt *opt, QuadTerm *term) {
    if (term == nullptr) return nullptr;
    if (term->kind == QuadTermKind::TEMP) {
        QuadTemp *quad_temp = term->get_temp();
        if (quad_temp != nullptr && quad_temp->temp != nullptr) {
            RtValue value = opt->getRtValue(quad_temp->temp->num);
            if (value.getType() == ValueType::ONE_VALUE) {
                return new QuadTerm(value.getIntValue());
            }
        }
    }
    return term->clone();
}

set<Temp*>* makeDefSet(int temp_num) {
    set<Temp*> *defs = new set<Temp*>();
    if (temp_num >= 0) defs->insert(new Temp(temp_num));
    return defs;
}

set<Temp*>* makeUseSetFromTerm(QuadTerm *term) {
    set<Temp*> *uses = new set<Temp*>();
    if (term != nullptr && term->kind == QuadTermKind::TEMP) {
        QuadTemp *quad_temp = term->get_temp();
        if (quad_temp != nullptr && quad_temp->temp != nullptr) {
            uses->insert(new Temp(quad_temp->temp->num));
        }
    }
    return uses;
}

void addTermUses(set<Temp*> *uses, QuadTerm *term) {
    if (uses == nullptr || term == nullptr || term->kind != QuadTermKind::TEMP) return;
    QuadTemp *quad_temp = term->get_temp();
    if (quad_temp != nullptr && quad_temp->temp != nullptr) {
        uses->insert(new Temp(quad_temp->temp->num));
    }
}

vector<Label*>* executableExitLabels(Opt *opt, QuadBlock *block) {
    vector<Label*> *labels = new vector<Label*>();
    if (block == nullptr || block->exit_labels == nullptr || block->entry_label == nullptr) return labels;
    int from = block->entry_label->num;
    for (auto label : *block->exit_labels) {
        if (label != nullptr && edgeExecutable(opt, from, label->num)) {
            labels->push_back(label);
        }
    }
    return labels;
}

} // namespace

QuadFuncDecl* Opt::optFunc() {
    calculateBT();
    modifyFunc();
    return func;
}

void Opt::calculateBT() {
    label2block.clear();
    block_executable.clear();
    temp_value.clear();
    executable_edges[this].clear();

    map<int, int> temp_def_label;

    if (func == nullptr || func->quadblocklist == nullptr || func->quadblocklist->empty()) return;

    if (func->params != nullptr) {
        for (auto param : *func->params) {
            if (param != nullptr) temp_value[param->num] = RtValue(ValueType::MANY_VALUES);
        }
    }

    for (auto block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr) continue;
        int label_num = block->entry_label->num;
        label2block[label_num] = block;
        block_executable[label_num] = false;

        if (block->quadlist == nullptr) continue;
        for (auto quad : *block->quadlist) {
            if (quad == nullptr) continue;
            switch (quad->kind) {
                case QuadKind::MOVE: {
                    auto move = static_cast<QuadMove*>(quad);
                    temp_def_label[tempNum(move->dst)] = label_num;
                    getRtValue(tempNum(move->dst));
                    break;
                }
                case QuadKind::LOAD: {
                    auto load = static_cast<QuadLoad*>(quad);
                    temp_def_label[tempNum(load->dst)] = label_num;
                    getRtValue(tempNum(load->dst));
                    break;
                }
                case QuadKind::MOVE_BINOP: {
                    auto binop = static_cast<QuadMoveBinop*>(quad);
                    temp_def_label[tempNum(binop->dst)] = label_num;
                    getRtValue(tempNum(binop->dst));
                    break;
                }
                case QuadKind::MOVE_CALL: {
                    auto call = static_cast<QuadMoveCall*>(quad);
                    temp_def_label[tempNum(call->dst)] = label_num;
                    getRtValue(tempNum(call->dst));
                    break;
                }
                case QuadKind::MOVE_EXTCALL: {
                    auto call = static_cast<QuadMoveExtCall*>(quad);
                    temp_def_label[tempNum(call->dst)] = label_num;
                    getRtValue(tempNum(call->dst));
                    break;
                }
                case QuadKind::PHI: {
                    auto phi = static_cast<QuadPhi*>(quad);
                    temp_def_label[tempNum(phi->temp_exp)] = label_num;
                    getRtValue(tempNum(phi->temp_exp));
                    break;
                }
                case QuadKind::PTR_CALC: {
                    auto ptr_calc = static_cast<QuadPtrCalc*>(quad);
                    if (ptr_calc->dst != nullptr && ptr_calc->dst->kind == QuadTermKind::TEMP) {
                        temp_def_label[tempNum(ptr_calc->dst->get_temp())] = label_num;
                        getRtValue(tempNum(ptr_calc->dst->get_temp()));
                    }
                    break;
                }
                default:
                    break;
            }
        }
    }

    markExecutableBlock(this, func->quadblocklist->front()->entry_label->num);

    bool changed = true;
    while (changed) {
        changed = false;
        for (auto block : *func->quadblocklist) {
            if (block == nullptr || block->entry_label == nullptr) continue;
            int block_label = block->entry_label->num;
            if (!block_executable[block_label] || block->quadlist == nullptr) continue;

            for (auto quad : *block->quadlist) {
                if (quad == nullptr) continue;
                switch (quad->kind) {
                    case QuadKind::MOVE: {
                        auto move = static_cast<QuadMove*>(quad);
                        changed |= updateTempValue(this, tempNum(move->dst),
                                                   termValue(this, move->src, true, temp_def_label));
                        break;
                    }
                    case QuadKind::LOAD: {
                        auto load = static_cast<QuadLoad*>(quad);
                        termValue(this, load->src, true, temp_def_label);
                        changed |= updateTempValue(this, tempNum(load->dst), RtValue(ValueType::MANY_VALUES));
                        break;
                    }
                    case QuadKind::STORE: {
                        auto store = static_cast<QuadStore*>(quad);
                        termValue(this, store->src, true, temp_def_label);
                        termValue(this, store->dst, true, temp_def_label);
                        break;
                    }
                    case QuadKind::MOVE_BINOP: {
                        auto binop = static_cast<QuadMoveBinop*>(quad);
                        RtValue left = termValue(this, binop->left, true, temp_def_label);
                        RtValue right = termValue(this, binop->right, true, temp_def_label);
                        RtValue result;
                        if (left.getType() == ValueType::ONE_VALUE && right.getType() == ValueType::ONE_VALUE) {
                            int folded = 0;
                            if (evalBinop(binop->binop, left.getIntValue(), right.getIntValue(), folded)) {
                                result = RtValue(folded);
                            }
                            else {
                                result = RtValue(ValueType::MANY_VALUES);
                            }
                        }
                        else if (left.getType() == ValueType::MANY_VALUES || right.getType() == ValueType::MANY_VALUES) {
                            result = RtValue(ValueType::MANY_VALUES);
                        }
                        changed |= updateTempValue(this, tempNum(binop->dst), result);
                        break;
                    }
                    case QuadKind::CALL: {
                        auto call = static_cast<QuadCall*>(quad);
                        termValue(this, call->obj_term, true, temp_def_label);
                        if (call->args != nullptr) {
                            for (auto arg : *call->args) termValue(this, arg, true, temp_def_label);
                        }
                        break;
                    }
                    case QuadKind::MOVE_CALL: {
                        auto call = static_cast<QuadMoveCall*>(quad);
                        if (call->call != nullptr) {
                            termValue(this, call->call->obj_term, true, temp_def_label);
                            if (call->call->args != nullptr) {
                                for (auto arg : *call->call->args) termValue(this, arg, true, temp_def_label);
                            }
                        }
                        changed |= updateTempValue(this, tempNum(call->dst), RtValue(ValueType::MANY_VALUES));
                        break;
                    }
                    case QuadKind::EXTCALL: {
                        auto call = static_cast<QuadExtCall*>(quad);
                        if (call->args != nullptr) {
                            for (auto arg : *call->args) termValue(this, arg, true, temp_def_label);
                        }
                        break;
                    }
                    case QuadKind::MOVE_EXTCALL: {
                        auto call = static_cast<QuadMoveExtCall*>(quad);
                        if (call->extcall != nullptr && call->extcall->args != nullptr) {
                            for (auto arg : *call->extcall->args) termValue(this, arg, true, temp_def_label);
                        }
                        changed |= updateTempValue(this, tempNum(call->dst), RtValue(ValueType::MANY_VALUES));
                        break;
                    }
                    case QuadKind::JUMP: {
                        auto jump = static_cast<QuadJump*>(quad);
                        if (jump->label != nullptr) changed |= markExecutableEdge(this, block_label, jump->label->num);
                        break;
                    }
                    case QuadKind::CJUMP: {
                        auto cjump = static_cast<QuadCJump*>(quad);
                        RtValue left = termValue(this, cjump->left, true, temp_def_label);
                        RtValue right = termValue(this, cjump->right, true, temp_def_label);
                        if (left.getType() == ValueType::ONE_VALUE && right.getType() == ValueType::ONE_VALUE) {
                            bool branch = false;
                            if (evalRelop(cjump->relop, left.getIntValue(), right.getIntValue(), branch)) {
                                Label *target = branch ? cjump->t : cjump->f;
                                if (target != nullptr) changed |= markExecutableEdge(this, block_label, target->num);
                            }
                            else {
                                if (cjump->t != nullptr) changed |= markExecutableEdge(this, block_label, cjump->t->num);
                                if (cjump->f != nullptr) changed |= markExecutableEdge(this, block_label, cjump->f->num);
                            }
                        }
                        else if (left.getType() == ValueType::MANY_VALUES || right.getType() == ValueType::MANY_VALUES) {
                            if (cjump->t != nullptr) changed |= markExecutableEdge(this, block_label, cjump->t->num);
                            if (cjump->f != nullptr) changed |= markExecutableEdge(this, block_label, cjump->f->num);
                        }
                        break;
                    }
                    case QuadKind::PHI: {
                        auto phi = static_cast<QuadPhi*>(quad);
                        RtValue result;
                        if (phi->args != nullptr) {
                            for (auto arg : *phi->args) {
                                if (arg.first == nullptr || arg.second == nullptr) continue;
                                if (!edgeExecutable(this, arg.second->num, block_label)) continue;

                                RtValue value = getRtValue(arg.first->num);
                                if (value.getType() == ValueType::NO_VALUE &&
                                    !tempMayStillBeDefined(arg.first->num, temp_def_label, block_executable)) {
                                    temp_value[arg.first->num] = RtValue(ValueType::MANY_VALUES);
                                    value = temp_value[arg.first->num];
                                    changed = true;
                                }
                                result = meetRtValue(result, value);
                            }
                        }
                        changed |= updateTempValue(this, tempNum(phi->temp_exp), result);
                        break;
                    }
                    case QuadKind::RETURN: {
                        auto ret = static_cast<QuadReturn*>(quad);
                        termValue(this, ret->exp, true, temp_def_label);
                        break;
                    }
                    case QuadKind::PTR_CALC: {
                        auto ptr_calc = static_cast<QuadPtrCalc*>(quad);
                        termValue(this, ptr_calc->ptr, true, temp_def_label);
                        termValue(this, ptr_calc->offset, true, temp_def_label);
                        if (ptr_calc->dst != nullptr && ptr_calc->dst->kind == QuadTermKind::TEMP) {
                            changed |= updateTempValue(this, tempNum(ptr_calc->dst->get_temp()), RtValue(ValueType::MANY_VALUES));
                        }
                        break;
                    }
                    default:
                        break;
                }
            }
        }
    }
}

void Opt::modifyFunc() {
    if (func == nullptr || func->quadblocklist == nullptr) return;

    struct PhiPlan {
        int mode = 0; // 0: delete, 1: move from single arg, 2: keep phi
        vector<pair<Temp*, Label*>> args;
    };

    map<QuadPhi*, PhiPlan> phi_plans;
    set<int> temps_needed_by_kept_phi;
    map<int, vector<QuadMove*>> phi_const_moves;
    int next_temp_num = func->last_temp_num + 1;

    for (auto block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || !block_executable[block->entry_label->num]) continue;
        if (block->quadlist == nullptr) continue;

        int block_label = block->entry_label->num;
        for (auto quad : *block->quadlist) {
            if (quad == nullptr || quad->kind != QuadKind::PHI) continue;
            auto phi = static_cast<QuadPhi*>(quad);
            PhiPlan plan;

            if (phi->args != nullptr) {
                for (auto arg : *phi->args) {
                    if (arg.first == nullptr || arg.second == nullptr) continue;
                    if (edgeExecutable(this, arg.second->num, block_label)) {
                        plan.args.push_back(arg);
                    }
                }
            }

            RtValue phi_value = getRtValue(tempNum(phi->temp_exp));
            if (phi_value.getType() == ValueType::ONE_VALUE || plan.args.empty()) {
                plan.mode = 0;
            }
            else if (plan.args.size() == 1) {
                plan.mode = 1;
            }
            else {
                plan.mode = 2;
                for (auto &arg : plan.args) {
                    if (arg.first == nullptr || arg.second == nullptr) continue;
                    RtValue arg_value = getRtValue(arg.first->num);
                    if (arg_value.getType() == ValueType::ONE_VALUE) {
                        Temp *new_temp = new Temp(next_temp_num++);
                        auto dst = new QuadTemp(new Temp(new_temp->num), phi->temp_exp->type);
                        auto src = new QuadTerm(arg_value.getIntValue());
                        phi_const_moves[arg.second->num].push_back(
                            new QuadMove(dst, src, makeDefSet(new_temp->num), new set<Temp*>()));
                        arg.first = new_temp;
                    }
                    temps_needed_by_kept_phi.insert(arg.first->num);
                }
            }
            phi_plans[phi] = plan;
        }
    }

    vector<Temp*> *new_params = new vector<Temp*>();
    if (func->params != nullptr) {
        for (auto param : *func->params) {
            if (param != nullptr) new_params->push_back(new Temp(param->num));
        }
    }

    vector<QuadBlock*> *new_blocks = new vector<QuadBlock*>();

    for (auto block : *func->quadblocklist) {
        if (block == nullptr || block->entry_label == nullptr || !block_executable[block->entry_label->num]) continue;

        vector<QuadStm*> *new_quads = new vector<QuadStm*>();
        if (block->quadlist != nullptr) {
            for (auto quad : *block->quadlist) {
                if (quad == nullptr) continue;

                switch (quad->kind) {
                    case QuadKind::MOVE: {
                        auto move = static_cast<QuadMove*>(quad);
                        int dst_num = tempNum(move->dst);
                        RtValue dst_value = getRtValue(dst_num);
                        if (dst_value.getType() == ValueType::ONE_VALUE &&
                            temps_needed_by_kept_phi.find(dst_num) == temps_needed_by_kept_phi.end()) {
                            break;
                        }
                        QuadTerm *src = replaceConstTerm(this, move->src);
                        set<Temp*> *uses = makeUseSetFromTerm(src);
                        new_quads->push_back(new QuadMove(move->dst->clone(), src, makeDefSet(dst_num), uses));
                        break;
                    }
                    case QuadKind::LOAD: {
                        auto load = static_cast<QuadLoad*>(quad);
                        QuadTerm *src = replaceConstTerm(this, load->src);
                        set<Temp*> *uses = makeUseSetFromTerm(src);
                        new_quads->push_back(new QuadLoad(load->dst->clone(), src, makeDefSet(tempNum(load->dst)), uses));
                        break;
                    }
                    case QuadKind::STORE: {
                        auto store = static_cast<QuadStore*>(quad);
                        QuadTerm *src = replaceConstTerm(this, store->src);
                        QuadTerm *dst = replaceConstTerm(this, store->dst);
                        set<Temp*> *uses = new set<Temp*>();
                        addTermUses(uses, src);
                        addTermUses(uses, dst);
                        new_quads->push_back(new QuadStore(src, dst, new set<Temp*>(), uses));
                        break;
                    }
                    case QuadKind::MOVE_BINOP: {
                        auto binop = static_cast<QuadMoveBinop*>(quad);
                        int dst_num = tempNum(binop->dst);
                        RtValue dst_value = getRtValue(dst_num);
                        if (dst_value.getType() == ValueType::ONE_VALUE &&
                            temps_needed_by_kept_phi.find(dst_num) == temps_needed_by_kept_phi.end()) {
                            break;
                        }
                        QuadTerm *left = replaceConstTerm(this, binop->left);
                        QuadTerm *right = replaceConstTerm(this, binop->right);
                        set<Temp*> *uses = new set<Temp*>();
                        addTermUses(uses, left);
                        addTermUses(uses, right);
                        new_quads->push_back(new QuadMoveBinop(binop->dst->clone(), left, binop->binop, right,
                                                               makeDefSet(dst_num), uses));
                        break;
                    }
                    case QuadKind::CALL: {
                        auto call = static_cast<QuadCall*>(quad);
                        vector<QuadTerm*> *args = new vector<QuadTerm*>();
                        set<Temp*> *uses = new set<Temp*>();
                        QuadTerm *obj = replaceConstTerm(this, call->obj_term);
                        addTermUses(uses, obj);
                        if (call->args != nullptr) {
                            for (auto arg : *call->args) {
                                QuadTerm *new_arg = replaceConstTerm(this, arg);
                                addTermUses(uses, new_arg);
                                args->push_back(new_arg);
                            }
                        }
                        new_quads->push_back(new QuadCall(call->name, obj, args, new set<Temp*>(), uses));
                        break;
                    }
                    case QuadKind::MOVE_CALL: {
                        auto move_call = static_cast<QuadMoveCall*>(quad);
                        vector<QuadTerm*> *args = new vector<QuadTerm*>();
                        set<Temp*> *uses = new set<Temp*>();
                        QuadTerm *obj = nullptr;
                        string name;
                        if (move_call->call != nullptr) {
                            name = move_call->call->name;
                            obj = replaceConstTerm(this, move_call->call->obj_term);
                            addTermUses(uses, obj);
                            if (move_call->call->args != nullptr) {
                                for (auto arg : *move_call->call->args) {
                                    QuadTerm *new_arg = replaceConstTerm(this, arg);
                                    addTermUses(uses, new_arg);
                                    args->push_back(new_arg);
                                }
                            }
                        }
                        auto call = new QuadCall(name, obj, args, new set<Temp*>(), uses);
                        new_quads->push_back(new QuadMoveCall(move_call->dst->clone(), call,
                                                             makeDefSet(tempNum(move_call->dst)), uses));
                        break;
                    }
                    case QuadKind::EXTCALL: {
                        auto extcall = static_cast<QuadExtCall*>(quad);
                        vector<QuadTerm*> *args = new vector<QuadTerm*>();
                        set<Temp*> *uses = new set<Temp*>();
                        if (extcall->args != nullptr) {
                            for (auto arg : *extcall->args) {
                                QuadTerm *new_arg = replaceConstTerm(this, arg);
                                addTermUses(uses, new_arg);
                                args->push_back(new_arg);
                            }
                        }
                        new_quads->push_back(new QuadExtCall(extcall->extfun, args, new set<Temp*>(), uses));
                        break;
                    }
                    case QuadKind::MOVE_EXTCALL: {
                        auto move_extcall = static_cast<QuadMoveExtCall*>(quad);
                        vector<QuadTerm*> *args = new vector<QuadTerm*>();
                        set<Temp*> *uses = new set<Temp*>();
                        string name;
                        if (move_extcall->extcall != nullptr) {
                            name = move_extcall->extcall->extfun;
                            if (move_extcall->extcall->args != nullptr) {
                                for (auto arg : *move_extcall->extcall->args) {
                                    QuadTerm *new_arg = replaceConstTerm(this, arg);
                                    addTermUses(uses, new_arg);
                                    args->push_back(new_arg);
                                }
                            }
                        }
                        auto extcall = new QuadExtCall(name, args, new set<Temp*>(), uses);
                        new_quads->push_back(new QuadMoveExtCall(move_extcall->dst->clone(), extcall,
                                                                makeDefSet(tempNum(move_extcall->dst)), uses));
                        break;
                    }
                    case QuadKind::LABEL: {
                        new_quads->push_back(static_cast<QuadStm*>(quad->clone()));
                        break;
                    }
                    case QuadKind::JUMP: {
                        if (phi_const_moves.find(block->entry_label->num) != phi_const_moves.end()) {
                            for (auto move : phi_const_moves[block->entry_label->num]) {
                                new_quads->push_back(move);
                            }
                            phi_const_moves.erase(block->entry_label->num);
                        }
                        auto jump = static_cast<QuadJump*>(quad);
                        if (jump->label != nullptr && edgeExecutable(this, block->entry_label->num, jump->label->num)) {
                            new_quads->push_back(static_cast<QuadStm*>(quad->clone()));
                        }
                        break;
                    }
                    case QuadKind::CJUMP: {
                        if (phi_const_moves.find(block->entry_label->num) != phi_const_moves.end()) {
                            for (auto move : phi_const_moves[block->entry_label->num]) {
                                new_quads->push_back(move);
                            }
                            phi_const_moves.erase(block->entry_label->num);
                        }
                        auto cjump = static_cast<QuadCJump*>(quad);
                        RtValue left_value;
                        RtValue right_value;
                        if (cjump->left != nullptr) {
                            if (cjump->left->kind == QuadTermKind::CONST) left_value = RtValue(cjump->left->get_const());
                            else if (cjump->left->kind == QuadTermKind::TEMP) left_value = getRtValue(cjump->left->get_temp()->temp->num);
                            else left_value = RtValue(ValueType::MANY_VALUES);
                        }
                        if (cjump->right != nullptr) {
                            if (cjump->right->kind == QuadTermKind::CONST) right_value = RtValue(cjump->right->get_const());
                            else if (cjump->right->kind == QuadTermKind::TEMP) right_value = getRtValue(cjump->right->get_temp()->temp->num);
                            else right_value = RtValue(ValueType::MANY_VALUES);
                        }
                        if (left_value.getType() == ValueType::ONE_VALUE && right_value.getType() == ValueType::ONE_VALUE) {
                            bool branch = false;
                            if (evalRelop(cjump->relop, left_value.getIntValue(), right_value.getIntValue(), branch)) {
                                Label *target = branch ? cjump->t : cjump->f;
                                if (target != nullptr) {
                                    new_quads->push_back(new QuadJump(target, new set<Temp*>(), new set<Temp*>()));
                                }
                                break;
                            }
                        }
                        QuadTerm *left = replaceConstTerm(this, cjump->left);
                        QuadTerm *right = replaceConstTerm(this, cjump->right);
                        set<Temp*> *uses = new set<Temp*>();
                        addTermUses(uses, left);
                        addTermUses(uses, right);
                        new_quads->push_back(new QuadCJump(cjump->relop, left, right, cjump->t, cjump->f,
                                                          new set<Temp*>(), uses));
                        break;
                    }
                    case QuadKind::PHI: {
                        auto phi = static_cast<QuadPhi*>(quad);
                        PhiPlan plan = phi_plans[phi];
                        if (plan.mode == 1) {
                            int src_num = plan.args.front().first->num;
                            RtValue src_value = getRtValue(src_num);
                            QuadTerm *src = nullptr;
                            if (src_value.getType() == ValueType::ONE_VALUE) {
                                src = new QuadTerm(src_value.getIntValue());
                            }
                            else {
                                src = new QuadTerm(new QuadTemp(new Temp(src_num), phi->temp_exp->type));
                            }
                            new_quads->push_back(new QuadMove(phi->temp_exp->clone(), src,
                                                             makeDefSet(tempNum(phi->temp_exp)), makeUseSetFromTerm(src)));
                        }
                        else if (plan.mode == 2) {
                            auto args = new vector<pair<Temp*, Label*>>(plan.args);
                            set<Temp*> *uses = new set<Temp*>();
                            for (auto arg : plan.args) {
                                if (arg.first != nullptr) uses->insert(new Temp(arg.first->num));
                            }
                            new_quads->push_back(new QuadPhi(phi->temp_exp->clone(), args,
                                                            makeDefSet(tempNum(phi->temp_exp)), uses));
                        }
                        break;
                    }
                    case QuadKind::RETURN: {
                        if (phi_const_moves.find(block->entry_label->num) != phi_const_moves.end()) {
                            for (auto move : phi_const_moves[block->entry_label->num]) {
                                new_quads->push_back(move);
                            }
                            phi_const_moves.erase(block->entry_label->num);
                        }
                        auto ret = static_cast<QuadReturn*>(quad);
                        QuadTerm *exp = replaceConstTerm(this, ret->exp);
                        new_quads->push_back(new QuadReturn(exp, new set<Temp*>(), makeUseSetFromTerm(exp)));
                        break;
                    }
                    case QuadKind::PTR_CALC: {
                        auto ptr_calc = static_cast<QuadPtrCalc*>(quad);
                        QuadTerm *dst = ptr_calc->dst != nullptr ? ptr_calc->dst->clone() : nullptr;
                        QuadTerm *ptr = replaceConstTerm(this, ptr_calc->ptr);
                        QuadTerm *offset = replaceConstTerm(this, ptr_calc->offset);
                        set<Temp*> *uses = new set<Temp*>();
                        addTermUses(uses, ptr);
                        addTermUses(uses, offset);
                        int dst_num = -1;
                        if (dst != nullptr && dst->kind == QuadTermKind::TEMP) dst_num = tempNum(dst->get_temp());
                        new_quads->push_back(new QuadPtrCalc(dst, ptr, offset, makeDefSet(dst_num), uses));
                        break;
                    }
                    default:
                        break;
                }
            }
        }

        if (phi_const_moves.find(block->entry_label->num) != phi_const_moves.end()) {
            for (auto move : phi_const_moves[block->entry_label->num]) {
                new_quads->push_back(move);
            }
            phi_const_moves.erase(block->entry_label->num);
        }

        new_blocks->push_back(new QuadBlock(new_quads, block->entry_label, executableExitLabels(this, block)));
    }

    func = new QuadFuncDecl(func->funcname, new_params, new_blocks, func->last_label_num,
                            max(func->last_temp_num, next_temp_num - 1));
}

QuadProgram* optProg(QuadProgram* prog) {
    QuadProgram* newProg = new QuadProgram(new vector<QuadFuncDecl*>(), prog->last_label_num, prog->last_temp_num);
    for (int i=0; i < prog->quadFuncDeclList->size(); i++) {
        Opt optthis(prog->quadFuncDeclList->at(i));
        newProg->quadFuncDeclList->push_back(optthis.optFunc());
    }
    return newProg;
}