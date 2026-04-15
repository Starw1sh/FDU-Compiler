#define DEBUG
#undef DEBUG

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <set>
#include "treep.hh"
#include "quad.hh"
#include "tree2quad.hh"

using namespace std;
using namespace tree;
using namespace quad;

namespace {

QuadType to_quad_type(tree::Type t) {
    return (t == tree::Type::PTR) ? QuadType::PTR : QuadType::INT;
}

QuadTemp* make_quad_temp(tree::Temp* t, tree::Type ty) {
    return new QuadTemp(t, to_quad_type(ty));
}

void add_term_use(set<Temp*>* use, QuadTerm* term) {
    if (use == nullptr || term == nullptr) {
        return;
    }
    if (term->kind == QuadTermKind::TEMP) {
        QuadTemp* qt = term->get_temp();
        if (qt != nullptr && qt->temp != nullptr) {
            use->insert(qt->temp);
        }
    }
}

set<Temp*>* copy_temp_set(const set<Temp*>* src) {
    set<Temp*>* dst = new set<Temp*>();
    if (src != nullptr) {
        dst->insert(src->begin(), src->end());
    }
    return dst;
}

} // namespace

/*
We use an instruction selection method (pattern matching) to convert the IR tree to Quad.
*/

// you need to implement the following function to convert the IR tree to Quad, 
// and the visit functions for each tree node (the visit functions should generate the 
// corresponding Quad instructions and add them to the visit_result vector)

QuadProgram* tree2quad(Program* prog) {
#ifdef DEBUG
    cout << "in Tree2Quad::Converting IR to Quad" << endl;
#endif
    if (prog == nullptr) {
        return nullptr;
    }

    Tree2Quad v;
    v.visit_result = nullptr;
    v.output_term = nullptr;
    v.temp_map = nullptr;

    vector<QuadFuncDecl*>* quadfuncdecllist = new vector<QuadFuncDecl*>(); //to be filled in the visit function for FuncDecl
    int prog_last_label = 0; //to be determined
    int prog_last_temp = 0; //to be determined 

    v.quadprog = new QuadProgram(quadfuncdecllist, prog_last_label, prog_last_temp);
    prog->accept(v);

    return v.quadprog;
}

void Tree2Quad::visit(tree::Program *prog) {
    if (prog == nullptr || quadprog == nullptr || quadprog->quadFuncDeclList == nullptr) {
        return;
    }

    int max_last_label = quadprog->last_label_num;
    int max_last_temp = quadprog->last_temp_num;

    if (prog->funcdecllist != nullptr) {
        for (auto* func : *prog->funcdecllist) {
            if (func == nullptr) {
                continue;
            }
            func->accept(*this);
            if (func->last_label_num > max_last_label) {
                max_last_label = func->last_label_num;
            }
            if (func->last_temp_num > max_last_temp) {
                max_last_temp = func->last_temp_num;
            }
        }
    }

    quadprog->last_label_num = max_last_label;
    quadprog->last_temp_num = max_last_temp;
}

void Tree2Quad::visit(tree::FuncDecl *func) {
    if (func == nullptr || quadprog == nullptr || quadprog->quadFuncDeclList == nullptr) {
        return;
    }

    temp_map = new Temp_map();
    temp_map->next_temp = func->last_temp_num + 1;
    temp_map->next_label = func->last_label_num + 1;//在IR阶段已经使用的，避免重复

    visit_result = new vector<QuadStm*>();
    output_term = nullptr;

    Label* entry = temp_map->newlabel();
    visit_result->push_back(new QuadLabel(entry, new set<Temp*>(), new set<Temp*>()));
    //每次都 new set<Temp*>() 传进去，这是符合当前结构的；因为 QuadStm 统一要求有 def/use 字段，即使某些指令（如 Label）逻辑上为空。
    if (func->stm != nullptr) {
        func->stm->accept(*this);
    }

    vector<QuadBlock*>* blocks = new vector<QuadBlock*>();
    blocks->push_back(new QuadBlock(visit_result, entry, nullptr));

    QuadFuncDecl* qf = new QuadFuncDecl(
        func->name,
        func->args,
        blocks,
        temp_map->next_label - 1,
        temp_map->next_temp - 1
    );
    quadprog->quadFuncDeclList->push_back(qf);

    func->last_label_num = qf->last_label_num;
    func->last_temp_num = qf->last_temp_num;//更新

    if (temp_map != nullptr) {
        delete temp_map;
        temp_map = nullptr;
    }
}

void Tree2Quad::visit(tree::Jump *jump) {
    if (jump == nullptr || visit_result == nullptr) {
        return;
    }
    visit_result->push_back(new QuadJump(jump->label, new set<Temp*>(), new set<Temp*>()));
}

void Tree2Quad::visit(tree::Cjump *cjump) {
    if (cjump == nullptr || visit_result == nullptr) {
        return;
    }

    output_term = nullptr;
    if (cjump->left != nullptr) {
        cjump->left->accept(*this);
    }
    QuadTerm* left_term = output_term;
    /*QuadTerm 只有三种形态：

TEMP
一个带类型的临时变量（QuadTemp*，例如 t107:int）
CONST
一个整型常量（例如 1、-1）
NAME
一个名字（通常是标签/符号名，比如方法名 C^m）*/

    output_term = nullptr;
    if (cjump->right != nullptr) {
        cjump->right->accept(*this);
    }
    QuadTerm* right_term = output_term;

    set<Temp*>* use = new set<Temp*>();
    add_term_use(use, left_term);
    add_term_use(use, right_term);

    visit_result->push_back(new QuadCJump(cjump->relop, left_term, right_term, cjump->t, cjump->f,
                                          new set<Temp*>(), use));
}

void Tree2Quad::visit(tree::Move *move) {
    if (move == nullptr || visit_result == nullptr) {
        return;
    }

    bool dst_is_temp = move->dst != nullptr && move->dst->getTreeKind() == Kind::TEMPEXP;
    bool dst_is_mem = move->dst != nullptr && move->dst->getTreeKind() == Kind::MEM;
    TempExp* dst_temp_exp = dst_is_temp ? static_cast<TempExp*>(move->dst) : nullptr;

    QuadTerm* dst_term = nullptr;
    if (dst_is_mem) {
        Mem* dst_mem = static_cast<Mem*>(move->dst);
        output_term = nullptr;
        if (dst_mem->mem != nullptr) {
            dst_mem->mem->accept(*this);
        }
        dst_term = output_term;
    } else {
        output_term = nullptr;
        if (move->dst != nullptr) {
            move->dst->accept(*this);
        }
        dst_term = output_term;
    }
    //temp<-call
    if (dst_is_temp && dst_temp_exp != nullptr && move->src != nullptr && move->src->getTreeKind() == Kind::CALL) {
        Call* call = static_cast<Call*>(move->src);

        output_term = nullptr;
        if (call->obj != nullptr) {
            call->obj->accept(*this);
        }
        QuadTerm* obj_term = output_term;

        vector<QuadTerm*>* args = new vector<QuadTerm*>();
        if (call->args != nullptr) {
            for (auto* arg : *call->args) {
                output_term = nullptr;
                if (arg != nullptr) {
                    arg->accept(*this);
                }
                args->push_back(output_term);
            }
        }

        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, obj_term);
        for (auto* arg_term : *args) {
            add_term_use(use, arg_term);
        }

        QuadCall* qcall = new QuadCall(call->id, obj_term, args, new set<Temp*>(), copy_temp_set(use));
        set<Temp*>* def = new set<Temp*>();
        def->insert(dst_temp_exp->temp);
        visit_result->push_back(new QuadMoveCall(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type),
                                                 qcall, def, use));
        return;
    }
    //temp-<extcall
    if (dst_is_temp && dst_temp_exp != nullptr && move->src != nullptr && move->src->getTreeKind() == Kind::EXTCALL) {
        ExtCall* extcall = static_cast<ExtCall*>(move->src);

        vector<QuadTerm*>* args = new vector<QuadTerm*>();
        if (extcall->args != nullptr) {
            for (auto* arg : *extcall->args) {
                output_term = nullptr;
                if (arg != nullptr) {
                    arg->accept(*this);
                }
                args->push_back(output_term);
            }
        }

        set<Temp*>* use = new set<Temp*>();
        for (auto* arg_term : *args) {
            add_term_use(use, arg_term);
        }

        QuadExtCall* qext = new QuadExtCall(extcall->extfun, args, new set<Temp*>(), copy_temp_set(use));
        set<Temp*>* def = new set<Temp*>();
        def->insert(dst_temp_exp->temp);
        visit_result->push_back(new QuadMoveExtCall(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type),
                                                    qext, def, use));
        return;
    }
    //temp<-mem
    if (dst_is_temp && dst_temp_exp != nullptr && move->src != nullptr && move->src->getTreeKind() == Kind::MEM) {
        Mem* src_mem = static_cast<Mem*>(move->src);
        output_term = nullptr;
        if (src_mem->mem != nullptr) {
            src_mem->mem->accept(*this);
        }
        QuadTerm* addr_term = output_term;

        set<Temp*>* def = new set<Temp*>();
        def->insert(dst_temp_exp->temp);
        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, addr_term);

        visit_result->push_back(new QuadLoad(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type),
                                             addr_term, def, use));
        return;
    }
    //temp<-binop
    if (dst_is_temp && dst_temp_exp != nullptr && move->src != nullptr && move->src->getTreeKind() == Kind::BINOP) {
        Binop* src_binop = static_cast<Binop*>(move->src);

        output_term = nullptr;
        if (src_binop->left != nullptr) {
            src_binop->left->accept(*this);
        }
        QuadTerm* left_term = output_term;

        output_term = nullptr;
        if (src_binop->right != nullptr) {
            src_binop->right->accept(*this);
        }
        QuadTerm* right_term = output_term;

        set<Temp*>* def = new set<Temp*>();
        def->insert(dst_temp_exp->temp);
        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, left_term);
        add_term_use(use, right_term);

        if (src_binop->op == "+" && src_binop->type == tree::Type::PTR) {
            visit_result->push_back(new QuadPtrCalc(new QuadTerm(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type)),
                                                    left_term, right_term, def, use));
        } else {
            visit_result->push_back(new QuadMoveBinop(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type),
                                                      left_term, src_binop->op, right_term, def, use));
        }
        return;
    }

    output_term = nullptr;
    if (move->src != nullptr) {
        move->src->accept(*this);
    }
    QuadTerm* src_term = output_term;
    //mem<-src
    if (move->dst != nullptr && move->dst->getTreeKind() == Kind::MEM) {
        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, src_term);
        add_term_use(use, dst_term);
        visit_result->push_back(new QuadStore(src_term, dst_term, new set<Temp*>(), use));
        return;
    }
    //temp<-src
    if (dst_is_temp && dst_temp_exp != nullptr) {
        set<Temp*>* def = new set<Temp*>();
        def->insert(dst_temp_exp->temp);
        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, src_term);
        visit_result->push_back(new QuadMove(make_quad_temp(dst_temp_exp->temp, dst_temp_exp->type),
                                             src_term, def, use));
    }
}

void Tree2Quad::visit(tree::Seq *seq) {
    if (seq == nullptr || seq->sl == nullptr) {
        return;
    }
    for (auto* stm : *seq->sl) {
        if (stm != nullptr) {
            stm->accept(*this);
        }
    }
}

void Tree2Quad::visit(tree::LabelStm *labelstm) {
    if (labelstm == nullptr || visit_result == nullptr) {
        return;
    }
    visit_result->push_back(new QuadLabel(labelstm->label, new set<Temp*>(), new set<Temp*>()));
}

void Tree2Quad::visit(tree::Return *ret) {
    if (ret == nullptr || visit_result == nullptr) {
        return;
    }
    output_term = nullptr;
    if (ret->exp != nullptr) {
        ret->exp->accept(*this);
    }
    QuadTerm* ret_term = output_term;
    set<Temp*>* use = new set<Temp*>();
    add_term_use(use, ret_term);
    visit_result->push_back(new QuadReturn(ret_term, new set<Temp*>(), use));
}

void Tree2Quad::visit(tree::ExpStm *exp) {
    if (exp == nullptr || visit_result == nullptr || exp->exp == nullptr) {
        return;
    }

    if (exp->exp->getTreeKind() == Kind::CALL) {
        Call* call = static_cast<Call*>(exp->exp);

        output_term = nullptr;
        if (call->obj != nullptr) {
            call->obj->accept(*this);
        }
        QuadTerm* obj_term = output_term;

        vector<QuadTerm*>* args = new vector<QuadTerm*>();
        if (call->args != nullptr) {
            for (auto* arg : *call->args) {
                output_term = nullptr;
                if (arg != nullptr) {
                    arg->accept(*this);
                }
                args->push_back(output_term);
            }
        }

        set<Temp*>* use = new set<Temp*>();
        add_term_use(use, obj_term);
        for (auto* arg_term : *args) {
            add_term_use(use, arg_term);
        }
        visit_result->push_back(new QuadCall(call->id, obj_term, args, new set<Temp*>(), use));
        return;
    }

    if (exp->exp->getTreeKind() == Kind::EXTCALL) {
        ExtCall* extcall = static_cast<ExtCall*>(exp->exp);

        vector<QuadTerm*>* args = new vector<QuadTerm*>();
        if (extcall->args != nullptr) {
            for (auto* arg : *extcall->args) {
                output_term = nullptr;
                if (arg != nullptr) {
                    arg->accept(*this);
                }
                args->push_back(output_term);
            }
        }

        set<Temp*>* use = new set<Temp*>();
        for (auto* arg_term : *args) {
            add_term_use(use, arg_term);
        }
        visit_result->push_back(new QuadExtCall(extcall->extfun, args, new set<Temp*>(), use));
        return;
    }

    output_term = nullptr;
    exp->exp->accept(*this);
}

void Tree2Quad::visit(tree::Binop *binop) {
    if (binop == nullptr || visit_result == nullptr || temp_map == nullptr) {
        output_term = nullptr;
        return;
    }

    output_term = nullptr;
    if (binop->left != nullptr) {
        binop->left->accept(*this);
    }
    QuadTerm* left_term = output_term;

    output_term = nullptr;
    if (binop->right != nullptr) {
        binop->right->accept(*this);
    }
    QuadTerm* right_term = output_term;

    Temp* dst_temp = temp_map->newtemp();
    QuadTemp* dst = make_quad_temp(dst_temp, binop->type);

    set<Temp*>* def = new set<Temp*>();
    set<Temp*>* use = new set<Temp*>();
    def->insert(dst_temp);
    add_term_use(use, left_term);
    add_term_use(use, right_term);

    if (binop->op == "+" && binop->type == tree::Type::PTR) {
        visit_result->push_back(new QuadPtrCalc(new QuadTerm(dst), left_term, right_term, def, use));
    } else {
        visit_result->push_back(new QuadMoveBinop(dst, left_term, binop->op, right_term, def, use));
    }

    output_term = new QuadTerm(dst);
}

void Tree2Quad::visit(tree::Mem *mem) {
    if (mem == nullptr || visit_result == nullptr || temp_map == nullptr) {
        output_term = nullptr;
        return;
    }

    output_term = nullptr;
    if (mem->mem != nullptr) {
        mem->mem->accept(*this);
    }
    QuadTerm* addr_term = output_term;

    Temp* dst_temp = temp_map->newtemp();
    QuadTemp* dst = make_quad_temp(dst_temp, mem->type);

    set<Temp*>* def = new set<Temp*>();
    set<Temp*>* use = new set<Temp*>();
    def->insert(dst_temp);
    add_term_use(use, addr_term);

    visit_result->push_back(new QuadLoad(dst, addr_term, def, use));
    output_term = new QuadTerm(dst);
}

void Tree2Quad::visit(tree::TempExp *tempexp) {
    if (tempexp == nullptr) {
        output_term = nullptr;
        return;
    }
    output_term = new QuadTerm(make_quad_temp(tempexp->temp, tempexp->type));
}

void Tree2Quad::visit(tree::Eseq *eseq) {
    if (eseq == nullptr) {
        output_term = nullptr;
        return;
    }
    if (eseq->stm != nullptr) {
        eseq->stm->accept(*this);
    }
    output_term = nullptr;
    if (eseq->exp != nullptr) {
        eseq->exp->accept(*this);
    }
}

void Tree2Quad::visit(tree::Name *name) {
    if (name == nullptr) {
        output_term = nullptr;
        return;
    }
    if (name->sname != nullptr) {
        output_term = new QuadTerm(name->sname->str());
        return;
    }
    if (name->name != nullptr) {
        output_term = new QuadTerm(name->name->str());
        return;
    }
    output_term = nullptr;
}

void Tree2Quad::visit(tree::Const *constexp) {
    if (constexp == nullptr) {
        output_term = nullptr;
        return;
    }
    output_term = new QuadTerm(constexp->constVal);
}

void Tree2Quad::visit(tree::Call *call) {
    if (call == nullptr || visit_result == nullptr || temp_map == nullptr) {
        output_term = nullptr;
        return;
    }

    output_term = nullptr;
    if (call->obj != nullptr) {
        call->obj->accept(*this);
    }
    QuadTerm* obj_term = output_term;

    vector<QuadTerm*>* args = new vector<QuadTerm*>();
    if (call->args != nullptr) {
        for (auto* arg : *call->args) {
            output_term = nullptr;
            if (arg != nullptr) {
                arg->accept(*this);
            }
            args->push_back(output_term);
        }
    }

    set<Temp*>* use = new set<Temp*>();
    add_term_use(use, obj_term);
    for (auto* arg_term : *args) {
        add_term_use(use, arg_term);
    }

    QuadCall* qcall = new QuadCall(call->id, obj_term, args, new set<Temp*>(), copy_temp_set(use));

    Temp* dst_temp = temp_map->newtemp();
    QuadTemp* dst = make_quad_temp(dst_temp, call->type);
    set<Temp*>* def = new set<Temp*>();
    def->insert(dst_temp);

    visit_result->push_back(new QuadMoveCall(dst, qcall, def, use));
    output_term = new QuadTerm(dst);
}

void Tree2Quad::visit(tree::ExtCall *extcall) {
    if (extcall == nullptr || visit_result == nullptr || temp_map == nullptr) {
        output_term = nullptr;
        return;
    }

    vector<QuadTerm*>* args = new vector<QuadTerm*>();
    if (extcall->args != nullptr) {
        for (auto* arg : *extcall->args) {
            output_term = nullptr;
            if (arg != nullptr) {
                arg->accept(*this);
            }
            args->push_back(output_term);
        }
    }

    set<Temp*>* use = new set<Temp*>();
    for (auto* arg_term : *args) {
        add_term_use(use, arg_term);
    }

    QuadExtCall* qext = new QuadExtCall(extcall->extfun, args, new set<Temp*>(), copy_temp_set(use));

    Temp* dst_temp = temp_map->newtemp();
    QuadTemp* dst = make_quad_temp(dst_temp, extcall->type);
    set<Temp*>* def = new set<Temp*>();
    def->insert(dst_temp);

    visit_result->push_back(new QuadMoveExtCall(dst, qext, def, use));
    output_term = new QuadTerm(dst);
}
