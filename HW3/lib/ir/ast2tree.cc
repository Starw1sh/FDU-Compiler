#define DEBUG
//#undef DEBUG

#include <iostream> // IWYU pragma: keep
#include <string>
#include <map> // IWYU pragma: keep
#include <vector>
#include <algorithm> // IWYU pragma: keep
#include <variant>
#include "config.hh" // IWYU pragma: keep
#include "ASTheader.hh" // IWYU pragma: keep
#include "FDMJAST.hh" // IWYU pragma: keep
#include "treep.hh" // IWYU pragma: keep
#include "temp.hh" // IWYU pragma: keep
#include "ast2tree.hh" // IWYU pragma: keep

using namespace std;
//using namespace fdmj;
//using namespace tree;

static tree::Type ast_type_to_tree_type(fdmj::TypeKind tk) {
    if (tk == fdmj::TypeKind::INT) {
        return tree::Type::INT;
    }
    return tree::Type::PTR;
}

static tree::Type semant_to_tree_type(AST_Semant_Map *semant_map, fdmj::AST *node) {
    if (semant_map == nullptr || node == nullptr) {
        return tree::Type::INT;
    }
    AST_Semant *s = semant_map->getSemant(node);
    if (s == nullptr) {
        return tree::Type::INT;
    }
    return ast_type_to_tree_type(s->get_type());
}

static bool is_relop(const string &op) {
    return op == "==" || op == "!=" || op == "<" || op == ">" || op == "<=" || op == ">=";
}

static bool is_arithop(const string &op) {
    return op == "+" || op == "-" || op == "*" || op == "/" || op == "%" || op == "xor";
}

static tree::Seq *to_seq(vector<tree::Stm*> *sl) {
    if (sl == nullptr) {
        return new tree::Seq();
    }
    return new tree::Seq(sl);
}

static tree::Label *new_pending_label(Temp_map *tm) {
    return tm->newlabel();
}

tree::Program* generate_a_testIR_ast2tree(); //forward decl

// you need to code this function!
tree::Program* ast2tree(fdmj::Program* prog, AST_Semant_Map* semant_map) {
    ASTToTreeVisitor v;
    v.semant_map = semant_map;
    v.class_table = generate_class_table(semant_map);
    prog->accept(v);
    return dynamic_cast<tree::Program*>(v.getTree());
}

Class_table* generate_class_table(AST_Semant_Map* semant_map) {
    Class_table *ct = new Class_table();
    if (semant_map == nullptr || semant_map->getNameMaps() == nullptr) {
        return ct;
    }
    Name_Maps *nm = semant_map->getNameMaps();
    int int_len = Compiler_Config::get("int_length");
    int var_pos = 0;
    int method_pos = 0;

    set<string> *classes = nm->get_class_list();
    for (const string &cn : *classes) {
        set<string> *vl = nm->get_class_var_list(cn);
        for (const string &vn : *vl) {
            string key = cn + "^" + vn;
            if (ct->var_pos_map.find(key) == ct->var_pos_map.end()) {
                ct->var_pos_map[key] = var_pos;
                var_pos += int_len;
            }
        }
        delete vl;

        set<string> *ml = nm->get_method_list(cn);
        for (const string &mn : *ml) {
            if (ct->method_pos_map.find(mn) == ct->method_pos_map.end()) {
                ct->method_pos_map[mn] = method_pos;
                method_pos += Compiler_Config::get("address_length");
            }
        }
        delete ml;
    }
    return ct;
}

Method_var_table* generate_method_var_table(string class_name, string method_name, Name_Maps* nm, Temp_map* tm) {
    Method_var_table *mvt = new Method_var_table();
    if (nm == nullptr || tm == nullptr) {
        return mvt;
    }

    bool has_return_formal = false;
    string return_formal_name;
    tree::Type return_formal_type = tree::Type::INT;

    vector<string> *fl = nm->get_method_formal_list_string(class_name, method_name);
    if (fl != nullptr) {
        for (const string &fn : *fl) {
            Formal *f = nm->get_method_formal(class_name, method_name, fn);
            tree::Type t = tree::Type::INT;
            if (f != nullptr && f->type != nullptr) {
                t = ast_type_to_tree_type(f->type->typeKind);
            }
            if (fn.rfind("_^return^_", 0) == 0) {
                has_return_formal = true;
                return_formal_name = fn;
                return_formal_type = t;
                continue;
            }
            (*(mvt->var_temp_map))[fn] = tm->newtemp();
            (*(mvt->var_type_map))[fn] = t;
        }
        delete fl;
    }

    set<string> *vl = nm->get_method_var_list(class_name, method_name);
    if (vl != nullptr) {
        for (const string &vn : *vl) {
            VarDecl *vd = nm->get_method_var(class_name, method_name, vn);
            tree::Type t = tree::Type::INT;
            if (vd != nullptr && vd->type != nullptr) {
                t = ast_type_to_tree_type(vd->type->typeKind);
            }
            // local vars override formal vars with same name
            (*(mvt->var_temp_map))[vn] = tm->newtemp();
            (*(mvt->var_type_map))[vn] = t;
        }
        delete vl;
    }

    if (has_return_formal) {
        (*(mvt->var_temp_map))[return_formal_name] = tm->newtemp();
        (*(mvt->var_type_map))[return_formal_name] = return_formal_type;
    }

    return mvt;
}

void ASTToTreeVisitor::visit(fdmj::Program* node) {
    vector<tree::FuncDecl*> *fdl = new vector<tree::FuncDecl*>();

    current_class = "__$main__";
    current_method = "main";
    if (node->main != nullptr) {
        node->main->accept(*this);
        tree::FuncDecl *main_fd = dynamic_cast<tree::FuncDecl*>(visit_tree_result);
        if (main_fd != nullptr) {
            fdl->push_back(main_fd);
        }
    }

    // HW3 only requires main method translation.
    visit_tree_result = new tree::Program(fdl);
}

void ASTToTreeVisitor::visit(fdmj::MainMethod* node) {
    method_temp_map = new Temp_map();
    Name_Maps *nm = (semant_map == nullptr) ? nullptr : semant_map->getNameMaps();
    method_var_table = generate_method_var_table("__$main__", "main", nm, method_temp_map);

    vector<tree::Stm*> *sl = new vector<tree::Stm*>();

    if (node->sl != nullptr) {
        for (auto s : *(node->sl)) {
            if (s == nullptr) {
                continue;
            }
            s->accept(*this);
            tree::Stm *ts = dynamic_cast<tree::Stm*>(visit_tree_result);
            if (ts != nullptr) {
                sl->push_back(ts);
            }
        }
    }

    tree::FuncDecl *fd = new tree::FuncDecl(
        "__$main__^main",
        nullptr,
        to_seq(sl),
        tree::Type::INT,
        method_temp_map->next_temp - 1,
        method_temp_map->next_label - 1
    );
    visit_tree_result = fd;
}

void ASTToTreeVisitor::visit(fdmj::ClassDecl* node) {
    (void)node;
    visit_tree_result = nullptr;
}

void ASTToTreeVisitor::visit(fdmj::Type* node) {
    (void)node;
    visit_tree_result = nullptr;
}

void ASTToTreeVisitor::visit(fdmj::VarDecl* node) {
    (void)node;
    visit_tree_result = nullptr;
}

void ASTToTreeVisitor::visit(fdmj::MethodDecl* node) {
    (void)node;
    visit_tree_result = nullptr;
}

void ASTToTreeVisitor::visit(fdmj::Formal* node) {
    (void)node;
    visit_tree_result = nullptr;
}

void ASTToTreeVisitor::visit(fdmj::Nested* node) {
    vector<tree::Stm*> *sl = new vector<tree::Stm*>();
    if (node->sl != nullptr) {
        for (auto s : *(node->sl)) {
            if (s == nullptr) {
                continue;
            }
            s->accept(*this);
            tree::Stm *ts = dynamic_cast<tree::Stm*>(visit_tree_result);
            if (ts != nullptr) {
                sl->push_back(ts);
            }
        }
    }
    visit_tree_result = to_seq(sl);
}

void ASTToTreeVisitor::visit(fdmj::If* node) {
    node->exp->accept(*this);
    Tr_cx *cond = visit_exp_result->unCx(method_temp_map);
    tree::Stm *then_stm = nullptr;
    tree::Stm *else_stm = nullptr;

    if (node->stm1 != nullptr) {
        node->stm1->accept(*this);
        then_stm = dynamic_cast<tree::Stm*>(visit_tree_result);
    }

    if (node->stm2 != nullptr) {
        node->stm2->accept(*this);
        else_stm = dynamic_cast<tree::Stm*>(visit_tree_result);
    }

    tree::Label *lt = method_temp_map->newlabel();
    tree::Label *lf = method_temp_map->newlabel();
    tree::Label *le = method_temp_map->newlabel();
    cond->true_list->patch(lt);
    cond->false_list->patch(lf);

    vector<tree::Stm*> *sl = new vector<tree::Stm*>();
    sl->push_back(cond->stm);
    sl->push_back(new tree::LabelStm(lt));
    if (then_stm != nullptr) {
        sl->push_back(then_stm);
    }
    sl->push_back(new tree::Jump(le));
    sl->push_back(new tree::LabelStm(lf));
    if (else_stm != nullptr) {
        sl->push_back(else_stm);
    }

    sl->push_back(new tree::LabelStm(le));
    visit_tree_result = to_seq(sl);
}

void ASTToTreeVisitor::visit(fdmj::While* node) {
    tree::Label *old_continue = continue_label;
    tree::Label *old_break = break_label;

    node->exp->accept(*this);
    Tr_cx *cond = visit_exp_result->unCx(method_temp_map);

    tree::Label *lt = method_temp_map->newlabel();
    tree::Label *lb = method_temp_map->newlabel();
    tree::Label *le = method_temp_map->newlabel();
    cond->true_list->patch(lb);
    cond->false_list->patch(le);

    continue_label = lt;
    break_label = le;

    vector<tree::Stm*> *sl = new vector<tree::Stm*>();
    sl->push_back(new tree::LabelStm(lt));
    sl->push_back(cond->stm);
    sl->push_back(new tree::LabelStm(lb));

    if (node->stm != nullptr) {
        node->stm->accept(*this);
        tree::Stm *body = dynamic_cast<tree::Stm*>(visit_tree_result);
        if (body != nullptr) {
            sl->push_back(body);
        }
    }

    sl->push_back(new tree::Jump(lt));
    sl->push_back(new tree::LabelStm(le));

    continue_label = old_continue;
    break_label = old_break;

    visit_tree_result = to_seq(sl);
}

void ASTToTreeVisitor::visit(fdmj::Assign* node) {
    node->left->accept(*this);
    tree::Exp *dst = visit_exp_result->unEx(method_temp_map)->exp;
    node->exp->accept(*this);
    tree::Exp *src = visit_exp_result->unEx(method_temp_map)->exp;
    visit_tree_result = new tree::Move(dst, src);
}

void ASTToTreeVisitor::visit(fdmj::CallStm* node) {
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    if (node->par != nullptr) {
        for (auto e : *(node->par)) {
            e->accept(*this);
            args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
        }
    }

    tree::Exp *exp = nullptr;
    if (node->obj == nullptr) {
        exp = new tree::ExtCall(tree::Type::INT, node->name->id, args);
    } else {
        node->obj->accept(*this);
        tree::Exp *obj = visit_exp_result->unEx(method_temp_map)->exp;
        exp = new tree::Call(tree::Type::INT, node->name->id, obj, args);
    }
    visit_tree_result = new tree::ExpStm(exp);
}

void ASTToTreeVisitor::visit(fdmj::Continue* node) {
    (void)node;
    if (continue_label == nullptr) {
        visit_tree_result = new tree::Seq(new vector<tree::Stm*>());
        return;
    }
    visit_tree_result = new tree::Jump(continue_label);
}

void ASTToTreeVisitor::visit(fdmj::Break* node) {
    (void)node;
    if (break_label == nullptr) {
        visit_tree_result = new tree::Seq(new vector<tree::Stm*>());
        return;
    }
    visit_tree_result = new tree::Jump(break_label);
}

void ASTToTreeVisitor::visit(fdmj::Return* node) {
    node->exp->accept(*this);
    tree::Exp *ret_exp = visit_exp_result->unEx(method_temp_map)->exp;
    visit_tree_result = new tree::Return(ret_exp);
}

void ASTToTreeVisitor::visit(fdmj::PutInt* node) {
    node->exp->accept(*this);
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
    visit_tree_result = new tree::ExpStm(new tree::ExtCall(tree::Type::INT, "putint", args));
}

void ASTToTreeVisitor::visit(fdmj::PutCh* node) {
    node->exp->accept(*this);
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
    visit_tree_result = new tree::ExpStm(new tree::ExtCall(tree::Type::INT, "putch", args));
}

void ASTToTreeVisitor::visit(fdmj::PutArray* node) {
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    node->n->accept(*this);
    args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
    node->arr->accept(*this);
    args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
    visit_tree_result = new tree::ExpStm(new tree::ExtCall(tree::Type::INT, "putarray", args));
}

void ASTToTreeVisitor::visit(fdmj::Starttime* node) {
    (void)node;
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    visit_tree_result = new tree::ExpStm(new tree::ExtCall(tree::Type::INT, "starttime", args));
}

void ASTToTreeVisitor::visit(fdmj::Stoptime* node) {
    (void)node;
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    visit_tree_result = new tree::ExpStm(new tree::ExtCall(tree::Type::INT, "stoptime", args));
}

void ASTToTreeVisitor::visit(fdmj::BinaryOp* node) {
    const string op = node->op->op;

    if (op == "&&" || op == "||") {
        node->left->accept(*this);
        Tr_cx *lcx = visit_exp_result->unCx(method_temp_map);
        node->right->accept(*this);
        Tr_cx *rcx = visit_exp_result->unCx(method_temp_map);

        tree::Label *mid = method_temp_map->newlabel();
        vector<tree::Stm*> *sl = new vector<tree::Stm*>();
        Patch_list *tl = new Patch_list();
        Patch_list *fl = new Patch_list();

        if (op == "&&") {
            lcx->true_list->patch(mid);
            tl->add(rcx->true_list);
            fl->add(lcx->false_list);
            fl->add(rcx->false_list);
        } else {
            lcx->false_list->patch(mid);
            tl->add(lcx->true_list);
            tl->add(rcx->true_list);
            fl->add(rcx->false_list);
        }

        sl->push_back(lcx->stm);
        sl->push_back(new tree::LabelStm(mid));
        sl->push_back(rcx->stm);
        visit_exp_result = new Tr_cx(tl, fl, to_seq(sl));
        return;
    }

    node->left->accept(*this);
    tree::Exp *l = visit_exp_result->unEx(method_temp_map)->exp;
    node->right->accept(*this);
    tree::Exp *r = visit_exp_result->unEx(method_temp_map)->exp;

    if (is_relop(op)) {
        Patch_list *tl = new Patch_list();
        Patch_list *fl = new Patch_list();
        tree::Label *t = new_pending_label(method_temp_map);
        tree::Label *f = new_pending_label(method_temp_map);
        tl->add_patch(t);
        fl->add_patch(f);
        visit_exp_result = new Tr_cx(tl, fl, new tree::Cjump(op, l, r, t, f));
        return;
    }

    string bop = op;
    if (!is_arithop(bop)) {
        bop = "+";
    }
    visit_exp_result = new Tr_ex(new tree::Binop(tree::Type::INT, bop, l, r));
}

void ASTToTreeVisitor::visit(fdmj::UnaryOp* node) {
    const string op = node->op->op;
    node->exp->accept(*this);

    if (op == "-") {
        tree::Exp *e = visit_exp_result->unEx(method_temp_map)->exp;
        visit_exp_result = new Tr_ex(new tree::Binop(tree::Type::INT, "-", new tree::Const(0), e));
        return;
    }
    if (op == "!") {
        Tr_cx *cx = visit_exp_result->unCx(method_temp_map);
        visit_exp_result = new Tr_cx(cx->false_list, cx->true_list, cx->stm);
        return;
    }

    visit_exp_result = visit_exp_result->unEx(method_temp_map);
}

void ASTToTreeVisitor::visit(fdmj::ArrayExp* node) {
    node->arr->accept(*this);
    tree::Exp *arr = visit_exp_result->unEx(method_temp_map)->exp;
    node->index->accept(*this);
    tree::Exp *idx = visit_exp_result->unEx(method_temp_map)->exp;

    int int_len = Compiler_Config::get("int_length");
    tree::Exp *off = new tree::Binop(tree::Type::INT, "*", idx, new tree::Const(int_len));
    tree::Exp *addr = new tree::Binop(tree::Type::PTR, "+", arr, off);
    visit_exp_result = new Tr_ex(new tree::Mem(tree::Type::INT, addr));
}

void ASTToTreeVisitor::visit(fdmj::CallExp* node) {
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    if (node->par != nullptr) {
        for (auto e : *(node->par)) {
            e->accept(*this);
            args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
        }
    }
    tree::Type ret_t = semant_to_tree_type(semant_map, node);

    if (node->obj == nullptr) {
        visit_exp_result = new Tr_ex(new tree::ExtCall(ret_t, node->name->id, args));
    } else {
        node->obj->accept(*this);
        tree::Exp *obj = visit_exp_result->unEx(method_temp_map)->exp;
        visit_exp_result = new Tr_ex(new tree::Call(ret_t, node->name->id, obj, args));
    }
}

void ASTToTreeVisitor::visit(fdmj::ClassVar* node) {
    node->obj->accept(*this);
    tree::Exp *obj = visit_exp_result->unEx(method_temp_map)->exp;

    string class_name = class_var_class_name;
    if (semant_map != nullptr) {
        AST_Semant *s = semant_map->getSemant(node->obj);
        if (s != nullptr && s->get_type() == fdmj::TypeKind::CLASS && holds_alternative<string>(s->get_type_par())) {
            class_name = get<string>(s->get_type_par());
        }
    }

    int offset = 0;
    if (class_table != nullptr && !class_name.empty() && class_table->has_var(class_name, node->id->id)) {
        offset = class_table->get_var_pos(class_name, node->id->id);
    }
    tree::Exp *addr = new tree::Binop(tree::Type::PTR, "+", obj, new tree::Const(offset));
    tree::Type t = semant_to_tree_type(semant_map, node);
    visit_exp_result = new Tr_ex(new tree::Mem(t, addr));
}

void ASTToTreeVisitor::visit(fdmj::This* node) {
    (void)node;
    tree::Temp *this_temp = (method_var_table == nullptr) ? nullptr : method_var_table->get_var_temp("this");
    if (this_temp == nullptr) {
        visit_exp_result = new Tr_ex(new tree::Const(0));
        return;
    }
    visit_exp_result = new Tr_ex(new tree::TempExp(tree::Type::PTR, this_temp));
}

void ASTToTreeVisitor::visit(fdmj::Length* node) {
    node->exp->accept(*this);
    tree::Exp *arr = visit_exp_result->unEx(method_temp_map)->exp;
    int int_len = Compiler_Config::get("int_length");
    tree::Exp *addr = new tree::Binop(tree::Type::PTR, "-", arr, new tree::Const(int_len));
    visit_exp_result = new Tr_ex(new tree::Mem(tree::Type::INT, addr));
}

void ASTToTreeVisitor::visit(fdmj::NewArray* node) {
    node->size->accept(*this);
    tree::Exp *size = visit_exp_result->unEx(method_temp_map)->exp;
    int int_len = Compiler_Config::get("int_length");

    tree::TempExp *base = new tree::TempExp(tree::Type::PTR, method_temp_map->newtemp());
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    tree::Exp *bytes = new tree::Binop(
        tree::Type::INT,
        "*",
        new tree::Binop(tree::Type::INT, "+", size, new tree::Const(1)),
        new tree::Const(int_len)
    );
    args->push_back(bytes);

    vector<tree::Stm*> *sl = new vector<tree::Stm*>();
    sl->push_back(new tree::Move(base, new tree::ExtCall(tree::Type::PTR, "malloc", args)));
    sl->push_back(new tree::Move(new tree::Mem(tree::Type::INT, base), size));

    tree::Exp *arr_ptr = new tree::Binop(tree::Type::PTR, "+", base, new tree::Const(int_len));
    visit_exp_result = new Tr_ex(new tree::Eseq(tree::Type::PTR, to_seq(sl), arr_ptr));
}

void ASTToTreeVisitor::visit(fdmj::NewObject* node) {
    int obj_size = Compiler_Config::get("address_length");
    if (class_table != nullptr) {
        int fields = 0;
        for (const auto &kv : class_table->var_pos_map) {
            if (kv.first.rfind(node->id->id + "^", 0) == 0) {
                fields++;
            }
        }
        if (fields > 0) {
            obj_size = fields * Compiler_Config::get("int_length");
        }
    }
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    args->push_back(new tree::Const(obj_size));
    visit_exp_result = new Tr_ex(new tree::ExtCall(tree::Type::PTR, "malloc", args));
}

void ASTToTreeVisitor::visit(fdmj::GetInt* node) {
    (void)node;
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    visit_exp_result = new Tr_ex(new tree::ExtCall(tree::Type::INT, "getint", args));
}

void ASTToTreeVisitor::visit(fdmj::GetCh* node) {
    (void)node;
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    visit_exp_result = new Tr_ex(new tree::ExtCall(tree::Type::INT, "getch", args));
}

void ASTToTreeVisitor::visit(fdmj::GetArray* node) {
    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    if (node->exp != nullptr) {
        node->exp->accept(*this);
        args->push_back(visit_exp_result->unEx(method_temp_map)->exp);
    }
    visit_exp_result = new Tr_ex(new tree::ExtCall(tree::Type::INT, "getarray", args));
}

void ASTToTreeVisitor::visit(fdmj::IdExp* node) {
    tree::Temp *t = (method_var_table == nullptr) ? nullptr : method_var_table->get_var_temp(node->id);
    tree::Type ty = tree::Type::INT;
    if (method_var_table != nullptr && method_var_table->var_type_map->find(node->id) != method_var_table->var_type_map->end()) {
        ty = method_var_table->get_var_type(node->id);
    }
    if (t == nullptr) {
        // fallback for undeclared names in HW3 tests
        t = method_temp_map->newtemp();
        (*(method_var_table->var_temp_map))[node->id] = t;
        (*(method_var_table->var_type_map))[node->id] = ty;
    }
    visit_exp_result = new Tr_ex(new tree::TempExp(ty, t));
}

void ASTToTreeVisitor::visit(fdmj::OpExp* node) {
    (void)node;
    visit_exp_result = new Tr_ex(new tree::Const(0));
}

void ASTToTreeVisitor::visit(fdmj::IntExp* node) {
    visit_exp_result = new Tr_ex(new tree::Const(node->val));
}

//this is only for a test
tree::Program* generate_a_testIR_ast2tree() {
    Temp_map *tm = new Temp_map();
    tree::Label *entry_label = tm->newlabel();
    tree::LabelStm *label_stm = new tree::LabelStm(entry_label);
    tree::Move *move = new tree::Move(new tree::TempExp(tree::Type::INT, tm->newtemp()), new tree::Const(1));

    vector<tree::Stm*> *sl1 = new vector<tree::Stm*>(); sl1->push_back(move);

    vector<tree::Exp*> *args = new vector<tree::Exp*>();
    tree::Eseq *eseq = new tree::Eseq(tree::Type::INT, new tree::Seq(sl1), new tree::Const(19));
    args->push_back(eseq);

    tree::ExtCall *call = new tree::ExtCall(tree::Type::INT, "putchar", args);
    tree::Return *ret = new tree::Return(new tree::Const(100));
    vector<tree::Stm*> *sl = new vector<tree::Stm*>();
    sl->push_back(label_stm);
    sl->push_back(new tree::ExpStm(call));
    sl->push_back(ret);
    tree::FuncDecl *fd = new tree::FuncDecl("_^main^_main", nullptr, new tree::Seq(sl), tree::Type::INT, 100, 100);
    vector<tree::FuncDecl*> *fdl = new vector<tree::FuncDecl*>();
    fdl->push_back(fd);
    return new tree::Program(fdl);
}
