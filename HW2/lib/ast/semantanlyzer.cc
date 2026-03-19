#define DEBUG
#undef DEBUG

#include <iostream>
#include <map>
#include <vector>
#include <algorithm>
#include <cstdlib>
#include <set>
#include "namemaps.hh"
#include "semant.hh"

using namespace std;
using namespace fdmj;

namespace {

constexpr const char* kMainClassName = "__main__";
constexpr const char* kMainMethodName = "main";
constexpr const char* kReturnFormalName = "__return__";

[[noreturn]] void fail_with_msg(const string& msg, AST* node = nullptr) {
    if (node != nullptr && node->getPos() != nullptr) {
        cerr << "at position: " << node->getPos()->print() << endl;
    }
    cerr << "Error: " << msg << endl;
    exit(1);
}

AST_Semant* make_int_semant(bool lvalue = false) {
    return new AST_Semant(AST_Semant::Kind::Value, TypeKind::INT, monostate{}, lvalue);
}

AST_Semant* make_array_semant(int arity = 0, bool lvalue = false) {
    return new AST_Semant(AST_Semant::Kind::Value, TypeKind::ARRAY, arity, lvalue);
}

AST_Semant* make_class_semant(const string& cid, bool lvalue = false) {
    return new AST_Semant(AST_Semant::Kind::Value, TypeKind::CLASS, cid, lvalue);
}

bool is_same_value_type(AST_Semant* a, AST_Semant* b) {
    if (a == nullptr || b == nullptr) {
        return false;
    }
    if (a->get_kind() != AST_Semant::Kind::Value || b->get_kind() != AST_Semant::Kind::Value) {
        return false;
    }
    if (a->get_type() != b->get_type()) {
        return false;
    }
    if (a->get_type() == TypeKind::CLASS) {
        if (!holds_alternative<string>(a->get_type_par()) || !holds_alternative<string>(b->get_type_par())) {
            return false;
        }
        return get<string>(a->get_type_par()) == get<string>(b->get_type_par());
    }
    if (a->get_type() == TypeKind::ARRAY) {
        if (!holds_alternative<int>(a->get_type_par()) || !holds_alternative<int>(b->get_type_par())) {
            return false;
        }
        return get<int>(a->get_type_par()) == get<int>(b->get_type_par());
    }
    return true;
}

AST_Semant* semant_from_type(Type* t, bool lvalue) {
    if (t == nullptr) {
        return nullptr;
    }
    if (t->typeKind == TypeKind::INT) {
        return make_int_semant(lvalue);
    }
    if (t->typeKind == TypeKind::ARRAY) {
        int arity = 0;
        if (t->arity != nullptr) {
            arity = t->arity->val;
        }
        return make_array_semant(arity, lvalue);
    }
    if (t->cid == nullptr) {
        return nullptr;
    }
    return make_class_semant(t->cid->id, lvalue);
}

bool is_subclass_or_same(Name_Maps* nm, const string& child, const string& parent) {
    if (child == parent) {
        return true;
    }
    string cur = child;
    set<string> seen;
    while (!cur.empty()) {
        if (seen.find(cur) != seen.end()) {
            break;
        }
        seen.insert(cur);
        cur = nm->get_parent(cur);
        if (cur == parent) {
            return true;
        }
    }
    return false;
}

bool is_value_assignable(Name_Maps* nm, AST_Semant* to_type, AST_Semant* from_type) {
    if (to_type == nullptr || from_type == nullptr) {
        return false;
    }
    if (to_type->get_kind() != AST_Semant::Kind::Value || from_type->get_kind() != AST_Semant::Kind::Value) {
        return false;
    }
    if (to_type->get_type() != from_type->get_type()) {
        return false;
    }
    if (to_type->get_type() == TypeKind::CLASS) {
        if (!holds_alternative<string>(to_type->get_type_par()) || !holds_alternative<string>(from_type->get_type_par())) {
            return false;
        }
        return is_subclass_or_same(nm, get<string>(from_type->get_type_par()), get<string>(to_type->get_type_par()));
    }
    if (to_type->get_type() == TypeKind::ARRAY) {
        if (!holds_alternative<int>(to_type->get_type_par()) || !holds_alternative<int>(from_type->get_type_par())) {
            return false;
        }
        return get<int>(to_type->get_type_par()) == get<int>(from_type->get_type_par());
    }
    return true;
}

bool is_int_value(AST_Semant* s) {
    return s != nullptr && s->get_kind() == AST_Semant::Kind::Value && s->get_type() == TypeKind::INT;
}

} // namespace

AST_Semant_Map* semant_analyze(Program* node) {
    if (node == nullptr) {
        return nullptr;
    }
    Name_Maps* name_maps = makeNameMaps(node);
    AST_Semant_Visitor semant_visitor(name_maps);
    node->accept(semant_visitor);
    return semant_visitor.getSemantMap();
}

void AST_Semant_Visitor::visit(Program* node) {
#ifdef DEBUG
    std::cout << "Visiting Program" << std::endl;
#endif
    if (node == nullptr) {
        return;
    }
    if (node->main != nullptr) {
        node->main->accept(*this);
    }
    if (node->cdl != nullptr) {
        for (auto cl : *(node->cdl)) {
            if (cl != nullptr) {
                cl->accept(*this);
            }
        }
    }
}

void AST_Semant_Visitor::visit(MainMethod* node) {
    if (node == nullptr) {
        return;
    }
    current_visiting_class = kMainClassName;
    current_visiting_method = kMainMethodName;

    if (node->vdl != nullptr) {
        for (auto vd : *(node->vdl)) {
            if (vd != nullptr) {
                vd->accept(*this);
            }
        }
    }
    if (node->sl != nullptr) {
        for (auto stm : *(node->sl)) {
            if (stm != nullptr) {
                stm->accept(*this);
            }
        }
    }

    current_visiting_method.clear();
    current_visiting_class.clear();
}

void AST_Semant_Visitor::visit(ClassDecl* node) {
    if (node == nullptr || node->id == nullptr) {
        return;
    }
    current_visiting_class = node->id->id;

    // Enforce single-level inheritance and reject cycles defensively.
    string parent = name_maps->get_parent(current_visiting_class);
    if (!parent.empty()) {
        if (!name_maps->get_parent(parent).empty()) {
            fail_with_msg("single-level inheritance violated for class: " + current_visiting_class, node);
        }
        /*
        set<string> seen;
        string cur = current_visiting_class;
        while (!cur.empty()) {
            if (seen.find(cur) != seen.end()) {
                fail_with_msg("inheritance cycle detected at class: " + current_visiting_class, node);
            }
            seen.insert(cur);
            cur = name_maps->get_parent(cur);
        }*/
    }

    if (node->vdl != nullptr) {
        for (auto vd : *(node->vdl)) {
            if (vd != nullptr) {
                vd->accept(*this);
            }
        }
    }
    if (node->mdl != nullptr) {
        for (auto md : *(node->mdl)) {
            if (md != nullptr) {
                md->accept(*this);
            }
        }
    }

    current_visiting_class.clear();
}

void AST_Semant_Visitor::visit(Type* node) {
    (void)node;
}

void AST_Semant_Visitor::visit(VarDecl* node) {
    if (node == nullptr || node->type == nullptr) {
        return;
    }
    // Validate declaration initializers.
    if (holds_alternative<IntExp*>(node->init)) {
        if (node->type->typeKind != TypeKind::INT) {
            fail_with_msg("int initializer only allowed for int variables", node);
        }
        IntExp* init = get<IntExp*>(node->init);
        if (init != nullptr) {
            init->accept(*this);
        }
    } else if (holds_alternative<vector<IntExp*>*>(node->init)) {
        if (node->type->typeKind != TypeKind::ARRAY) {
            fail_with_msg("array initializer only allowed for array variables", node);
        }
        vector<IntExp*>* init_list = get<vector<IntExp*>*>(node->init);
        if (init_list != nullptr) {
            for (auto ie : *init_list) {
                if (ie != nullptr) {
                    ie->accept(*this);
                }
            }
        }
    }
}

void AST_Semant_Visitor::visit(MethodDecl* node) {
    if (node == nullptr || node->id == nullptr || node->type == nullptr) {
        return;
    }
    if (current_visiting_class.empty()) {
        fail_with_msg("method declaration outside class scope", node);
    }

    current_visiting_method = node->id->id;

    // Check override signature (same params, covariant return type).
    string parent = name_maps->get_parent(current_visiting_class);
    if (!parent.empty() && name_maps->is_method(parent, current_visiting_method)) {
        vector<Formal*>* child_fl = name_maps->get_method_formal_list(current_visiting_class, current_visiting_method);
        vector<Formal*>* parent_fl = name_maps->get_method_formal_list(parent, current_visiting_method);
        if (child_fl == nullptr || parent_fl == nullptr || child_fl->empty() || parent_fl->empty()) {
            fail_with_msg("cannot resolve method signature while checking override: " + current_visiting_method, node);
        }
        if (child_fl->size() != parent_fl->size()) {
            fail_with_msg("override formal count mismatch in method: " + current_visiting_method, node);
        }

        for (size_t i = 0; i + 1 < child_fl->size(); ++i) {
            AST_Semant* c = semant_from_type((*child_fl)[i]->type, false);
            AST_Semant* p = semant_from_type((*parent_fl)[i]->type, false);
            if (!is_same_value_type(c, p)) {
                fail_with_msg("override formal type mismatch in method: " + current_visiting_method, (*child_fl)[i]);
            }
        }

        AST_Semant* child_ret = semant_from_type((*child_fl)[child_fl->size() - 1]->type, false);
        AST_Semant* parent_ret = semant_from_type((*parent_fl)[parent_fl->size() - 1]->type, false);
        if (!is_value_assignable(name_maps, parent_ret, child_ret)) {
            fail_with_msg("override return type is not covariant in method: " + current_visiting_method, node);
        }
    }

    if (node->fl != nullptr) {
        for (auto f : *(node->fl)) {
            if (f != nullptr) {
                f->accept(*this);
            }
        }
    }
    if (node->vdl != nullptr) {
        for (auto vd : *(node->vdl)) {
            if (vd != nullptr) {
                vd->accept(*this);
            }
        }
    }
    if (node->sl != nullptr) {
        for (auto stm : *(node->sl)) {
            if (stm != nullptr) {
                stm->accept(*this);
            }
        }
    }

    current_visiting_method.clear();
}

void AST_Semant_Visitor::visit(Formal* node) {
    (void)node;
}

void AST_Semant_Visitor::visit(Nested* node) {
    if (node == nullptr || node->sl == nullptr) {
        return;
    }
    for (auto stm : *(node->sl)) {
        if (stm != nullptr) {
            stm->accept(*this);
        }
    }
}

void AST_Semant_Visitor::visit(If* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* cond = semant_map->getSemant(node->exp);
    if (!is_int_value(cond)) {
        fail_with_msg("if condition must be int", node->exp);
    }
    if (node->stm1 != nullptr) {
        node->stm1->accept(*this);
    }
    if (node->stm2 != nullptr) {
        node->stm2->accept(*this);
    }
}

void AST_Semant_Visitor::visit(While* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* cond = semant_map->getSemant(node->exp);
    if (!is_int_value(cond)) {
        fail_with_msg("while condition must be int", node->exp);
    }

    ++in_a_while_loop;
    if (node->stm != nullptr) {
        node->stm->accept(*this);
    }
    --in_a_while_loop;
}

void AST_Semant_Visitor::visit(Assign* node) {
    if (node == nullptr || node->left == nullptr || node->exp == nullptr) {
        return;
    }
    node->left->accept(*this);
    node->exp->accept(*this);
    AST_Semant* lhs = semant_map->getSemant(node->left);
    AST_Semant* rhs = semant_map->getSemant(node->exp);
    if (lhs == nullptr || rhs == nullptr) {
        fail_with_msg("assignment operand semantic missing", node);
    }
    if (!lhs->is_lvalue()) {
        fail_with_msg("left-hand side of assignment must be lvalue", node->left);
    }
    if (!is_value_assignable(name_maps, lhs, rhs)) {
        fail_with_msg("assignment type mismatch", node);
    }
    semant_map->setSemant(node, lhs);
}

static vector<Formal*>* resolve_method_formals(Name_Maps* name_maps, const string& cls, const string& method, AST* site) {
    string cur = cls;
    set<string> seen;
    while (!cur.empty()) {
        if (seen.find(cur) != seen.end()) {
            break;
        }
        seen.insert(cur);
        if (name_maps->is_method(cur, method)) {
            vector<Formal*>* fl = name_maps->get_method_formal_list(cur, method);
            if (fl == nullptr) {
                fail_with_msg("failed to resolve formal list for method: " + cur + "::" + method, site);
            }
            return fl;
        }
        cur = name_maps->get_parent(cur);
    }
    return nullptr;
}

void AST_Semant_Visitor::visit(CallStm* node) {
    if (node == nullptr || node->obj == nullptr || node->name == nullptr) {
        return;
    }
    node->obj->accept(*this);
    AST_Semant* obj_sem = semant_map->getSemant(node->obj);
    if (obj_sem == nullptr || obj_sem->get_type() != TypeKind::CLASS || !holds_alternative<string>(obj_sem->get_type_par())) {
        fail_with_msg("method call receiver must be class object", node->obj);
    }
    string obj_class = get<string>(obj_sem->get_type_par());
    vector<Formal*>* fl = resolve_method_formals(name_maps, obj_class, node->name->id, node);
    if (fl == nullptr || fl->empty()) {
        fail_with_msg("method not found: " + obj_class + "::" + node->name->id, node->name);
    }

    size_t expected = fl->size() - 1;
    size_t actual = (node->par == nullptr) ? 0 : node->par->size();
    if (expected != actual) {
        fail_with_msg("method call argument count mismatch for: " + node->name->id, node);
    }
    if (node->par != nullptr) {
        for (size_t i = 0; i < node->par->size(); ++i) {
            Exp* arg = (*(node->par))[i];
            if (arg == nullptr) {
                fail_with_msg("null argument in method call", node);
            }
            arg->accept(*this);
            AST_Semant* arg_sem = semant_map->getSemant(arg);
            AST_Semant* formal_sem = semant_from_type((*fl)[i]->type, false);
            if (!is_value_assignable(name_maps, formal_sem, arg_sem)) {
                fail_with_msg("method call argument type mismatch at index " + to_string(i), arg);
            }
        }
    }
}

void AST_Semant_Visitor::visit(Continue* node) {
    if (in_a_while_loop <= 0) {
        fail_with_msg("continue must be inside while", node);
    }
}

void AST_Semant_Visitor::visit(Break* node) {
    if (in_a_while_loop <= 0) {
        fail_with_msg("break must be inside while", node);
    }
}

void AST_Semant_Visitor::visit(Return* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* ret_sem = semant_map->getSemant(node->exp);
    if (ret_sem == nullptr) {
        fail_with_msg("return expression semantic missing", node);
    }

    Formal* declared_ret = name_maps->get_method_formal(current_visiting_class, current_visiting_method, kReturnFormalName);
    if (declared_ret == nullptr) {
        fail_with_msg("cannot find declared return type", node);
    }
    AST_Semant* declared_ret_sem = semant_from_type(declared_ret->type, false);
    if (!is_value_assignable(name_maps, declared_ret_sem, ret_sem)) {
        fail_with_msg("return type mismatch", node);
    }
    semant_map->setSemant(node, ret_sem);
}

void AST_Semant_Visitor::visit(PutInt* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* e = semant_map->getSemant(node->exp);
    if (!is_int_value(e)) {
        fail_with_msg("putint expects int expression", node->exp);
    }
}

void AST_Semant_Visitor::visit(PutCh* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* e = semant_map->getSemant(node->exp);
    if (!is_int_value(e)) {
        fail_with_msg("putch expects int expression", node->exp);
    }
}

void AST_Semant_Visitor::visit(PutArray* node) {
    if (node == nullptr || node->n == nullptr || node->arr == nullptr) {
        return;
    }
    node->n->accept(*this);
    node->arr->accept(*this);
    AST_Semant* n = semant_map->getSemant(node->n);
    AST_Semant* arr = semant_map->getSemant(node->arr);
    if (!is_int_value(n)) {
        fail_with_msg("putarray first parameter must be int", node->n);
    }
    if (arr == nullptr || arr->get_kind() != AST_Semant::Kind::Value || arr->get_type() != TypeKind::ARRAY) {
        fail_with_msg("putarray second parameter must be array", node->arr);
    }
}

void AST_Semant_Visitor::visit(Starttime* node) {
    (void)node;
}

void AST_Semant_Visitor::visit(Stoptime* node) {
    (void)node;
}

void AST_Semant_Visitor::visit(BinaryOp* node) {
    if (node == nullptr || node->left == nullptr || node->right == nullptr || node->op == nullptr) {
        return;
    }
    node->left->accept(*this);
    node->right->accept(*this);
    AST_Semant* lhs = semant_map->getSemant(node->left);
    AST_Semant* rhs = semant_map->getSemant(node->right);
    if (lhs == nullptr || rhs == nullptr) {
        fail_with_msg("binary operand semantic missing", node);
    }

    const string& op = node->op->op;
    //Actually, HW2 only contains +, -, *, /, ||, &&, <, ==
    if (op == "+" || op == "-" || op == "*" || op == "/" || op == "&&" || op == "||" || op == "<" || op == ">" || op == "<=" || op == ">=") {
        if (!is_int_value(lhs) || !is_int_value(rhs)) {
            fail_with_msg("binary operator " + op + " requires int operands", node);
        }
        semant_map->setSemant(node, make_int_semant(false));
        return;
    }
    if (op == "==" || op == "!=") {
        if (lhs->get_type() != rhs->get_type()) {
            fail_with_msg("operator " + op + " requires comparable operands", node);
        }
        if (lhs->get_type() == TypeKind::CLASS) {
            if (!holds_alternative<string>(lhs->get_type_par()) || !holds_alternative<string>(rhs->get_type_par())) {
                fail_with_msg("invalid class operands for equality", node);
            }
            const string& lc = get<string>(lhs->get_type_par());
            const string& rc = get<string>(rhs->get_type_par());
            if (!is_subclass_or_same(name_maps, lc, rc) && !is_subclass_or_same(name_maps, rc, lc)) {
                fail_with_msg("incompatible class types for equality", node);
            }
        } else if (lhs->get_type() == TypeKind::ARRAY) {
            if (!is_same_value_type(lhs, rhs)) {
                fail_with_msg("incompatible array types for equality", node);
            }
        } else if (!is_int_value(lhs) || !is_int_value(rhs)) {
            fail_with_msg("invalid operands for equality", node);
        }
        semant_map->setSemant(node, make_int_semant(false));
        return;
    }

    fail_with_msg("unknown binary operator: " + op, node->op);
}

void AST_Semant_Visitor::visit(UnaryOp* node) {
    if (node == nullptr || node->op == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* e = semant_map->getSemant(node->exp);
    if (!is_int_value(e)) {
        fail_with_msg("unary operator requires int operand", node);
    }
    if (node->op->op != "-" && node->op->op != "!") {
        fail_with_msg("unknown unary operator: " + node->op->op, node->op);
    }
    semant_map->setSemant(node, make_int_semant(false));
}

void AST_Semant_Visitor::visit(ArrayExp* node) {
    if (node == nullptr || node->arr == nullptr || node->index == nullptr) {
        return;
    }
    node->arr->accept(*this);
    node->index->accept(*this);
    AST_Semant* arr = semant_map->getSemant(node->arr);
    AST_Semant* idx = semant_map->getSemant(node->index);
    if (arr == nullptr || arr->get_kind() != AST_Semant::Kind::Value || arr->get_type() != TypeKind::ARRAY) {
        fail_with_msg("array indexing target must be array", node->arr);
    }
    if (!is_int_value(idx)) {
        fail_with_msg("array index must be int", node->index);
    }
    semant_map->setSemant(node, make_int_semant(true));
}

void AST_Semant_Visitor::visit(CallExp* node) {
    if (node == nullptr || node->obj == nullptr || node->name == nullptr) {
        return;
    }
    node->obj->accept(*this);
    AST_Semant* obj_sem = semant_map->getSemant(node->obj);
    if (obj_sem == nullptr || obj_sem->get_type() != TypeKind::CLASS || !holds_alternative<string>(obj_sem->get_type_par())) {
        fail_with_msg("method call receiver must be class object", node->obj);
    }

    string obj_class = get<string>(obj_sem->get_type_par());
    vector<Formal*>* fl = resolve_method_formals(name_maps, obj_class, node->name->id, node);
    if (fl == nullptr || fl->empty()) {
        fail_with_msg("method not found: " + obj_class + "::" + node->name->id, node->name);
    }

    size_t expected = fl->size() - 1;
    size_t actual = (node->par == nullptr) ? 0 : node->par->size();
    if (expected != actual) {
        fail_with_msg("method call argument count mismatch for: " + node->name->id, node);
    }

    if (node->par != nullptr) {
        for (size_t i = 0; i < node->par->size(); ++i) {
            Exp* arg = (*(node->par))[i];
            if (arg == nullptr) {
                fail_with_msg("null argument in method call", node);
            }
            arg->accept(*this);
            AST_Semant* arg_sem = semant_map->getSemant(arg);
            AST_Semant* formal_sem = semant_from_type((*fl)[i]->type, false);
            if (!is_value_assignable(name_maps, formal_sem, arg_sem)) {
                fail_with_msg("method call argument type mismatch at index " + to_string(i), arg);
            }
        }
    }

    AST_Semant* ret_sem = semant_from_type((*fl)[fl->size() - 1]->type, false);
    if (ret_sem == nullptr) {
        fail_with_msg("failed to determine call return type", node);
    }
    semant_map->setSemant(node, ret_sem);
}

void AST_Semant_Visitor::visit(ClassVar* node) {
    if (node == nullptr || node->obj == nullptr || node->id == nullptr) {
        return;
    }
    node->obj->accept(*this);
    AST_Semant* obj_sem = semant_map->getSemant(node->obj);
    if (obj_sem == nullptr || obj_sem->get_type() != TypeKind::CLASS || !holds_alternative<string>(obj_sem->get_type_par())) {
        fail_with_msg("field access receiver must be class object", node->obj);
    }

    string cur = get<string>(obj_sem->get_type_par());
    set<string> seen;
    while (!cur.empty()) {
        if (seen.find(cur) != seen.end()) {
            break;
        }
        seen.insert(cur);
        VarDecl* vd = name_maps->get_class_var(cur, node->id->id);
        if (vd != nullptr && vd->type != nullptr) {
            AST_Semant* field_sem = semant_from_type(vd->type, true);
            semant_map->setSemant(node->id, field_sem);
            semant_map->setSemant(node, field_sem);
            return;
        }
        cur = name_maps->get_parent(cur);
    }
    fail_with_msg("field not found: " + node->id->id, node->id);
}

void AST_Semant_Visitor::visit(This* node) {
    if (current_visiting_class.empty() || current_visiting_class == kMainClassName) {
        fail_with_msg("this is only valid inside class methods", node);
    }
    semant_map->setSemant(node, make_class_semant(current_visiting_class, false));
}

void AST_Semant_Visitor::visit(Length* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* e = semant_map->getSemant(node->exp);
    if (e == nullptr || e->get_type() != TypeKind::ARRAY) {
        fail_with_msg("length expects array expression", node->exp);
    }
    semant_map->setSemant(node, make_int_semant(false));
}

void AST_Semant_Visitor::visit(NewArray* node) {
    if (node == nullptr || node->size == nullptr) {
        return;
    }
    node->size->accept(*this);
    AST_Semant* sz = semant_map->getSemant(node->size);
    if (!is_int_value(sz)) {
        fail_with_msg("new array size must be int", node->size);
    }
    semant_map->setSemant(node, make_array_semant(0, false));
}

void AST_Semant_Visitor::visit(NewObject* node) {
    if (node == nullptr || node->id == nullptr) {
        return;
    }
    if (!name_maps->is_class(node->id->id)) {
        fail_with_msg("unknown class in object creation: " + node->id->id, node->id);
    }
    semant_map->setSemant(node, make_class_semant(node->id->id, false));
}

void AST_Semant_Visitor::visit(GetInt* node) {
    semant_map->setSemant(node, make_int_semant(false));
}

void AST_Semant_Visitor::visit(GetCh* node) {
    semant_map->setSemant(node, make_int_semant(false));
}

void AST_Semant_Visitor::visit(GetArray* node) {
    if (node == nullptr || node->exp == nullptr) {
        return;
    }
    node->exp->accept(*this);
    AST_Semant* target = semant_map->getSemant(node->exp);
    if (target == nullptr || target->get_type() != TypeKind::ARRAY) {
        fail_with_msg("getarray expects array argument", node->exp);
    }
    // getarray returns number of read elements.
    semant_map->setSemant(node, make_int_semant(false));
}

void AST_Semant_Visitor::visit(IdExp* node) {
    if (node == nullptr) {
        return;
    }

    if (!current_visiting_class.empty() && !current_visiting_method.empty()) {
        VarDecl* mv = name_maps->get_method_var(current_visiting_class, current_visiting_method, node->id);
        if (mv != nullptr && mv->type != nullptr) {
            semant_map->setSemant(node, semant_from_type(mv->type, true));
            return;
        }

        Formal* mf = name_maps->get_method_formal(current_visiting_class, current_visiting_method, node->id);
        if (mf != nullptr && mf->type != nullptr) {
            semant_map->setSemant(node, semant_from_type(mf->type, true));
            return;
        }
    }

    fail_with_msg("identifier not declared in local/formal scope: " + node->id +
        " (class field must be accessed as obj.field)", node);
}

void AST_Semant_Visitor::visit(OpExp* node) {
    (void)node;
}

void AST_Semant_Visitor::visit(IntExp* node) {
    if (node == nullptr) {
        return;
    }
    semant_map->setSemant(node, make_int_semant(false));
}