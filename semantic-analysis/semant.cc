#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;
ObjectEnvironment *func_table = new ObjectEnvironment();
ObjectEnvironment *global_var_table = new ObjectEnvironment();
ObjectEnvironment *formal_par_table = new ObjectEnvironment();
ObjectEnvironment *local_var_table = new ObjectEnvironment();

SymbolTable<Symbol, Variables> *func_para_table = new SymbolTable<Symbol, Variables>();

bool has_return = false;
Symbol return_type;

int stmt_level = 0, call_level = 0, loop_level = 0;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol 
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");  
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic 
    analysis in a recursive way. 
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    func_table->enterscope();
    func_para_table->enterscope();
    func_table->addid(print, new Symbol(Void));
    for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
        Decl decl = decls->nth(i);
        if (!decl->isCallDecl()) continue;
        if (decl->getName() == print)
            semant_error(decl) << "Function printf cannot be defined.\n";
        else if (func_table->lookup(decl->getName()) == NULL) {
            func_table->addid(decl->getName(), new Symbol(decl->getType()));
            func_para_table->addid(decl->getName(), new Variables(decl->getVariables()));
        }
        else
            semant_error(decl) << "Function " << decl->getName() << " has already been defined.\n";
    }
}

static void install_globalVars(Decls decls) {
    global_var_table->enterscope();
    for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
        Decl decl = decls->nth(i);
        if (decl->isCallDecl()) continue;
        else if (decl->getType() == Void)
            semant_error(decl) << "Variable " << decl->getName() << " cannot have Void type.\n";
        else if (global_var_table->lookup(decl->getName()) == NULL) {
            global_var_table->addid(decl->getName(), new Symbol(decl->getType()));
        }
        else
            semant_error(decl) << "Variable " << decl->getName() << " has already been defined.\n";
    }
}

static void check_calls(Decls decls) {
    for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
        Decl decl = decls->nth(i);
        if (!decl->isCallDecl()) continue;
        decl->check();
    }
}

static void check_main() {
    if (!func_table->lookup(Main))
        semant_error() << "Main function has not been defined\n";
}

void VariableDecl_class::check() {
    if (getType() == Void)
        semant_error(this) << "Variable " << getName() << " cannot have Void type.\n";
}

void CallDecl_class::check() {
    call_level++;
    if (getName() == Main) {
        if (getType() != Void)
            semant_error(this) << "Main function should have return Void type.\n";
        if (getVariables()->len() > 0)
            semant_error(this) << "Main function should not have parameters.\n";
    }
    if (getType() != Int && getType() != Void && getType() != String && getType() != Float && getType() != Bool)
        semant_error(this) << "Return type: " << getType() << " is incorrect.\n";
    if (getVariables()->len() > 6)
        semant_error(this) << "Function " << getName() << " should not have more than six parameters.\n";
    formal_par_table->enterscope();
    Variables vars = getVariables();
    for (int i = vars->first(); vars->more(i); i = vars->next(i)) {
        Variable var = vars->nth(i);
        if (var->getType() == Void)
            semant_error(var) << "Function " << getName() << 
                "'s parameter " << var->getName() << " cannot have Void type.\n";
        else if (formal_par_table->probe(var->getName()) == NULL)
            formal_par_table->addid(var->getName(), new Symbol(var->getType()));
        else
            semant_error(var) << "Function " << getName() << 
                "'s parameter " << var->getName() << " has already been declared.\n";
    }

    has_return = false;
    return_type = getType();
    getBody()->check(Int);
    if (!has_return)
        semant_error(this) << "Function "<< getName() << " must have an overall return statement.\n";

    call_level--;
    formal_par_table->exitscope();
}

void StmtBlock_class::check(Symbol type) {
    stmt_level++;
    local_var_table->enterscope();
    VariableDecls vars = getVariableDecls();
    for (int i = vars->first(); vars->more(i); i = vars->next(i)) {
        VariableDecl var = vars->nth(i);
        var->check();
        if (local_var_table->probe(var->getName()) == NULL)
            local_var_table->addid(var->getName(), new Symbol(var->getType()));
        else
            semant_error(var) << "Variable " << var->getName() << " has already been defined.\n";
    }

    Stmts sts = getStmts();
    for (int i = sts->first(); sts->more(i); i = sts->next(i)) {
        sts->nth(i)->check(Int);
    }

    stmt_level--;
    local_var_table->exitscope();
}

void IfStmt_class::check(Symbol type) {
    getCondition()->check(Int);
    if (getCondition()->getType() != Bool) {
        semant_error(this) << "Condition type must be Bool, not " << condition->getType() << ".\n";
    }
    getThen()->check(Int);
    getElse()->check(Int);
}

void WhileStmt_class::check(Symbol type) {
    loop_level++;
    getCondition()->check(Int);
    if (getCondition()->getType() != Bool) {
        semant_error(this) << "Condition type must be Bool, not " << condition->getType() << ".\n";
    }
    getBody()->check(Int);
    loop_level--;
}

void ForStmt_class::check(Symbol type) {
    loop_level++;
    getInit()->check(Int);
    getCondition()->check(Int);
    if (getCondition()->is_empty_Expr() == false)
        if (getCondition()->getType() != Bool)
            semant_error(this) << "Condition type must be Bool, not " << condition->getType() << ".\n";
    getLoop()->check(Int);
    getBody()->check(Int);
    loop_level--;
}

void ReturnStmt_class::check(Symbol type) {
    if (stmt_level == call_level) has_return = true;
    getValue()->check(Int);
    if (return_type != getValue()->getType()) {
        semant_error(this) << "Returns " << getValue()->getType() << " , but need " << return_type << "\n";
    }
}

void ContinueStmt_class::check(Symbol type) {
    if (loop_level == 0) {
        semant_error(this) << "continue must be used in a loop sentence.\n";
    }
}

void BreakStmt_class::check(Symbol type) {
    if (loop_level == 0) {
        semant_error(this) << "break must be used in a loop sentence.\n";
    }
}

Symbol Call_class::checkType(){
    Actuals acts = getActuals();
    if (getName() == print) {
        if (acts->len() < 1) {
            semant_error(this) << "printf function must have at least one parameter.\n";
        } else {
            int i = acts->first();
            Actual one = acts->nth(i);
            one->check(Int);
            if (one->getType() != String) {
                semant_error(one) << "printf function's first parameter must be String type.\n";
            } else {
                for (i = acts->next(i); acts->more(i); i = acts->next(i))
                    acts->nth(i)->check(Int);
            }
        }
        setType(Void);
        return getType();
    }

    if (func_table->lookup(getName()) == NULL) {
        semant_error(this) << "Function "<< getName() << " has not been defined.\n";
        setType(Void);
        return getType();
    }

    Variables vs = *func_para_table->lookup(getName());
    if (acts->len() != vs->len()) {
        semant_error(this) << "Function " << getName() << " is used with wrong number of parameters.\n";
    } else {
        for (int i = acts->first(); acts->more(i); i = acts->next(i)) {
            acts->nth(i)->check(Int);
            if (acts->nth(i)->getType() != vs->nth(i)->getType()) {
                semant_error(this) << "Function " << getName() << ", the " << i + 1 
                    << " parameter should be " << vs->nth(i)->getType() 
                    << " but provided a " << acts->nth(i)->getType() << ".\n";
                break;
            }
        }
    }
    Symbol t = *func_table->lookup(getName());
    setType(t);
    return getType();
}

Symbol Actual_class::checkType(){
    expr->check(Int);
    setType(expr->getType());
    return getType();
}

Symbol Assign_class::checkType(){
    value->check(Int);
    if (global_var_table->lookup(lvalue) == NULL && formal_par_table->probe(lvalue) == NULL 
        && local_var_table->lookup(lvalue) == NULL) {
        semant_error(this) << "Left value " << lvalue << " has not been defined.\n";
        setType(Void);
        return getType();
    }

    Symbol s;
    if (local_var_table->lookup(lvalue) != NULL)
        s = *local_var_table->lookup(lvalue);

    if (formal_par_table->probe(lvalue) != NULL)
        s = *formal_par_table->probe(lvalue);

    if (global_var_table->lookup(lvalue) != NULL) 
        s = *global_var_table->lookup(lvalue);
    
    if (s != value->getType()) {
        semant_error(this) << "Right value's type is " << value->getType() << " but needs " << s << ".\n";
    }
    setType(s);
    return getType();
}

Symbol Add_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int)) {
        setType(Float);
        return getType();
    }
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot add a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Minus_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int)) {
        setType(Float);
        return getType();
    }
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot minus a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Multi_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int)) {
        setType(Float);
        return getType();
    }
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot multiply a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Divide_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) || (t1 == Float && t2 == Int)) {
        setType(Float);
        return getType();
    }
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot divide a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Mod_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot mod a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Neg_class::checkType(){
    e1->check(Int);
    Symbol t1 = e1->getType();
    
    if (t1 == Int || t1 == Float) {
        setType(t1);
        return getType();
    }
    
    semant_error(this) << t1 << " has not negative\n";
    setType(Void);
    return getType();
}

Symbol Lt_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Le_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Equ_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int) || (t1 == Bool && t2 == Bool)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Neq_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int) || (t1 == Bool && t2 == Bool)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Ge_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Gt_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Float && t2 == Float) || (t1 == Int && t2 == Float) ||
        (t1 == Float && t2 == Int) || (t1 == Int && t2 == Int)) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot compare a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol And_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if (t1 == Bool && t2 == Bool) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot AND a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Or_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if (t1 == Bool && t2 == Bool) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot OR between a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Xor_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if ((t1 == Bool && t2 == Bool) || (t1 == Int && t2 == Int)) {
        setType(t1);
        return getType();
    }

    semant_error(this) << "cannot XOR between a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Not_class::checkType(){
    e1->check(Int);
    Symbol t1 = e1->getType();
    
    if (t1 == Bool) {
        setType(Bool);
        return getType();
    }

    semant_error(this) << "cannot NOT a " << t1 << '\n';
    setType(Void);
    return getType();
}

Symbol Bitand_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot bitand between a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Bitor_class::checkType(){
    e1->check(Int);
    e2->check(Int);
    Symbol t1 = e1->getType(), t2 = e2->getType();
    
    if (t1 == Int && t2 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot bitor between a " << t1 << " and a " << t2 << '\n';
    setType(Void);
    return getType();
}

Symbol Bitnot_class::checkType(){
    e1->check(Int);
    Symbol t1 = e1->getType();
    
    if (t1 == Int) {
        setType(Int);
        return getType();
    }

    semant_error(this) << "cannot bitnot a " << t1 << '\n';
    setType(Void);
    return getType();
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if (global_var_table->lookup(var) == NULL && formal_par_table->probe(var) == NULL 
        && local_var_table->lookup(var) == NULL) {
        semant_error(this) << "object " << var << " has not been defined.\n";
        setType(Void);
        return getType();
    }

    Symbol obj;
    if (local_var_table->lookup(var) != NULL) 
        obj = *local_var_table->lookup(var);
    else if (formal_par_table->probe(var) != NULL) 
        obj = *formal_par_table->probe(var);
    else if (global_var_table->lookup(var) != NULL) 
        obj = *global_var_table->lookup(var);
    
    setType(obj);
    return getType();
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



