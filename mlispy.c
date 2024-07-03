#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <signal.h>

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

#include "include/mpc.h"
#include "include/mathutil.h"

/* If we are compiling on Windows compile these functions */
#ifdef _WIN32
#include <string.h>

static char buffer[2048];

/* Fake readline function */
char* readline(char* prompt) {
	fputs(prompt, stdout);
	fgets(buffer, 2048, stdin);
	char* cpy = malloc(strlen(buffer)+1);
	strcpy(cpy, buffer);
	cpy[strlen(cpy)-1] = '\0';
	return cpy;
}

/* Fake add_history function */
void add_history(char* unused) {}

/* Otherwise include the editline headers */
#else
#include <editline/readline.h>
#endif

#define MAX_STACK (64*1024*1024UL) // 64 MB

static uintptr_t first_stack = (uintptr_t)NULL;

#define error(msg) \
  fprintf(stderr, msg); exit(EXIT_FAILURE);
#define safe_malloc(p, n) \
  if((p = malloc(n)) == NULL) {error("malloc error");}
#define safe_realloc(p, n) \
  {                                                   \
    void *realloc_ptr = realloc(p, n);                      \
    if(realloc_ptr == NULL) {error("realloc error");} \
    p = realloc_ptr;                                  \
  }
#define LASSERT(args, cond, fmt, ...) \
  if (!(cond)) { \
    lval* err = lval_err(fmt, ##__VA_ARGS__); \
    lval_del(args); \
    return err; \
  }
#define LASSERT_TYPE(f, a, i, t) \
  LASSERT(a, a->cell[i]->type == t, \
          "function '%s' expected type %s, got %s", \
          f, ltype_name(t), ltype_name(a->cell[i]->type))
#define LASSERT_NUM(f, a, n) \
    LASSERT(a, a->count == n,\
        "function '%s' passed incorrect number of arguments (got %i expected %i)", \
        f, a->count, n);



/************************/
/* Forward declarations */
/************************/
struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

mpc_parser_t* Number;
mpc_parser_t* Bool;
mpc_parser_t* Symbol;
mpc_parser_t* String;
mpc_parser_t* Comment;
mpc_parser_t* Sexpr;
mpc_parser_t* Qexpr;
mpc_parser_t* Expr;
mpc_parser_t* Lispy;

void lval_print(lval *v);
lval *lval_eval(lenv *e, lval *v);
lval* builtin_op(lenv *e, lval* a, char* op);
lval* builtin(lval* a, char* func);
lval* lval_join(lval* x, lval* y);
lval* lval_copy(lval* v);
lval *builtin_define(lenv *e, lval *a);
lval *builtin_put(lenv *e, lval *a);
lenv* lenv_new(void);
void lenv_del(lenv* e);
lenv* lenv_copy(lenv* e);
lval *lval_call(lenv *e, lval *f, lval *a);
lval *builtin_lambda_lexical(lenv *e, lval *a);
lval *builtin_lambda_dynamic(lenv *e, lval *a);
bool lval_eq(lval *x, lval *y);
lval *builtin_if(lenv *e, lval *a);
void lval_println(lval* v);
char* ltype_name(int t);

/****************/
/* MLisp values */
/****************/
enum {LVAL_NUM, LVAL_ERR, LVAL_SYM, LVAL_SEXPR, 
      LVAL_QEXPR, LVAL_FUN, LVAL_BOOL, LVAL_STR};

enum {LEXICAL, DYNAMIC};

/*************************/
/* Builtin function type */
/*************************/
typedef lval*(*lbuiltin)(lenv*, lval*);

struct lval{
	int type;
  // Basic
	long num;
	char *err;
	char *sym;
  char *str;
  bool bval;
  // Function
  lbuiltin builtin;
  lenv *env;
  lval *formals;
  lval *body;
  int scoping;
  // Expression
	int count;
	lval **cell;
  // q-expr
  lval *qval;
  lval *qnext;
};

struct lenv{
  lenv *par;
  int count;
  char **syms;
  lval **vals;
};

/****************/
/* Constructors */
/****************/
lval *lval_num(long x) {
	lval *v;
	safe_malloc(v, sizeof(lval));
	v->type = LVAL_NUM;
	v->num = x;
	return v;
}
lval *lval_err(char *fmt, ...) {
	lval *v;
	safe_malloc(v, sizeof(lval));
  v->type = LVAL_ERR;

  va_list va;
  va_start(va, fmt);

  safe_malloc(v->err, 512);
  vsnprintf(v->err, 511, fmt, va);

  safe_realloc(v->err, strlen(v->err)+1);

  va_end(va);

	return v;
}
lval *lval_sym(char *s){
	lval *v;
  safe_malloc(v, sizeof(lval));
	v->type = LVAL_SYM;
	safe_malloc(v->sym, strlen(s) + 1);
	strcpy(v->sym, s);
	return v;
}
lval *lval_sexpr(void) {
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}
lval *lval_qexpr(lval *qval){
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_QEXPR;
  v->qval = qval;
  v->qnext = NULL;
  return v;
}
lval *lval_fun(lbuiltin func, char *s) {
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = func;
  safe_malloc(v->sym, strlen(s) + 1);
	strcpy(v->sym, s);
  return v;
}
lval *lval_lambda(lval *formals, lval *body){
  lval *v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = NULL; // user defined functions have null builtin
  v->env = lenv_new();
  v->formals = formals;
  v->body = body;
  return v;
}
lval *lval_bool(bool bval){
  lval *v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_BOOL;
  v->bval = bval;
  return v;
}
lval *lval_str(char *str){
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_STR;
  safe_malloc(v->str, strlen(str) + 1);
  strcpy(v->str, str);
  return v;
}

lenv* lenv_new(void) {
  lenv* e;
  safe_malloc(e, sizeof(lenv));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

/***************/
/* Destructors */
/***************/
void lval_del(lval* v) {
  if(v == NULL) return;
  switch (v->type) {
    case LVAL_NUM: break;
    case LVAL_ERR: free(v->err); break;
    case LVAL_SYM: free(v->sym); break;
    case LVAL_STR: free(v->str); break;
    case LVAL_SEXPR:
      for (int i = 0; i < v->count; i++) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
    break;
    case LVAL_QEXPR:
      if(v->qval != NULL) lval_del(v->qval);
      if(v->qnext != NULL) lval_del(v->qnext);
    break;
    case LVAL_FUN:
      if (!v->builtin) {
        lenv_del(v->env);
        lval_del(v->formals);
        lval_del(v->body);
      }
    break;
  }
  free(v);
}
void lenv_del(lenv* e) {
  for (int i = 0; i < e->count; i++) {
    free(e->syms[i]);
    lval_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

/*************************/
/* Environment functions */
/*************************/
lval *lenv_get(lenv *e, lval *k){
  for(int i=0; i!=e->count; ++i){
    if(strcmp(e->syms[i], k->sym) == 0) return lval_copy(e->vals[i]);
  }
  if(e->par) return lenv_get(e->par, k);
  return lval_err("Unbound symbol '%s'!", k->sym);
}
void lenv_put(lenv *e, lval *k, lval *v){

  for(int i=0; i!=e->count; ++i){
    if(strcmp(e->syms[i], k->sym) == 0){
      lval_del(e->vals[i]);
      e->vals[i] = lval_copy(v);
      return;
    }
  }
  // no match found
  e->count++;
  safe_realloc(e->vals, sizeof(lval*) * e->count);
  safe_realloc(e->syms, sizeof(char*) * e->count);
  // Copy contents of lval and symbol string into new location
  e->vals[e->count-1] = lval_copy(v);
  e->syms[e->count-1] = malloc(strlen(k->sym)+1);
  strcpy(e->syms[e->count-1], k->sym);
}
void lenv_def(lenv* e, lval* k, lval* v) {
  // global define
  while (e->par) { e = e->par; }
  lenv_put(e, k, v);
}
lenv* lenv_copy(lenv* e) {
  lenv* n;
  safe_malloc(n, sizeof(lenv));
  n->par = e->par;
  n->count = e->count;
  n->syms = malloc(sizeof(char*) * n->count);
  n->vals = malloc(sizeof(lval*) * n->count);
  for (int i = 0; i < e->count; i++) {
    n->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(n->syms[i], e->syms[i]);
    n->vals[i] = lval_copy(e->vals[i]);
  }
  return n;
}

/************************/
/* Expression functions */
/************************/
lval* lval_add(lval* v, lval* x) {
  if(v->type == LVAL_SEXPR){
    v->count++;
    safe_realloc(v->cell, sizeof(lval*) * v->count);
    v->cell[v->count-1] = x;
  } else if(v->type == LVAL_QEXPR){
    if(v->qnext == NULL && v->qval == NULL){ // adding to '()
      v->qval = x;
      v->qnext = lval_qexpr(NULL);
    } else {
      lval_add(v->qnext, x); // list
    }
  }
  return v;
}
lval* lval_pop(lval* v, int i) {
  if(v->type == LVAL_SEXPR){
    lval* x = v->cell[i];
    memmove(&v->cell[i], &v->cell[i+1],
      sizeof(lval*) * (v->count-i-1));
    v->count--;
    v->cell = realloc(v->cell, sizeof(lval*) * v->count);
    return x;
  } else if(v->type == LVAL_QEXPR){
    return lval_err("Not yet implemented");
  }
  return NULL;
}
lval* lval_take(lval* v, int i) {
  if(v->type == LVAL_SEXPR){
    lval *x = lval_pop(v, i);
    lval_del(v);
    return x;
  } else if(v->type == LVAL_QEXPR){
    if(v == NULL) return lval_err("Null pointer exception");
    if(i == 0) return v->qval;
    return lval_take(v->qnext, i-1);
  }
  return NULL;
}
lval* lval_copy(lval* v) {
  if(v == NULL) return NULL;

  lval* x = malloc(sizeof(lval));
  x->type = v->type;
  switch (v->type) {
    case LVAL_FUN: 
      if(v->builtin){
        x->builtin = v->builtin;
        safe_malloc(x->sym, strlen(v->sym) + 1);
        strcpy(x->sym, v->sym); break;
      } else {
        x->builtin = NULL;
        x->env = lenv_copy(v->env);
        x->formals = lval_copy(v->formals);
        x->body = lval_copy(v->body);
        x->scoping = v->scoping;
        break;
      }
    case LVAL_NUM: x->num = v->num; break;
    case LVAL_BOOL: x->bval = v->bval; break;
    case LVAL_ERR:
      x->err = malloc(strlen(v->err) + 1);
      strcpy(x->err, v->err); break;
    case LVAL_SYM:
      x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym); break;
    case LVAL_STR:
      x->str = malloc(strlen(v->str) + 1);
      strcpy(x->str, v->str); break;
    case LVAL_SEXPR:
      x->count = v->count;
      x->cell = malloc(sizeof(lval*) * x->count);
      for (int i = 0; i < x->count; i++) {
        x->cell[i] = lval_copy(v->cell[i]);
      }
    break;
    case LVAL_QEXPR:
      x->qval = lval_copy(v->qval);
      x->qnext = lval_copy(v->qnext);
    break;
  }

  return x;
}

/********************/
/* Output functions */
/********************/
void lval_print_str(lval* v) {
  char* escaped = malloc(strlen(v->str)+1);
  strcpy(escaped, v->str);
  escaped = mpcf_escape(escaped);
  printf("\"%s\"", escaped);
  free(escaped);
}
void lval_expr_print(lval* v, const char *open, const char *close) {
  if(v->count == 0) return;
  printf(open);
  for (int i = 0; i < v->count; i++) {
    lval_print(v->cell[i]);
    if (i != (v->count-1)) putchar(' ');
  }
  printf(close);
}
void lval_qexpr_print(lval* v, const char *open, const char *close) {
  printf(open);
  for (lval *cur = v; cur != NULL; cur = cur->qnext) {
    if(cur->qval != NULL) lval_print(cur->qval);
    if(cur->qnext != NULL && cur->qnext->type != LVAL_QEXPR){ // cons pair
      printf(" . ");
      lval_print(cur->qnext);
      break;
    }
    if(cur->qnext != NULL && cur->qnext->qnext != NULL) putchar(' ');
  }
  printf(close);
}
void lval_print(lval *v){
	switch(v->type){
		case LVAL_NUM: printf("%li", v->num); break;
    case LVAL_BOOL: printf("%s", v->bval ? "true" : "false"); break;
		case LVAL_ERR:   printf("Error: %s", v->err); break;
		case LVAL_SYM:   printf("%s", v->sym); break;
    case LVAL_SEXPR: lval_expr_print(v, "(", ")"); break;	
    case LVAL_QEXPR: lval_qexpr_print(v, "(", ")"); break;	
    case LVAL_STR:   lval_print_str(v); break;
    case LVAL_FUN: 
      if(v->builtin) printf("<function:%s>", v->sym); 
      else {
        printf("<function:(%s ", v->scoping == LEXICAL ? "\\" : "\\d"); 
        lval_print(v->formals); putchar(' '); lval_print(v->body); 
        putchar(')'); putchar('>');
      }
    break;
	}
}
void lval_println(lval* v) { 
  if(v->type == LVAL_SEXPR && v->count == 0) return;
  if(v->type == LVAL_QEXPR) putchar('\'');
  lval_print(v); 
  putchar('\n'); 
}

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "Function";
    case LVAL_NUM: return "Number";
    case LVAL_ERR: return "Error";
    case LVAL_SYM: return "Symbol";
    case LVAL_SEXPR: return "S-Expression";
    case LVAL_QEXPR: return "Q-Expression";
    case LVAL_BOOL: return "Boolean";
    case LVAL_STR: return "String";
    default: return "Unknown";
  }
}

/*******************/
/* Input functions */
/*******************/
lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  long x = strtol(t->contents, NULL, 10);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number");
}
lval *lval_read_bool(mpc_ast_t *t){
  if(strcmp(t->contents, "true") == 0) return lval_bool(true);
  else return lval_bool(false);
}
lval* lval_read_str(mpc_ast_t* t) {
  t->contents[strlen(t->contents)-1] = '\0'; // remove last quote
  char* unescaped = malloc(strlen(t->contents+1)+1);
  strcpy(unescaped, t->contents+1);
  unescaped = mpcf_unescape(unescaped);
  lval* str = lval_str(unescaped);
  free(unescaped);
  return str;
}
lval* lval_read(mpc_ast_t* t) {
  /* If Symbol or Number return conversion to that type */
  if (strstr(t->tag, "number")) { return lval_read_num(t); }
  if (strstr(t->tag, "bool"))   { return lval_read_bool(t); }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }
  if (strstr(t->tag, "string")) { return lval_read_str(t); }

  /* If root (>) or sexpr then create empty list */
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { return lval_read(t->children[1]); }
  if (strstr(t->tag, "sexpr"))  { x = lval_sexpr(); }
  if (strstr(t->tag, "qexpr"))  { x = lval_qexpr(NULL); }

  /* Fill this list with any valid expression contained within */
  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) continue;
    if (strcmp(t->children[i]->contents, ")") == 0) continue; 
    if (strcmp(t->children[i]->contents, "'") == 0) continue;
    if (strcmp(t->children[i]->tag,  "regex") == 0) continue; 
    if (strstr(t->children[i]->tag, "comment"))     continue; 
    x = lval_add(x, lval_read(t->children[i]));
  }

  return x;
}
lval **lval_read_all(mpc_ast_t *t){
  if(strcmp(t->tag, ">") != 0){ // assert root
    puts("Parser error");
    return NULL;
  }

  lval **lvals;
  safe_malloc(lvals, sizeof(lval*) * (t->children_num - 2));
  for(int i=1; i < t->children_num-1; ++i){
    lvals[i-1] = lval_read(t->children[i]);
  }
  return lvals;
}

/************************/
/* Evaluation functions */
/************************/
lval *lval_eval_sexpr(lenv *e, lval *v){

  if(v->count == 0) return v; // empty expression

	// evaluate children and check for errors
	for(int i=0; i<v->count; ++i){
    // don't evaluate first argument of define or put
    if(i == 1 && (v->cell[0]->builtin == builtin_define
               || v->cell[0]->builtin == builtin_put)) {
      continue;
    }
    // dont evaluate arguments of lambda
    if(i == 1 && (v->cell[0]->builtin == builtin_lambda_lexical
               || v->cell[0]->builtin == builtin_lambda_dynamic)) {
      break;
    }
    // dont evaluate branches of if
    if(i == 2 && (v->cell[0]->builtin == builtin_if)){
      break;
    }

    v->cell[i] = lval_eval(e, v->cell[i]);
    if(v->cell[i]->type == LVAL_ERR) return lval_take(v, i);
  }

	lval *f = lval_pop(v, 0);
	if(f->type != LVAL_FUN){
		lval *err = lval_err("S-Expression does not begin with correct type" 
                    " (expected %s, got %s)", 
                    ltype_name(LVAL_FUN), ltype_name(f->type));
    lval_del(f); lval_del(v);
    return err;
	}

	lval *res = lval_call(e, f, v);
	lval_del(f);

	return res;
}
lval *lval_eval(lenv *e, lval *v){

  // Stack checking
  int stack;
  uintptr_t s_add = (uintptr_t)(&stack);
  if(first_stack == (uintptr_t)NULL) first_stack = s_add;
  if((first_stack > s_add && first_stack - s_add > MAX_STACK)
      || (s_add > first_stack && s_add - first_stack > MAX_STACK)){
    return lval_err("Stack overflow");
  }
  
  // evaluation
  if(v->type == LVAL_SYM){
    lval *x = lenv_get(e, v);
    lval_del(v);
    return x;
  }
	if(v->type == LVAL_SEXPR) return lval_eval_sexpr(e, v);
	return v;
}

/*********************/
/* Builtin functions */
/*********************/
// arithmetic
lval* builtin_op(lenv *e, lval* a, char* op) {
  /* Check at least one argument passed in */
  LASSERT(a, a->count != 0, "function '%s' passed zero arguments", op);

  /* Ensure all arguments are numbers */
  for (int i = 0; i < a->count; i++) {
    LASSERT_TYPE(op, a, i, LVAL_NUM);
  }

  lval* x = lval_pop(a, 0);
  /* If no arguments and sub then perform unary negation */
  if ((strcmp(op, "-") == 0) && a->count == 0) x->num = -x->num;

  // Evaluate all operands
  while (a->count > 0) {
    lval* y = lval_pop(a, 0);

    if (strcmp(op, "+") == 0) { x->num += y->num; }
    if (strcmp(op, "-") == 0) { x->num -= y->num; }
    if (strcmp(op, "*") == 0) { x->num *= y->num; }
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        lval_del(x); lval_del(y);
        x = lval_err("Division By Zero!"); break;
      }
      x->num /= y->num;
    }

    lval_del(y);
  }

  lval_del(a); return x;
}
lval* builtin_add(lenv* e, lval* a) {
  return builtin_op(e, a, "+");
}
lval* builtin_sub(lenv* e, lval* a) {
  return builtin_op(e, a, "-");
}
lval* builtin_mul(lenv* e, lval* a) {
  return builtin_op(e, a, "*");
}
lval* builtin_div(lenv* e, lval* a) {
  return builtin_op(e, a, "/");
}
// List functions
lval *builtin_car(lenv* e, lval *a){
  LASSERT_NUM("car", a, 1);
  LASSERT_TYPE("car", a, 0, LVAL_QEXPR);
  LASSERT(a, a->cell[0]->qval != NULL,
    "function 'car' passed '()!");

  lval* v = lval_take(a, 0); // take argument to car
  lval *ret = lval_take(v, 0);

  return ret;
}
lval* builtin_cdr(lenv* e, lval *a) {
  LASSERT_NUM("cdr", a, 1);
  LASSERT_TYPE("cdr", a, 0, LVAL_QEXPR)
  LASSERT(a, a->cell[0]->qval != NULL,
    "function 'cdr' passed '()!");

  lval* v = lval_take(a, 0); // take argyment to cdr
  lval *ret = lval_copy(v->qnext);
  lval_del(v);
  return ret;    
}
lval *builtin_list(lenv* e, lval *a){
  lval *x = lval_qexpr(NULL);
  while(a->count != 0) lval_add(x, lval_pop(a, 0));
  lval_del(a);
  return x;
}
lval *builtin_cons(lenv* e, lval *a){
  LASSERT_NUM("cons", a, 2);
  lval *c = lval_qexpr(lval_pop(a, 0));
  c->qnext = lval_pop(a, 0);
  lval_del(a);
  return c;
}
// defining variables
lval *builtin_var(lenv *e, lval *a, char *func){
  LASSERT_NUM(func, a, 2);
  LASSERT_TYPE(func, a, 0, LVAL_SYM);

  if(strcmp(func, "define") == 0) lenv_def(e, a->cell[0], a->cell[1]);
  if(strcmp(func, "=") == 0) lenv_put(e, a->cell[0], a->cell[1]);
  
  lval_del(a);
  return lval_sexpr();
}
lval *builtin_define(lenv *e, lval *a){
  return builtin_var(e, a, "define");
}
lval *builtin_put(lenv *e, lval *a){
  return builtin_var(e, a, "=");
}
// function functions
lval *builtin_lambda(lenv *e, lval *a, char *scope){
  LASSERT_NUM("\\", a, 2);
  LASSERT_TYPE("\\", a, 0, LVAL_SEXPR);
  // LASSERT_TYPE("\\", a, 1, LVAL_QEXPR);
  /* Check first Q-Expression contains only Symbols */
  for (int i = 0; i < a->cell[0]->count; i++) {
    LASSERT(a, (a->cell[0]->cell[i]->type == LVAL_SYM),
      "Cannot define non-symbol. Got %s, Expected %s.",
      ltype_name(a->cell[0]->cell[i]->type),ltype_name(LVAL_SYM));
  }
  lval* formals = lval_pop(a, 0);
  lval* body = lval_pop(a, 0);
  lval_del(a);

  lval *lambda = lval_lambda(formals, body);
  if(strcmp(scope, "lexical") == 0) {
    lambda->env->par = e;
    lambda->scoping = LEXICAL;
  }
  else {
    lambda->scoping = DYNAMIC;
  }
  return lambda;
}
lval *builtin_lambda_lexical(lenv *e, lval *a){
  return builtin_lambda(e, a, "lexical");
}
lval *builtin_lambda_dynamic(lenv *e, lval *a){
  return builtin_lambda(e, a, "dynamic");
}
// logical
lval *builtin_nand(lenv *e, lval *a){
  LASSERT_NUM("nand", a, 2);
  LASSERT_TYPE("nand", a, 0, LVAL_BOOL);
  LASSERT_TYPE("nand", a, 1, LVAL_BOOL);

  bool res = !(a->cell[0]->bval && a->cell[1]->bval);
  lval_del(a);
  return lval_bool(res);
}
lval *builtin_ord(lenv *e, lval *a, char *op){
  LASSERT_NUM(op, a, 2);
  LASSERT_TYPE(op, a, 0, LVAL_NUM);
  LASSERT_TYPE(op, a, 1, LVAL_NUM);

  int res;
  if (strcmp(op, ">")  == 0) res = (a->cell[0]->num >  a->cell[1]->num);
  if (strcmp(op, "<")  == 0) res = (a->cell[0]->num <  a->cell[1]->num);
  if (strcmp(op, ">=") == 0) res = (a->cell[0]->num >= a->cell[1]->num);
  if (strcmp(op, "<=") == 0) res = (a->cell[0]->num <= a->cell[1]->num);
  
  lval_del(a);
  return lval_bool(res);
}
lval* builtin_gt(lenv* e, lval* a) {
  return builtin_ord(e, a, ">");
}
lval* builtin_lt(lenv* e, lval* a) {
  return builtin_ord(e, a, "<");
}
lval* builtin_ge(lenv* e, lval* a) {
  return builtin_ord(e, a, ">=");
}
lval* builtin_le(lenv* e, lval* a) {
  return builtin_ord(e, a, "<=");
}
lval *builtin_equal(lenv *e, lval *a){
  LASSERT_NUM("equal?", a, 2);
  lval *ret = lval_bool(lval_eq(a->cell[0], a->cell[1]));
  lval_del(a);
  return ret;
}
lval *builtin_if(lenv *e, lval *a){
  LASSERT_NUM("if", a, 3);
  LASSERT_TYPE("if", a, 0, LVAL_BOOL);

  lval *ret;
  if(a->cell[0]->bval) ret = lval_eval(e, lval_pop(a, 1));
  else ret = lval_eval(e, lval_pop(a, 2));

  lval_del(a);
  return ret;
}
// loading from programs
lval *builtin_load(lenv* e, lval* a, bool verbose) {
  LASSERT_NUM("load", a, 1);
  LASSERT_TYPE("load", a, 0, LVAL_STR);

  /* Parse File given by string name */
  mpc_result_t r;
  if (mpc_parse_contents(a->cell[0]->str, Lispy, &r)) {

    lval **r_out = lval_read_all(r.output);
    int num_exprs = ((mpc_ast_t*)r.output)->children_num-2;

    if(r_out == NULL || num_exprs <= 0) return lval_sexpr();

    for(int i=0; i<num_exprs; ++i){
      if(r_out[i] == NULL) continue;

      lval* x = lval_eval(e, r_out[i]);

      if (x->type == LVAL_ERR || verbose) lval_println(x);
      lval_del(x);
    }
    free(r_out);
    mpc_ast_delete(r.output);
    return lval_sexpr();
  } else {
    char* err_msg = mpc_err_string(r.error);
    mpc_err_delete(r.error);

    lval* err = lval_err("Could not load Library %s", err_msg);
    
    free(err_msg);
    lval_del(a);
    return err;
  }
}
lval *builtin_run_file(lenv *e, lval *a){
  return builtin_load(e, a, true);
}
lval *builtin_load_lib(lenv *e, lval *a){
  return builtin_load(e, a, false);
}
// output functions
lval* builtin_print(lenv* e, lval* a) {
  /* Print each argument followed by a space */
  for (int i = 0; i < a->count; i++) {
    lval_print(a->cell[i]); putchar(' ');
  }
  /* Print a newline and delete arguments */
  putchar('\n');
  lval_del(a);
  return lval_sexpr();
}
lval* builtin_error(lenv* e, lval* a) {
  LASSERT_NUM("error", a, 1);
  LASSERT_TYPE("error", a, 0, LVAL_STR);
  /* Construct Error from first argument */
  lval* err = lval_err(a->cell[0]->str);
  /* Delete arguments and return */
  lval_del(a);
  return err;
}
// other functions
lval *builtin_eval(lenv* e, lval* a) {
  LASSERT_NUM("eval", a, 1);
  LASSERT_TYPE("eval", a, 0, LVAL_QEXPR);

  lval* x = lval_take(a, 0);
  // check if it is a value or a sexpr
  if(x->qnext->qval == NULL) return lval_eval(e, lval_take(x, 0));
  x->type = LVAL_SEXPR;
  return lval_eval(e, x);
}
lval *builtin_typeof(lenv *e, lval *a){
  LASSERT_NUM("typeof", a, 1);
  lval *ret = lval_str(ltype_name(lval_pop(a, 0)->type));
  lval_del(a);
  return ret; 
}

/*******************/
/* L-Val Functions */
/*******************/
lval* lval_join(lval* x, lval* y) {
  while (y->count) {
    x = lval_add(x, lval_pop(y, 0));
  }
  lval_del(y);
  return x;
}
lval *lval_call(lenv *e, lval *f, lval *a){
  // Stack checking
  int stack;
  uintptr_t s_add = (uintptr_t)(&stack);
  if(first_stack == (uintptr_t)NULL) first_stack = s_add;
  if((first_stack > s_add && first_stack - s_add > MAX_STACK)
      || (s_add > first_stack && s_add - first_stack > MAX_STACK)){
    return lval_err("Stack overflow");
  }


  if(f->builtin) return f->builtin(e, a); // builtin function

  int given = a->count;
  int total = f->formals->count;

  while(a->count){
    if (f->formals->count == 0) { // too many arguments passed
      lval_del(a); return lval_err(
        "Function passed too many arguments. "
        "Got %i, Expected %i.", given, total);
    }
    lval* sym = lval_pop(f->formals, 0);

    if(strcmp(sym->sym, "&") == 0){
      if(f->formals->count != 1){
        lval_del(a);
        return lval_err("Function format invalid. "
          "Symbol '&' not followed by single symbol.");
      }
      lval* nsym = lval_pop(f->formals, 0);
      lenv_put(f->env, nsym, builtin_list(e, a));
      lval_del(sym); lval_del(nsym);
      break;
    }

    lval* val = lval_pop(a, 0);
    lenv_put(f->env, sym, val);
    lval_del(sym); lval_del(val);
  }

  lval_del(a); // done with argument

  /* If '&' remains in formal list bind to empty list */
  if (f->formals->count > 0 &&
    strcmp(f->formals->cell[0]->sym, "&") == 0) {
    /* Check to ensure that & is not passed invalidly. */
    if (f->formals->count != 2) {
      return lval_err("Function format invalid. "
        "Symbol '&' not followed by single symbol.");
    }
    /* Pop and delete '&' symbol */
    lval_del(lval_pop(f->formals, 0));
    /* Pop next symbol and create empty list */
    lval* sym = lval_pop(f->formals, 0);
    lval* val = lval_qexpr(NULL);
    /* Bind to environment and delete */
    lenv_put(f->env, sym, val);
    lval_del(sym); lval_del(val);
  }

  if (f->formals->count == 0) {
    if(f->scoping == DYNAMIC){
      f->env->par = e; // dynamic scope...
    }
    return builtin_eval(
      f->env, lval_add(lval_sexpr(), lval_add(lval_qexpr(NULL), lval_copy(f->body))));
  } else return lval_copy(f);
}
bool lval_eq(lval *x, lval *y){

  if(x == NULL && y == NULL) return true;
  else if(x == NULL || y == NULL) return false;

  if(x->type != y->type) return false;

  switch (x->type){
    case LVAL_NUM: return x->num == y->num;
    case LVAL_ERR: return strcmp(x->err, y->err) == 0;
    case LVAL_SYM: return strcmp(x->sym, y->sym) == 0;
    case LVAL_STR: return (strcmp(x->str, y->str) == 0);
    case LVAL_SEXPR:
      if(x->count != y->count) return false;
      // check each cell
      for(int i=0; i<x->count; ++i) if(!lval_eq(x->cell[i], y->cell[i])) return false;
      break;
    case LVAL_QEXPR:
      if(!lval_eq(x->qval, y->qval)) return false;
      return lval_eq(x->qnext, y->qnext);
    case LVAL_FUN:
      if(x->builtin != NULL) return x->builtin == y->builtin;
      bool scoping = x->scoping == y->scoping;
      bool formals = lval_eq(x->formals, y->formals);
      bool body = lval_eq(x->body, y->body);
      return scoping && formals && body;
  }

  return true;
}

/***************/
/* L-Env Setup */
/***************/
void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name);
  lval* v = lval_fun(func, name);
  lenv_put(e, k, v);
  lval_del(k); lval_del(v);
}
void lenv_add_builtins(lenv* e) {
  /* Functions */
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "car",  builtin_car);
  lenv_add_builtin(e, "cdr",  builtin_cdr);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "cons", builtin_cons);
  lenv_add_builtin(e, "define", builtin_define);
  lenv_add_builtin(e, "=", builtin_put);
  lenv_add_builtin(e, "\\", builtin_lambda_lexical);
  lenv_add_builtin(e, "\\d", builtin_lambda_dynamic);
  lenv_add_builtin(e, "equal?", builtin_equal);
  lenv_add_builtin(e, "if", builtin_if);
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);
  lenv_add_builtin(e, "<", builtin_lt);
  lenv_add_builtin(e, ">", builtin_gt);
  lenv_add_builtin(e, "<=", builtin_le);
  lenv_add_builtin(e, ">=", builtin_ge);
  lenv_add_builtin(e, "typeof", builtin_typeof);
  lenv_add_builtin(e, "load", builtin_load_lib);
  lenv_add_builtin(e, "print", builtin_print);
  lenv_add_builtin(e, "error", builtin_error);
  lenv_add_builtin(e, "nand", builtin_nand);

}


int main(int argc, char **argv){
  // Resource limits
  struct rlimit limit;
  limit.rlim_cur = MAX_STACK * 2;
  limit.rlim_max = MAX_STACK * 2;
  setrlimit(RLIMIT_STACK, &limit);

  // Parser
	Number  = mpc_new("number");
  Bool    = mpc_new("bool");
	Symbol  = mpc_new("symbol");
  String  = mpc_new("string");
  Comment = mpc_new("comment");
	Sexpr   = mpc_new("sexpr");
	Qexpr   = mpc_new("qexpr");
	Expr    = mpc_new("expr");
	Lispy   = mpc_new("lispy");

	mpca_lang(MPCA_LANG_DEFAULT,
	"                                                         \
		number  : /-?[0-9]+/ ;                                  \
    bool    : \"true\" | \"false\" ;                        \
		symbol  : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&^#$%@~?\\.]+/    \
            | \"list\" | \"car\" | \"cdr\"                  \
            | \"join\" | \"eval\" | \"cons\"                \
            | \"define\"   ;                                \
		string  : /\"(\\\\.|[^\"])*\"/ ;                        \
    comment : /;[^\\r\\n]*/ ;                               \
    sexpr   : '(' <expr>* ')' ;                             \
		qexpr   : '\'' '(' <expr>* ')' ;                        \
		expr    : <bool> | <number> | <symbol>                  \
            | <qexpr> | <sexpr> | <string>                  \
            | <comment> ;                                   \
		lispy   : /^/ <expr>* /$/ ;                             \
	",
	Number, Bool, Symbol, String, Comment, Sexpr, Qexpr, Expr, Lispy);
  // create lenv

  lenv* e = lenv_new();
  lenv_add_builtins(e);
  // load stdlib
  lval_del(builtin_load_lib(e, lval_add(lval_sexpr(), lval_str("lib/stdlib.mlspy"))));

  /************************/
  /* List of files to run */
  /************************/
  if (argc >= 2) {
    for (int i = 1; i < argc; i++) {
      lval* args = lval_add(lval_sexpr(), lval_str(argv[i]));
      lval* x = builtin_run_file(e, args);
      if (x->type == LVAL_ERR) { lval_println(x); }
      lval_del(x);
    }
    return EXIT_SUCCESS;
  }

  /*********************************/
  /* Beginning of interpreter loop */
  /*********************************/
	puts("MLispy Version 0.0.0.0.1");
	puts("Press Ctrl+C to exit\n");

  lenv_def(e, lval_sym("_"), lval_qexpr(NULL));

	while(1){

		char *input = readline("mlispy> ");
		add_history(input);

		mpc_result_t r;
		if(mpc_parse("<stdin>", input, Lispy, &r)){
      lval **r_out = lval_read_all(r.output);
      int num_exprs = ((mpc_ast_t*)r.output)->children_num-2;

      if(r_out == NULL || num_exprs <= 0) continue;

      for(int i=0; i<num_exprs; ++i){
        if(r_out[i] == NULL) continue;

        lval* x = lval_eval(e, r_out[i]);
        lval_println(x);
        lenv_def(e, lval_sym("_"), x);
        // lval_del(x);
      }
      free(r_out);
      mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	mpc_cleanup(9, Number, Bool, Symbol, Comment, String, Sexpr, Qexpr, Expr, Lispy);
}
