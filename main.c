#include <stdio.h>
#include <stdlib.h>

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


/* Forward declarations */
struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

void print_lval(lval *v);
lval *lval_eval(lenv *e, lval *v);
lval* builtin_op(lenv *e, lval* a, char* op);
lval* builtin(lval* a, char* func);
lval* lval_join(lval* x, lval* y);
lval* lval_copy(lval* v);
lval *builtin_define(lenv *e, lval *a);

/* MLisp values */
enum {LVAL_NUM, LVAL_ERR, LVAL_SYM, LVAL_SEXPR, 
      LVAL_QEXPR, LVAL_FUN};

/* Builtin function type */
typedef lval*(*lbuiltin)(lenv*, lval*);

struct lval{
	int type;

	long num;
	char *err;
	char *sym;
  lbuiltin fun;

	int count;
	lval **cell;
};

struct lenv{
  int count;
  char **syms;
  lval **vals;
};

/* Constructors */
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
lval *lval_qexpr(void){
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}
lval* lval_fun(lbuiltin func, char *s) {
  lval* v;
  safe_malloc(v, sizeof(lval));
  v->type = LVAL_FUN;
  v->fun = func;
  safe_malloc(v->sym, strlen(s) + 1);
	strcpy(v->sym, s);
  return v;
}

lenv* lenv_new(void) {
  lenv* e = malloc(sizeof(lenv));
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

/* Destructors */
void lval_del(lval* v) {
  switch (v->type) {
    case LVAL_NUM: break;
    case LVAL_ERR: free(v->err); break;
    case LVAL_SYM: free(v->sym); break;
    case LVAL_SEXPR:
    case LVAL_QEXPR:
      for (int i = 0; i < v->count; i++) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
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

/* Environment functions */
lval *lenv_get(lenv *e, lval *k){
  for(int i=0; i!=e->count; ++i){
    if(strcmp(e->syms[i], k->sym) == 0) return lval_copy(e->vals[i]);
  }
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

/* S-Expression functions */
lval* lval_add(lval* v, lval* x) {
  v->count++;
  safe_realloc(v->cell, sizeof(lval*) * v->count);
  v->cell[v->count-1] = x;
  return v;
}
lval* lval_pop(lval* v, int i) {
  lval* x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i+1],
    sizeof(lval*) * (v->count-i-1));
  v->count--;
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  return x;
}
lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);
  return x;
}
lval* lval_copy(lval* v) {
  lval* x = malloc(sizeof(lval));
  x->type = v->type;
  switch (v->type) {
    /* Copy Functions and Numbers Directly */
    case LVAL_FUN: 
      x->fun = v->fun;
      x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym); break;
    case LVAL_NUM: x->num = v->num; break;
    /* Copy Strings using malloc and strcpy */
    case LVAL_ERR:
      x->err = malloc(strlen(v->err) + 1);
      strcpy(x->err, v->err); break;
    case LVAL_SYM:
      x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym); break;
    /* Copy Lists by copying each sub-expression */
    case LVAL_SEXPR:
    case LVAL_QEXPR:
      x->count = v->count;
      x->cell = malloc(sizeof(lval*) * x->count);
      for (int i = 0; i < x->count; i++) {
        x->cell[i] = lval_copy(v->cell[i]);
      }
    break;
  }

  return x;
}

/* Output functions */
void lval_expr_print(lval* v, const char *open, const char *close) {
  printf(open);
  for (int i = 0; i < v->count; i++) {
    print_lval(v->cell[i]);
    if (i != (v->count-1)) putchar(' ');
  }
  printf(close);
}
void print_lval(lval *v){
	switch(v->type){
		case LVAL_NUM: printf("%li", v->num); break;
		case LVAL_ERR:   printf("Error: %s", v->err); break;
		case LVAL_SYM:   printf("%s", v->sym); break;
    case LVAL_SEXPR: lval_expr_print(v, "(", ")"); break;	
    case LVAL_QEXPR: lval_expr_print(v, "'(", ")"); break;	
    case LVAL_FUN: printf("<function:%s>", v->sym); break;
		break;
	}
}
void lval_println(lval* v) { print_lval(v); putchar('\n'); }

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "Function";
    case LVAL_NUM: return "Number";
    case LVAL_ERR: return "Error";
    case LVAL_SYM: return "Symbol";
    case LVAL_SEXPR: return "S-Expression";
    case LVAL_QEXPR: return "Q-Expression";
    default: return "Unknown";
  }
}

/* Input functions */
lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  long x = strtol(t->contents, NULL, 10);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number");
}
lval* lval_read(mpc_ast_t* t) {

  /* If Symbol or Number return conversion to that type */
  if (strstr(t->tag, "number")) { return lval_read_num(t); }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }

  /* If root (>) or sexpr then create empty list */
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); }
  if (strstr(t->tag, "sexpr"))  { x = lval_sexpr(); }
  if (strstr(t->tag, "qexpr"))  { x = lval_qexpr(); }

  /* Fill this list with any valid expression contained within */
  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) continue;
    if (strcmp(t->children[i]->contents, ")") == 0) continue; 
    if (strcmp(t->children[i]->contents, "'") == 0) continue;
    // if (strcmp(t->children[i]->contents, "}") == 0) continue; 
    if (strcmp(t->children[i]->tag,  "regex") == 0) continue; 
    x = lval_add(x, lval_read(t->children[i]));
  }

  return x;
}

/* Evaluation functions */
lval *lval_eval_sexpr(lenv *e, lval *v){
	// evaluate children and check for errors
	for(int i=0; i<v->count; ++i){
    // don't evaluate first argument of define
    if(v->cell[0] != NULL && v->cell[0]->fun == builtin_define && i == 1) continue;
    v->cell[i] = lval_eval(e, v->cell[i]);
    if(v->cell[i]->type == LVAL_ERR) return lval_take(v, i);
  }

  if(v->count == 0) return v;
	if(v->count == 1) return lval_take(v, 0);

	lval *f = lval_pop(v, 0);
	if(f->type != LVAL_FUN){
		lval_del(f); lval_del(v);
		return lval_err("S-expr does not begin with function");
	}

	lval *res = f->fun(e, v);
	lval_del(f);
	return res;
}

lval *lval_eval(lenv *e, lval *v){
  if(v->type == LVAL_SYM){
    lval *x = lenv_get(e, v);
    lval_del(v);
    return x;
  }
	if(v->type == LVAL_SEXPR) return lval_eval_sexpr(e, v);
	return v;
}

/* Builtin functions */
lval* builtin_op(lenv *e, lval* a, char* op) {
  /* Ensure all arguments are numbers */
  for (int i = 0; i < a->count; i++) {
    LASSERT(a, a->cell[i]->type == LVAL_NUM,
      "Expected type %s, recieved %s", 
      ltype_name(LVAL_NUM), ltype_name(a->cell[i]->type));
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

lval *builtin_car(lenv* e, lval *a){
  LASSERT(a, a->count == 1,
    "function 'car' passed too many arguments! Got %i, expected 1.", a->count);
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
    "Function 'car' passed incorrect type! Expected %s, received %s.",
    ltype_name(LVAL_QEXPR), ltype_name(a->cell[0]->type));
  LASSERT(a, a->cell[0]->count != 0,
    "Function 'car' passed {}!");

  lval* v = lval_take(a, 0); // take argument to car
  while (v->count > 1) { lval_del(lval_pop(v, 1)); } // delete cdr
  return lval_take(v, 0);
}

lval* builtin_cdr(lenv* e, lval *a) {
  LASSERT(a, a->count == 1,
    "Function 'cdr' passed too many arguments! Got %i, expected 1.", a->count);
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
    "Function 'cdr' passed incorrect type! Expected %s, received %s.",
    ltype_name(LVAL_QEXPR), ltype_name(a->cell[0]->type));
  LASSERT(a, a->cell[0]->count != 0,
    "Function 'cdr' passed {}!");

  lval* v = lval_take(a, 0); // take argyment to cdr
  lval_del(lval_pop(v, 0)); // delete car
  return v-> count == 1 ? lval_take(v, 0) : v;
}

lval *builtin_list(lenv* e, lval *a){
  a->type = LVAL_QEXPR;
  return a;
}

lval* builtin_eval(lenv* e, lval* a) {
  LASSERT(a, a->count == 1,
    "Function 'eval' passed too many arguments! Got %i, expected 1.", a->count);
  LASSERT(a, a->cell[0]->type == LVAL_QEXPR,
    "Function 'eval' passed incorrect type! Expected %s, received %s.",
    ltype_name(LVAL_QEXPR), ltype_name(a->cell[0]->type));

  lval* x = lval_take(a, 0);
  x->type = LVAL_SEXPR;
  return lval_eval(e, x);
}

lval* builtin_join(lenv* e, lval* a) {
  for (int i = 0; i < a->count; i++) {
    LASSERT(a, a->cell[i]->type == LVAL_QEXPR,
      "Function 'join' passed incorrect type. Expected %s, received %s.",
    ltype_name(LVAL_QEXPR), ltype_name(a->cell[0]->type));
  }

  lval* x = lval_pop(a, 0);
  while (a->count) {
    x = lval_join(x, lval_pop(a, 0));
  }
  lval_del(a);
  return x;
}

lval *builtin_cons(lenv* e, lval *a){
  LASSERT(a, a->count == 2,
    "Function 'cons' passed incorrect number of arguments. Got %i, expected 2.", a->count);
  lval *c = lval_qexpr();
  lval_add(c, lval_pop(a, 0));
  lval_add(c, lval_pop(a, 0));
  lval_del(a);
  return c;
}

lval *builtin_define(lenv *e, lval *a){
  LASSERT(a, a->count == 2,
    "Function 'define' incorrect number of arguments!! Got %i, expected 2.", a->count);
  LASSERT(a, a->cell[0]->type == LVAL_SYM,
    "Function 'define' cannot define non-symbol!");

  lenv_put(e, a->cell[0], a->cell[1]);
  lval_del(a);
  return lval_sexpr();
}

lval* lval_join(lval* x, lval* y) {
  while (y->count) {
    x = lval_add(x, lval_pop(y, 0));
  }
  lval_del(y);
  return x;
}

void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name);
  lval* v = lval_fun(func, name);
  lenv_put(e, k, v);
  lval_del(k); lval_del(v);
}

void lenv_add_builtins(lenv* e) {
  /* List Functions */
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "car",  builtin_car);
  lenv_add_builtin(e, "cdr",  builtin_cdr);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "join", builtin_join);
  lenv_add_builtin(e, "cons", builtin_cons);
  lenv_add_builtin(e, "define", builtin_define);

  /* Mathematical Functions */
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);
}

int main(int argc, char **argv){

	mpc_parser_t* Number = mpc_new("number");
	mpc_parser_t* Symbol = mpc_new("symbol");
	mpc_parser_t* Sexpr  = mpc_new("sexpr");
	mpc_parser_t* Qexpr  = mpc_new("qexpr");
	mpc_parser_t* Expr   = mpc_new("expr");
	mpc_parser_t* Lispy  = mpc_new("lispy");

	mpca_lang(MPCA_LANG_DEFAULT,
	"                                          \
		number : /-?[0-9]+/ ;                    \
		symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&^$#%@~]+/           \
           | \"list\" | \"car\" | \"cdr\"  \
           | \"join\" | \"eval\" | \"cons\" \
           | \"define\"   ;         \
		sexpr  : '(' <expr>* ')' ;               \
		qexpr  : '\'' '(' <expr>* ')' ;          \
		expr   : <number> | <symbol> | <sexpr> | <qexpr> ; \
		lispy  : /^/ <expr>* /$/ ;               \
	",
	Number, Symbol, Sexpr, Qexpr, Expr, Lispy);


	puts("MLispy Version 0.0.0.0.1");
	puts("Press Ctrl+C to exit\n");

  lenv* e = lenv_new();
  lenv_add_builtins(e);

	while(1){
		char *input = readline("mlispy> ");
		add_history(input);

		mpc_result_t r;
		if(mpc_parse("<stdin>", input, Lispy, &r)){
      lval* r_out = lval_read(r.output);
			lval* x = lval_eval(e, r_out);
			lval_println(x);
			lval_del(x);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	mpc_cleanup(6, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);
}