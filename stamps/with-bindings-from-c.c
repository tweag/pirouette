
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include<z3.h>

/**
   \defgroup capi_ex C API examples
*/
/**@{*/
/**
   @name Auxiliary Functions
*/
/**@{*/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char* message)
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable()
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions.

   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_context c, Z3_error_code e)
{
    longjmp(g_catch_buffer, e);
}

/**
   \brief Error handling that depends on checking an error code on the context.

*/

void nothrow_z3_error(Z3_context c, Z3_error_code e) {
    // no-op
}

/**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

void my_parser_example(char const* const fileName) {
  Z3_context ctx;

  ctx = mk_context();

  FILE* file = fopen(fileName, "r"); /* should check the result */
  char line[8192];
  Z3_string result = malloc(256 * sizeof(char));

  while (fgets(line, sizeof(line), file)) {
    /* note that fgets don't strip the terminating \n, checking its
       presence would allow to handle lines longer that sizeof(line) */
    result = Z3_eval_smtlib2_string(ctx, line);
    printf("%s", result);
  }
  /* may check feof here to make a difference between eof and io failure -- network
     timeout for instance */
  fclose(file);
}

/**@}*/
/**@}*/

int main(int argc, char* argv[]) {
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif
    char const* const fileName = argv[1]; /* should check that argc > 1 */
    my_parser_example(fileName);
    return 0;
}
