#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<z3.h>

void my_parser_example(char const* const fileName) {
  Z3_config cfg;
  Z3_context ctx;
  cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");
  ctx = Z3_mk_context(cfg);
  Z3_del_config(cfg);

  FILE* file = fopen(fileName, "r");
  char* buffer = NULL;
  size_t len;
  ssize_t bytes_read = getdelim( &buffer, &len, '\0', file);

  printf("%s", Z3_eval_smtlib2_string(ctx, buffer));
  fclose(file);
}

int main(int argc, char* argv[]) {
    char const* const fileName = argv[1];
    my_parser_example(fileName);
    return 0;
}
