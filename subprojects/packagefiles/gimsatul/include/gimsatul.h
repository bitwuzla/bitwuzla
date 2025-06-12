#include <stdint.h>

struct gimsatul;

const char* gimsatul_version();

struct gimsatul* gimsatul_init(uint32_t threads, int32_t max_var);

void gimsatul_release(struct gimsatul* gimsatul);

void gimsatul_add_clauses(struct gimsatul* gimsatul,
                          int32_t variables,
                          int32_t nliterals,
                          int32_t* literals,
                          int32_t expected_clauses);

int32_t gimsatul_solve(struct gimsatul* gimsatul);

int32_t gimsatul_value(struct gimsatul* gimsatul, int32_t lit);
