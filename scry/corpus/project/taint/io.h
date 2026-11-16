#ifndef PROJECT_TAINT_IO_H
#define PROJECT_TAINT_IO_H

char *getenv(const char *name);
int system(const char *command);
char *escape_shell(char *s);
void run_cmd(char *cmd);
void safe_cmd(char *cmd);
int io_helper(int x);
void maybe(void);

#endif
