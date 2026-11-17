/* Does VST 2.17 let a function drop owned memory at return? */
#include <stddef.h>
struct node { int i; struct node *next; };
void drop_int(int *p) { return; }
void drop_node(struct node *p) { return; }
