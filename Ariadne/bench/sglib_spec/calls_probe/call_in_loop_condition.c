typedef struct node { int n; struct node *prev; } node;

/*@ requires \valid_read(a) && \valid_read(b);
    assigns \nothing; */
int cmp1(node *a, node *b) { return (a->n > b->n) - (a->n < b->n); }

/*@ requires f == \null || f == &cmp1;
    requires \valid_read(x) && \valid(y) && y->prev == \null;
    assigns \nothing; */
int walk(int (*f)(node *, node *), node *x, node *y) {
  node *ce = y;
  if (f != 0) {
    /*@ calls cmp1; */
    /*@ loop invariant ce == y || ce == \null;
        loop assigns ce; */
    while (ce != 0 && f(x, ce) != 0)
      ce = ce->prev;
  }
  return ce != 0;
}
