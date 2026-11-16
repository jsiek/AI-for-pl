typedef struct node { int n; struct node *next; } node;

/*@ predicate cmp_reads(node *p) = \initialized(&p->n); */

/*@ requires \valid_read(a) && \valid_read(b) && cmp_reads(a) && cmp_reads(b);
    assigns \nothing; */
int cmp1(node *a, node *b) { return (a->n > b->n) - (a->n < b->n); }

/*@ requires \valid_read(a) && \valid_read(b) && cmp_reads(a) && cmp_reads(b);
    assigns \nothing;
    ensures \result == 0; */
int cmp2(node *a, node *b) { return 0; }

/*@ requires f == \null || f == &cmp1 || f == &cmp2;
    requires \valid_read(x) && \valid_read(y) && cmp_reads(x) && cmp_reads(y);
    assigns \nothing; */
int use(int (*f)(node *, node *), node *x, node *y) {
  int r = 0;
  if (f != 0) {
    /*@ calls cmp1, cmp2; */
    r = f(x, y);
  }
  return r;
}

/*@ requires f == &cmp1 || f == &cmp2;
    requires \valid_read(x) && \valid_read(y);
    assigns \nothing; */
int bad(int (*f)(node *, node *), node *x, node *y) {
  /*@ calls cmp1, cmp2; */
  return f(x, y);
}
