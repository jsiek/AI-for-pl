"""Write the 9 stage-1 client programs of the approved client survey
(../../sglib_spec/CLIENT_SURVEY.md, "New clients", stage 1) as
client1.c .. client9.c: the frozen instance ../dllist.c (types and the
six sglib functions, verbatim, asserted), <stdlib.h> for malloc/free,
the client's driver and a main.  Every client frees every node it
allocates (leak freedom, owner 2026-11-17).

    python3 -I make_clients.py          (from this directory)
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = open(os.path.join(HERE, "..", "dllist.c")).read()
BODY = LIB[LIB.index("#include <stddef.h>"):]
assert BODY in LIB

BUILD = """\
/* build a list of n nodes with payloads input[0..n-1] by prepending;
   returns the number of nodes (malloc may fail) */
static int build(dllist **list, const int *input, int n) {
  int m = 0;
  for (int k = 0; k < n; k++) {
    dllist *l = malloc(sizeof(dllist));
    if (l == NULL)
      break;
    l->i = input[k];
    sglib_dllist_add(list, l);
    m++;
  }
  return m;
}

/* free every node of the list that has node p, by one iteration */
static void free_all(dllist *p) {
  struct sglib_dllist_iterator it;
  dllist *l;
  for (l = sglib_dllist_it_init(&it, p); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
}

int input[5] = {6, 7, 3, 4, 7};
"""



def helpers(driver):
    """BUILD's helpers that the driver uses (an unused static function
    is a compiler warning), and the input array."""
    parts = BUILD.split("\n\n")
    keep = [p for p in parts
            if not p.lstrip().startswith("/*")
            or ("build(" in p and "build(" in driver)
            or ("free_all(" in p and "free_all(" in driver)]
    return "\n\n".join(keep)


CLIENTS = {
    1: ("Old nodes after add (A4): build, keep the head h and a middle "
        "node m, add a node before m, walk forward from get_first(h) "
        "summing payloads, free everything by an iteration from h.", """\
unsigned client(const int *input, int n) {
  dllist *list = NULL, *h, *m, *e, *l;
  struct sglib_dllist_iterator it;
  unsigned sum = 0;
  int k = 0, cnt = build(&list, input, n);
  if (cnt == 0)
    return 0;
  h = list;
  m = list;
  for (l = sglib_dllist_it_init(&it, list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    if (k == cnt / 2)
      m = l;
    k++;
  }
  e = malloc(sizeof(dllist));
  if (e != NULL) {
    e->i = 0;
    list = m;
    sglib_dllist_add(&list, e);
  }
  for (l = sglib_dllist_get_first(h); l != NULL; l = l->ptr_to_next)
    sum += (unsigned)l->i;
  free_all(h);
  return sum;
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    2: ("Several lists (A7): build two lists from alternate input values, "
        "iterate the first and add copies of its payloads to the second, "
        "free both by iteration.", """\
void client(const int *input, int n) {
  dllist *a = NULL, *b = NULL, *l, *c;
  struct sglib_dllist_iterator it;
  for (int k = 0; k < n; k++) {
    l = malloc(sizeof(dllist));
    if (l == NULL)
      break;
    l->i = input[k];
    if (k % 2 == 0)
      sglib_dllist_add(&a, l);
    else
      sglib_dllist_add(&b, l);
  }
  for (l = sglib_dllist_it_init(&it, a); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    c = malloc(sizeof(dllist));
    if (c == NULL)
      break;
    c->i = l->i;
    sglib_dllist_add(&b, c);
  }
  free_all(a);
  free_all(b);
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    3: ("A global list head (A8): as B1a's driver, with the head a global "
        "variable; main calls the driver twice.", """\
dllist *the_list = NULL;

unsigned client(const int *input, int n) {
  dllist *l;
  struct sglib_dllist_iterator it;
  unsigned sum = 0;
  build(&the_list, input, n);
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    sum += (unsigned)l->i;
    free(l);
  }
  the_list = NULL;
  return sum;
}

int main(void) {
  client(input, 5);
  client(input, 3);
  return 0;
}
"""),
    4: ("List head and iterator in heap memory (A8, I14): a malloc'ed "
        "struct holds the head and an iterator; build through &s->head, "
        "iterate with &s->it, free the nodes, then the struct.", """\
struct holder {
  dllist *head;
  struct sglib_dllist_iterator it;
};

unsigned client(const int *input, int n) {
  struct holder *s = malloc(sizeof(struct holder));
  dllist *l;
  unsigned sum = 0;
  if (s == NULL)
    return 0;
  s->head = NULL;
  build(&s->head, input, n);
  for (l = sglib_dllist_it_init(&s->it, s->head); l != NULL;
       l = sglib_dllist_it_next(&s->it)) {
    sum += (unsigned)l->i;
    free(l);
  }
  free(s);
  return sum;
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    5: ("get_first/get_last from the middle (G2): take a middle node, walk "
        "forward from get_first(mid) and backward from get_last(mid), "
        "free by an iteration from mid.", """\
unsigned client(const int *input, int n) {
  dllist *list = NULL, *mid, *l;
  struct sglib_dllist_iterator it;
  unsigned sum = 0;
  int k = 0, cnt = build(&list, input, n);
  if (cnt == 0)
    return 0;
  mid = list;
  for (l = sglib_dllist_it_init(&it, list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    if (k == cnt / 2)
      mid = l;
    k++;
  }
  for (l = sglib_dllist_get_first(mid); l != NULL; l = l->ptr_to_next)
    sum += (unsigned)l->i;
  for (l = sglib_dllist_get_last(mid); l != NULL; l = l->ptr_to_previous)
    sum += (unsigned)l->i;
  free_all(mid);
  return sum;
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    6: ("Partial iteration (I6): iterate from the head and stop after k "
        "nodes; start a new iteration with the same iterator struct and "
        "free every node.", """\
unsigned client(const int *input, int n, int k) {
  dllist *list = NULL, *l;
  struct sglib_dllist_iterator it;
  unsigned sum = 0;
  int c = 0;
  build(&list, input, n);
  for (l = sglib_dllist_it_init(&it, list); l != NULL && c < k;
       l = sglib_dllist_it_next(&it)) {
    sum += (unsigned)l->i;
    c++;
  }
  for (l = sglib_dllist_it_init(&it, list); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
  return sum;
}

int main(void) {
  client(input, 5, 2);
  return 0;
}
"""),
    7: ("Two iterators (I9): for each node of an outer iteration, an "
        "inner iteration with a comparator whose equalto is the outer "
        "iterator's current node counts the nodes with the same payload; "
        "then free by iteration.", """\
int same_payload(dllist *a, dllist *b) {
  return a->i == b->i ? 0 : 1;
}

unsigned client(const int *input, int n) {
  dllist *list = NULL, *l, *m;
  struct sglib_dllist_iterator outer, inner;
  unsigned count = 0;
  build(&list, input, n);
  for (l = sglib_dllist_it_init(&outer, list); l != NULL;
       l = sglib_dllist_it_next(&outer)) {
    for (m = sglib_dllist_it_init_on_equal(&inner, list, same_payload, l);
         m != NULL; m = sglib_dllist_it_next(&inner))
      count++;
  }
  free_all(list);
  return count;
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    8: ("it_next after the end (I13): a complete iteration that frees "
        "every node, then it_next once more (memory safety of that call "
        "only).", """\
void client(const int *input, int n) {
  dllist *list = NULL, *l;
  struct sglib_dllist_iterator it;
  build(&list, input, n);
  for (l = sglib_dllist_it_init(&it, list); l != NULL;
       l = sglib_dllist_it_next(&it))
    free(l);
  sglib_dllist_it_next(&it);
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
    9: ("A comparator with its own state (C3): it_init_on_equal with a "
        "comparator that compares payloads and increments a global "
        "unsigned counter (wraps, so any number of calls is defined: "
        "owner, 2026-11-20); the client reads the count, then frees every node by "
        "an iteration without a comparator.", """\
unsigned counter = 0;

int counting_cmp(dllist *a, dllist *b) {
  counter++;
  return a->i == b->i ? 0 : 1;
}

unsigned client(const int *input, int n) {
  dllist *list = NULL, *l, key;
  struct sglib_dllist_iterator it;
  unsigned found = 0;
  key.i = input[0];
  key.ptr_to_next = NULL;
  key.ptr_to_previous = NULL;
  build(&list, input, n);
  for (l = sglib_dllist_it_init_on_equal(&it, list, counting_cmp, &key);
       l != NULL; l = sglib_dllist_it_next(&it))
    found++;
  free_all(list);
  return found + counter;
}

int main(void) {
  client(input, 5);
  return 0;
}
"""),
}

for n, (what, driver) in CLIENTS.items():
    open(os.path.join(HERE, "client%d.c" % n), "w").write(
        "/* Stage-1 client %d of the approved client survey (plan M6).\n"
        "   %s\n"
        "   Generated by make_clients.py from ../dllist.c (the six sglib\n"
        "   functions, verbatim); do not edit. */\n\n" % (
            n, "\n   ".join(_wrap for _wrap in
                             __import__("textwrap").wrap(what, 66)))
        + BODY.replace("#include <stddef.h>\n",
                       "#include <stddef.h>\n#include <stdlib.h>\n", 1)
        + "\n" + helpers(driver) + "\n" + driver)
