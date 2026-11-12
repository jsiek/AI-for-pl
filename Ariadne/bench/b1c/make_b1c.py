"""Build the B1c inputs of plan Q10 (a client that reuses the list after
iterating), with the iterator spec of 2026-11-08 (owner-approved).

    python3 -I make_b1c.py          (from this directory)

Writes
  b1c_frozen.c   the Frama-C input: B1a's code, spec block and template
                 contract invocations (verbatim from ../b1a/b1a_frozen.c,
                 asserted), and B1c's driver with its contract;
  b1c.c          the VST input: the same code with real malloc/free and a
                 main;
  b1c_ref.c      the hand-made reference: B1's annotated, certified b1.c
                 (../b1/b1.c) with B1c's driver and its annotations, and
                 one lemma of its own (dll_shared, proved in Coq:
                 session/interactive/lemma_dll_shared.v);
  spec/sglib_dl_list_spec.h
                 the public part of ../sglib_spec/sglib_dl_list_spec.h, as
                 ../b1a/make_b1a.py writes B1a's (B1a keeps its own copy:
                 the snapshot its runs used)."""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
WP_A = open(os.path.join(HERE, "..", "b1a", "b1a_frozen.c")).read()
VST_A = open(os.path.join(HERE, "..", "b1a", "b1a.c")).read()
B1 = open(os.path.join(HERE, "..", "b1", "b1.c")).read()
TEMPLATE = open(os.path.join(HERE, "..", "sglib_spec",
                             "sglib_dl_list_spec.h")).read()

COMMENT = """/* Driver (B1c), modelled on sglib's self-test of the DL list: build a
   list from input[0..n-1] with sglib_dllist_add; walk it once with the
   iterator without freeing, summing the payloads (unsigned, so the sum
   cannot overflow) and recording the node at position m / 2; if the walk
   returned a node, add a new node before that recorded node (add with
   *list set to a middle node); then iterate again starting from the new
   node, which exercises the iterator's backward phase, freeing every node
   returned.  Returns the sum. */
"""
# The driver's contract: B1a's (the driver reads the same input and
# payloads), for an unsigned result.
CONTRACT = WP_A[WP_A.index("/*@ requires 0 <= n"):
                WP_A.index("int b1(const int *input, int n) {")]

DRIVER_WP = """unsigned b1(const int *input, int n) {
  dllist *l = NULL, *the_list = NULL, *mid = NULL, *e = NULL;
  struct sglib_dllist_iterator it;
  unsigned sum = 0, c = 0;
  int m = 0;
  for (int k = 0; k < n; k++) {
  before_alloc:
    l = ariadne_alloc_dllist();
    if (l == NULL)
      break;
    l->i = input[k];
    sglib_dllist_add(&the_list, l);
    m++;
  }
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    sum += (unsigned)l->i;
    if (c == (unsigned)m / 2)
      mid = l;
    c++;
  }
  if (mid != NULL) {
  before_alloc2:
    e = ariadne_alloc_dllist();
    if (e != NULL) {
      e->i = 0;
      the_list = mid;
      sglib_dllist_add(&the_list, e);
    }
  }
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
  before_free:
    ariadne_free_dllist(l);
  }
  return sum;
}
"""
DRIVER_VST = (DRIVER_WP.replace("  before_alloc:\n", "")
              .replace("  before_alloc2:\n", "")
              .replace("  before_free:\n", "")
              .replace("ariadne_alloc_dllist()", "malloc(sizeof(dllist))")
              .replace("ariadne_free_dllist(l)", "free(l)"))
assert DRIVER_VST.count("malloc(") == 2 and DRIVER_VST.count("free(l)") == 1

# ---- the reference's own lemma and the driver's annotations -----------

LEMMA = r"""/*@ // Two whole lists that share a node are the same list, index for
    // index (dll_links, dll_first; induction, Coq).
    lemma dll_shared{L}:
      \forall dllist *h1, *h2, \list<dllist *> s1, s2, integer i, j;
        dll(\null, h1, s1) ==> dll(\null, h2, s2)
        ==> 0 <= i < \length(s1) ==> 0 <= j < \length(s2)
        ==> \nth(s1, i) == \nth(s2, j)
        ==> \forall integer k; 0 <= k < \length(s1)
              ==> k < \length(s2) && \nth(s1, k) == \nth(s2, k);
    // So a whole list (at L2) that shares a node with a whole live list
    // (at L1, its links unchanged at L2) has only live nodes (at L1).
    // A client needs it to know that the list it_init iterates (some
    // whole list holding `list`) is its own live list.
    lemma dll_shared_live{L1, L2}:
      \forall dllist *h1, *h2, \list<dllist *> s1, s2, integer i, j;
        dll{L2}(\null, h1, s1) ==> live_dll{L1}(\null, h2, s2)
        ==> unchanged{L1, L2}(s2)
        ==> 0 <= i < \length(s1) ==> 0 <= j < \length(s2)
        ==> \nth(s1, i) == \nth(s2, j) ==> all_live{L1}(s1);
*/
"""
ANNOTATED = r"""unsigned b1(const int *input, int n) {
  dllist *l = NULL, *the_list = NULL, *mid = NULL, *e = NULL;
  struct sglib_dllist_iterator it;
  unsigned sum = 0, c = 0;
  int m = 0;
  //@ assert live_dll(\null, the_list, \Nil);
  /*@ loop invariant 0 <= k <= n && 0 <= m <= k;
      loop invariant !dead(__heap, \base_addr(input));
      loop invariant \initialized(&the_list);
      loop invariant \initialized(input + (0 .. n - 1));
      loop invariant \exists \list<dllist *> s; live_dll(\null, the_list, s);
      loop invariant payload_init:
        \forall dllist *q; live(q) ==> \initialized(&q->i);
      loop assigns k, m, l, the_list, __heap,
        { q->i | dllist *q; heap(\base_addr(q)) },
        { q->ptr_to_next | dllist *q },
        { q->ptr_to_previous | dllist *q; heap(\base_addr(q)) };
      loop variant n - k;
  */
  for (int k = 0; k < n; k++) {
  before_alloc:
    l = ariadne_alloc_dllist();
    if (l == NULL)
      break;
    /*@ assert old_nodes_live:
          \forall dllist *q; live{before_alloc}(q) ==> live(q) && q != l; */
    /*@ assert old_lists_live:
          \forall \list<dllist *> s;
            all_live{before_alloc}(s) ==> all_live(s) && !mem(l, s); */
    l->i = input[k];
    /*@ assert old_head: the_list == \null
          || the_list->ptr_to_previous == \null; */
    /*@ assert add_pre: the_list == \null
          || \exists \list<dllist *> s; live_dll(\null, the_list, s)
             && the_list == \nth(s, 0) && !mem(l, s); */
    /*@ assert payload_written:
          \forall dllist *q; live(q) ==> \initialized(&q->i); */
    sglib_dllist_add(&the_list, l);
    /*@ assert head_after_add:
          \exists \list<dllist *> s; live_dll(\null, the_list, s); */
    /*@ assert payload_kept:
          \forall dllist *q; live(q) ==> \initialized(&q->i); */
    m++;
  }
  /*@ assert head_is_node0:
        the_list == \null
        || \exists \list<dllist *> t;
             live_dll(\null, the_list, \Cons(the_list, t)); */
  /*@ loop invariant walk_null: the_list == \null ==> l == \null && mid == \null;
      loop invariant walk_it: the_list != \null ==>
        \exists \list<dllist *> s; iter_ok(&it, s, l) && all_live(s)
          && mem(the_list, s) && (mid == \null || mem(mid, s));
      loop invariant it.subcomparator == \null;
      loop invariant payload_init:
        \forall dllist *q; live(q) ==> \initialized(&q->i);
      loop assigns l, it, sum, c, mid;
  */
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
    /*@ assert l_node: \exists \list<dllist *> s; iter_ok(&it, s, l)
          && all_live(s) && mem(the_list, s) && (mid == \null || mem(mid, s))
          && mem(l, s); */
    sum += (unsigned)l->i;
    if (c == (unsigned)m / 2)
      mid = l;
    c++;
  }
  /*@ assert after_walk: the_list == \null
        || \exists dllist *h, \list<dllist *> s; live_dll(\null, h, s)
           && mem(the_list, s) && (mid == \null || mem(mid, s)); */
  if (mid != NULL) {
  before_alloc2:
    e = ariadne_alloc_dllist();
    /*@ assert lists_live2:
          \forall \list<dllist *> s; all_live{before_alloc2}(s)
            ==> all_live(s) && (e == \null || !mem(e, s)); */
    if (e != NULL) {
      /*@ assert old_nodes_live2:
            \forall dllist *q; live{before_alloc2}(q) ==> live(q) && q != e; */
      e->i = 0;
      /*@ assert init_kept2: \forall \list<dllist *> s;
            all_init{before_alloc2}(s) ==> all_init(s); */
      the_list = mid;
      /*@ assert add_pre2b:
            \forall dllist *h, \list<dllist *> s;
              live_dll{before_alloc2}(\null, h, s)
              ==> live_dll(\null, h, s) && !mem(e, s); */
      /*@ assert add_pre2:
            \exists dllist *h, \list<dllist *> s, integer k;
              live_dll(\null, h, s) && 0 <= k < \length(s)
              && the_list == \nth(s, k) && !mem(e, s); */
      sglib_dllist_add(&the_list, e);
    }
  }
  /*@ assert start_node: the_list == \null || in_live_list(the_list); */
  /*@ loop invariant l == \null
        || \exists \list<dllist *> s; iter_ok(&it, s, l);
      loop invariant it.subcomparator == \null;
      loop assigns l, it, __heap;
  */
  for (l = sglib_dllist_it_init(&it, the_list); l != NULL;
       l = sglib_dllist_it_next(&it)) {
  before_free:
    ariadne_free_dllist(l);
    /*@ assert others_live:
          \forall dllist *q; live{before_free}(q) && q != l ==> live(q); */
    /*@ assert iter_after_free:
          \forall \list<dllist *> s, integer b, f, c;
            iter_at{before_free}(&it, s, b, f) && b < c < f
            && l == \nth(s, c) ==> iter_at(&it, s, b, f); */
  }
  return sum;
}
"""
# the annotated driver is the driver plus annotations
strip = re.sub(r"[ \t]*/\*@.*?\*/\n|[ \t]*//@[^\n]*\n", "", ANNOTATED,
               flags=re.S)
assert strip == DRIVER_WP, "the reference's driver differs from b1c.c's"

# ---- the public header (as ../b1a/make_b1a.py) -------------------------

PRIVATE = re.compile(r"#define SGLIB_DL_LIST_(LEMMAS|ANNOT_\w+|_ADD_PRE"
                     r"|_ADD_HYPS)\(")  # _INSERTED: public since 2026-11-10
out, chunk, i = [], [], 0
src = TEMPLATE.split("\n")
while i < len(src):
    line = src[i]
    if line.startswith("#define"):
        macro = [line]
        while macro[-1].endswith("\\"):
            i += 1
            macro.append(src[i])
        if PRIVATE.match(line):
            chunk = []
        else:
            out += chunk + macro
            chunk = []
    elif line == "":
        if not any(re.match(r"/\* (---- private|Private)", c)
                   for c in chunk):
            out += chunk
        out.append("")
        chunk = []
    else:
        chunk.append(line)
    i += 1
out += chunk
public = re.sub(r"\n{3,}", "\n\n", "\n".join(out))
public = public.replace(
    "#ifndef SGLIB_DL_LIST_SPEC_H",
    "/* The public part only (plan Q11), generated by\n"
    "   ../make_b1c.py from ../../sglib_spec/sglib_dl_list_spec.h. */\n\n"
    "#ifndef SGLIB_DL_LIST_SPEC_H", 1)
assert not re.search(r"SGLIB_DL_LIST_(LEMMAS|ANNOT_|_ADD_)\w*\(",
                     public.split("#ifndef", 1)[1])

# ---- the files ---------------------------------------------------------

i = WP_A.index("/* Driver: build a list")
WP = (WP_A[:i].replace("Benchmark B1a, frozen-only (plan Q10)",
                       "Benchmark B1c, frozen-only (plan Q10)", 1)
      .replace("Generated by make_b1a.py from ../b1/b1_gen.c (code) and\n"
               "   ../b1/b1_frozen.c (spec)",
               "Generated by make_b1c.py from ../b1a/b1a_frozen.c (B1a's\n"
               "   code and contract invocations, a new driver; the spec of\n"
               "   2026-11-08 through spec/)", 1)
      + COMMENT + CONTRACT + DRIVER_WP)
j = VST_A.index("/* Driver: build a list")
VST = (VST_A[:j].replace(
    "/* Benchmark B1a for VST (plan Q10).  Generated by make_b1a.py: the",
    "/* Benchmark B1c for VST (plan Q10).  Generated by make_b1c.py from\n"
    "   ../b1a/b1a.c with a new driver.  As there: the", 1)
    + COMMENT + DRIVER_VST + """
int input[4] = {6, 7, 3, 4};

int main(void) {
  b1(input, 4);
  return 0;
}
""")
k = B1.index("/* Driver for B1a: build a list")
REF = (B1[:k].replace(
    "/* Benchmark B1a (plan section 6.2)",
    "/* Reference for B1c (plan Q10), written by ../b1c/make_b1c.py from\n"
    "   ../b1/b1.c: B1's certified annotations, B1c's driver annotated by\n"
    "   hand, and the lemma dll_shared.\n\n   Benchmark B1a (plan section 6.2)", 1)
    + LEMMA + "\n" + COMMENT + CONTRACT + ANNOTATED)
assert "Reference for B1c" in REF and "Benchmark B1c" in WP and \
    "Benchmark B1c" in VST
os.makedirs(os.path.join(HERE, "spec"), exist_ok=True)
for name, text in [("b1c_frozen.c", WP), ("b1c.c", VST), ("b1c_ref.c", REF),
                   ("spec/sglib_dl_list_spec.h", public)]:
    open(os.path.join(HERE, name), "w").write(text)
