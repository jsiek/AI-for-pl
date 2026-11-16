/* Generality test for gen_twins.py: inductives that are not in B1.
   - lseg: a singly linked list segment (sglib's lists, B2/B3), with a
     repeated variable in a conclusion (lseg(p, p, \Nil));
   - tree: a binary tree with its nodes in preorder and no sharing, two
     inductive premises and \concat (sglib's rbtree, M4);
   - bst: binary search tree bounds, integer arguments and arithmetic;
   - bst_tree, seg_to_null: predicates with an \exists over lists, which
     the generator replaces by witnesses.
   Only the spec matters here; shapes_test.c runs the generated twins. */
#include "shapes.h"

/*@ predicate mem(node *p, \list<node *> s) =
      \exists integer k; 0 <= k < \length(s) && \nth(s, k) == p;

    // The nodes from `from` up to (not including) `to` by next are s.
    inductive lseg{L}(node *from, node *to, \list<node *> s) {
      case lseg_nil{L}: \forall node *p; lseg{L}(p, p, \Nil);
      case lseg_cons{L}:
        \forall node *from, *to, \list<node *> s;
          from != to ==> \valid(from) ==> !mem(from, s) ==>
          lseg{L}(from->next, to, s) ==> lseg{L}(from, to, \Cons(from, s));
    }

    predicate disjoint(\list<node *> a, \list<node *> b) =
      \forall integer i, j; 0 <= i < \length(a) ==> 0 <= j < \length(b) ==>
        \nth(a, i) != \nth(b, j);

    // t is a binary tree whose nodes, in preorder, are s; no sharing.
    inductive tree{L}(node *t, \list<node *> s) {
      case tree_leaf{L}: tree{L}(\null, \Nil);
      case tree_node{L}:
        \forall node *t, \list<node *> l, r;
          t != \null ==> \valid(t) ==>
          tree{L}(t->left, l) ==> tree{L}(t->right, r) ==>
          !mem(t, l) ==> !mem(t, r) ==> disjoint(l, r) ==>
          tree{L}(t, \Cons(t, \concat(l, r)));
    }

    // Every key of the tree at t is in [lo, hi], in search-tree order.
    inductive bst{L}(node *t, integer lo, integer hi) {
      case bst_leaf{L}: \forall integer lo, hi; bst{L}(\null, lo, hi);
      case bst_node{L}:
        \forall node *t, integer lo, hi;
          t != \null ==> \valid(t) ==> lo <= t->key <= hi ==>
          bst{L}(t->left, lo, t->key - 1) ==>
          bst{L}(t->right, t->key + 1, hi) ==> bst{L}(t, lo, hi);
    }

    predicate bst_tree{L}(node *t, integer lo, integer hi) =
      (\exists \list<node *> s; tree(t, s)) && bst(t, lo, hi);

    predicate seg_to_null{L}(node *h) =
      \exists \list<node *> s; lseg(h, \null, s) && \length(s) <= 1000;
*/
