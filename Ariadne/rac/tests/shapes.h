/* Node type of the generality test (shapes.c): one struct for a singly
   linked list (next) and a binary tree (left, right). */
#ifndef SHAPES_H
#define SHAPES_H
typedef struct node {
  int key;
  struct node *next;
  struct node *left;
  struct node *right;
} node;
#endif
