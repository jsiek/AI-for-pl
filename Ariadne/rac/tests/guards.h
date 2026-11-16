/* Types of the review regression fixture (guards.c): two list element
   types, and a struct with an array field. */
#ifndef GUARDS_H
#define GUARDS_H
#include "shapes.h"
typedef struct pair {
  int v;
  struct pair *nx;
} pair;
typedef struct arr4 {
  int a[4];
} arr4;
#endif
