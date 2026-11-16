"""Verification refactor #1 (../CHANGES.md): sglib.h with the doubly
linked list's it_next calling the subcomparator in a statement of its
own, so that WP's `calls` annotation can attach to each indirect call.

   usage: python3 -I it_next_calls.py SGLIB_H OUT_H

Exactly two lines of SGLIB_DEFINE_DL_LIST_FUNCTIONS change, the two
search loops of it_next; each must occur once (the singly linked list's
it_next, at another indentation, is left alone):

    while (ce!=NULL && scp(eq, ce)!=0) ce = ce->previous;
 -> while (ce!=NULL) { if (scp(eq, ce)==0) break; ce = ce->previous; }

    while (ce!=NULL && scp(ce, eq)!=0) ce = ce->next;
 -> while (ce!=NULL) { if (scp(ce, eq)==0) break; ce = ce->next; }

Both evaluate the same expressions in the same order: test ce, call the
comparator only if ce is not NULL, stop when it returns 0, otherwise
step."""
import sys

CHANGES = [
    ("     while (ce!=NULL && scp(eq, ce)!=0) ce = ce->previous;\\\n",
     "     while (ce!=NULL) { if (scp(eq, ce)==0) break; "
     "ce = ce->previous; }\\\n"),
    ("       while (ce!=NULL && scp(ce, eq)!=0) ce = ce->next;\\\n",
     "       while (ce!=NULL) { if (scp(ce, eq)==0) break; "
     "ce = ce->next; }\\\n"),
]
s = open(sys.argv[1]).read()
for old, new in CHANGES:
    if s.count(old) != 1:
        sys.exit(f"it_next_calls.py: expected once: {old!r}")
    s = s.replace(old, new)
open(sys.argv[2], "w").write(s)
