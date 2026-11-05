"""Write the B1 mutants of b1.c into a directory: seven of the driver and
two of add's contract (nowashead, noassign).

   usage: python3 -I mutants.py [b1.c] [outdir]   (defaults: b1.c, mutants)

Used by check.sh (WP must reject each) and rac/check.sh (runtime checking).
Each mutant is a textual edit of b1.c; an edit whose anchor text is not
found exactly once is an error, so a change to b1.c cannot silently
produce an unmutated copy."""
import os
import sys

src_path = sys.argv[1] if len(sys.argv) > 1 else "b1.c"
out = sys.argv[2] if len(sys.argv) > 2 else "mutants"
os.makedirs(out, exist_ok=True)
src = open(src_path).read()


def write(name, text):
    open(os.path.join(out, f"{name}.c"), "w").write(text)


def mutant(name, old, new):
    assert src.count(old) == 1, (name, old)
    write(name, src.replace(old, new))


# The forward walk (the loop after the head_is_node0 assert, which stays
# in place for the backward walk) and the backward walk, each moved after
# the free loop in its own mutant.
assert_start = src.index("  /*@ assert head_is_node0:")
assert_end = "             live_dll(\\null, the_list, \\Cons(the_list, t)); */\n"
fwd_start = src.index(assert_end, assert_start) + len(assert_end)
back_start = src.index("  /*@ loop invariant l == \\null || in_live_list(l);",
                        src.index("sglib_dllist_get_first(the_list)"))
tail = "       l = l->ptr_to_previous)\n    last = l->i;\n"
back_end = src.index(tail, back_start) + len(tail)
mutant("vacuity", "  return last;\n}",
       "  //@ assert vacuity: \\false;\n  return last;\n}")
free_loop_end = ("            && l == \\nth(s, c) ==> iter_at(&it, s, b, f); */"
                 "\n  }\n")
j = src.index(free_loop_end) + len(free_loop_end)


def move_after_free(name, a, b):
    write(name, src[:a] + src[b:j] + src[a:b] + src[j:])


move_after_free("uaf", fwd_start, back_start)
move_after_free("uaf_back", back_start, back_end)
mutant("nullchk", "    if (l == NULL)\n      break;\n", "")


def null_result(name, fun):
    i = src.index(f"dllist *{fun}(dllist *list) {{")
    j = src.index("    (result) = _dll_;", i)
    write(name, src[:j] + "    (result) = NULL;"
          + src[j + len("    (result) = _dll_;"):])


null_result("nullfirst", "sglib_dllist_get_first")
null_result("nulllast", "sglib_dllist_get_last")
mutant("noinit", "    l->i = input[k];\n", "")


# Mutants of add's public contract: the template macro is redefined just
# before its invocation, from the template's own text with one clause
# changed, so the mutant tracks the template.
HERE = os.path.dirname(os.path.abspath(__file__))
HDR = next(p for p in (
    os.path.join(HERE, "..", "sglib_spec", "sglib_dl_list_spec.h"),
    "/ariadne/bench/sglib_spec/sglib_dl_list_spec.h",   # a harness copy
    os.path.join(HERE, "..", "..", "..", "bench", "sglib_spec",
                 "sglib_dl_list_spec.h")) if os.path.exists(p))
hdr = open(HDR).read()
i = hdr.index("#define SGLIB_DL_LIST_CONTRACT_ADD(")
j = hdr.index("\n\n", i)
add_def = hdr[i:j]
ADD_CALL = "/*@ SGLIB_DL_LIST_CONTRACT_ADD(dllist, ptr_to_previous, ptr_to_next) */"


def contract_mutant(name, old, new):
    if ADD_CALL not in src:   # an expanded b1.c (rac/check.sh): skipped
        return
    assert add_def.count(old) == 1, (name, old)
    d = add_def.replace(old, new)
    mutant(name, ADD_CALL, "#undef SGLIB_DL_LIST_CONTRACT_ADD\n" + d + "\n"
           + ADD_CALL)


# was_head dropped: the driver can no longer tell that the new node is
# the head (its assert head_after_add fails).
k = add_def.index("  ensures was_head:")
contract_mutant("nowashead", add_def[k:], "  ensures \\true;")
# elem->previous dropped from assigns: add's assigns clause fails.
contract_mutant("noassign", "elem->next, elem->previous,", "elem->next,")
