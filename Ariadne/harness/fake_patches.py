"""Patches of b1_frozen.c for the offline annotator tests
(test_annotator.py), made from the human's b1.c so they stay in step
with it:

  good          get_first's loop annotations and assert from b1.c
  good_full     the same with all eleven of the human's lemmas
  frozen_edit   good, with get_first's precondition weakened
  new_logic     good, plus a new `predicate` (plan 7.3a)
  ghost_loop    good, plus a ghost loop (vacuity through non-termination)
  false_inv     a loop invariant that E-ACSL refutes (step 0 rejects it)
  weak(k)       a different true but useless assert each time (a stall)
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
B1 = os.path.join(os.path.dirname(HERE), "bench", "b1")
human = open(os.path.join(B1, "b1.c")).read()
frozen = open(os.path.join(B1, "b1_frozen.c")).read()

HEAD = "dllist *sglib_dllist_get_first(dllist *list) {"
LOOP = ("      for (; _dll_->ptr_to_previous != NULL; "
        "_dll_ = _dll_->ptr_to_previous)\n        ;\n")


def body(text):
    i = text.index(HEAD)
    return i, text.index("\n}\n", i)


def edit(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


# The spec annotation of b1_frozen.c (spec template, no lemmas) and of
# b1.c (the same with the human's lemmas, SGLIB_DL_LIST_LEMMAS).
ARGS = "dllist, ptr_to_previous, ptr_to_next"
SPEC = f"/*@ SGLIB_DL_LIST_SPEC({ARGS})\n*/"
SPEC_LEMMAS = (f"/*@ SGLIB_DL_LIST_SPEC({ARGS})\n"
               f"    SGLIB_DL_LIST_LEMMAS({ARGS})\n*/")
assert human.count(SPEC_LEMMAS) == 1 and frozen.count(SPEC) == 1

# The human's lemmas that need Coq (open in a run without the Coq
# scripts); SMT proves the other six.
SMT_LEMMAS_DROP = ("mem_cons", "all_live_cons", "all_init_cons",
                   "dll_links", "dll_frame")


def good():
    """frozen-only, with get_first's body as the human annotated it (the
    loop annotations and the assert, as template invocations)."""
    hi, hj = body(human)
    fi, fj = body(frozen)
    return frozen[:fi] + human[hi:hj] + frozen[fj:]


def good_full():
    """good, plus all eleven of the human's lemmas (the template's)."""
    return edit(good(), SPEC, SPEC_LEMMAS)


def frozen_edit():
    """good, with get_first's contract written out and its precondition
    weakened to \\true."""
    return edit(good(), f"/*@ SGLIB_DL_LIST_CONTRACT_GET_FIRST({ARGS}) */",
                "/*@ requires \\true;\n    assigns \\nothing;\n    ensures "
                "list == \\null ==> \\result == \\null;\n    ensures "
                "heads_list: list != \\null ==>\n      \\exists "
                "\\list<dllist *> s, integer k;\n        live_dll(\\null, "
                "\\result, s) && 0 <= k < \\length(s)\n        && "
                "\\nth(s, k) == list;\n*/")


def new_logic():
    return edit(good(), "/*@ ARIADNE_ALLOC */",
                "/*@ predicate easy(dllist *p) = \\true; */\n"
                "/*@ ARIADNE_ALLOC */")


def ghost_loop():
    return edit(good(), "    (result) = _dll_;\n  };\n  return (result);\n}\n"
                "/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(",
                "    //@ ghost while (1) ;\n"
                "    (result) = _dll_;\n  };\n  return (result);\n}\n"
                "/*@ SGLIB_DL_LIST_CONTRACT_GET_LAST(")


def false_inv():
    fi, _ = body(frozen)
    i = frozen.index(LOOP, fi)
    return frozen[:i] + ("      /*@ loop invariant _dll_ != list; "
                         "loop assigns _dll_; */\n") + frozen[i:]


def weak(k):
    fi, _ = body(frozen)
    i = frozen.index(LOOP, fi)
    return frozen[:i] + f"      //@ assert weak_{k}: {k} == {k};\n" \
        + frozen[i:]


def write(d, names):
    """Write the named patches into d and the list file for
    `harness.py --annotator fake:LIST.json`; returns its path."""
    import json
    os.makedirs(d, exist_ok=True)
    out = []
    for n in names:
        if n is None or n == "FENCED":
            out.append(n)
            continue
        f = f"{n}.c"
        text = weak(int(n[4:])) if n.startswith("weak") else globals()[n]()
        open(os.path.join(d, f), "w").write(text)
        out.append(f)
    p = os.path.join(d, "list.json")
    json.dump(out, open(p, "w"))
    return p
