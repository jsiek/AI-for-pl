"""Patches of b1_frozen.c for the offline annotator tests
(test_annotator.py), made from the human's b1.c so they stay in step
with it:

  good          get_first's loop annotations and assert from b1.c, with
                the human's lemmas that SMT proves
  good_full     the same with all eleven of the human's lemmas
  frozen_edit   good, with get_first's precondition weakened
  new_logic     good, plus a new `predicate` (plan 7.3a)
  ghost_loop    good, plus a ghost loop (vacuity through non-termination)
  false_inv     a loop invariant that E-ACSL refutes (step 0 rejects it)
  weak(k)       a different true but useless assert each time (a stall)
"""
import os
import re

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


SPEC = "/*@ // p is a usable list node"


def spec_block(text):
    i = text.index(SPEC)
    return i, text.index("*/\n", i) + 3


def human_lemmas(drop):
    """The human's spec block, without the lemmas named in `drop` (each
    lemma runs to the next declaration, comment or blank line)."""
    i, j = spec_block(human)
    block = human[i:j]
    for n in drop:
        k = block.index(f"    lemma {n}")
        m = re.compile(r"^(    (lemma|predicate|inductive|//)|\s*$|\*/)",
                       re.M).search(block, block.index("\n", k) + 1)
        block = block[:k] + block[m.start():]
    return block


# The human's lemmas that SMT proves (the other five need Coq).
SMT_LEMMAS_DROP = ("mem_cons", "all_live_cons", "all_init_cons",
                   "dll_links", "dll_frame")


def good(drop=SMT_LEMMAS_DROP):
    """frozen-only, with get_first's body as the human annotated it and
    the human's lemmas but those in `drop`."""
    hi, hj = body(human)
    fi, fj = body(frozen)
    text = frozen[:fi] + human[hi:hj] + frozen[fj:]
    i, j = spec_block(text)
    return text[:i] + human_lemmas(drop) + text[j:]


def good_full():
    return good(drop=())


def frozen_edit():
    return edit(good(), "/*@ requires list == \\null || in_live_list(list);"
                "\n    assigns \\nothing;\n    ensures list == \\null ==> "
                "\\result == \\null;\n    // the result heads",
                "/*@ requires \\true;\n    assigns \\nothing;\n    ensures "
                "list == \\null ==> \\result == \\null;\n    // the result "
                "heads")


def new_logic():
    return edit(good(), "/*@ ARIADNE_ALLOC */",
                "/*@ predicate easy(dllist *p) = \\true; */\n"
                "/*@ ARIADNE_ALLOC */")


def ghost_loop():
    return edit(good(), "    (result) = _dll_;\n  };\n  return (result);\n}\n"
                "/*@ requires list == \\null || in_live_list(list);",
                "    //@ ghost while (1) ;\n"
                "    (result) = _dll_;\n  };\n  return (result);\n}\n"
                "/*@ requires list == \\null || in_live_list(list);")


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
