"""Tests of the guardrail checks (guardrails.py), each with a deliberately
bad input next to a good one.  No model calls; the overlay and allow-list
tests run Frama-C and coqc/coqchk in the M0 image.

    python3 test_guardrails.py [--quick]     (--quick: the image only for
                                              cpp, to expand b1.c's spec
                                              templates)
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import guardrails as g  # noqa: E402

ARIADNE = g.ARIADNE
B1 = os.path.join(ARIADNE, "bench", "b1", "b1.c")
GOAL = os.path.join(ARIADNE, "bench", "b1", "session", "interactive",
                    "lemma_mem_cons.v")
fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:800].replace("\n", "\n    "))


def edit(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


CPP = "-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec"
raw = open(B1).read()
# b1.c writes its spec with the templates of bench/sglib_spec; the
# textual checks below run on the expanded text, as spec_checks does.
base = g.expand(raw, CPP)

# ---- macro expansion (acsl_expand.py) -------------------------------------
expect("expand: same line count, C code unchanged",
       base.count("\n") == raw.count("\n")
       and g.strip_annotations(base).split() ==
       g.strip_annotations(raw).split())
expect("expand: the template's predicates appear",
       "inductive dll{L}(dllist *prev" in base
       and "SGLIB_DL_LIST_SPEC" not in base)
v = g.spec_checks(raw, raw, CPP)
expect("spec_checks: unchanged b1.c passes",
       all(x["ok"] for x in v.values()), v)
v = g.spec_checks(raw, edit(raw, "#include \"sglib_dl_list_spec.h\"\n",
                            "#include \"sglib_dl_list_spec.h\"\n"
                            "#define live(p) \\true\n"), CPP)
expect("spec_checks: a #define that changes a predicate rejected",
       not v["frozen_spec"]["ok"]
       and "predicate:live" not in v["frozen_spec"]["changed"]
       and v["frozen_spec"]["changed"], v)
v = g.spec_checks(raw, edit(raw, "SGLIB_DL_LIST_CONTRACT_ADD(dllist, "
                            "ptr_to_previous, ptr_to_next, i)",
                            "SGLIB_DL_LIST_CONTRACT_ADD(dllist, "
                            "ptr_to_previous, ptr_to_previous, i)"), CPP)
expect("spec_checks: a changed template argument rejected",
       v["frozen_spec"]["changed"] == ["contract:sglib_dllist_add"], v)
v = g.spec_checks(raw, edit(raw, "SGLIB_DL_LIST_CONTRACT_ADD(", "("), CPP)
expect("spec_checks: a broken invocation rejected",
       not v["frozen_spec"]["ok"], v)

# ---- 7.2 frozen spec ----------------------------------------------------
v = g.frozen(base, base)
expect("frozen: unchanged file passes", v["ok"] and v["items"] == 18, v)
v = g.frozen(base, edit(base, " requires live(elem);",
                        " requires live(elem) || elem == \\null;"))
expect("frozen: weakened requires of add rejected",
       not v["ok"] and v["changed"] == ["contract:sglib_dllist_add"], v)
v = g.frozen(base, edit(base, " ensures \\initialized(list);", ""))
expect("frozen: dropped ensures rejected",
       not v["ok"] and v["changed"] == ["contract:sglib_dllist_add"], v)
v = g.frozen(base, edit(
    base, "\\exists integer k; 0 <= k < \\length(s) && \\nth(s, k) == p;",
    "\\exists integer k; 0 <= k <= \\length(s) && \\nth(s, k) == p;"))
expect("frozen: changed predicate mem rejected",
       not v["ok"] and v["changed"] == ["predicate:mem"], v)
v = g.frozen(base, edit(
    base, " lemma all_live_nil{L}: all_live(\\Nil);",
    " lemma all_live_nil{L}: all_live(\\Nil);\n"
    "    predicate helper(dllist *p) = p != \\null;"))
expect("frozen: added predicate rejected",
       not v["ok"] and v["added"] == ["predicate:helper"], v)
v = g.frozen(base, edit(
    base, " lemma all_live_nil{L}: all_live(\\Nil);",
    " lemma all_live_nil{L}: all_live(\\Nil);\n"
    "    // a helper lemma\n"
    "    lemma mem_nil: \\forall dllist *x; !mem(x, \\Nil);"))
expect("frozen: added lemma allowed (lemmas are proved)", v["ok"], v)
v = g.frozen(base, edit(base, " predicate live{L}(",
                        " // a node we can use\n predicate live{L}("))
expect("frozen: changed ACSL comment allowed", v["ok"], v)
v = g.frozen(base, edit(base, "/*@ requires 0 <= n &&",
                        "/*@ requires \\false;\n    requires 0 <= n &&"))
expect("frozen: `requires \\false` on b1 rejected",
       not v["ok"] and v["changed"] == ["contract:b1"], v)

# ---- 7.3 / 7.3a ACSL lint -----------------------------------------------
v = g.lint_acsl(base, base)
expect("lint_acsl: unchanged file passes", v["ok"], v)
ax = edit(base, " lemma all_live_nil{L}: all_live(\\Nil);",
          " lemma all_live_nil{L}: all_live(\\Nil);\n"
          "    axiomatic Cheat { axiom cheat: \\false; }")
v = g.lint_acsl(base, ax)
expect("lint_acsl: added axiomatic + axiom rejected",
       not v["ok"] and v["added"].get("axiom") == 1
       and v["added"].get("axiomatic") == 1, v)
expect("frozen: added axiomatic rejected too",
       "axiomatic:Cheat" in g.frozen(base, ax)["added"])
v = g.lint_acsl(base, edit(base,
                           "  //@ assert live_dll(\\null, the_list, \\Nil);",
                           "  //@ admit live_dll(\\null, the_list, \\Nil);"))
expect("lint_acsl: admit rejected",
       not v["ok"] and v["added"] == {"admit": 1}, v)
v = g.lint_acsl(base, edit(base, " lemma all_live_nil{L}:",
                           "    logic integer bad(integer n) = bad(n) + 1;\n"
                           "    lemma all_live_nil{L}:"))
expect("lint_acsl: added logic definition rejected (bad_def)",
       not v["ok"] and v["added"] == {"logic": 1}, v)
v = g.lint_acsl(base, edit(base,
                           "  //@ assert live_dll(\\null, the_list, \\Nil);",
                           "  //@ assert live_dll(\\null, the_list, \\Nil);\n"
                           "  //@ assert \\true;"))
expect("lint_acsl: added assert allowed", v["ok"], v)

# ---- 7.3 ghost code ---------------------------------------------------
ANCHOR = "  //@ assert live_dll(\\null, the_list, \\Nil);"
for name, ghost in (("ghost loop", "//@ ghost while (1) ;"),
                    ("ghost write of __heap", "//@ ghost __heap = 0;"),
                    ("ghost call", "//@ ghost ariadne_free_dllist(l);"),
                    ("ghost return", "//@ ghost return 0;"),
                    ("parenthesised ghost call",
                     "/*@ ghost int x; (sglib_dllist_get_first)(l); */"),
                    ("ghost call through a pointer",
                     "/*@ ghost (*sglib_dllist_get_first)(l); */")):
    v = g.lint_ghost(base, edit(base, ANCHOR, ANCHOR + "\n  " + ghost))
    expect(f"lint_ghost: {name} rejected", not v["ok"], v)
v = g.lint_ghost(base, edit(base, ANCHOR, ANCHOR + "\n  //@ ghost int gk = 0;"
                            "\n  //@ ghost gk = gk + 1;"))
expect("lint_ghost: ghost declaration and assignment allowed", v["ok"], v)

# ---- 7.1 overlay (textual part; Frama-C part below) ------------------------
s = g.strip_annotations("int f(int *p) { /*@ ghost int g = 0; */ //@ assert p;\n"
                        "  return *p; /* plain */ }")
expect("strip: ghost code and asserts removed, comments kept",
       "ghost" not in s and "assert" not in s and "return *p;" in s, s)

# ---- 7.3 Coq lint -------------------------------------------------------------
tmp = tempfile.mkdtemp(dir=os.path.join(ARIADNE, "runs"), prefix="test_")
text = open(GOAL).read()
prefix, script, suffix = g.split_goal(text)


def goal_file(name, body):
    p = os.path.join(tmp, name)
    open(p, "w").write(body)
    return p


v = g.lint_coq(goal_file("good.v", text), prefix)
expect("lint_coq: B1's proof of mem_cons passes", v["ok"], v)
for bad in ["\nAdmitted.\n", "\nintros. admit.\n",
            "\nAxiom cheat : False.\nexfalso; exact cheat.\n",
            "\nParameter p : nat.\n"]:
    p = goal_file("bad.v", prefix + bad + "Qed.\n")
    v = g.lint_coq(p, prefix)
    expect(f"lint_coq: {bad.strip()[:24]!r} rejected", not v["ok"], v)
cheat_prefix = prefix.replace("(* Why3 goal *)",
                              "Axiom cheat : False.\n\n(* Why3 goal *)")
v = g.lint_coq(goal_file("ctx.v", cheat_prefix + "\nexfalso; exact cheat.\n"
                         "Qed.\n"), prefix)
expect("lint_coq: axiom added to the context rejected",
       not v["ok"] and "context" in v.get("error", ""), v)

# ---- 7.4 allow-list (unit) -----------------------------------------------------
wp = {"Goals.m": g.wp_axioms(prefix)}
v = g.allow_list(["Goals.m.nth_cons", "Stdlib.Logic.Classical_Prop.classic"],
                 wp)
expect("allow_list: WP context + classical axioms pass", v["ok"], v)
v = g.allow_list(["Goals.m.nth_cons", "Goals.m.cheat",
                  "Stdlib.Logic.ProofIrrelevance."
                  "proof_irrelevance"], wp)
expect("allow_list: unknown axioms rejected",
       not v["ok"] and len(v["not_allowed"]) == 2, v)

# ---- 7.5 goal accounting -----------------------------------------------------
goals = [{"goal": "a", "pass": "f", "discharger": "qed"},
         {"goal": "b", "pass": "f", "discharger": "smt:Alt-Ergo"},
         {"goal": "c", "pass": "l", "discharger": "coq"}]
v = g.accounting(goals, {"f": 2, "l": 1}, (), {"c"})
expect("accounting: all proved, counts right", v["ok"], v)
v = g.accounting(goals + [{"goal": "d", "pass": "f",
                           "discharger": "open"}], {"f": 3, "l": 1})
expect("accounting: open goal rejected",
       not v["ok"] and v["unproved"] == ["d"], v)
v = g.accounting(goals + [{"goal": "d", "pass": "f",
                           "discharger": "open"}], {"f": 3, "l": 1}, ["d"])
expect("accounting: open goal marked out of scope passes", v["ok"], v)
v = g.accounting(goals[:1], {"f": 2, "l": 1})
expect("accounting: shrunken selection rejected",
       not v["ok"] and v["wrong_counts"] == ["f", "l"], v)
v = g.accounting(goals, {"f": 2, "l": 1}, (), set())
expect("accounting: Coq goal without a certified script rejected",
       not v["ok"] and v["coq_uncertified"] == ["c"], v)

# ---- with the image: overlay and coqchk -----------------------------------------
if "--quick" not in sys.argv:
    log = os.path.join(tmp, "overlay.log")
    cpp = CPP
    v = g.overlay(tmp, base, base, cpp, log)
    expect("overlay: unchanged file passes", v["ok"], v)
    ann = edit(base, "    l->i = input[k];",
               "    l->i = input[k];\n    //@ assert l->i == input[k];\n"
               "    /*@ ghost int g = k; */")
    v = g.overlay(tmp, base, ann, cpp, log)
    expect("overlay: added assert and ghost code pass", v["ok"], v)
    v = g.overlay(tmp, base, edit(base, "    l->i = input[k];",
                                  "    l->i = input[k] + 1;"), cpp, log)
    expect("overlay: changed C statement rejected",
           not v["ok"] and "+ 1" in v.get("edited", ""), v)
    v = g.overlay(tmp, base, edit(base, "dllist *l = NULL,", "dllist *l,"),
                  cpp, log)
    expect("overlay: dropped initialiser rejected", not v["ok"], v)

    # coqchk on a goal file whose context gained an axiom: the proof is
    # accepted by coqc, and only the allow-list catches it.
    cert = os.path.join(tmp, "cert")
    os.makedirs(cert)
    open(os.path.join(cert, "cheat.v"), "w").write(
        cheat_prefix + "\nexfalso; exact cheat.\nQed.\n")
    inner = "/ariadne/" + os.path.relpath(cert, ARIADNE)
    why3 = "/home/rocq/.opam/4.14.2/lib/why3/coq"
    r = subprocess.run(
        [g.RUN, "sh", "-c", f"cd {inner} && coqc -native-compiler no "
         f"-R {why3} Why3 -Q . Goals cheat.v && coqchk -silent -o -R "
         f"{why3} Why3 -Q . Goals Goals.cheat"],
        capture_output=True, text=True)
    axioms = g.coqchk_axioms(r.stdout + r.stderr)
    expect("coqchk: lists the axioms", axioms and "Goals.cheat.cheat" in
           axioms, (r.stdout + r.stderr)[-1500:])
    v = g.allow_list(axioms or [], {"Goals.cheat": g.wp_axioms(prefix)})
    expect("allow_list: coqchk's extra axiom rejected",
           not v["ok"] and v["not_allowed"] == ["Goals.cheat.cheat"], v)

shutil.rmtree(tmp)
print(f"{'FAIL' if fails else 'PASS'}: {len(fails)} failed")
sys.exit(1 if fails else 0)
