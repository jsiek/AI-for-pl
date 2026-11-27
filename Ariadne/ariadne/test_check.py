"""Tests of check.py on hand-written proof files standing in for the
prover (needs the VST image; several minutes per case):

  good       sglib's dllist: body_it_init proved by hand
             (test_it_init_proof.txt), the other five stated exactly and
             Admitted: it_init PROVED, the others OPEN, verdict NOT
             PROVED;
  axiom      an `Axiom`: rejected by the keyword lint;
  shadow     body_it_init closed with an Admitted lemma named like a VST
             axiom (`mem_mgr`, Codex on PR #241): it_init OPEN, and
             coqchk names the lemma by its full name;
  spec_edit  body_get_first proved against a weaker funspec of its own:
             its statement fails;
  tt_post    a helper funspec with TT in its postcondition: rejected by
             the leak lint;
  client     client 1 with a stub Gprog: the library entries at
             Rc_client pass (prog_correct is Admitted: OPEN);
  client_rc  the same with it_next at another Rc: the Gprog line fails;
  empty_list an empty proof_files.txt: NOT PROVED with a diagnostic, and
             a manifest (Codex on PR #242), without compiling.

    python3 test_check.py [case ...]
"""
import os
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check  # noqa: E402
import targets  # noqa: E402

FUNCS = [("add", "add_spec", False), ("get_first", "get_first_spec", False),
         ("get_last", "get_last_spec", False),
         ("it_init_on_equal", "it_init_on_equal_spec", True),
         ("it_init", "it_init_spec", False),
         ("it_next", "it_next_spec", True)]
HEAD = """Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.dllist SglibVST.spec_dllist.

Section Proofs.
Variable Rc : globals -> val -> mpred.
"""
IT_INIT = open(os.path.join(HERE, "test_it_init_proof.txt")).read()


def lemma(f, spec, rc, proof="Admitted."):
    sp = "(%s Rc)" % spec if rc else spec
    return ("Lemma body_%s :\n  semax_body Vprog (Gprog Rc) "
            "f_sglib_dllist_%s %s.\n%s\n" % (f, f, sp, proof))


def verif(extra="", overrides=None):
    overrides = overrides or {}
    body = [overrides.get(f, lemma(f, s, r, IT_INIT if f == "it_init"
                                   else "Admitted."))
            for f, s, r in FUNCS]
    return HEAD + extra + "\n".join(body) + "\nEnd Proofs.\n"


WEAK_GET_FIRST = """Definition my_get_first_spec :=
 DECLARE _sglib_dllist_get_first
  WITH p: val
  PRE [ tptr t_dl ] PROP () PARAMS (p) SEP ()
  POST [ tptr t_dl ] PROP () RETURN (p) SEP ().
Lemma body_get_first :
  semax_body Vprog (Gprog Rc) f_sglib_dllist_get_first my_get_first_spec.
Admitted.
"""
TT_HELPER = """Definition helper_spec : funspec :=
  WITH p: val
  PRE [ tptr tint ] PROP () PARAMS (p) SEP ()
  POST [ tvoid ] PROP () RETURN () SEP (TT).
"""
SHADOW = ("Lemma mem_mgr : False.\nAdmitted.\n"
          + lemma("it_init", "it_init_spec", False,
                  "Proof. destruct mem_mgr. Qed."))
CLIENT = """Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import SglibVST.client1 SglibVST.spec_client1.
Require SglibVST.lib_client1.

Definition Rc_client : globals -> val -> mpred := fun _ _ => emp.
#[export] Existing Instance NullExtension.Espec.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] PROP () RETURN (Vint (Int.repr 0)) SEP (mem_mgr gv).

Definition Gprog : funspecs :=
  ltac:(with_library prog [add_spec; get_first_spec; get_last_spec;
                           it_init_on_equal_spec Rc_client; it_init_spec;
                           it_next_spec RC; main_spec]).

Lemma prog_correct : semax_prog prog tt Vprog Gprog.
Admitted.
"""

CASES = {
    "good": ("dllist", verif(), False),
    "axiom": ("dllist", verif(extra="Axiom cheat : False.\n"), False),
    "shadow": ("dllist", verif(overrides={"it_init": SHADOW}), True),
    "spec_edit": ("dllist", verif(overrides={"get_first": WEAK_GET_FIRST}),
                  False),
    "tt_post": ("dllist", verif(extra=TT_HELPER), False),
    "client": ("client1", CLIENT.replace("RC", "Rc_client"), False),
    "client_rc": ("client1", CLIENT.replace("RC", "(fun _ _ => FF)"), False),
    "empty_list": ("dllist", verif(), False),
}


def expect(name, cond, detail):
    print(("ok  " if cond else "FAIL") + " " + name, flush=True)
    if not cond:
        print("    " + repr(detail)[:1500])
    return cond


def main(names):
    fails = 0
    for case in names or list(CASES):
        target, text, coqchk = CASES[case]
        d = os.path.join(targets.ARIADNE, "runs", "test_check", case)
        shutil.rmtree(d, ignore_errors=True)
        os.makedirs(d)
        open(os.path.join(d, targets.load(target)["proof"]), "w").write(text)
        if case == "empty_list":
            open(os.path.join(d, "proof_files.txt"), "w").write("")
        s = check.check(target, d, coqchk=coqchk)
        v, g = s["violations"], s.get("goals", {})
        if case == "good":
            ok = expect("good: it_init PROVED, the other five OPEN",
                        g.get("body_it_init") == "PROVED" and len(
                            [x for x in g.values() if x.startswith("OPEN")])
                        == 5 and s["verdict"] == "NOT PROVED", s)
        elif case == "axiom":
            ok = expect("axiom: rejected by the keyword lint",
                        any("forbidden" in x for x in v), s)
        elif case == "shadow":
            ok = expect("shadow: it_init OPEN (assumes mem_mgr); coqchk "
                        "names SglibVST.verif_dllist.mem_mgr",
                        g.get("body_it_init", "").startswith("OPEN")
                        and "mem_mgr" in g["body_it_init"]
                        and "SglibVST.verif_dllist.mem_mgr" in
                        s["coqchk"]["unexpected"], s)
        elif case == "spec_edit":
            ok = expect("spec_edit: get_first's statement fails",
                        any("not its statement" in x for x in v)
                        and "body_get_first" in s.get("error", ""), s)
        elif case == "tt_post":
            ok = expect("tt_post: rejected by the leak lint",
                        any("post_lint" in x for x in v)
                        and "helper_spec" in s["post_lint"]["out"], s)
        elif case == "empty_list":
            ok = expect("empty_list: NOT PROVED (proof files), manifest written",
                        s["verdict"] == "NOT PROVED"
                        and any("proof files" in x for x in v)
                        and os.path.exists(os.path.join(
                            d, "manifest_dllist.json")), s)
        elif case == "client":
            ok = expect("client: library entries at Rc_client pass; "
                        "prog_correct OPEN",
                        g.get("prog_correct", "").startswith("OPEN"), s)
        else:
            ok = expect("client_rc: it_next at another Rc fails",
                        any("extra line fails" in x for x in v)
                        and "_sglib_dllist_it_next" in s.get("error", ""), s)
        fails += 0 if ok else 1
    print("%s: %d failed" % ("FAIL" if fails else "PASS", fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
