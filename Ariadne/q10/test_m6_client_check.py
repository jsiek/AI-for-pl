"""Tests of m6.check on a client (needs the VST image; a few minutes):
lib_client1.v (the library proof over client 1's program) compiles; a
Gprog with the frozen library funspecs at Rc_client passes the Gprog
check (prog_correct is Admitted here, so it is OPEN); a Gprog that
gives it_next the frozen funspec at another Rc fails it.

    python3 test_m6_client_check.py
"""
import os
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import m6  # noqa: E402

STUB = """\
Require Import VST.floyd.proofauto.
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

fails = []


def expect(name, cond, detail=""):
    print(("ok  " if cond else "FAIL") + f" {name}")
    if not cond:
        fails.append(name)
        print("    " + str(detail)[:1500])


def case(tmp, label, rc):
    run = os.path.join(tmp, "client1-" + label)
    os.makedirs(run)
    m6.setup(run, "client1")
    open(os.path.join(run, "verif_client1.v"), "w").write(
        STUB.replace("RC", rc))
    s = m6.check(run, "client1")
    log = os.path.join(run, "m6-check", "control", "check_prog_correct.v.log")
    s["log"] = open(log).read()[-1500:] if os.path.exists(log) else ""
    return s


tmp = tempfile.mkdtemp(prefix="test_m6_client_check_")
try:
    s = case(tmp, "good", "Rc_client")
    expect("good: compiles (lib_client1.v included)",
           not any(s.get("compile", {"x": 1}).values())
           and "lib" in s["compile"], s)
    expect("good: Gprog check passes; prog_correct is OPEN (Admitted)",
           s.get("lemmas", {}).get("prog_correct", "").startswith("OPEN"),
           s)
    s = case(tmp, "bad", "(fun _ _ => FF)")
    expect("bad: it_next at another Rc fails the Gprog check",
           s.get("lemmas", {}).get("prog_correct")
           == "MISSING OR WRONG STATEMENT"
           # the semax_prog statement checked; a find_id goal failed
           and "semax_prog prog tt" in s["log"], s)
finally:
    shutil.rmtree(tmp, ignore_errors=True)
print("FAILED: %s" % fails if fails else "all passed")
sys.exit(1 if fails else 0)
