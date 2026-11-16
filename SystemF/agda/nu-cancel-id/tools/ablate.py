"""For each boundary rule, the examples that get stuck without it.  The
step relation is deterministic, so a run without a rule stops at the
first state whose only step is that rule."""
import nuc


def run_without(rule, src):
    M = nuc.elab([], src)
    flags, cells, n = [], [], 0
    while not nuc.is_value(M):
        M2, al, r = nuc.step(flags, M)
        if r == rule:
            return 'stuck', n, M, cells
        M, n = M2, n + 1
        if al is not None:
            g = nuc.GREEK[len(cells)]
            cells = [(al[0], g, False)] + cells
            flags = [False] + flags
    return 'value', n, M, cells


exs = dict(a=nuc.ex5a, b=nuc.ex5b, c=nuc.ex5c, d=nuc.ex5d, e=nuc.ex5e)
for rule in ['Cancel-□', 'CancelId', 'Sink', 'Swap', 'Push']:
    for k, src in exs.items():
        res, n, M, cells = run_without(rule, src)
        if res != 'value':
            print('%-9s 5%s stuck after %d steps: %s'
                  % (rule, k, n, nuc.Printer().show(M, cells, [])))
