"""Print the Agda for examples 5a, 5d and 5e of Examples.agda: the
abbreviations, the elaborated term, its typing, the run, and the typed
result.  Usage: python3 gen_examples.py 5a 5d 5e"""
import sys
import nuc
import agdagen as g

W5d = ('bnd', '-', 0, ('const', 5, 'Int'), 'seal')

# example: (source, term abbreviations, conversion abbreviations, type)
# a term abbreviation gives a path into the elaborated term, or the term
EX = {
 '5a': (nuc.ex5a, [
    ('F5a', 'λf:(∀Y. Y → Bool). ν Y:=X. (f Y)⟨−Y → id⟩', [1, 1, 3, 2]),
    ('K5a', 'λz:Z. true', [1, 2, 2]),
    ('G5a', 'ΛZ. λz:Z. true', [1, 2])], [], ('Bool',)),
 '5d': (nuc.ex5d, [
    ('F5d', 'λx:X. λg:(Int → X) → Int → Int. g (λn:Int. x)',
     [1, 1, 1, 3, 2]),
    ('H5d', 'λh:Int → Int. h', [1, 2]),
    ('W5d', 'the argument 5, sealed as X', W5d),
    ('N5d', 'λn:Int. 5, with 5 sealed', ('lam', 'n', ('Int',), W5d))],
   [('d5d', '((id → +X) → (id → id)) → (id → id)',
     ('fun', ('fun', ('fun', 'id', 'unseal'), ('fun', 'id', 'id')),
      ('fun', 'id', 'id')))], ('Int',)),
 '5e': (nuc.ex5e, [
    ('F5e', 'λf:(∀Y. Y → Y). ν Y:=X. (f Y)⟨−Y → +Y⟩', [1, 1, 3, 2]),
    ('I5e', 'λz:Z. z, under ΛW', [1, 2, 2, 3, 2]),
    ('G5e', 'ΛZ. ν W:=Bool. ((ΛW. λz:Z. z) W)⟨id → id⟩', [1, 2])],
   [], ('Bool',)),
}

if __name__ == '__main__':
    for k in sys.argv[1:] or sorted(EX):
        src, defs, cdefs, rty = EX[k]
        body, res, n = g.emit(k, src, defs, cdefs, rty)
        print('-- %s (%d steps)\n\n%s\n%s\n' % (k, n, body, res))
