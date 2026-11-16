"""An interpreter for nu-cancel-id, mirroring Reduction.agda rule by rule,
with the elaboration of System F (type application -> nu, conversion
reveal 0 C) and a printer in named notation."""

# ---------------------------------------------------------------- types
# ('var', i) | ('Int',) | ('Bool',) | ('fun', A, B) | ('all', A, name)

def rename_ty(r, T):
    t = T[0]
    if t == 'var': return ('var', r(T[1]))
    if t in ('Int', 'Bool'): return T
    if t == 'fun': return ('fun', rename_ty(r, T[1]), rename_ty(r, T[2]))
    if t == 'all':
        return ('all', rename_ty(lambda a: 0 if a == 0 else r(a - 1) + 1,
                                 T[1]), T[2])
    raise ValueError(T)

def shift_ty(d, c, T):
    return rename_ty_cut(d, c, T)

def rename_ty_cut(d, c, T):
    t = T[0]
    if t == 'var': return ('var', T[1] + d if T[1] >= c else T[1])
    if t in ('Int', 'Bool'): return T
    if t == 'fun':
        return ('fun', rename_ty_cut(d, c, T[1]), rename_ty_cut(d, c, T[2]))
    return ('all', rename_ty_cut(d, c + 1, T[1]), T[2])

def subst_ty(j, S, T):
    """T[j := S], S closed at the level of j (shifted as we go)."""
    t = T[0]
    if t == 'var':
        i = T[1]
        if i == j: return shift_ty(j, 0, S)
        return ('var', i - 1) if i > j else T
    if t in ('Int', 'Bool'): return T
    if t == 'fun': return ('fun', subst_ty(j, S, T[1]), subst_ty(j, S, T[2]))
    return ('all', subst_ty(j + 1, S, T[1]), T[2])

# ---------------------------------------------------------------- source
# ('var', i) | ('const', v, ty) | ('lam', x, A, N) | ('app', L, M)
# | ('Lam', X, N) | ('tapp', L, A)

def erase(T):
    if T[0] == 'fun': return ('fun', erase(T[1]), erase(T[2]))
    if T[0] == 'all': return ('all', erase(T[1]))
    return T

def infer(G, M):
    t = M[0]
    if t == 'var': return G[M[1]]
    if t == 'const': return (M[2],)
    if t == 'lam': return ('fun', M[2], infer([M[2]] + G, M[3]))
    if t == 'app':
        F = infer(G, M[1]); A = infer(G, M[2])
        assert F[0] == 'fun' and erase(F[1]) == erase(A), (F, A)
        return F[2]
    if t == 'Lam':
        return ('all', infer([shift_ty(1, 0, T) for T in G], M[2]), M[1])
    if t == 'tapp':
        F = infer(G, M[1]); assert F[0] == 'all', F
        return subst_ty(0, M[2], F[1])
    raise ValueError(M)

def reveal(X, T):
    t = T[0]
    if t == 'var': return 'unseal' if T[1] == X else 'id'
    if t in ('Int', 'Bool'): return 'id'
    if t == 'fun': return ('fun', conceal(X, T[1]), reveal(X, T[2]))
    return ('all', reveal(X + 1, T[1]), T[2])

def conceal(X, T):
    t = T[0]
    if t == 'var': return 'seal' if T[1] == X else 'id'
    if t in ('Int', 'Bool'): return 'id'
    if t == 'fun': return ('fun', reveal(X, T[1]), conceal(X, T[2]))
    return ('all', conceal(X + 1, T[1]), T[2])

def elab(G, M):
    t = M[0]
    if t in ('var', 'const'): return M
    if t == 'lam': return ('lam', M[1], M[2], elab([M[2]] + G, M[3]))
    if t == 'app': return ('app', elab(G, M[1]), elab(G, M[2]))
    if t == 'Lam':
        return ('Lam', M[1], elab([shift_ty(1, 0, T) for T in G], M[2]))
    if t == 'tapp':
        F = infer(G, M[1])
        return ('nu', F[2], M[2], elab(G, M[1]), reveal(0, F[1]))
    raise ValueError(M)

# ---------------------------------------------------------------- target
# ('var', i) | ('const', v, ty) | ('lam', x, A, N) | ('app', L, M)
# | ('Lam', X, N) | ('nu', X, A, L, c) | ('bnd', s, a, M, c)
# conversions: 'id' | ('fun', c, d) | ('all', c, name) | 'seal' | 'unseal'

def ren(r, M):
    t = M[0]
    if t in ('var', 'const'): return M
    if t == 'lam': return ('lam', M[1], M[2], ren(r, M[3]))
    if t == 'app': return ('app', ren(r, M[1]), ren(r, M[2]))
    if t == 'Lam':
        return ('Lam', M[1], ren(lambda a: 0 if a == 0 else r(a - 1) + 1,
                                 M[2]))
    if t == 'nu': return ('nu', M[1], M[2], ren(r, M[3]), M[4])
    if t == 'bnd': return ('bnd', M[1], r(M[2]), ren(r, M[3]), M[4])
    raise ValueError(M)

suc = lambda a: a + 1

def crossL(V): return ('bnd', '-', 0, ren(suc, V), 'id')

def subst(j, V, M):
    t = M[0]
    if t == 'var':
        x = M[1]
        if x == j: return V
        return ('var', x - 1) if x > j else M
    if t == 'const': return M
    if t == 'lam': return ('lam', M[1], M[2], subst(j + 1, V, M[3]))
    if t == 'app': return ('app', subst(j, V, M[1]), subst(j, V, M[2]))
    if t == 'Lam': return ('Lam', M[1], subst(j, crossL(V), M[2]))
    if t == 'nu': return ('nu', M[1], M[2], subst(j, V, M[3]), M[4])
    if t == 'bnd': return M
    raise ValueError(M)

def is_fun(M):
    t = M[0]
    if t in ('lam', 'Lam'): return True
    if t != 'bnd': return False
    _, s, a, V, c = M
    if c != 'id' and c[0] in ('fun', 'all'): return is_value(V)
    if c == 'id' and s == '+': return is_fun(V)
    if c == 'id' and s == '-':
        if V[0] == 'bnd' and V[1] == '+' and V[2] == a and V[4] == 'id':
            return False
        return is_fun(V)
    return False

def is_sealed(M):
    if M[0] != 'bnd': return False
    _, s, a, V, c = M
    if s == '-' and c == 'seal': return is_value(V)
    if s == '+' and c == 'id': return is_sealed(V)
    return False

def is_value(M):
    return M[0] == 'const' or is_fun(M) or is_sealed(M)

def inst(V):
    if V[0] == 'Lam': return V[2]
    if V[0] == 'bnd':
        _, s, a, W, c = V
        if c == 'id': return ('bnd', s, a + 1, inst(W), 'id')
        if c[0] == 'all': return ('bnd', s, a + 1, inst(W), c[1])
    raise ValueError('inst', V)

def spell(flags, A):
    t = A[0]
    if t == 'var':
        X = A[1]
        for a, f in enumerate(flags):
            if f:
                if X == 0: return ('var', a)
                X -= 1
        raise ValueError('unbound name', A, flags)
    if t in ('Int', 'Bool'): return A
    if t == 'fun': return ('fun', spell(flags, A[1]), spell(flags, A[2]))
    return ('all', spell([True] + flags, A[1]), A[2])

def set_flag(flags, a, b):
    f = list(flags); f[a] = b; return f

def up(alloc, M): return M if alloc is None else ren(suc, M)

class Stuck(Exception): pass

def step(flags, M):
    """returns (M', alloc, rule); alloc is None or (name, payload)"""
    t = M[0]
    if t == 'app':
        L, N = M[1], M[2]
        if not is_value(L):
            L2, al, r = step(flags, L)
            return ('app', L2, up(al, N)), al, r
        if not is_value(N):
            N2, al, r = step(flags, N)
            return ('app', up(al, L), N2), al, r
        if L[0] == 'lam': return subst(0, N, L[3]), None, 'Beta'
        if L[0] == 'bnd':
            _, s, a, V, c = L
            fs = '-' if s == '+' else '+'
            if c == 'id':
                return (('bnd', s, a, ('app', V, ('bnd', fs, a, N, 'id')),
                         'id'), None, 'Wrap-id')
            if c[0] == 'fun':
                return (('bnd', s, a, ('app', V, ('bnd', fs, a, N, c[1])),
                         c[2]), None, 'Wrap')
        raise Stuck(M)
    if t == 'nu':
        _, X, A, L, c = M
        if not is_value(L):
            L2, al, r = step(flags, L)
            return ('nu', X, A, L2, c), al, r
        P = spell(flags, A)
        return ('bnd', '+', 0, inst(L), c), (X, P), 'TyBeta'
    if t == 'bnd':
        _, s, a, V, c = M
        if not is_value(V):
            inner = set_flag(flags, a, s == '+')
            V2, al, r = step(inner, V)
            return ('bnd', s, a if al is None else a + 1, V2, c), al, r
        if c == 'id' and V[0] == 'const': return V, None, 'Id'
        if V[0] == 'bnd':
            _, s2, b, W, c2 = V
            if s == '+' and c == 'unseal':
                if s2 == '-' and b == a and c2 == 'seal':
                    return W, None, 'Cancel-□'
                if s2 == '+' and c2 == 'id' and is_sealed(W):
                    return (('bnd', '+', b, ('bnd', '+', a, W, 'unseal'),
                             'id'), None, 'Push')
            if s == '-' and c == 'id':
                if s2 == '+' and b == a and c2 == 'id':
                    return W, None, 'CancelId'
                if s2 == '-' and b != a and c2 == 'seal':
                    return (('bnd', '-', b, ('bnd', '-', a, W, 'id'),
                             'seal'), None, 'Sink')
                if s2 == '+' and b != a and c2 == 'id' and is_sealed(W):
                    return (('bnd', '+', b, ('bnd', '-', a, W, 'id'),
                             'id'), None, 'Swap')
        raise Stuck(M)
    raise Stuck(M)

# ---------------------------------------------------------------- printing
GREEK = 'αβγδκλμπσ'
LGREEK = 'ζηθικ'

def show_ty_named(T, cells, binders=()):
    """named type; cells: list of (letter, greek, flag) newest first"""
    t = T[0]
    if t == 'var':
        X = T[1]
        for (l, g, f) in cells:
            if f:
                if X == 0: return l
                X -= 1
        return '?%d' % T[1]
    if t in ('Int', 'Bool'): return t
    if t == 'fun':
        A = show_ty_named(T[1], cells)
        if T[1][0] in ('fun', 'all'): A = '(' + A + ')'
        return A + ' → ' + show_ty_named(T[2], cells)
    return '∀' + T[2] + '. ' + show_ty_named(T[1], [(T[2], None, True)]
                                              + cells)

def show_rt(T, cells):
    """runtime type over the store"""
    t = T[0]
    if t == 'var':
        l, g, f = cells[T[1]]
        return g if g else l
    if t in ('Int', 'Bool'): return t
    if t == 'fun':
        A = show_rt(T[1], cells)
        if T[1][0] in ('fun', 'all'): A = '(' + A + ')'
        return A + ' → ' + show_rt(T[2], cells)
    return '∀' + T[2] + '. ' + show_rt(T[1], [(T[2], None, True)] + cells)

def show_conv(c, X):
    if c == 'id': return 'id'
    if c == 'seal': return '−' + X
    if c == 'unseal': return '+' + X
    if c[0] == 'fun':
        a = show_conv(c[1], X)
        if c[1] != 'id' and not isinstance(c[1], str): a = '(' + a + ')'
        b = show_conv(c[2], X)
        if not isinstance(c[2], str) and c[2][0] == 'fun': b = '(' + b + ')'
        return a + ' → ' + b
    return '∀' + c[2] + '. ' + show_conv(c[1], X)

class Printer:
    def __init__(self): self.lam_count = 0

    def show(self, M, cells, xs, ctx='top'):
        t = M[0]
        if t == 'var': return xs[M[1]]
        if t == 'const':
            v = M[1]
            return ('true' if v else 'false') if isinstance(v, bool) else str(v)
        if t == 'lam':
            s = 'λ%s:%s. %s' % (M[1], show_ty_named(M[2], cells),
                                self.show(M[3], cells, [M[1]] + xs))
            return '(' + s + ')' if ctx in ('fun', 'arg', 'body') else s
        if t == 'Lam':
            g = LGREEK[self.lam_count % len(LGREEK)]; self.lam_count += 1
            s = 'Λ%s^%s. %s' % (M[1], g, self.show(
                M[2], [(M[1], g, True)] + cells, xs))
            return '(' + s + ')' if ctx in ('fun', 'arg', 'body') else s
        if t == 'app':
            s = self.show(M[1], cells, xs, 'fun') + ' ' + \
                self.show(M[2], cells, xs, 'arg')
            return '(' + s + ')' if ctx in ('arg', 'body') else s
        if t == 'nu':
            _, X, A, L, c = M
            s = 'ν %s:=%s. (%s %s)⟨%s⟩' % (
                X, show_ty_named(A, cells), self.show(L, cells, xs, 'fun'),
                X, show_conv(c, X))
            return '(' + s + ')' if ctx in ('fun', 'arg', 'body') else s
        if t == 'bnd':
            # flatten a tower
            entries, convs, body = [], [], M
            cs = cells
            while body[0] == 'bnd':
                _, s, a, V, c = body
                l, g, f = cs[a]
                entries.append('[%s%s^%s]' % ('+' if s == '+' else '−', l, g))
                convs.append(show_conv(c, l))
                cs = list(cs); cs[a] = (l, g, s == '+')
                body = V
            inner = self.show(body, cs, [], 'body')
            s = ' '.join(entries) + ' ' + inner + ' ' + \
                ' '.join('⟨%s⟩' % c for c in reversed(convs))
            return '(' + s + ')' if ctx == 'arg' else s
        raise ValueError(M)

def run(src, max_steps=200, quiet=False):
    T = infer([], src)
    M = elab([], src)
    flags, cells = [], []   # global store: cells (letter, greek, flag=False)
    out = []
    pr = Printer()
    out.append(('source type', show_ty_named(T, [])))
    out.append(('elaborate', pr.show(M, cells, [])))
    n = 0
    while not is_value(M):
        M, al, r = step(flags, M)
        n += 1
        note = ''
        if al is not None:
            X, P = al
            g = GREEK[len(cells)]
            note = '   ⊣ %s^%s:=%s' % (g, X, show_rt(P, cells))
            cells = [(X, g, False)] + cells
            flags = [False] + flags
        pr = Printer()
        out.append((r, pr.show(M, cells, []) + note))
        if n > max_steps: raise RuntimeError('too many steps')
    return out, n

def show_run(name, src):
    out, n = run(src)
    print('=== %s (%d steps)' % (name, n))
    for r, s in out:
        print('%-10s %s' % (r, s))
    print()

# ---------------------------------------------------------------- examples
V = lambda i: ('var', i)
INT, BOOL = ('Int',), ('Bool',)
def lam(x, A, N): return ('lam', x, A, N)
def app(*ms):
    m = ms[0]
    for n in ms[1:]: m = ('app', m, n)
    return m
def Lam(X, N): return ('Lam', X, N)
def tapp(L, A): return ('tapp', L, A)
def fun(A, B): return ('fun', A, B)
def all_(X, A): return ('all', A, X)
def tv(i): return ('var', i)
def num(n): return ('const', n, 'Int')
def boo(b): return ('const', b, 'Bool')

# 5a: ((ΛX. λf:∀Y. Y→Bool. f [X]) [Bool] (ΛZ. λz:Z. true)) false
ex5a = app(tapp(Lam('X', lam('f', all_('Y', fun(tv(0), BOOL)),
                             tapp(V(0), tv(0)))), BOOL),
           Lam('Z', lam('z', tv(0), boo(True))), boo(False))

# 5b: ((ΛX. λf:∀Y. Y→Y. f [X]) [Bool] (ΛZ. λz:Z. z)) false
ex5b = app(tapp(Lam('X', lam('f', all_('Y', fun(tv(0), tv(0))),
                             tapp(V(0), tv(0)))), BOOL),
           Lam('Z', lam('z', tv(0), V(0))), boo(False))

# 5c: (ΛX. λx:X. (ΛY. λ_:Int. x) [Bool] 0) [Int] 3
ex5c = app(tapp(Lam('X', lam('x', tv(0),
                             app(tapp(Lam('Y', lam('_', INT, V(1))), BOOL),
                                 num(0)))), INT),
           num(3))

# 5d: ((ΛX. λx:X. λg:(Int→X)→(Int→Int). g (λn:Int. x)) [Int] 5 (λh:Int→Int. h)) 0
ex5d = app(tapp(Lam('X', lam('x', tv(0),
                             lam('g', fun(fun(INT, tv(0)), fun(INT, INT)),
                                 app(V(0), lam('n', INT, V(2)))))), INT),
           num(5), lam('h', fun(INT, INT), V(0)), num(0))

# 5e: ((ΛX. λf:∀Y. Y→Y. f [X]) [Bool] (ΛZ. (ΛW. λz:Z. z) [Bool])) false
ex5e = app(tapp(Lam('X', lam('f', all_('Y', fun(tv(0), tv(0))),
                             tapp(V(0), tv(0)))), BOOL),
           Lam('Z', tapp(Lam('W', lam('z', tv(1), V(0))), BOOL)), boo(False))

if __name__ == '__main__':
    import sys
    exs = dict(a=ex5a, b=ex5b, c=ex5c, d=ex5d, e=ex5e)
    for k in (sys.argv[1:] or 'abcde'):
        show_run('5' + k, exs[k])
