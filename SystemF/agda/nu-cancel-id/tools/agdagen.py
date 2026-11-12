"""Generate Agda for an example run of nu-cancel-id: the elaborated term,
its typing derivation, and the run with every step's derivation."""
import nuc

# ---------------------------------------------------------------- docs
# a doc is a str, ('cat', [docs]), ('line',), ('nest', i, doc),
# ('group', doc).  'line' is a space when its group fits, else a newline.

def cat(*ds): return ('cat', list(ds))
LINE = ('line',)
def nest(i, d): return ('nest', i, d)
def group(d): return ('group', d)

def flat_width(d):
    if isinstance(d, str): return len(d)
    t = d[0]
    if t == 'cat': return sum(flat_width(x) for x in d[1])
    if t == 'line': return 1
    if t == 'nest': return flat_width(d[2])
    return flat_width(d[1])

def fits(w, items):
    """does the rest fit in w columns, up to the first break?"""
    stack = list(items)
    while stack:
        if w < 0: return False
        i, flat, d = stack.pop()
        if isinstance(d, str): w -= len(d); continue
        t = d[0]
        if t == 'cat':
            stack.extend((i, flat, x) for x in reversed(d[1]))
        elif t == 'line':
            if flat: w -= 1
            else: return True
        elif t == 'nest': stack.append((i + d[1], flat, d[2]))
        else: stack.append((i, flat, d[1]))
    return w >= 0

def render(d, width=80, indent=0):
    out, col = [], indent
    stack = [(indent, False, d)]
    while stack:
        i, flat, d = stack.pop()
        if isinstance(d, str):
            out.append(d); col += len(d); continue
        t = d[0]
        if t == 'cat':
            stack.extend((i, flat, x) for x in reversed(d[1]))
        elif t == 'line':
            if flat: out.append(' '); col += 1
            else: out.append('\n' + ' ' * i); col = i
        elif t == 'nest': stack.append((i + d[1], flat, d[2]))
        else:
            f = flat or fits(width - col, stack + [(i, True, d[1])])
            stack.append((i, f, d[1]))
    return ''.join(out)

def paren(d): return cat('(', nest(1, d), ')')

# ---------------------------------------------------------------- printing

def ty(T, top=True):
    t = T[0]
    if t == 'var': s = '` %d' % T[1]
    elif t == 'Int': return '`ℕ'
    elif t == 'Bool': return '`𝔹'
    elif t == 'fun':
        l = T[1]
        s = '%s ⇒ %s' % ('(' + ty(l) + ')' if l[0] == 'fun' else ty(l),
                         '(' + ty(T[2]) + ')' if T[2][0] == 'fun'
                         else ty(T[2]))
    else: s = '`∀ ' + ty(T[1], False)
    return s if top or t in ('Int', 'Bool') else '(' + s + ')'

def conv(c, top=True, abbr=None):
    abbr = abbr or {}
    if c in abbr: return abbr[c]
    if c == 'id': return 'idᶜ'
    if c in ('seal', 'unseal'): return c
    if c[0] == 'fun':
        def side(x):
            return '(' + conv(x, True, abbr) + ')' \
                if x != 'id' and x[0] == 'fun' and x not in abbr \
                else conv(x, True, abbr)
        s = '%s ↦ %s' % (side(c[1]), side(c[2]))
    else: s = '∀ᶜ ' + conv(c[1], False, abbr)
    return s if top else '(' + s + ')'

SIGN = {'+': '⁺', '-': '⁻'}

def const(M):
    v, k = M[1], M[2]
    return '$ nat %d' % v if k == 'Int' else \
        '$ bool %s' % ('true' if v else 'false')

def term(M, abbr, ctx='top'):
    """ctx: 'top' (any), 'fun' (left of ·), 'arg' (right of ·)"""
    if M in abbr: return abbr[M]
    t = M[0]
    if t == 'var': return '` %d' % M[1]
    if t == 'const': return const(M)
    # boundary, ν and Λ bodies are parenthesized unless atomic
    if ctx == 'body': return paren(term(M, abbr))
    if t == 'nu':
        return group(cat('ν ', ty(M[2], False), ' · ',
                         nest(2, term(M[3], abbr, 'body')),
                         nest(2, cat(LINE, '⟨ ', conv(M[4], True, cabbr),
                                     ' ⟩'))))
    if t == 'bnd':
        return group(cat('[ %s , %d ]' % (SIGN[M[1]], M[2]),
                         nest(2, cat(LINE, term(M[3], abbr, 'body'))), LINE,
                         '⟨ ', conv(M[4], True, cabbr), ' ⟩'))
    if t == 'lam':
        d = group(cat('ƛ ', ty(M[2]), ' ∙', nest(2, cat(LINE,
                                                         term(M[3], abbr)))))
        return d if ctx == 'top' else paren(d)
    if t == 'Lam':
        d = cat('Λ ', term(M[2], abbr, 'body'))
        return d if ctx == 'top' else paren(d)
    if t == 'app':
        spine, m = [], M
        while m[0] == 'app' and m not in abbr:
            spine.append(m[2]); m = m[1]
        spine.reverse()
        d = group(cat(term(m, abbr, 'fun'),
                      nest(2, cat(*[cat(LINE, '· ', term(a, abbr, 'arg'))
                                    for a in spine]))))
        return d if ctx in ('top', 'fun') else paren(d)
    raise ValueError(M)

cabbr = {}

# ---------------------------------------------------------------- proofs
# a proof is (head, [args]) or a string

def pf(p, top=True):
    if isinstance(p, str): return p
    h, args = p
    if not args: return h
    d = group(cat(h, nest(2, cat(*[cat(LINE, pf(a, False)) for a in args]))))
    return d if top else paren(d)

def name_pf(flags, X):
    if not flags: raise ValueError('unbound name')
    if flags[0]:
        return 'n-here' if X == 0 else ('n-named', [name_pf(flags[1:], X - 1)])
    return ('n-hidden', [name_pf(flags[1:], X)])

def spell_pf(flags, A):
    t = A[0]
    if t == 'var': return ('s-var', [name_pf(flags, A[1])])
    if t == 'Int': return 's-ℕ'
    if t == 'Bool': return 's-𝔹'
    if t == 'fun':
        return ('s-⇒', [spell_pf(flags, A[1]), spell_pf(flags, A[2])])
    return ('s-∀', [spell_pf([True] + flags, A[1])])

def lookup_pf(a):
    return 'p-here' if a == 0 else ('p-there', [lookup_pf(a - 1)])

def conv_pf(c, s, a):
    if c == 'id': return 'c-id'
    if c == 'seal': assert s == '-'; return ('c-seal', [lookup_pf(a)])
    if c == 'unseal': assert s == '+'; return ('c-unseal', [lookup_pf(a)])
    if c[0] == 'fun':
        return ('c-fun', [conv_pf(c[1], '-' if s == '+' else '+', a),
                          conv_pf(c[2], s, a)])
    return ('c-all', [conv_pf(c[1], s, a + 1)])

def var_pf(x):
    return 'x-here' if x == 0 else ('x-there', [var_pf(x - 1)])

def typing(flags, G, M):
    """typing derivation for an elaborated (boundary-free) term"""
    t = M[0]
    if t == 'var': return ('⊢`', [var_pf(M[1])]), G[M[1]]
    if t == 'const':
        return ('⊢nat' if M[2] == 'Int' else '⊢bool'), (M[2],)
    if t == 'lam':
        p, B = typing(flags, [M[2]] + G, M[3])
        return ('⊢ƛ', [spell_pf(flags, M[2]), p]), ('fun', M[2], B)
    if t == 'app':
        p, F = typing(flags, G, M[1]); q, A = typing(flags, G, M[2])
        assert F[0] == 'fun' and nuc.erase(F[1]) == nuc.erase(A)
        return ('⊢·', [p, q]), F[2]
    if t == 'Lam':
        p, C = typing([True] + flags,
                      [nuc.shift_ty(1, 0, T) for T in G], M[2])
        return ('⊢Λ', [p]), ('all', C, M[1])
    if t == 'nu':
        _, X, A, L, c = M
        p, F = typing(flags, G, L)
        C = F[1]
        B = nuc.subst_ty(0, A, C)
        return ('⊢ν', [spell_pf(flags, A), p, spell_pf([True] + flags, C),
                       spell_pf([False] + flags, B),
                       conv_pf(c, '+', 0)]), B
    raise ValueError(M)

def value_pf(M):
    if M[0] == 'const': return 'V-$'
    if nuc.is_fun(M): return ('V-fun', [fun_pf(M)])
    if nuc.is_sealed(M): return ('V-sealed', [sealed_pf(M)])
    raise ValueError('not a value', M)

def fun_pf(M):
    if M[0] == 'lam': return 'F-ƛ'
    if M[0] == 'Lam': return 'F-Λ'
    _, s, a, V, c = M
    if c != 'id' and c[0] == 'fun': return ('F-↦', [value_pf(V)])
    if c != 'id' and c[0] == 'all': return ('F-∀', [value_pf(V)])
    if s == '+': return ('F-id⁺', [fun_pf(V)])
    return ('F-id⁻', [fun_pf(V), '(λ ())'])

def sealed_pf(M):
    _, s, a, V, c = M
    if c == 'seal': return ('S-seal', [value_pf(V)])
    return ('S-rev', [sealed_pf(V)])

def inst_pf(V):
    if V[0] == 'Lam': return 'inst-Λ'
    c = V[4]
    return ('inst-id' if c == 'id' else 'inst-∀', [inst_pf(V[3])])

def step_pf(flags, M):
    """(M', alloc, rule, proof), mirroring nuc.step"""
    t = M[0]
    if t == 'app':
        L, N = M[1], M[2]
        if not nuc.is_value(L):
            L2, al, r, p = step_pf(flags, L)
            return ('app', L2, nuc.up(al, N)), al, r, ('ξ-·₁', [p])
        if not nuc.is_value(N):
            N2, al, r, p = step_pf(flags, N)
            return (('app', nuc.up(al, L), N2), al, r,
                    ('ξ-·₂', [value_pf(L), p]))
        M2, al, r = nuc.step(flags, M)
        if r == 'Beta': return M2, al, r, ('β-ƛ', [value_pf(N)])
        if r == 'Wrap':
            return M2, al, r, ('wrap', [value_pf(L[3]), value_pf(N)])
        return M2, al, r, ('wrap-id', [value_pf(L), value_pf(N)])
    if t == 'nu':
        _, X, A, L, c = M
        if not nuc.is_value(L):
            L2, al, r, p = step_pf(flags, L)
            return ('nu', X, A, L2, c), al, r, ('ξ-ν', [p])
        M2, al, r = nuc.step(flags, M)
        return M2, al, r, ('tyβ', [spell_pf(flags, A), value_pf(L),
                                   inst_pf(L)])
    if t == 'bnd':
        _, s, a, V, c = M
        if not nuc.is_value(V):
            V2, al, r, p = step_pf(nuc.set_flag(flags, a, s == '+'), V)
            return (('bnd', s, a if al is None else a + 1, V2, c), al, r,
                    ('ξ-[]', [p]))
        M2, al, r = nuc.step(flags, M)
        W = V[3] if V[0] == 'bnd' else None
        p = {'Id': lambda: 'id-$',
             'Cancel-□': lambda: ('cancel-□', [value_pf(W)]),
             'CancelId': lambda: ('cancel-id', [value_pf(W)]),
             'Sink': lambda: ('sink', ['(λ ())', value_pf(W)]),
             'Swap': lambda: ('swap', ['(λ ())', sealed_pf(W)]),
             'Push': lambda: ('push', [sealed_pf(W)])}[r]()
        return M2, al, r, p
    raise ValueError(M)

def payload(P):
    return 'pay ' + ty(P, False)

def ctx_str(pays, n):
    if not pays: return '∅'
    return '((%s ∷ []) ∣ (%s ∷ []))' % (' ∷ '.join(map(payload, pays)),
                                         ' ∷ '.join(['false'] * n))

def subterm(M, path):
    for i in path: M = M[i]
    return M

def emit(k, src, defs, convdefs, rty):
    """defs: list of (name, comment, path into the elaborated term);
    convdefs: list of (name, comment, conversion)"""
    global cabbr
    M0 = nuc.elab([], src)
    abbr, cabbr, out = {}, {}, []
    for name, com, c in convdefs:
        out += ['-- ' + com, name + ' : Conv',
                render(cat(name + ' = ', nest(2, conv(c, True, cabbr)))), '']
        cabbr[c] = name
    for name, com, path in defs:
        T = subterm(M0, path) if isinstance(path, list) else path
        out += ['-- ' + com, name + ' : Term',
                render(group(cat(name + ' =', nest(2, cat(LINE, term(T, abbr)))))),
                '']
        abbr[T] = name
    ex = 'ex' + k
    out += [ex + ' : Term',
            render(group(cat(ex + ' =', nest(2, cat(LINE, term(M0, abbr)))))), '']
    p, T = typing([], [], M0)
    assert nuc.erase(T) == nuc.erase(rty), T
    out += ['⊢%s : ∅ ∣ [] ⊢ %s ⦂ %s' % (ex, ex, ty(rty)),
            render(cat('⊢%s =' % ex, nest(2, cat(LINE, pf(p))))), '']
    M, flags, pays, steps, n = M0, [], [], [], 0
    steps.append(render(nest(4, cat('    ', term(M, abbr)))))
    while not nuc.is_value(M):
        M, al, r, p = step_pf(flags, M)
        n += 1
        if al is not None:
            pays = [al[1]] + pays; flags = [False] + flags
        steps.append(render(cat('  —→⟨ ', nest(6, pf(p)), ' ⟩')))
        steps.append(render(nest(4, cat('    ', term(M, abbr)))))
    steps.append('  ∎')
    fin = ctx_str(pays, len(pays))[1:-1]
    gam = 'Γ' + k
    res = render(term(M, abbr))
    out += ['-- the context at the end of the run',
            gam + ' : Ctx',
            render(group(cat(gam + ' =', nest(2, cat(LINE, fin))))), '',
            'run-%s : ∅ ⊢ %s —↠ %s ⊣ %s' % (k, ex, res, gam),
            'run-%s =' % k] + steps
    result = ['⊢result-%s : %s ∣ [] ⊢ %s ⦂ %s' % (k, gam, res, ty(rty)),
              '⊢result-%s = preservation* ⊢%s run-%s' % (k, ex, k)]
    return '\n'.join(out), '\n'.join(result), n
