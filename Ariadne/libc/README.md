# libc: musl source for verified libc functions

Plan §4 (owner, 2026-11-21): a libc function is verified from musl's
source if clightgen accepts it and one prover run with a $10 cap proves
it (`check_vst.py` accepts); otherwise it gets a trusted spec, written
for memory safety and approved by the owner.  This directory holds the
pinned source and the checks; the per-function choices go in the table
below.

```
python3 -I fetch_musl.py                 # musl 1.2.6, SHA-256 pinned; git-ignored
python3 -I musl_clight.py strlen ...     # closure of the given functions + clightgen
```

`musl_clight.py` uses CompCert's preprocessor defines (`-U__GNUC__
-U__SIZEOF_INT128__`, from `compcert.ini`), which also select musl's
byte-at-a-time string loops: musl's `strlen` has a word-at-a-time loop
under `#ifdef __GNUC__` that reads past the end of the string (an
out-of-bounds read in CompCert's memory model); its Clight output has
only the byte loop (variables `s` and `a`, no `w`).  One shim: CompCert
has no `__typeof`, so musl's `weak_alias` macro is defined as nothing.

## picol's functions (2026-11-21)

`musl_clight.py strlen strcmp strchr memcpy isupper strtod snprintf`:
35 files; boundary `__lock`/`__unlock` (threads).

| Function | clightgen | Reason | Choice |
|---|---|---|---|
| `strlen`, `strcmp`, `strchr` (+ `strchrnul`), `memcpy`, `isupper` | accepted | | verify ($10 run each) |
| `snprintf` | rejected | `vsnprintf`/`vfprintf` include musl's stdio internals, which reach `arch/x86_64/syscall_arch.h` (inline-asm register variables); `vfprintf`'s float formatting uses `long double` | picol calls it only through `fmt_double` (`bench/picol/trusted.c`), which gets the trusted spec |
| `strtod` | rejected | the same stdio internals (`shgetc`, `floatscan`); `floatscan` uses `long double`, which CompCert does not support | trusted spec |
| `fopen`, `fgets`, `fputs`, `fread`, `fclose`, `fflush`, `perror`, `exit` | not tried | system calls | trusted spec |

Variadic calls (owner, 2026-11-22): VST cannot verify a call to a
variadic function (its `printf`/`fprintf` support is experimental and
outside its soundness proof), so a program's variadic calls are
replaced by fixed-argument functions: plain C where possible (verified
with the program), a trusted wrapper otherwise.

libc globals (owner, 2026-11-22): VST verifies one translation unit, in
which a libc global such as `stdout` is an extern without initializer,
so `main` gets no permission to read it.  The verified unit is
`<program>_vst.c`: the program plus musl's definitions of the globals
it reads (`bench/picol/picol_vst.c`).
| `malloc`, `free`, `realloc` | not tried | allocator: VST's `malloc`/`free` specs are axioms on the allow-list | trusted (`realloc`: spec approved 2026-11-22) |

The trusted specs picol uses, all approved by the owner on 2026-11-22:
`bench/picol/TRUSTED_SPECS.md`.
