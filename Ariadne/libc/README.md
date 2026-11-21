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
| `snprintf` | rejected | `vsnprintf`/`vfprintf` include musl's stdio internals, which reach `arch/x86_64/syscall_arch.h` (inline-asm register variables); `vfprintf`'s float formatting uses `long double` | trusted spec |
| `strtod` | rejected | the same stdio internals (`shgetc`, `floatscan`); `floatscan` uses `long double`, which CompCert does not support | trusted spec |
| `fopen`, `fgets`, `fread`, `fclose`, `fflush`, `printf`, `fprintf`, `perror`, `exit` | not tried | system calls | trusted spec |
| `malloc`, `free`, `realloc` | not tried | allocator: VST's `malloc`/`free` specs are axioms on the allow-list | trusted (`realloc`: spec to write) |
