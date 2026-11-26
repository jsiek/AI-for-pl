# picol: feedback for upstream (drafts, not posted)

Drafts of issues for github.com/antirez/picol, from verifying picol at
commit `5f902e9b211fff21fb6e6abfd116df665e4091d5` (2026-02-18).  Line
numbers are upstream's `picol.c` at that commit.  Post only with the
owner's approval.

Issues 1–3 are bugs.  The last section lists the other changes we made,
which are only for the verifier; it is context, not a request.

---

## Issue 1: use after free when a proc redefines itself

```tcl
proc f {} { proc f {} {}; puts after }
f
```

Built with `-fsanitize=address`, this reports a heap-use-after-free
read in `picolGetToken` (`picol.c:278`).

- `picolCommandCallProc` evaluates the body in place:
  `picolEval(i,body)` with `body = cmd->body` (`picol.c:708`, `:736`).
- While that body is being parsed, the inner `proc f` reaches
  `picolRegisterCommand`, which frees the old body (`picol.c:369`).
- The parser then reads the freed memory to find the next token.

Without ASan this usually still prints `after`, but the result depends
on what the allocator does with the freed block.

Suggested fix (what we did): evaluate a copy of the body.

```c
char *body = xstrdup(cmd->body);   /* in picolCommandCallProc */
...
errcode = picolEval(i,body);
free(body);
```

This costs one copy per call.  Reference-counting the body would avoid
the copy.

## Issue 2: the REPL leaks the interpreter at end of input

```sh
printf 'set a 1\nproc f {x} {return $x}\n' | ./picol
```

LeakSanitizer reports 541 bytes leaked in 28 allocations.  When
`fgets` returns NULL, the REPL does `return 0` (`picol.c:790`), so
`main` never reaches `picolFreeInterp`.  The OS reclaims the memory at
exit, so the only harm is a noisy report under LSan or valgrind.

Suggested fix: `break` out of the loop instead of `return 0`, so that
the existing `picolFreeInterp` runs.

## Issue 3: `int` overflow on strings of 2 GB or more

```tcl
set a xxxxxxxx
set a $a$a      ;# repeated 28 times: $a reaches 2^30 bytes,
set a $a$a      ;# then the next concatenation needs 2^31 + 1 bytes
```

String lengths are kept in `int`, and the sums overflow, which is
undefined behaviour in C.

- **`picolEval`** (`picol.c:475-478`): `int oldlen = strlen(...)`,
  `tlen = strlen(t)`, then `xrealloc(argv[argc-1], oldlen+tlen+1)`.
  If `oldlen = tlen = 2^30`, the sum overflows.  In practice it wraps
  to a negative `int`, which converts to a huge `size_t`.
- **The parser** (`picol.c:77`, `:401-403`): `len` and `tlen` are
  `int`.  If one token spans a whole script of `INT_MAX` bytes, then
  `tlen+1` overflows.
- **`picolExprExpansion`** (`picol.c:561-562`):
  `int len = strlen(s); xmalloc(len+6)`.  This overflows for a string
  within 6 bytes of `INT_MAX`.

We found these while proving the code, not by running it.  We have not
run the example above, since it needs several GB of memory.

What we did: `picolEval` counts the size of the current command's
arguments (each length + 1).  If the next argument would take the
total past `PICOL_MAX_ARGS_SIZE` (default `INT_MAX - 10`), the command
fails with `Command too long`.  A smaller bound shows the behaviour:

```sh
cc -DPICOL_MAX_ARGS_SIZE=40 -o picol picol.c
```

```tcl
set a 0123456789
puts [set b $a$a$a]     ;# prints 012345678901234567890123456789
set c $a$a$a$a          ;# fails: Command too long
```

The proof also requires the script passed to `picolEval` to be shorter
than `INT_MAX` bytes.  Using `size_t` for lengths throughout would be
the more thorough fix.

---

## Other changes we made (only for the verifier)

These do not change picol's behaviour.  `run_asan.sh` checks that the
output matches upstream on the examples and on a script that reaches
every error message.

- **Variadic calls replaced:** the 6 `snprintf`, 4 `printf` and 1
  `fprintf` calls became fixed-argument helpers (`fmt_str3`,
  `fmt_int`, `fputs`).  For example:
  ```c
  snprintf(errbuf,sizeof(errbuf),"No such variable '%s'",t);    /* upstream */
  fmt_str3(errbuf,sizeof(errbuf),"No such variable '",t,"'");   /* ours */
  ```
  Only `%.12g` formatting of doubles stays in `snprintf`.  One message
  changed: `xrealloc`'s out-of-memory message no longer prints the
  pointer and size.
- **No reachable `goto`:** `picolEval`'s four `goto err` are now
  `break`.  `picolCommandCallProc`'s two error exits now call a new
  function, `picolCallProcFail`.
- **`default: break;`** was added to the `switch` in `picolParseString`
  and to the operator `switch` in `picolExpr`.

## What was verified

With these changes, picol is proved memory safe and leak free with the
Verified Software Toolchain (VST 2.17).  This covers every function,
the parser and the interpreter, through `main`'s return.

The proof assumes:

- trusted specifications of the libc functions picol calls (`malloc`,
  `free`, `realloc`, stdio and `strtod`);
- musl's sources for `strlen`, `strcmp`, `strchr`, `memcpy` and
  `isupper`, which are verified together with picol.
