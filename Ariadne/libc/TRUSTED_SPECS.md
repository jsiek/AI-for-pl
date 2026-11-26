# picol: trusted specs

Specs of the functions picol calls that are not verified with VST (libc
functions with trusted specs, `../../libc/README.md`, and `trusted.c`).
Each is written for memory safety and leak freedom only, and approved by
the owner (`HUMAN_STEPS.md`).  They enter the trust base (plan §2.2,
item 7).

## `realloc` (approved 2026-11-22)

```c
void *realloc(void *ptr, size_t size);
```
Called only from `xrealloc` (`picol.c:39`), which exits on NULL:
1. `xmalloc(...)` (= `xrealloc(NULL, ...)`): no old block (7 sites).
2. `argv = xrealloc(argv, sizeof(char*)*(argc+1))`: grows an array of
   pointers; `argv[0..argc)` is read afterwards.
3. `argv[argc-1] = xrealloc(argv[argc-1], oldlen+tlen+1)`: grows a
   string; its first `oldlen` bytes are kept.

```coq
WITH t : type, p : val, n : Z, m : Z, old : list (reptype t), gv : globals
PRE  [ tptr tvoid, size_t ]
  PROP (0 < m;  sizeof t * m <= Ptrofs.max_unsigned;           (* 1 *)
        p = nullval -> n = 0 /\ old = [])                       (* 2 *)
  PARAMS (p; Vptrofs (Ptrofs.repr (sizeof t * m)))  GLOBALS (gv)
  SEP (mem_mgr gv;
       if p is null then emp
       else malloc_token Ews (tarray t n) p * data_at Ews (tarray t n) old p)   (* 3 *)
POST [ tptr tvoid ] EX q : val,
  RETURN (q)
  SEP (mem_mgr gv;
       if q is null then <the precondition's block, unchanged>                   (* 4 *)
       else malloc_token Ews (tarray t m) q *
            data_at Ews (tarray t m)
              (sublist 0 (min n m) old ++ Zrepeat (default_val t) (m - min n m)) q)  (* 5 *)
```
1. The new size is positive and representable (`realloc(p, 0)` is
   implementation-defined; picol never asks for 0 bytes).
2. A NULL `ptr` has no old block (`malloc`).
3. The caller gives up the old block and its allocator token.
4. On failure the caller keeps the old block.
5. On success the caller owns `m` elements, the first `min(n,m)` the old
   ones, the rest uninitialised; the old pointer is no longer owned.

`t` is a parameter: site 1 takes the struct type with `m = 1`, site 2
`tptr tschar`, site 3 `tschar`.

## `fmt_double` (approved 2026-11-22)

```c
/* trusted.c */
void fmt_double(char *buf, size_t n, double v) {
    snprintf(buf,n,"%.12g",v);
}
```
One call site, `picolCommandExpr`: `char buf[64]; ...
fmt_double(buf,sizeof(buf),v); picolSetResult(i,buf);`, where
`picolSetResult` does `xstrdup(buf)` (`strlen`, then a copy of
`strlen(buf)+1` bytes).

```coq
WITH buf : val, n : Z, v : float
PRE  [ tptr tschar, size_t, tdouble ]
  PROP (0 < n <= Ptrofs.max_unsigned)                           (* 1 *)
  PARAMS (buf; Vptrofs (Ptrofs.repr n); Vfloat v)
  SEP (data_at_ Ews (tarray tschar n) buf)                      (* 2 *)
POST [ tvoid ] EX s : list byte,
  PROP ()
  RETURN ()
  SEP (cstringn Ews s n buf)                                    (* 3 *)
```
1. Room for at least the NUL; any double, including NaN and infinities.
2. `n` writable bytes, contents irrelevant.
3. Some string `s`: no zero byte in `s`, a NUL after it within `n`
   bytes, the rest uninitialised (VST's `cstringn`,
   `floyd/data_at_lemmas.v:1928`).  Which string is unspecified
   (functional correctness is out of scope).

## `strtod` (approved 2026-11-22)

```c
double strtod(const char *nptr, char **endptr);
```
Call sites: `picolExpr` (`a = strtod(*p,&e); if (e == *p) *err = 1;
*p = e;`, then parsing continues at `e`, so `e` must stay within the
string; `*p` points into the middle of the `expr` buffer), and
`strtod(i->result,NULL)` in `if` and `while` (value only).

```coq
WITH sh : share, str : val, s : list byte, endptr : val
PRE  [ tptr tschar, tptr (tptr tschar) ]
  PROP (readable_share sh)
  PARAMS (str; endptr)
  SEP (cstring sh s str;                                                (* 1 *)
       if endptr is null then emp else data_at_ Ews (tptr tschar) endptr)   (* 2 *)
POST [ tdouble ] EX d : float, EX k : Z,
  PROP (0 <= k <= Zlength s)                                            (* 3 *)
  RETURN (Vfloat d)
  SEP (cstring sh s str;                                                (* 4 *)
       if endptr is null then emp
       else data_at Ews (tptr tschar) (offset_val k str) endptr)        (* 5 *)
```
1. Reads a NUL-terminated string (read permission; may be interior).
2. If `endptr` is not NULL, one writable `char*` slot.
3. Parsing stops at an offset `k` within the string (`k = 0`: nothing
   parsed).
4. The string is unchanged.
5. The slot holds `str + k`.

`d` and `k` are otherwise unspecified.  Approved with one gap: on
overflow `strtod` writes `errno`, which the spec does not mention.
Picol never reads `errno`, and its storage is libc's, outside any
memory picol owns.

## `FILE_handle`, `fopen`, `fclose` (approved 2026-11-22)

Call sites (`main`, script mode): `FILE *fp = fopen(argv[1],"r"); if
(!fp) { perror("open"); exit(1); } ... fread(buf,1,1024*16-1,fp); ...
fclose(fp);`

```coq
Parameter FILE_handle : val -> mpred.            (* owning an open stream *)
Axiom FILE_handle_valid : forall f, FILE_handle f |-- valid_pointer f.   (* a *)
Axiom FILE_handle_ptr   : forall f, FILE_handle f |-- !! isptr f.        (* b *)
```
(a) lets `if (!fp)` compare `fp` with NULL; (b) an open stream is not
NULL.  `FILE_handle` is not `emp`, so leak freedom covers streams: a
stream left open fails `main`'s spec like an unfreed block.

```coq
(* fopen *)
WITH sh1 : share, sh2 : share, path : val, mode : val, sp : list byte, sm : list byte
PRE  [ tptr tschar, tptr tschar ]
  PROP (readable_share sh1; readable_share sh2)
  PARAMS (path; mode)
  SEP (cstring sh1 sp path; cstring sh2 sm mode)                       (* 1 *)
POST [ tptr (Tstruct _FILE noattr) ] EX f : val,
  RETURN (f)
  SEP (cstring sh1 sp path; cstring sh2 sm mode;                       (* 2 *)
       if f is null then emp else FILE_handle f)                       (* 3 *)

(* fclose *)
WITH f : val
PRE  [ tptr (Tstruct _FILE noattr) ]
  PROP () PARAMS (f)
  SEP (FILE_handle f)                                                  (* 1 *)
POST [ tint ] EX r : int,
  RETURN (Vint r)
  SEP ()                                                               (* 2 *)
```
`fopen`: 1. reads two strings; 2. returns them unchanged; 3. NULL and
nothing owned, or a new stream owned by the caller.  `fclose`: 1. takes
the stream; 2. nothing owned afterwards, even if `r` reports an error
(C11 7.21.5.1: the stream is closed either way).  As with `strtod`, the
`errno` writes are not mentioned.

## `std_stream`, `fputs` (approved 2026-11-22)

Call sites: 10, all on `stdout` or `stderr` (`xrealloc`'s out-of-memory
message, the `puts` command, the REPL prompt and result, script-mode
errors); the strings are literals, heap strings (`argv[k]`,
`interp->result`) and a stack buffer (`num`); the result is ignored.
The standard streams' addresses come from `picol_vst.c`.

```coq
Definition std_stream (gv : globals) (f : val) : Prop :=
  f = gv ___stdin_FILE \/ f = gv ___stdout_FILE \/ f = gv ___stderr_FILE.

(* fputs *)
WITH sh : share, str : val, s : list byte, f : val, own : bool, gv : globals
PRE  [ tptr tschar, tptr (Tstruct __IO_FILE noattr) ]
  PROP (readable_share sh)
  PARAMS (str; f)  GLOBALS (gv)
  SEP (cstring sh s str;                                                   (* 1 *)
       if own then FILE_handle f else !! std_stream gv f && emp)           (* 2 *)
POST [ tint ] EX r : int,
  RETURN (Vint r)
  SEP (cstring sh s str;                                                   (* 3 *)
       if own then FILE_handle f else emp)                                 (* 4 *)
```
1. Reads a string (read permission, so literals work).
2. A stream the caller owns (`fopen`), or a standard stream (no
   ownership: libc owns its `FILE`).
3. The string is unchanged.  4. Ownership as before.  `r` unspecified;
bytes buffered in libc's `FILE` are libc's; `errno` not mentioned.

## `fflush` (approved 2026-11-22)

One call site: the REPL, `fputs("picol> ",stdout); fflush(stdout);`
(result ignored).

```coq
WITH f : val, own : bool, gv : globals
PRE  [ tptr (Tstruct __IO_FILE noattr) ]
  PROP ()
  PARAMS (f)  GLOBALS (gv)
  SEP (if own then FILE_handle f else !! std_stream gv f && emp)          (* 1 *)
POST [ tint ] EX r : int,
  RETURN (Vint r)
  SEP (if own then FILE_handle f else emp)                                (* 2 *)
```
1. An owned or standard stream (not `fflush(NULL)`).  2. Ownership as
before.  `r` unspecified; `errno` not mentioned.

## `fgets` (approved 2026-11-22)

One call site: the REPL, `char clibuf[1024]; ... if
(fgets(clibuf,1024,stdin) == NULL) break; retcode =
picolEval(interp,clibuf);` (parsed as a string; not read after NULL).

```coq
WITH buf : val, n : Z, f : val, own : bool, gv : globals
PRE  [ tptr tschar, tint, tptr (Tstruct __IO_FILE noattr) ]
  PROP (0 < n <= Int.max_signed)                                           (* 1 *)
  PARAMS (buf; Vint (Int.repr n); f)  GLOBALS (gv)
  SEP (data_at_ Ews (tarray tschar n) buf;                                 (* 2 *)
       if own then FILE_handle f else !! std_stream gv f && emp)
POST [ tptr tschar ] EX r : val,
  RETURN (r)
  SEP (if r is null then data_at_ Ews (tarray tschar n) buf               (* 3 *)
       else !! (r = buf) && EX s : list byte, cstringn Ews s n buf;        (* 4 *)
       if own then FILE_handle f else emp)                                 (* 5 *)
```
1. Room for the NUL; `n` fits in an `int`.  2. `n` writable bytes.
3. On NULL the buffer is unknown (C11 7.21.7.2: unchanged at end of
file, indeterminate after a read error).  4. Otherwise `buf`, holding
a string followed by a NUL within `n` bytes.  5. Ownership as before.

A line with a zero byte, `ab\0cd\n`, is stored whole plus a NUL (C11
7.21.7.2: only a newline, end of file or n-1 characters stop it; musl's
`fgets` searches only for `'\n'`; gcc/glibc gives the bytes
`61 62 00 63 64 0a 00`).  The spec describes it as `s = "ab"`, a NUL,
then `Vundef` cells, which VST's `mapsto` reads as "some byte"
(`veric/SeparationLogic.v:548`).

## `fread` (approved 2026-11-22)

One call site: script mode, `char buf[1024*16]; ... size_t bytesRead =
fread(buf,1,1024*16-1,fp); buf[bytesRead] = '\0'; fclose(fp);
picolEval(interp,buf)` (the write needs `bytesRead <= 16383`; parsing
needs the stored bytes to be known).  C11 7.21.8.1: up to `nmemb`
elements, returns the number read, a partially read element is
indeterminate; musl's `fread.c` returns `(len-l)/size` on a short read.

```coq
WITH buf : val, size : Z, nmemb : Z, f : val, own : bool, gv : globals
PRE  [ tptr tvoid, size_t, size_t, tptr (Tstruct __IO_FILE noattr) ]
  PROP (0 < size;  0 <= nmemb;  size * nmemb <= Ptrofs.max_unsigned)      (* 1 *)
  PARAMS (buf; Vptrofs (Ptrofs.repr size); Vptrofs (Ptrofs.repr nmemb); f)
  GLOBALS (gv)
  SEP (data_at_ Ews (tarray tschar (size * nmemb)) buf;                    (* 2 *)
       if own then FILE_handle f else !! std_stream gv f && emp)
POST [ size_t ] EX k : Z, EX bytes : list byte,
  PROP (0 <= k <= nmemb;  Zlength bytes = k * size)                       (* 3 *)
  RETURN (Vptrofs (Ptrofs.repr k))
  SEP (data_at Ews (tarray tschar (size * nmemb))
         (map Vbyte bytes ++ Zrepeat Vundef (size * (nmemb - k))) buf;    (* 4 *)
       if own then FILE_handle f else emp)                                (* 5 *)
```
1. Positive `size`, representable total.  2. `size*nmemb` writable
bytes (picol: the first 16383 of 16384).  3. A count `k <= nmemb`.
4. The first `k*size` bytes known (zeros possible), the rest unknown
(including a partial element).  5. Ownership as before.  Bytes typed
`char` (a program reading structs needs a typed variant); `errno` not
mentioned.

## `perror` (approved 2026-11-22)

One call site: `if (!fp) { perror("open"); exit(1); }`.

```coq
WITH sh : share, str : val, s : list byte
PRE  [ tptr tschar ]
  PROP (readable_share sh)
  PARAMS (str)
  SEP (cstring sh s str)                                                   (* 1 *)
POST [ tvoid ]
  PROP () RETURN ()
  SEP (cstring sh s str)                                                   (* 2 *)
```
1. Reads a string.  2. Returns it; nothing new owned.  Its reads of
`errno` and writes to `stderr` are libc's.

## `exit` (approved 2026-11-22)

Call sites: `xrealloc` (out of memory) and `main` (script file does not
open), both `exit(1)`.

```coq
WITH status : Z
PRE  [ tint ]
  PROP (Int.min_signed <= status <= Int.max_signed)
  PARAMS (Vint (Int.repr status))
  SEP ()
POST [ tvoid ]
  PROP () RETURN ()
  SEP (FF)                                                                 (* 1 *)
```
1. Never returns.  By VST's frame rule the caller may still own memory
at the call: leak freedom covers `main`'s return only (plan §2.1,
owner, 2026-11-22).
