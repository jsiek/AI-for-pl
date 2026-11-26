# huffman

A Huffman compressor CLI, `upstream/` = github.com/drichardson/huffman
at commit `102150ac8ca5d5b8aa4a9ddd897a98e6793b8342` (2021-04-24),
the Unlicense (public domain, `upstream/LICENSE`; pin in
`upstream/PIN.md`).  Chosen from `../CANDIDATES.md` §3.  `huffman.c`
(the library: file mode and memory mode) and `huffcode.c` (the CLI,
`-m` selects memory mode) are the program; nothing is changed yet.

## `run_asan.sh`

`./run_asan.sh [SRC]` (default `upstream`) builds `huffcode` with
`gcc -fsanitize=address,undefined -fno-omit-frame-pointer -g
-fno-sanitize-recover=all` (LSan on; a sanitizer report exits 23, so it
is never taken for huffcode's own error status 1), and runs:

1. upstream's `run_tests.sh` in a temporary copy (9 round trips of
   `test_data/`, then the 15 issue-2 fuzzer files must fail with
   status 1); again with UBSan's nonnull check off, to see the rest;
2. round trips in file mode and in memory mode (`-m`) of an empty file,
   `x`, the 256 byte values, 4096 × `a`, and 1 MiB of seeded random
   bytes;
3. the reproducers of bugs B4–B8 below.

Result on upstream (2026-11-26, 7.5 s): **7 PASS, 11 FAIL**.

| Check | Result | Bug |
|---|---|---|
| upstream `run_tests.sh` | FAIL at `test_data/1_byte` (UBSan, `huffman.c:507`) | B1 |
| upstream `run_tests.sh`, nonnull check off | PASS (all 24) | |
| round trips, file mode: empty, all 256, random 1 MiB | PASS | |
| round trips, file mode: `x`, 4096 × `a` | FAIL (UBSan, `huffman.c:507`) | B1 |
| round trips, `-m`: all 256, random 1 MiB | PASS | |
| round trips, `-m`: `x`, 4096 × `a` | FAIL (assertion, `huffman.c:268`) | B2 |
| round trip, `-m`: empty | FAIL (decoder exits 1, no report) | B3 |
| file mode rejects `leaf_on_path.huf` | PASS | |
| `-m -d` rejects `leaf_on_path.huf` | FAIL (UBSan, `huffman.c:816`) | B4 |
| `-m -d` rejects the 15 issue-2 files | FAIL, all 15 (`huffman.c:805`, `:816`, `:1084`, SEGV) | B4, B5 |
| `-m -d` survives a failed `malloc` | FAIL (UBSan, `huffman.c:1086`) | B6 |
| round trip of `ab` through a pipe | FAIL (decodes to nothing) | B7 |
| `-m` on a directory (plain gcc build) | FAIL (SIGSEGV in `free`, `huffcode.c:143`) | B8 |

No LSan report in any check that ran to the end.

## Bugs

Observed (B1–B6 under the sanitizers; B7, B8 as wrong output or a
crash):

- **B1. `fwrite(NULL, 1, 0, out)`** (`huffman.c:507`).  If the input
  has one distinct byte value then its code has 0 bits and
  `p->bits == NULL` (`new_code`, `huffman.c:123-128`), and
  `write_code_table` passes it to `fwrite` (C11 7.1.4: undefined even
  for 0 bytes).  `printf x > one; huffcode -i one -o one.huf` →
  `huffman.c:507:8: runtime error: null pointer passed as argument 1`.
  Upstream's own `run_tests.sh` stops here.
- **B2. `-m` cannot encode one distinct byte value.**  The same NULL
  `bits` reaches `write_cache(pc, NULL, 0)` (`huffman.c:560`), whose
  `assert(pc && to_write)` (`huffman.c:268`) aborts:
  `huffcode -m -i one -o one.huf` → `Assertion 'pc && to_write'
  failed`, empty output.  (With `NDEBUG` it would be
  `memcpy(…, NULL, 0)`, `huffman.c:289`.)
- **B3. `-m -d` rejects valid encodings of empty and one-symbol
  inputs.**  `memread` (`huffman.c:730`) tests
  `readlen + *pindex >= buflen`, so a read that ends exactly at the end
  of the buffer fails: `: > empty; huffcode -m -i empty -o e.huf;
  huffcode -m -d -i e.huf -o e.out` exits 1 (the 8-byte header is the
  whole file).  Also found by reading: a 0-bit code adds no leaf
  (`huffman.c:801` loop runs 0 times), so if the off-by-one were fixed
  alone then `aaa` would decode to nothing.
- **B4. `-m -d` reads a leaf's `symbol` as child pointers.**  File mode
  checks `p->isLeaf` while inserting a code (`huffman.c:674`); memory
  mode does not (`huffman.c:801-825`).  `leaf_on_path.huf` (15 bytes:
  count 2, length 1; `a` with the 1-bit code 0; `b` with the 3-bit code
  000; one data byte):
  ```
  00 00 00 02  00 00 00 01  61 01 00  62 03 00  00
  ```
  `huffcode -m -d -i leaf_on_path.huf` → `huffman.c:816:10: runtime
  error: member access within misaligned address 0xbebebebebebebe61`
  (the union's `zero` is `a` plus 7 uninitialized bytes).  File mode
  exits 1.
- **B5. `-m -d` follows a missing child.**  `huffman_decode_memory`
  dereferences `p` without the `p == NULL` test that file mode has
  (`huffman.c:1081-1084` vs `:985`).  All 15 files in
  `upstream/test_data/reported_issues/issue2/` crash in memory mode
  (6 at `huffman.c:1084`, `member access within null pointer`; 5 at
  `:805` and 3 at `:816` as in B4; 1 ASan SEGV); file mode rejects
  them.
- **B6. Unchecked `malloc(data_count)`** (`huffman.c:1071`), where
  `data_count` comes from the input.  With
  `ASAN_OPTIONS=allocator_may_return_null=1:max_allocation_size_mb=1`,
  `huffcode -m -d` on the encoding of 2 MiB of `abab…` → `huffman.c:1086:19:
  runtime error: store to null pointer`.
- **B7. Encoding from a pipe loses the data.**  The encoder reads its
  input twice; `rewind(in)` (`huffman.c:934`, no result) fails on a
  pipe, so the second pass reads nothing: `printf ab | huffcode |
  huffcode -d` prints nothing and both exit 0.  Found by reading: if
  the second pass sees a byte value the first did not (input changed
  between passes) then `code` is NULL and `code->numbits`
  (`huffman.c:845`) dereferences it.
- **B8. `-m` on a directory: double free** (`huffcode.c:143`; likewise
  `:190` with `-d`).  `fread` fails without setting end of file, so
  `while (!feof(in))` grows the buffer 1 KiB at a time until the
  `unsigned int len` wraps to 0; `realloc(buf, 0)` frees `buf` and
  returns NULL, and `free(buf)` frees it again.  `mkdir d; huffcode -m
  -i d -o x` → SIGSEGV in glibc `free` (gdb: `huffcode.c:143`, `len =
  0`); about 1 s in a plain build.  Not run under ASan, whose `realloc`
  copies the buffer each time.

Found by reading (not run):

- **B9. Unchecked allocations:** `malloc` at `huffman.c:64`, `:126`,
  `:138`, `:148`, `:453`, `:658`, `:787`; `realloc` at `huffman.c:109`
  (`bits[newSize - 1] = 0` on NULL).  `flush_cache`'s failure is
  ignored at `huffman.c:277` and `:1042` (output silently truncated,
  status 0).
- **B10. Files left open:** with `-m`, `main` returns at
  `huffcode.c:100` before the `fclose` calls; if the output file does
  not open then `huffcode.c:93` returns with the input open
  (`huffcode -i one -o /nonexistent/x`).  No visible effect (exit
  closes them), but a `FILE_handle` left at `main`'s return fails leak
  freedom (`../../libc/TRUSTED_SPECS.md`).
- **B11. Wrap at 4 GiB** (`unsigned int`, defined but wrong): the byte
  count `total_count` (`huffman.c:311`) of an input of 2^32 + k bytes
  is written as k, so decoding stops after k bytes; `len` in
  `huffcode.c:138`/`:185` wraps into B8.

No signed overflow found (the signed variables are `int c`, `int opt`
and `long curbyte` at `huffman.c:66`, bounded by 32).

## Proposed fixes to the C (pending the owner's decision)

Smallest change per item; none applied.  "Same output" means the bytes
written for every input on which upstream does not fail; checked later
by `run_asan.sh` against `upstream/` (to be added, as in picol).

1.  **Skip empty code writes** (B1, B2).  Bug.
    ```c
    if (fwrite(p->bits, 1, numbytes, out) != numbytes)        /* before, :507 */
    if (numbytes > 0 && fwrite(p->bits, 1, numbytes, out) != numbytes)  /* after */
    ```
    and `if (numbytes > 0 && write_cache(pc, p->bits, numbytes))` at
    `:560`.  Same output (0 bytes were written).
2.  **Memory decoder: same table rules as the file decoder** (B3, B4).
    Bug.  `memread`'s test becomes `if (readlen > buflen - *pindex)`
    (`:730`; also cannot wrap); `read_code_table_from_memory` takes
    `read_code_table`'s handling of a 0-bit code (`:626-653`: one leaf
    as the root) and its leaf test (`:674-680`):
    ```c
    for (curbit = 0; curbit < numbits; ++curbit)
    {
        if (p->isLeaf) { free(bytes); free_huffman_tree(root); return NULL; }  /* new */
        if (get_bit(bytes, curbit))
    ```
    and `huffman_decode_memory` handles a leaf root (repeat its symbol
    `data_count` times) and an empty table as `huffman_decode_file`
    does (`:957-974`).  Same output where upstream succeeds; empty and
    one-symbol encodings now decode.
3.  **Memory decoder: test for a missing child** (B5).  Bug.  As in
    file mode (`:985`):
    ```c
    p = byte & mask ? p->one : p->zero;
    if (p == NULL) { free(buf); free_huffman_tree(root); return 1; }   /* new */
    ```
4.  **Check every allocation** (B6, B9).  Bug.  As picol's `xrealloc`:
    `xmalloc`/`xrealloc` print `Out of memory` to `stderr` and
    `exit(1)` on NULL (the owner's 2026-11-22 decision: memory held at
    `exit` is outside leak freedom).
    ```c
    bits = (unsigned char*)realloc(bits, newSize);    /* before, :109 */
    bits = (unsigned char*)xrealloc(bits, newSize);   /* after */
    ```
    The `if (!tmp)` branches after `realloc` become unreachable and go.
    Same output unless memory runs out.  (Alternative: return errors up
    through `new_code`, `build_symbol_encoder` and
    `calculate_huffman_codes`; more code.)
5.  **Fail if the input cannot be read twice** (B7).  Bug, and needed
    for the proof: a `FILE` spec says nothing that relates the second
    pass's bytes to the first's, so `code` must be tested.
    ```c
    rewind(in);                                         /* before, :934 */
    if (fseek(in, 0, SEEK_SET) != 0) { rc = 1; ... }    /* after: skip to the frees */
    huffman_code* code = (*se)[uc];
    if (code == NULL) return 1;                         /* new, :842 */
    ```
    Same output for regular files; a pipe now exits 1 (upstream: a
    header only, status 0).  Replaces `rewind` by `fseek`.
6.  **`-m` read loop stops on a short read** (B8, B11).  Bug.
    ```c
    while (!feof(in)) { ...; cur += fread(buf + cur, 1, inc, in); }   /* before */
    do { ...; n = fread(buf + cur, 1, inc, in); cur += n; }           /* after */
    while (n == inc && len <= UINT_MAX - inc);
    ```
    (and fail if the bound stops it).  Same output for files; a
    directory then encodes as empty input, as file mode already does.
    Removes `feof`.
7.  **Close files on every path** (B10).  Bug (handles).  `return
    compress ? memory_encode_file(in, out) : ...;` (`huffcode.c:100`)
    becomes `rc = ...;` and falls through to the `fclose` calls; the
    output-open failure (`huffcode.c:93`) closes `in` first.  Same
    output.
8.  **No variadic calls** (VST cannot verify a call to `fprintf`,
    `huffcode.c:78`, `:91`; the owner's 2026-11-22 rule).
    ```c
    fprintf(stderr, "Can't open input file '%s': %s\n", file_in, strerror(errno));  /* before */
    fputs("Can't open input file '", stderr); fputs(file_in, stderr);              /* after */
    fputs("': ", stderr); fputs(errno_message(), stderr); fputs("\n", stderr);
    ```
    `errno_message()` (`return strerror(errno);`) is one trusted
    wrapper in place of `strerror` and `__errno_location`.  Same output
    (`stderr` is unbuffered; the same bytes in more writes).
9.  **A local sort instead of `qsort`** (VST: a call through the
    function pointer `SFComp`, `huffman.c:419`, `:449`; musl's
    `qsort.c` is rejected by clightgen, below).
    ```c
    qsort(pSF, n, sizeof(pSF[0]), SFComp);   /* before */
    sort_nodes(pSF, n);                      /* after: stable insertion sort with SFComp */
    ```
    Ties (equal counts) decide the tree, so the order matters.  A
    scratch build with a stable insertion sort gave byte-identical
    compressed output to glibc's `qsort` on 13 inputs (`test_data/`,
    `huffman.c`, the 256 byte values, 1 MiB random, 5000 random
    letters); upstream's output already depends on the libc's `qsort`.
10. **Parse `argv` locally instead of `getopt`** (VST: `getopt` writes
    the extern global `optarg`, `huffcode.c:44-52`; musl's `getopt.c`
    is rejected by clightgen).  A loop over `argv` for `-i FILE`,
    `-iFILE`, `-o`, `-c`, `-d`, `-h`, `-m`, clusters such as `-dm`,
    `--`, and the first non-option ending the options (POSIX getopt, as
    `__posix_getopt` does).  Same output on valid command lines; for an
    invalid option glibc's messages (`huffcode: invalid option -- 'x'`,
    `option requires an argument -- 'i'`) must be reproduced with
    `fputs`.  Note `-v` is in upstream's option string but has no case:
    it prints the usage and exits 1, like an unknown option.
    (Alternative: a trusted spec of `getopt` with `optarg`, `optind`.)
11. **Byte order without `htonl`/`ntohl` and without reading an `int`
    as bytes** (VST: `fread(&count, 4, 1, in)` at `huffman.c:580`,
    `:594`, `memcpy` into a `uint32_t` at `:747`, `:756`, `fwrite(&i,
    4, 1, out)` at `:486`, `:491` treat a `uint32_t` as 4 `char`s; the
    approved `fread` spec gives `char` cells, and VST has no rule that
    turns 4 bytes into an `int`).
    ```c
    if (fread(&count, sizeof(count), 1, in) != 1) ...; count = ntohl(count);  /* before */
    unsigned char b[4];                                                        /* after */
    if (fread(b, 1, 4, in) != 4) ...;
    count = (uint32_t)b[0] << 24 | (uint32_t)b[1] << 16 | (uint32_t)b[2] << 8 | b[3];
    ```
    and the inverse for writing.  Same bytes (network order is
    big-endian).  Removes `htonl`, `ntohl`.
12. **Name the union's members, or drop the union** (VST:
    `huffman.c:24-31` has an anonymous union holding an anonymous
    struct; clightgen names both members with the same bare number,
    `18727075383868559167%positive`, with no `Definition`, so proofs
    must spell field paths with it).  Smallest for the proofs: plain
    fields `zero`, `one`, `symbol` (8 more bytes per node), with
    `new_leaf_node` setting `zero = one = NULL`.  Same output.
13. **`assert`** (16 calls, `huffman.c:218`, `:235`, `:245`, `:268`,
    `:269`, `:655`, `:684`, `:690`, `:693`, `:698`, `:704`, `:707`,
    `:726`, `:727`; `huffcode.c:132`, `:179`) call `__assert_fail`.
    No C change: either a trusted spec of `__assert_fail` like the
    approved `exit` (postcondition `FF`), or verify a build with
    `-DNDEBUG` (fix 1 removes the one assertion that fails).

Not changes to the C, by earlier decisions: `stdin`/`stdout`/`stderr`
(`huffcode.c:37`, `:38`, `:61`, `:67`, `:79`, `:92`) are read through a
`huffman_vst.c` with musl's definitions, as `picol_vst.c`; `main(argc,
argv)` is proved as `huffcode_main` for every `argv` with a
`main(void)` wrapper.

## What VST cannot verify as is (survey, 2026-11-26)

| Feature | Where | Fix |
|---|---|---|
| reachable `goto` | none | |
| `switch` that can fall off the end | none (`huffcode.c:46` has `default`) | |
| variadic calls | `fprintf` at `huffcode.c:78`, `:91` (`printf` at `huffman.c:373-422` is under `#if 0`) | 8 |
| variadic definitions | none | |
| extern globals without initializer | `stdin` `huffcode.c:37`; `stdout` `:38`, `:61`; `stderr` `:67`, `:79`, `:92`; `optarg` `:49`, `:52` (`errno` is a call to `__errno_location`) | `huffman_vst.c`; 10 |
| calls through function pointers | `qsort(…, SFComp)` `huffman.c:419`, `:449` | 9 |
| struct arguments/returns by value | none | |
| `setjmp`/`longjmp` | none | |
| signed overflow | none found | |
| an `int` read or written as bytes | `huffman.c:486`, `:491`, `:580`, `:594`, `:747`, `:756` | 11 |
| anonymous union/struct members | `huffman.c:24-31` | 12 |
| union type punning on bad input | `huffman.c:805`, `:816` (B4) | 2 |

## clightgen (2026-11-26, CompCert 3.17, `../../vst/run.sh`)

`clightgen -normalize huffman.c`: accepted, no output.
`clightgen -normalize huffcode.c`: rejected:
```
huffcode.c:44: warning: implicit declaration of function 'getopt' is invalid in C99 [-Wimplicit-function-declaration]
huffcode.c:49: error: use of undeclared identifier 'optarg'
```
With `-D_POSIX_C_SOURCE=200809L` (or upstream Makefile's
`-D_POSIX_C_SOURCE=2`): accepted, no output.  As `../CANDIDATES.md`
says.  The image's headers are glibc's (`getopt` is `__posix_getopt`).

## External functions

22, from the two Clight files' `External` declarations (`malloc`,
`free` are `EF_malloc`, `EF_free`), plus the globals above.
`musl_clight.py` was run on the new candidates (2026-11-26).

| Function | Call sites | Status |
|---|---|---|
| `memcpy` | `huffman.c:80`, `:254`, `:282`, `:289`, `:732` | **verified** from musl (`../../libc/proofs/verif_memcpy.v`) |
| `malloc`, `free` | many | VST's allocator specs (axioms on the allow-list) |
| `realloc` | `huffman.c:109`, `:250`, `:279`; `huffcode.c:139`, `:186` | **approved** trusted spec (`../../libc/TRUSTED_SPECS.md`) |
| `fopen`, `fclose` | `huffcode.c:75`, `:88`, `:116`, `:121` | **approved** |
| `fputs` | `huffcode.c:22` (fix 8 adds more) | **approved** |
| `fread` | `huffman.c:580`, `:594`, `:659`; `huffcode.c:148`, `:195` | **approved** (`char` cells; `:580`, `:594` need fix 11) |
| `memset` | `huffman.c:68`, `:193`, `:454` | new; musl `memset.c` accepted by clightgen: verify from musl |
| `htonl`, `ntohl` | `huffman.c:485`, `:490`, `:531`, `:537`, `:585`, `:599`, `:753`, `:762` | new; musl accepted; removed by fix 11 |
| `qsort` | `huffman.c:419`, `:449` | new; musl `qsort.c` rejected (`atomic_arch.h:114`: inline `asm`); removed by fix 9 |
| `fwrite` | `huffman.c:486`, `:491`, `:507`; `huffcode.c:164`, `:211` | new: trusted spec (stdio) |
| `fgetc` | `huffman.c:305`, `:612`, `:619`, `:839`, `:978` | new: trusted spec |
| `fputc` | `huffman.c:502`, `:504`, `:854`, `:868`, `:970`, `:996` | new: trusted spec |
| `rewind` | `huffman.c:934` | new; fix 5 replaces it by `fseek` (new: trusted spec) |
| `feof` | `huffcode.c:135`, `:182` | new; removed by fix 6 |
| `fprintf` | `huffcode.c:78`, `:91` | new, variadic; removed by fix 8 |
| `strerror`, `__errno_location` | `huffcode.c:79`, `:92` | new; musl rejected (`syscall_arch.h`); fix 8: one trusted wrapper `errno_message` |
| `getopt` (`__posix_getopt`) | `huffcode.c:44` | new; musl `getopt.c` rejected (`syscall_arch.h`); removed by fix 10 |
| `__assert_fail` | the 16 `assert`s | new; trusted spec or `-DNDEBUG` (fix 13) |

Counts: 1 verified (`memcpy`); 5 with approved trusted specs (`realloc`,
`fopen`, `fclose`, `fputs`, `fread`) plus VST's `malloc`/`free`; 14
new.  If fixes 5, 8–11 and 13 (`-DNDEBUG`) are taken then the new
ones left are `memset` (verify from musl) and trusted specs for
`fwrite`, `fgetc`, `fputc`, `fseek` and `errno_message`, each for the
owner's approval.
