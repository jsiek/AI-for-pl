# Ariadne: candidate complete programs (survey, 2026-11-21)

Goal: replace sglib with a complete C program whose only claimed spec
is `main`'s (memory safe, every allocation freed at exit).  The trusted
base is then the specs of the external functions it calls.

How the numbers were produced:

- **LOC** = non-blank, non-comment lines of the `.c`/`.h` files the
  program needs (tests excluded); physical lines in brackets.
- **Externals** = distinct external *functions*, from the
  `EF_external` entries in clightgen's `.v` output (top 4), or from
  `nm -u` on `gcc -c` objects (the rest; gcc may add `puts`/`putchar`
  for `printf` calls).  `malloc`/`free` are counted although CompCert
  treats them as builtins.  The `stdin`/`stdout`/`stderr` globals are
  not counted.
- Nothing from the candidates was built with their scripts or run.

## Summary

| name | URL | kind | LOC | heap structures | ext. fns | threads / longjmp / varargs | tests | leak-clean at exit | licence | last commit |
|---|---|---|---|---|---|---|---|---|---|---|
| **picol** | github.com/antirez/picol | Tcl interpreter | 669 [809] | linked lists (vars, commands), call-frame stack, growable `argv`, strings | 18 | none / none / calls `printf`, `fprintf`, `snprintf` | `picol_test.c` (unit tests on `picolEval`) + `.tcl` scripts | yes for `picol file.tcl`; no if the REPL ends at EOF (`return 0` skips `picolFreeInterp`) | BSD-2 | 2026-02-18 (antirez; "Picol 2") |
| **clox** | github.com/munificent/craftinginterpreters (`c/`) | bytecode interpreter (Lox) | 2609 [4945] | open-addressing hash tables, growable arrays, intrusive object list, closures/upvalues, mark-sweep GC | 20 | none / none / **defines** variadic `runtimeError`; passes `Token` structs by value | 265 `.lox` tests with expected output | yes on success (`freeVM`); no on error exits `exit(65/70/74)` | MIT | 2024-08-01 |
| **huffman** | github.com/drichardson/huffman | Huffman compressor CLI | 961 [1338] | binary tree with parent pointers, 256-entry code table of heap arrays, growable output buffer | 22 | none / none / calls `fprintf` only | `run_tests.sh` round-trips 10 files; random inputs trivial | yes on normal paths (frees tree + encoder); `malloc` results unchecked | Unlicense (public domain) | 2021-04-24 |
| **sbase tsort** | git.suckless.org/sbase | Unix utility | 473 [615] incl. libutil | sorted linked list of vertices, each with a sorted edge list | 22 (≈12 used by tsort itself) | none / none / libutil **defines** `eprintf`, `enprintf`, `weprintf` | none in sbase; random pair lists trivial | **no**: graph never freed | MIT | 2026-05-25 |
| sbase dc | git.suckless.org/sbase | arbitrary-precision RPN calculator | 2110 [2635] | bignum digit buffers, value stack, register hash table with chains, arrays | 37 | none / **setjmp/longjmp** error recovery / defines `error(...)`; calls `system` | 25 dc test scripts | no (stack/registers not freed) | MIT | 2026-05-25 |
| sbase join | git.suckless.org/sbase | Unix utility | 466 [545] + libutil | growable arrays of lines and fields | ≈27 | none / none / libutil varargs | none | yes (`freespan`, `freespecs`) | MIT | 2026-05-25 |
| smu | github.com/karlb/smu | markdown to HTML | 708 [825] | growable char buffers only; most work is pointer arithmetic over input | 24 | none / none / defines `eprint`; uses `regcomp`/`regexec` | 30 `.text`/`.html` pairs | no: `regex_t` never `regfree`d | MIT | 2026-05-14 |
| kilo | github.com/antirez/kilo | text editor | 986 [1308] | growable row array, per-row char/render/highlight buffers | 35 | none / none / `signal(SIGWINCH)`, defines variadic status setter, termios | none; needs a TTY | no (`exit(0)` on quit) | BSD-2 | 2025-01-04 |
| md4c + md2html | github.com/mity/md4c | markdown to HTML | 8825 [11738] | many growable arrays, mark/span stacks, callbacks | ≈23 (17 in library) | none / none / few | CommonMark spec suite | yes (`membuf_fini`) | MIT | 2026-10-19 |
| re1 | github.com/rsc/re1 | regex engines + driver | 916 [1084] | parse tree, NFA program arrays | not counted | none / none / yacc parser, variadic `fatal` | none | no | BSD-3 | 2012-12-08 |
| brenns10/lisp | github.com/brenns10/lisp | Lisp interpreter | 1144 [1880] | cons cells, scopes, ref-counting | not counted | none / none / varargs in builtins | none | not checked | BSD-2 | 2015-10-30 |
| c4 | github.com/rswier/c4 | C interpreter | ≈500 | a few large pools, never freed | — | — | — | no | **GPL-2** (excluded) | 2019-03-14 |

## 1. picol

**Heap use.**  Variables are a linked list per call frame; frames are
a linked stack (`picol.c:84-112`):

```c
struct picolVar {
    char *name, *val;
    struct picolVar *next;
};
...
struct picolCallFrame {
    struct picolVar *vars;
    struct picolCallFrame *parent; /* parent is NULL at top level */
};
```

and `picolEval` builds each command's `argv` with `realloc`, appending
or concatenating tokens (`picol.c:470-479`):

```c
argv = xrealloc(argv, sizeof(char*)*(argc+1));
argv[argc] = t;
...
argv[argc-1] = xrealloc(argv[argc-1], oldlen+tlen+1);
memcpy(argv[argc-1]+oldlen, t, tlen);
```

**A use-after-free found by reading.**  This script:

```tcl
proc f {} { proc f {} {}; puts after }
f
```

calls `f`, whose `picolCommandCallProc` passes `cmd->body` to
`picolEval` (`picol.c:708`, `:736`).  The inner `proc f` reaches
`picolRegisterCommand`, which does `free(c->body)` on the *same*
command (`picol.c:368-369`).  The outer parser then keeps reading
`puts after` from the freed body.  (Not run; read from the code.)  A
proof of `main` cannot go through without a fix, e.g. evaluating a
private copy of the body.

**External functions (18):** `__ctype_b_loc` (from glibc's `isupper`
macro), `exit`, `fclose`, `fflush`, `fgets`, `fopen`, `fprintf`,
`fread`, `free`, `memcpy`, `perror`, `printf`, `realloc`, `snprintf`,
`strchr`, `strcmp`, `strlen`, `strtod`; globals `stdin`, `stdout`,
`stderr`.

**Changes for VST.**
- Replace `isupper(name[0])` with a local function (removes
  `__ctype_b_loc`; glibc's macro indexes a table).
- Fix the `proc` redefinition use-after-free above.
- REPL path: call `picolFreeInterp` before `return 0` at EOF.
- Calls to `printf`/`fprintf`/`snprintf` are variadic calls with fixed
  formats; no variadic function is defined.
- Command dispatch is through the function pointer `c->func`
  (`picol.c:457`); each command needs a funspec matching that type.

**clightgen -normalize:** accepted unchanged (`picol.c`).

## 2. clox

**Heap use.**  Growing a hash table allocates a new entry array,
re-inserts the live keys, and frees the old array
(`c/table.c:85-114`):

```c
static void adjustCapacity(Table* table, int capacity) {
  Entry* entries = ALLOCATE(Entry, capacity);
  ...
  for (int i = 0; i < table->capacity; i++) {
    Entry* entry = &table->entries[i];
    if (entry->key == NULL) continue;
    Entry* dest = findEntry(entries, capacity, entry->key);
  ...
  FREE_ARRAY(Entry, table->entries, table->capacity);
```

All objects (strings, functions, closures, upvalues, classes,
instances) are on one intrusive list `vm.objects`; `freeVM` walks it
(`c/memory.c:337`).  Allocation goes through `reallocate`, which may
run the mark-sweep collector (`c/memory.c:30-35`).

**External functions (20):** `clock`, `exit`, `fclose`, `fgets`,
`fopen`, `fprintf`, `fputs`, `fread`, `free`, `fseek`, `ftell`,
`malloc`, `memcmp`, `memcpy`, `printf`, `realloc`, `rewind`, `strlen`,
`strtod`, `vfprintf`; globals `stdin`, `stderr`.

**Changes for VST.**
- `Token` is passed and returned by value (e.g. `scanToken()`,
  `addLocal(Token name)`, `syntheticToken`): about 30 sites in
  `scanner.c`, 13 in `compiler.c`.  Rewrite to pass `Token*`.
- `runtimeError(const char* format, ...)` (`vm.c`) is a variadic
  definition; replace by fixed-argument variants.
- `NAN_BOXING` is on by default (`Value` is a `uint64_t` with type
  punning through `memcpy`).  Keeping it avoids struct-valued
  `Value`s; turning it off reintroduces struct passing.
- GC: either verify the mark-sweep collector (gray stack, reachability
  invariant) or disable collection, in which case objects live until
  `freeVM` and leak freedom at exit still holds.
- Error exits `exit(65)`, `exit(70)`, `exit(74)` skip `freeVM`.
- `Obj*` to `ObjString*` casts (struct "inheritance" by common first
  field) need a VST representation that relates the two layouts.

**clightgen -normalize:** 8 of 10 files accepted; `scanner.c` (55
errors) and `compiler.c` (31 errors) rejected, all "function
returning a struct or union" / "function parameter of struct or union
type" for `Token`.

## 3. huffman

**Heap use.**  The tree is built bottom-up from a 256-entry array of
node pointers; every new internal node gets back-pointers from both
children (`huffman.c:146-156`, `:445`):

```c
huffman_node* p = (huffman_node*)malloc(sizeof(huffman_node));
p->isLeaf = 0;
p->count = count;
p->zero = zero;
p->one = one;
...
pSF[0] = m1->parent = m2->parent = new_nonleaf_node(m1->count + m2->count, m1, m2);
```

The `zero`/`one` children share a union with `symbol`, selected by
`isLeaf` (`huffman.c:18-32`), so the tree predicate must follow the
tag.  `free_huffman_tree` recurses on that tag (`huffman.c:158-170`).

**External functions (22):** `__assert_fail`, `__errno_location`,
`__posix_getopt` (`getopt`), `fclose`, `feof`, `fgetc`, `fopen`,
`fprintf`, `fputc`, `fputs`, `fread`, `free`, `fwrite`, `htonl`,
`malloc`, `memcpy`, `memset`, `ntohl`, `qsort`, `realloc`, `rewind`,
`strerror`; globals `optarg`, `stdin`, `stdout`, `stderr`.

**Changes for VST.**
- `qsort(pSF, n, sizeof(pSF[0]), SFComp)` calls back into the program;
  replace with a local sort to avoid a higher-order trusted spec.
- Check `malloc`/`realloc` results (none are checked; a NULL
  return is dereferenced).
- `getopt`/`optarg`: either spec them or parse `argv` locally.
- `-m` mode returns before closing files (handles, not heap).

**clightgen -normalize:** `huffman.c` accepted unchanged (including the
anonymous struct in the union); `huffcode.c` accepted with
`-D_POSIX_C_SOURCE=200809L` (without it `getopt`/`optarg` are
undeclared).

## 4. sbase tsort

**Heap use.**  Insert into a sorted singly linked list through a
`prev` pointer whose head is a static sentinel (`tsort.c:54-70`):

```c
find_vertex(name, &vertex, &prev);
if (vertex)
	return vertex;

vertex = encalloc(2, 1, sizeof(*vertex));
vertex->name = name;
vertex->next = prev->next;
prev->next = vertex;
```

`sort_graph` later unlinks vertices without freeing them
(`tsort.c:167-169`), so nothing in the graph is ever freed.

**External functions (22 with the libutil helpers; tsort itself uses
about 12):** `__ctype_b_loc`, `__errno_location`, `calloc`, `exit`,
`fclose`, `ferror`, `fflush`, `fopen`, `fprintf`, `fputc`, `free`,
`getline`, `memset`, `perror`, `printf`, `realloc`, `strcmp`,
`strdup`, `strlen`, `strncmp`, `strndup`, `vfprintf`.

**Changes for VST.**  Add a teardown that frees vertices, edges and
names (including the ones `sort_graph` unlinks); replace libutil's
variadic `eprintf`/`enprintf`/`weprintf` with fixed-argument error
functions; replace `isspace`.

**clightgen -normalize:** `tsort.c`, `ealloc.c`, `eprintf.c`,
`fshut.c`, `reallocarray.c` all accepted (`tsort.c` and `ealloc.c`
need `-D_POSIX_C_SOURCE=200809L` to declare `getline`, `strdup`,
`strndup`).

## Ranking

1. **picol.**  The smallest complete program here with real heap
   structure: linked lists, a frame stack, growable arrays, strings
   with ownership moving between them, and indirect calls.  It is
   leak-clean today when run on a file, clightgen accepts it
   unchanged, and it calls 18 external functions, all ordinary stdio
   and string functions.  It was updated in February 2026 by a
   well-known author, under BSD-2, and ships unit tests.  The proc
   redefinition use-after-free above means the proof has a real bug
   to find, which shows the `main` spec is not trivially true.
2. **clox.**  The richest heap of the set (hash tables, object graph,
   closures) with a 265-program test suite, MIT, and very well
   known through the Crafting Interpreters book.  It needs the most
   preparation: `Token` by-pointer rewrite in two rejected files, a
   fixed-argument `runtimeError`, and a decision on the GC.  At about
   2.6k code lines it is a good second target once picol has shown
   the workflow on a whole program.
3. **huffman.**  A self-contained program with a tagged-union tree
   with parent pointers, accepted by clightgen as is.  Its costs are
   the `qsort` callback, unchecked `malloc`, and `getopt`; it is
   dormant since 2021.  Good if a non-interpreter target is wanted.
4. **sbase tsort.**  Tiny, actively maintained, MIT; a sorted
   linked-list graph.  It is not leak-clean (the graph is never
   freed), so the leak-freedom claim needs an added teardown.  Better
   as a warm-up than as the main target.

Not recommended: sbase dc (heap-rich and well tested, but error
recovery is `setjmp`/`longjmp` through `eval`), smu (heap is only char
buffers; `regex_t` is an opaque external), kilo (TTY, signals, no
tests), md4c (8.8k code lines), re1 and brenns10/lisp (dormant, no
tests), c4 (GPL-2).
