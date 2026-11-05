# sglib's self-test (`../sglib/selftest.c`)

sglib's own test program, vendored unmodified (`../sglib/README.md`).
It runs eight tests (arrays, lists, hashed list, doubly linked list,
sorted list, red-black tree), ten passes each, on 1000 random values,
and checks every result with `assert`.  Plan Q12 uses its doubly linked
list test as a second client of B1's contracts.

```bash
./check.sh        # seed 1; ./check.sh 7 for seed 7.  Needs the M0 image.
```

## Fixed seed

`main` calls `srandom(time(NULL))`.  The file stays unmodified: it is
linked with `seed.c` under `-Wl,--wrap=time`, so its call to `time`
goes to `__wrap_time`, which returns the seed (`SELFTEST_SEED`, default
1).  `check.sh` checks in the binary that the call goes to
`__wrap_time`.

## Result

| Build | Seeds | Result |
|-------|-------|--------|
| gcc 12, `-fsanitize=address,undefined -fno-sanitize-recover=all`, LeakSanitizer on | 1, 7, 12345 | passes: exit 0, no sanitizer report, no failed `assert` (about 2 s) |
