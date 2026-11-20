#!/bin/sh
# Compile and run each stage-1 client under ASan/UBSan (leaks included:
# LeakSanitizer is on by default with -fsanitize=address).  Prints one
# PASS/FAIL line per client; exits non-zero on any FAIL.
#   ./run_asan.sh          (from this directory; needs gcc)
set -u
status=0
tmp=$(mktemp -d)
for c in client1 client2 client3 client4 client5 client6 client7 \
         client8 client9 clientb1 clientb1a clientb1c clientst; do
  if gcc -std=c99 -Wall -Werror -fsanitize=address,undefined \
       -fno-sanitize-recover=all -g -o "$tmp/$c" "$c.c" \
     && ASAN_OPTIONS=detect_leaks=1 "$tmp/$c"; then
    echo "PASS: $c (ASan/UBSan/LSan clean)"
  else
    echo "FAIL: $c"
    status=1
  fi
done
rm -r "$tmp"
exit $status
