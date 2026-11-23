/* Ariadne: functions picol.c calls that are trusted, not verified with VST.
 * Each has an owner-approved spec (README.md, "Trusted functions"). */
#include <stdio.h>

/* snprintf(buf,n,"%.12g",v): VST cannot verify a variadic call, and musl's
 * float formatting uses long double, which CompCert rejects. */
void fmt_double(char *buf, size_t n, double v) {
    snprintf(buf,n,"%.12g",v);
}
