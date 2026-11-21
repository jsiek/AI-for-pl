"""Download musl 1.2.6 into libc/musl-1.2.6/ (git-ignored), checking the
pinned SHA-256.  usage: python3 -I fetch_musl.py"""
import hashlib, os, tarfile, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
VERSION = "1.2.6"
SHA256 = "d585fd3b613c66151fc3249e8ed44f77020cb5e6c1e635a616d3f9f82460512a"

dest = os.path.join(HERE, "musl-" + VERSION)
if os.path.isdir(dest):
    raise SystemExit(dest + " exists")
tgz = dest + ".tar.gz"
urllib.request.urlretrieve(
    "https://musl.libc.org/releases/musl-%s.tar.gz" % VERSION, tgz)
got = hashlib.sha256(open(tgz, "rb").read()).hexdigest()
if got != SHA256:
    os.remove(tgz)
    raise SystemExit("sha256 mismatch: " + got)
with tarfile.open(tgz) as t:
    t.extractall(HERE, filter="data")
os.remove(tgz)
print("musl", VERSION, "in", dest)
