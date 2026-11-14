#!/usr/bin/env python3
"""Print the header of a Lean 4 .olean (v2 layout)."""
import struct, sys
b = open(sys.argv[1], "rb").read()
print("magic", b[:5], "version", b[5], "flags", b[6])
print("lean", b[7:40].split(b"\0")[0].decode(), "githash", b[40:80].split(b"\0")[0].decode())
base = struct.unpack("<Q", b[80:88])[0]
print("base_addr", hex(base), "64KiB aligned", base % 65536 == 0, "size", len(b))
