# Complete public replay packet

This is the byte-identical 580-file standalone packet independently replayed for the all-positive-odd resolution. No private repository or network access is needed to run it. The archive includes full handwritten component proofs, actual certificate data, inputs, generators, numerical and independent checkers, reviews and recovery metadata. Python 3 and a C++20 compiler are required. The named external analytic publications remain mathematical imports, not kernel-checked dependencies.

Download [part 1](resolution-packet.zip.part1?raw=true) and [part 2](resolution-packet.zip.part2?raw=true), retaining their names, then run from their directory:

```sh
cat resolution-packet.zip.part1 resolution-packet.zip.part2 > resolution-packet.zip
printf '%s  %s\n' 9f7580594e535deb32421def057438e862db7b6c1bb140c8929c21f7def3a650 resolution-packet.zip | sha256sum -c -
unzip resolution-packet.zip -d resolution-packet
cd resolution-packet
python3 verify_packet.py
python3 -B problems/prime-line-sums/code/verify_sude_all_odd.py
```

Expected final status: `PASS_ALL_POSITIVE_ODD_ORDERS_FINITE_CERTIFICATE`. Read `START_HERE.md` and `problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md` inside the archive. The file-only replay does not require any historical Git objects. Optional Git-history audits are separate.

| File | Bytes | SHA-256 |
|---|---:|---|
| part 1 | 8071459 | `56517f1d05a9ac77b543678c95a8f71227af35bbb8db1fb812df7140c3fe2135` |
| part 2 | 8071458 | `294aec3bffea7f359d06d529674ef39779e99ee28168faa5a807ce95a3d13e30` |
| reconstructed ZIP | 16142917 | `9f7580594e535deb32421def057438e862db7b6c1bb140c8929c21f7def3a650` |

The neighbouring `proof-source/` folder is a byte-identical browsable selection of the directly cited manuscripts, not the full source tree. Follow cross-references in the extracted archive, where all packet paths are present. Historical private-repository links in unchanged source manuscripts are provenance, not required downloads.
