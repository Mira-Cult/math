#!/usr/bin/env python3
"""Reproduce the four FT geometric-versus-packed block checks.

Run from any directory. By default this writes the four Lean sources to a new
system temporary directory; pass --run to check them sequentially with
LEAN_NUM_THREADS=1 and macOS /usr/bin/time -l. The benchmark does not build
Lean dependencies or modify certificate sources. It uses the existing built
dependencies, which must match the checkout. Scratch files are retained for
inspection, and no raw timing logs are written.

Observed on 2026-11-04 at source revision c052e689f0211f27febfd952a8d6034421ee1517,
Lean 4.33.1, one run in fixed geometric-then-packed order: S013C00 geometric 8.93 s / 4,141,744,128 B and packed 11.88 s /
4,309,221,376 B; S012C00 geometric 8.74 s / 4,138,795,008 B and packed
12.14 s / 4,307,222,528 B. These host timings are single observations,
without cache control or repetition; they do not establish general speedup.
The input hash check covers the two plans and three scanner modules, not the
entire transitive dependency closure or host environment.
"""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = 'leanprover/lean4:v4.33.1'
EXPECTED_INPUTS = {
    'Sude/TwinGeometricScan.lean': '40a2a98d656a77352351a5388863f23257df46a2547db12c2cf74ffb76dfec65',
    'Sude/TwinGeometricPackedScan.lean': 'f7fac538c6b2e08435fd09062e9308aa730ef5e3199a79f92bbd2692b3b72eb4',
    'Sude/TwinPackedCounting.lean': '96420afe17ef502126dcb399e357fc78ea0e62274cc8f6344c83f0e45ee92bd9',
    'Sude/GeneratedTwinScan/S013C00.lean': '8e75ff609ebf4c51ad463eba8fbeb506c8e627436aec234d4d8bc325735023ab',
    'Sude/GeneratedTwinScan/S012C00.lean': '91a656fbf52e3227a4c03becea64ab1690c912c0ac51ec1e040232c87c99aa51',
}
CASES = (
    ('S013C00_geometric', 27263021, 128, 'geometricActiveStreamingTwinScan',
     'ecd6cf1cbfbb6858d547847a5cc0b2ea4a1e32c7110f56833d0138a0a0495df9'),
    ('S013C00_packed', 27263021, 128, 'geometricPackedTwinScan',
     '8c7c8571a2b8e6002d6322a3da36c10de0044bf7e666078031f05a54928ee448'),
    ('S012C00_geometric', 25165869, 134, 'geometricActiveStreamingTwinScan',
     'de2903373ed5b80a4cdf3dfb1866f31ba234a5facc202ed3920642abccd75865'),
    ('S012C00_packed', 25165869, 134, 'geometricPackedTwinScan',
     '8a42f01cca44b526bb912822dee445305c0193a62dc1df4db13ec8c622f16c47'),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source(lo, count, scanner):
    return f'''import Sude.FiniteTwinOddBaseComplete
import Sude.TwinGeometricPackedScan

namespace Sude.TwinBench
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths : List ℕ := [4096, 4096, 4096, 4096]
theorem checked : {scanner} finiteTwinCheckedBase {lo} widths = {count} := by
  decide +kernel
end Sude.TwinBench
'''.encode('utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true',
                        help='run the four kernel checks sequentially with macOS time -l')
    args = parser.parse_args()
    if (ROOT / 'lean-toolchain').read_text().strip() != EXPECTED_TOOLCHAIN:
        raise RuntimeError('pinned Lean toolchain differs from the measured run')
    for name, expected in EXPECTED_INPUTS.items():
        if digest((ROOT / name).read_bytes()) != expected:
            raise RuntimeError(f'benchmark input changed: {name}')
    if args.run and (sys.platform != 'darwin' or not Path('/usr/bin/time').is_file()):
        raise RuntimeError('--run requires macOS /usr/bin/time -l')
    if args.run and shutil.which('lake') is None:
        raise RuntimeError('--run requires lake on PATH and prebuilt Lean dependencies')
    scratch = Path(tempfile.mkdtemp(prefix='sude-twin-scanner-bench-'))
    print(f'Scratch source directory: {scratch}', flush=True)
    for name, lo, count, scanner, expected in CASES:
        data = source(lo, count, scanner)
        if digest(data) != expected:
            raise RuntimeError(f'generated source differs from measured source: {name}')
        path = scratch / f'{name}.lean'
        with path.open('xb') as handle:
            handle.write(data)
        print(f'{name}: SHA-256 {expected}', flush=True)
    if not args.run:
        print('Sources generated only; pass --run to execute the four checks.')
        return
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    for name, _, _, _, _ in CASES:
        path = scratch / f'{name}.lean'
        command = ['/usr/bin/time', '-l', 'lake', 'env', 'lean', str(path)]
        print(f'Running {name}', flush=True)
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        if result.returncode:
            print(result.stdout, result.stderr, file=sys.stderr)
            raise RuntimeError(f'{name} failed with exit status {result.returncode}')
        if result.stdout:
            print(result.stdout, end='', flush=True)
        for line in result.stderr.splitlines():
            if ' real ' in line or 'maximum resident set size' in line:
                print(line, flush=True)
    print('All four kernel checks passed; these are single-run host measurements.')


if __name__ == '__main__':
    main()
