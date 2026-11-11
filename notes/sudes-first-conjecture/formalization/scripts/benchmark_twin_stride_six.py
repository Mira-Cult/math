#!/usr/bin/env python3
"""Prepare or run bounded kernel-only twin-scanner comparisons.

From formalizations/sude, run this script without flags to write six Lean
sources in a new temporary directory. Pass --run only after coordinating a
quiet host. Each pair checks the same half-open interval and proposed count;
the geometric scanner uses four odd widths of 4096, while the compressed
scanner uses one internally aligned interval. Both invoke `decide +kernel`.
The Python count hints are not proofs; Lean must accept every numerical claim.

This script checks the listed source hashes and pinned toolchain, not the full
transitive dependency closure or the provenance of cached .olean files. Build
and audit dependencies at the intended revision before running. The six
checks run sequentially in a fixed order with one Lean thread. Capture logs
and generated files only in the temporary output directory, not in Git.
Single runs include startup, cache, and load effects and do not justify a
universal speedup or extrapolation to the full finite-twin scan.
"""

import argparse
import hashlib
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = 'leanprover/lean4:v4.33.1'
EXPECTED = {
    'Sude/TwinStrideSixCompressed.lean': '040d2d3a70def8aa2d8592af73d076b8b06a4c1ac4af622d31e93124ce64da55',
    'Sude/TwinStrideSixScan.lean': '7221458f0ba5d8b3c4333524f1f1d9853c4c8c8132a6fa190b6be229a4f34792',
    'Sude/TwinGeometricScan.lean': '40a2a98d656a77352351a5388863f23257df46a2547db12c2cf74ffb76dfec65',
    'Sude/TwinProgressionMask.lean': '74b06767193f1eb770cbd97be948a4f3eef65cf22edc923971a1c4f76896f91a',
    'Sude/FiniteTwinOddBaseComplete.lean': '954d108b985c5717743c264aa7aeb726512768d06f37aeeebfb1170f254f27ff',
    'Sude/ActiveTwinBase.lean': 'a37588667d262b4ef3a1ec7fe659fbc44264c24a3f0990a951617de770d76b1e',
    'Sude/TwinStreaming.lean': 'd2b86bc18084d4f03c28677ce109f917ade900a8569e146fce79eca6fe1c6103',
}
# Labels describe position in the full 2^30 interval, not separate source claims.
# Counts are untrusted hints, subsequently checked by `decide +kernel`.
CASES = (
    ('low', 25165869, 25198637, 134),
    ('middle', 538968109, 539000877, 104),
    ('high', 1073709055, 1073741823, 90),
)
# Interleave order to avoid always giving the same scanner the earlier slot.
ORDER = (('low', 'geometric'), ('low', 'compressed'),
         ('middle', 'compressed'), ('middle', 'geometric'),
         ('high', 'geometric'), ('high', 'compressed'))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source(lo, hi, count, scanner):
    if hi - lo != 2 * 4 * 4096:
        raise ValueError('comparison interval differs from the geometric plan')
    if scanner == 'geometric':
        term = f'geometricActiveStreamingTwinScan finiteTwinCheckedBase {lo} [4096,4096,4096,4096]'
    elif scanner == 'compressed':
        term = f'strideSixCompressedIntervalScan finiteTwinCheckedBase {lo} {hi}'
    else:
        raise ValueError('unknown scanner')
    return f'''import Sude.FiniteTwinOddBaseComplete
import Sude.TwinStrideSixCompressed

namespace Sude.TwinStrideSixBenchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : {term} = {count} := by
  decide +kernel
end Sude.TwinStrideSixBenchmark
'''.encode('utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--run', action='store_true', help='execute the six checks sequentially')
    parser.add_argument('--timeout-seconds', type=int, default=300,
                        help='maximum seconds per check (default: 300)')
    args = parser.parse_args()
    if args.timeout_seconds < 1:
        parser.error('--timeout-seconds must be positive')
    if (ROOT / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise RuntimeError('pinned Lean toolchain differs')
    for name, expected in EXPECTED.items():
        if digest((ROOT / name).read_bytes()) != expected:
            raise RuntimeError(f'benchmark input hash changed: {name}')
    if args.run and (sys.platform != 'darwin' or not Path('/usr/bin/time').is_file()):
        raise RuntimeError('--run requires macOS /usr/bin/time -l')
    if args.run and shutil.which('lake') is None:
        raise RuntimeError('--run requires lake and prebuilt dependencies')
    scratch = Path(tempfile.mkdtemp(prefix='sude-stride-six-bench-'))
    cases = {label: (lo, hi, count) for label, lo, hi, count in CASES}
    paths = {}
    for label, scanner in ORDER:
        lo, hi, count = cases[label]
        path = scratch / f'{label}_{scanner}.lean'
        data = source(lo, hi, count, scanner)
        with path.open('xb') as output:
            output.write(data)
        paths[(label, scanner)] = path
        print(f'{label} {scanner}: [{lo}, {hi}), expected {count}, source SHA-256 {digest(data)}', flush=True)
    print(f'Scratch directory: {scratch}', flush=True)
    if not args.run:
        print('Prepared only; no Lean checks or timings were run.', flush=True)
        return
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    for label, scanner in ORDER:
        path = paths[(label, scanner)]
        log = path.with_suffix('.log')
        command = ['/usr/bin/time', '-l', 'lake', 'env', 'lean', str(path)]
        print(f'Running {label} {scanner}', flush=True)
        with log.open('xb') as output:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                status = process.wait(timeout=args.timeout_seconds)
            except subprocess.TimeoutExpired as exc:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                raise RuntimeError(f'{label} {scanner} timed out; see {log}') from exc
        if status:
            raise RuntimeError(f'{label} {scanner} failed ({status}); see {log}')
        content = log.read_text(errors='replace')
        elapsed = re.search(r'^\s*([0-9.]+) real\s', content, re.MULTILINE)
        rss = re.search(r'^\s*([0-9]+)\s+maximum resident set size', content, re.MULTILINE)
        if elapsed is None or rss is None:
            raise RuntimeError(f'{label} {scanner} missing time data; see {log}')
        print(f'{label} {scanner}: {elapsed.group(1)} s, peak RSS {rss.group(1)} bytes', flush=True)
    print('All six numerical claims kernel-checked; timings are single observations.', flush=True)


if __name__ == '__main__':
    main()
