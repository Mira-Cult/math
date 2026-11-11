#!/usr/bin/env python3
"""Reproduce two bounded kernel-comparison inputs for the twin sieve.

From formalizations/sude run:
  python3 scripts/benchmark_twin_geometric.py --output-dir "$TMPDIR/sude-twin-bench"
  # Run the four printed commands sequentially, from formalizations/sude; or:
  python3 scripts/benchmark_twin_geometric.py --output-dir "$TMPDIR/sude-twin-bench-run" --run

The generated pairs use identical imports, definitions and fixed inputs. The
old and geometric results for S013 start at 27263021, with checked count 128;
those for S012C00 start at 25165869, with checked count 134. Every input uses
four 4096-candidate widths. The earlier unusually slow S012 component was
not identified; S012C00 is a representative input, not that slow case.

Commands use the pinned lake toolchain, one Lean thread, `decide +kernel`,
and macOS `/usr/bin/time -l`. Logs, generated sources, and build products are
not research evidence until the commands exit successfully; keep them out of
Git. Single ordered runs include startup, cache and host-load effects and do
not establish a general speedup. The `--run` option stops on any failure.
"""

import argparse
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREAMBLE = '''import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinProgressionMask

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Sude

def benchmarkGeometricScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      streamTwinCount (geometricSegmentMarkBits
        (activeMarkingBase base lo (width + 1)) lo (width + 1)) width +
      benchmarkGeometricScan base (lo + 2 * width) widths

theorem benchmarkGeometricScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    benchmarkGeometricScan base lo widths = activeStreamingTwinScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [benchmarkGeometricScan, activeStreamingTwinScan, geometricSegmentMarkBits_eq, ih]
'''
CASES = [
    ('s013_old', 'activeStreamingTwinScan', 27263021, 128),
    ('s013_geometric', 'benchmarkGeometricScan', 27263021, 128),
    ('s012_old', 'activeStreamingTwinScan', 25165869, 134),
    ('s012_geometric', 'benchmarkGeometricScan', 25165869, 134),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output-dir', type=Path,
                        help='scratch output directory (default: a new TMPDIR directory)')
    parser.add_argument('--run', action='store_true',
                        help='execute the four commands sequentially; save time output in scratch')
    args = parser.parse_args()
    out = args.output_dir or Path(tempfile.mkdtemp(prefix='sude-twin-bench-'))
    out.mkdir(parents=True, exist_ok=True)
    targets = [out / f'sude_bench_{name}.{suffix}'
               for name, _, _, _ in CASES for suffix in ('lean', 'log')]
    occupied = [p for p in targets if p.exists() or p.is_symlink()]
    if occupied:
        raise FileExistsError(f'refusing to overwrite benchmark file: {occupied[0]}')
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    for name, function, lo, count in CASES:
        src = out / f'sude_bench_{name}.lean'
        log = out / f'sude_bench_{name}.log'
        src.write_text(PREAMBLE +
            f'\nexample : {function} finiteTwinCheckedBase {lo} '
            f'[4096,4096,4096,4096] = {count} := by\n  decide +kernel\n')
        command = ['/usr/bin/time', '-l', 'lake', 'env', 'lean', str(src.resolve())]
        print('LEAN_NUM_THREADS=1 ' + shlex.join(command) + ' > ' +
              shlex.quote(str(log.resolve())) + ' 2>&1', flush=True)
        if args.run:
            with log.open('w') as output:
                subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                               stderr=subprocess.STDOUT, check=True)


if __name__ == '__main__':
    main()
