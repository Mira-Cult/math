#!/usr/bin/env python3
"""Run FT segment certificates sequentially; stop on any failed proof.

Run from formalizations/sude. Each generated numerical hint is checked by
Lean; this script is orchestration only. It never modifies Git state.
Existing generated targets are never overwritten: to resume an existing
segment, inspect its complete source set, build its aggregate directly, then
start at the next fresh segment. For partial output, investigate and recover
in an isolated scratch location; do not assume filenames are proof.
"""
import argparse
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

MIN_FREE_BYTES = 20 * (1 << 30)
ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--start', type=int, required=True)
    parser.add_argument('--end', type=int, default=511)
    parser.add_argument('--after-pid', type=int)
    parser.add_argument('--require-segment', type=int)
    args = parser.parse_args()
    if not 0 <= args.start <= args.end <= 511:
        raise ValueError('segment bounds must lie in 0..511')
    os.chdir(ROOT)
    if args.after_pid is not None:
        while True:
            try:
                os.kill(args.after_pid, 0)
            except ProcessLookupError:
                break
            time.sleep(30)
    if args.require_segment is not None:
        if not 0 <= args.require_segment <= 511:
            raise ValueError('required segment must lie in 0..511')
        subprocess.run(['lake', 'build', f'Sude.GeneratedTwinScan.S{args.require_segment:03}All'], check=True)
    for segment in range(args.start, args.end + 1):
        if shutil.disk_usage(ROOT).free < MIN_FREE_BYTES:
            raise RuntimeError('stopped before next segment: less than 20 GiB free')
        print(f'Generating segment {segment:03}', flush=True)
        subprocess.run([sys.executable, 'scripts/generate_twin_segment.py', str(segment)], check=True)
        print(f'Kernel-checking segment {segment:03}', flush=True)
        subprocess.run(['lake', 'build', f'Sude.GeneratedTwinScan.S{segment:03}All'], check=True)
        print(f'Accepted segment {segment:03}', flush=True)


if __name__ == '__main__':
    main()
