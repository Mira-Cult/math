#!/usr/bin/env python3
"""Reproduce the 15 example dispatcher paths. Lean checks their actual rows.

This deterministic BFS is provenance only; it does not prove path exhaustion
or identify which paths are reached by the source controller.
"""
from collections import deque
from pathlib import Path
import argparse
import re

HERE = Path(__file__).resolve().parent
TERMINALS = [76, 78, 90, 92, 94, 96, 98, 100, 102, 104, 80, 82, 84, 86, 88]


def read_table():
    rows = {}
    for line in (HERE / "events.tm").read_text().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        state, read, write, move, nxt, flag = line.split()
        rows[(int(state), int(read))] = (int(write), move, int(nxt), int(flag))
    if len(rows) != 570:
        raise ValueError("expected exactly 570 distinct transition rows")
    return rows


def paths(rows):
    pending = deque([(284, "")])
    seen = {284}
    found = {}
    while pending:
        state, code = pending.popleft()
        if state in TERMINALS:
            found[state] = code
            continue
        for bit in (0, 1):
            write, move, nxt, flag = rows[(state, bit)]
            if write == bit and move == "R" and flag == 0 and nxt not in seen:
                seen.add(nxt)
                pending.append((nxt, code + str(bit)))
    return [found[state] for state in TERMINALS]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = paths(read_table())
    if args.check:
        text = (HERE / "SymbolicDispatchCore.lean").read_text()
        actual = re.findall(r'^  \| (\d+) => "([01]+)"$', text, re.MULTILINE)
        if actual != [(str(i), code) for i, code in enumerate(result)]:
            raise SystemExit("path source does not match deterministic extraction")
        print("15 example paths match the literal table extraction; not an exhaustiveness proof")
    else:
        for i, code in enumerate(result):
            print(f'  | {i} => "{code}"')


if __name__ == "__main__":
    main()
