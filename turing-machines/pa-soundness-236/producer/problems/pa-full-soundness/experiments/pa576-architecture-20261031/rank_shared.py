#!/usr/bin/env python3
"""Compose the restoring finite-table bound with the shared lookup interface."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import restoring_bound
import shared_lookup
p=restoring_bound.p


class RankSharedLookup(restoring_bound.RestoringBound,shared_lookup.HSharedLookup):
    pass


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(RankSharedLookup,args.out)[1],indent=2))
