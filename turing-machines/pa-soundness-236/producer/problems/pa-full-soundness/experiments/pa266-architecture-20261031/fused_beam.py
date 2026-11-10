#!/usr/bin/env python3
"""Compose the paid beam grammar with event fusion; complete blank-start table."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import fused_output
import beam_rebind


class FusedBeam(fused_output.FusedOutput,beam_rebind.BeamGrammar):
    pass


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(fused_output.compile_candidate(FusedBeam,args.out)[1],indent=2))
