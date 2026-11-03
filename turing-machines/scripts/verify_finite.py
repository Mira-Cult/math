#!/usr/bin/env python3
"""Compatibility entry point; canonical implementation is in the Collatz family."""
from pathlib import Path
import runpy

if __name__ == "__main__":
    runpy.run_path(str(Path(__file__).resolve().parents[1] /
                      "collatz/scripts/verify_finite.py"), run_name="__main__")
