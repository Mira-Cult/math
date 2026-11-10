#!/usr/bin/env python3
"""Check the eight M236 source generators in a temporary source copy."""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
GENERATORS = (
    'generate_m236.py', 'generate_m236_bootstrap.py',
    'generate_m236_grammar.py', 'generate_m236_graph_text.py',
    'generate_m236_metadata_binding.py', 'generate_m236_occurrence_graph.py',
    'generate_m236_runtime.py', 'generate_m236_text_binding.py',
)
with tempfile.TemporaryDirectory(prefix='m236-regenerate-') as tmp:
    copy = Path(tmp) / 'formalization'
    shutil.copytree(ROOT / 'formalization', copy,
                    ignore=shutil.ignore_patterns('.lake','__pycache__'))
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    for name in GENERATORS:
        print(name, flush=True)
        subprocess.run([sys.executable, str(copy/'code'/name), '--check'], env=env, check=True)
print('All eight M236 generators reproduced their checked-in source inputs.')
print('Generator reproduction is not a Lean proof or an infinite-execution check.')
