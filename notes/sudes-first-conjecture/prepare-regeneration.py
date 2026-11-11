#!/usr/bin/env python3
"""Verify release sources and copy them into a new original-layout scratch tree.

This does not run generators, Lean, or the finite replay. The output must not
already exist. No symlinks are created or accepted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

def safe(root, relative):
    rel = Path(relative)
    if rel.is_absolute() or not rel.parts or '..' in rel.parts:
        raise ValueError('unsafe relative path: ' + relative)
    path = root / rel
    if any(p.is_symlink() for p in (path, *path.parents)):
        raise ValueError('symlink in source or destination: ' + str(path))
    return path

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new original-layout scratch directory')
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    manifest = json.loads((base / 'source-manifest.json').read_text())
    output = args.output.expanduser().absolute()
    if output.exists() or any(p.is_symlink() for p in output.parents):
        raise ValueError('output must be a new path without symlink ancestors')
    rows = manifest['files']
    seen = set()
    for row in rows:
        path = safe(base, row['export_path'])
        if not path.is_file():
            raise ValueError('missing source: ' + row['export_path'])
        raw = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256'] or blob != row['git_blob']:
            raise ValueError('source identity mismatch: ' + row['export_path'])
        safe(output, row['source_path'])
        if row['source_path'] in seen:
            raise ValueError('duplicate original path')
        seen.add(row['source_path'])
    output.mkdir(parents=True)
    for row in rows:
        dest = safe(output, row['source_path'])
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(safe(base, row['export_path']), dest)
        dest.chmod(int(row['mode'], 8) & 0o777)
    required = manifest['generation']['required_original_paths']
    missing = [p for p in required if not safe(output, p).is_file()]
    if missing:
        raise ValueError('missing generator input: ' + repr(missing))
    print(json.dumps({'status':'PASS_SOURCE_IDENTITIES_AND_LAYOUT', 'files':len(rows),
                      'generator_input_paths':len(required), 'output':str(output),
                      'executed_generators':False, 'executed_lean':False,
                      'executed_finite_replay':False}, sort_keys=True))

if __name__ == '__main__':
    main()
