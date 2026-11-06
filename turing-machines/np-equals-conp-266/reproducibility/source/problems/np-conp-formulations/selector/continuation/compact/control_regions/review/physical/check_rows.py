"""Nonauthor complete-row equations through all fresh physical maps."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parents[2] / 'operand_dispatch/review/physical/check_rows.py'
PIN = '9a8a1b4c1cf8a2e3826b2c3429537899f47f8f6e8a73e7b7ae41bdfc20ce0f07'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


assert sha(PRIOR) == PIN
spec = importlib.util.spec_from_file_location('control_regions_independent_row_reader', PRIOR)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)


def run(parent, selected):
    result = prior.run(parent, selected)
    result['format'] = 'np-conp-occurrence-control-independent-rows-v1'
    result['reviewer'] = 'internal-model-reviewer; nonauthor of selected producer'
    result['wrapper_sha256'] = sha(__file__)
    result['pinned_reader_sha256'] = PIN
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('parent', 'selected', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    result = run(args.parent, args.selected)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps(result['completion'], sort_keys=True))
