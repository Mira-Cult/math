"""Independent complete literal equations using the pinned nonauthor reader."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parents[2] / "repeated_control/review/physical/check_rows.py"
PIN = "60d9fdd8bde1e7826709de5b187e4152284540f895515a9f0e1988934ce6196a"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


assert sha(PRIOR) == PIN
spec = importlib.util.spec_from_file_location("independent_control_mode_row_reader", PRIOR)
prior = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prior)


def run(parent, selected):
    result = prior.run(parent, selected)
    result["format"] = "np-conp-control-mode-independent-rows-v1"
    result["wrapper_sha256"] = sha(__file__)
    result["pinned_reader_sha256"] = PIN
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("parent", "selected", "out"):
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    result = run(args.parent, args.selected)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps(result["completion"], sort_keys=True))
