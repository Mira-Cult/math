"""Download pinned public TM inputs and verify their exact byte hashes."""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    sources = json.loads(Path(__file__).with_name('sources.json').read_text())
    args.directory.mkdir(parents=True, exist_ok=True)
    for name, source in sources['machines'].items():
        with urlopen(source['raw_url'], timeout=60) as response:
            content = response.read()
        digest = hashlib.sha256(content).hexdigest()
        if digest != source['sha256']:
            raise ValueError(f'Unexpected source bytes for {name}: {digest}')
        output = args.directory / (name + '.tm')
        output.write_bytes(content)
        print(f'{name}: {digest} -> {output}')


if __name__ == '__main__':
    main()
