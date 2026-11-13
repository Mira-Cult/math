"""Check complete output identity of both tweet entries and reviewed source.

No finite sample is used: compare every byte of the generated polynomial.
The packed program must decompress to the entire uncompressed tweet program.
This is a representation check, not an arithmetic projection theorem.
"""
import ast
import base64
import hashlib
import json
import subprocess
import sys
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPECTED_OUTPUT = 'be0026c879a1aec7d9fceafaee1f2e2c14ca7744f1b77faa58c37284f4a1fd87'
EXPECTED_SOURCES = {
    'generate.py': (2518, 'd94a1ddb453ba515f30e8d08f69403cf609e350033a54f3f9f887e6bf1f45be6'),
    'tweet.py': (2200, 'f5aff4f2279a3204715dfbc0038162980a093b26e183b2f15b7894ac756fa021'),
    'tweet_packed.py': (1520, '0b5878b9ddd1c4516aa7b92833acfc1373dcf33ee3678bcc8f5c75667e95a9e5'),
}


def check():
    sources = {name: (HERE/name).read_bytes() for name in EXPECTED_SOURCES}
    outputs = {}
    for name, (size, digest) in EXPECTED_SOURCES.items():
        assert sources[name].isascii(), name
        assert len(sources[name]) == size, name
        assert hashlib.sha256(sources[name]).hexdigest() == digest, name
        outputs[name] = subprocess.check_output([sys.executable, str(HERE/name)])
    reference = outputs['generate.py']
    assert len(reference) == 99397
    assert hashlib.sha256(reference).hexdigest() == EXPECTED_OUTPUT
    assert all(output == reference for output in outputs.values())

    golf_ast = ast.parse(sources['tweet.py'])
    assert not any(isinstance(n, (ast.Import, ast.ImportFrom)) for n in ast.walk(golf_ast))
    packed_ast = ast.parse(sources['tweet_packed.py'])
    imports = [a.name for n in ast.walk(packed_ast) if isinstance(n, ast.Import) for a in n.names]
    assert imports == ['zlib', 'base64']
    decoder_calls = [n for n in ast.walk(packed_ast)
                     if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                     and n.func.attr == 'b85decode']
    assert len(decoder_calls) == 1
    payload = ast.literal_eval(decoder_calls[0].args[0])
    assert zlib.decompress(base64.b85decode(payload), -15) == sources['tweet.py']
    return {
        'source_bytes': {name: len(data) for name, data in sources.items()},
        'output_bytes_including_newline': len(reference),
        'output_sha256': EXPECTED_OUTPUT,
        'all_outputs_byte_identical': True,
        'packed_program_contains_full_tweet_program': True,
        'tweet_has_no_imports': True,
        'packed_imports': imports,
        'scope': 'Complete finite output identity; arithmetic premises are inherited.'
    }


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
