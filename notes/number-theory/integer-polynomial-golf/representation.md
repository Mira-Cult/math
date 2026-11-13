# Exact short representations of the reviewed quartic

The mathematical source and proof were frozen at
`1dc330d814a5e57bbd11d93bbb77fd02094bd062`. Its
[independent mathematical review](reviews/construction.md) concerns
[`code/generate.py`](code/generate.py), [the complete proof](proof.md),
[the uniform-factor lemma](uniform-factors.md), and [the source scope](source-scope.md).
Those four files are unchanged in this representation step.

## What the length counts

Lengths count every ASCII byte in the complete executable source, including
imports, literal data and any terminal newline. The 2,200-byte file has no
terminal newline; the 1,520-byte file includes one. Since every character is
ASCII, these byte lengths equal character counts. Captions, explanations and
attribution outside the program are separate text. No 280-character solution
or global optimality is claimed.

| Representation | Complete source bytes | Runtime dependencies |
|---|---:|---|
| Readable reviewed source | 2,518 | Python built-ins |
| Uncompressed golfing entry | 2,200 | Python built-ins |
| Compressed golfing entry | 1,520 | Python standard-library `zlib` and `base64` |

All three print exactly the same polynomial expression. All constants and
instructions are included. No custom module, URL, external input, theorem
search, or existing polynomial is consulted at runtime.

## Uncompressed golfing entry

[`code/tweet.py`](code/tweet.py) shortens identifiers and boilerplate while
retaining the reviewed gate sequence. Its finite allocator is
`iter(range(3779))`. It defines three fixed scalar operator methods by `exec`
from the literal operation names `add,sub,mul` and symbols `+,-,*`.
There is no external code input. Its field-power recursion produces the same
left-associated multiplication sequence as the readable implementation.
Unused interfaces are omitted, and the output is printed directly.

The decisive verification is whole-output equality with the reviewed
generator, not an inference from similar-looking code. Executing each complete
program and comparing their full stdout gives 99,397 identical bytes, including
the newline after the polynomial. The common SHA-256 is

`be0026c879a1aec7d9fceafaee1f2e2c14ca7744f1b77faa58c37284f4a1fd87`.

## Compressed golfing entry

[`code/tweet_packed.py`](code/tweet_packed.py) contains a Base85 representation
of a raw DEFLATE stream. Decompression gives all 2,200 bytes of `tweet.py`,
which the wrapper executes. Its 1,520-byte count includes both imports,
the complete payload, decompression, execution and the terminal newline.
This is a compact executable representation of the full construction.

The payload was produced from the included `tweet.py` with:

```python
import base64,zlib
payload=base64.b85encode(zlib.compress(source_bytes,9)[2:-4]).decode()
```

The two removed header bytes and four removed checksum bytes convert a zlib
stream to its raw DEFLATE payload. The wrapper uses the corresponding
`zlib.decompress(...,-15)`. The checker separately decodes that literal payload
and requires it to equal the entire uncompressed source, then also compares
the executed polynomial output with the reviewed reference.

## Source identities

| File | SHA-256 |
|---|---|
| `code/generate.py` | `d94a1ddb453ba515f30e8d08f69403cf609e350033a54f3f9f887e6bf1f45be6` |
| `code/tweet.py` | `f5aff4f2279a3204715dfbc0038162980a093b26e183b2f15b7894ac756fa021` |
| `code/tweet_packed.py` | `0b5878b9ddd1c4516aa7b92833acfc1373dcf33ee3678bcc8f5c75667e95a9e5` |

Run `python code/check_tweet.py` from this directory to reproduce the complete
identity checks. They establish that the short representations print the
reviewed polynomial, rather than independently establishing its inherited
arithmetic premises.
