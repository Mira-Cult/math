# Publication verification

On 2026-11-13 the publication pass reran:

```sh
python code/check_tweet.py
python code/check_compiler.py code/generate.py
python code/check_circuit_values.py
```

All passed: 36 exact rational-pair compiler cases, denominator guards,
integer-polynomial residual grammar, and separate circuit comparisons at primes
1,000,003 and 1,000,037. There are 3,779 variables and 3,751 residuals; total degree
is exactly four. These are finite algebraic checks, not proofs of the inherited
arithmetic premises.

The readable, uncompressed and packed programs have respectively 2,518, 2,200 and
1,520 ASCII bytes. Each prints the same 99,397 bytes including the final newline,
SHA-256 `be0026c879a1aec7d9fceafaee1f2e2c14ca7744f1b77faa58c37284f4a1fd87`.
The optional 1,559-byte `tweet_wrapped.py` was separately checked for identical
output and tolerance of whitespace inside its payload.

The existing reviews report exact comparison of all 234 quadratic rows and 3,494
coefficients of the separate 262-variable backup against pinned upstream tables.
That external-table comparison was not rerun in this publication pass. Its checker
and pinned table hashes are included for reproduction. Prior research workflow
runs were reported skipped, not passed; no remote CI pass is asserted here.

The elementary guarded-compilation argument and local valuation replacement were
read in this pass. The scoped source reviews are retained, not promoted to an
independent validation of the upstream elliptic, modular-realization, pole, or
prime-pattern premises. No complete Lean proof or human-expert review is claimed.
