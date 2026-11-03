# Replaying the quadratic controls

Requires Python 3 with the standard library only. From this directory:

```sh
python3 -B polynomial_bound_transfer.py q2
python3 -B polynomial_bound_transfer.py test
python3 -B polynomial_transfer_independent_oracle.py
```

The first reports all displayed dimension-specific cutoffs. The second runs exact producer controls. The third uses a separate reviewer implementation for factorization counts and cutoff budgets, verifying SHA-256 of the bundled original proof and producer before executing it. The reviewer script was adapted only to read those local files rather than private Git objects; the original script is in `../originals/`.

The scripts also retain historical finite-field subsystem regressions. These do not establish full fixed-field arrays and are not dependencies of the quadratic theorem. No enormous polynomial array is generated. Exact arithmetic checks finite inequalities; the written monotonicity and uniform-dimension proofs establish the infinite tails. The included JSON files record a fresh publication replay, not new theorem assumptions.
