# Lean build configuration

This directory contains the pinned Lean toolchain, unchanged Lake configuration,
lockfile, and original import inventory. Canonical source files are stored with
their machines or in the [shared library](../shared/README.md).

Run from the repository root:

```sh
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
```

The generated build workspace is `../.build/lean/`, not this directory.
See the [full verification guide](../README.md#verify-locally).
