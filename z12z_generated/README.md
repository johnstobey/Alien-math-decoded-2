# Generated Z12Z theorem instances

These 100 files contain 10,000 parameterized instances of ten proof families.
They formalize explicit ZMod 12 updates, constraint intersection, conditional
revision, append-only event logging, transition restriction, and antipodal closure.
They are not 10,000 independent mathematical discoveries or a formalization of
all claims in the source PDF. Classification and authorization are inputs.

Each file is checked independently. The common state definitions are repeated
under the same namespace, so these files are not intended to be imported together.
The manifest records validation status and SHA-256 hashes of the checked files.

From the repository root, with Lean 4.14.0 and locked mathlib dependencies installed:

```sh
export ELAN_HOME=/workspace/.elan
export PATH="$ELAN_HOME/bin:$PATH"
export XDG_CACHE_HOME=/workspace/.cache
lake env lean z12z_generated/Batch_00000_00099.lean
```

To regenerate all files and check them sequentially:

```sh
python3 generate_z12z.py --output z12z_generated --check
```

Regeneration replaces files with the same names. The manifest is reset to
`lean_checked: false` until every generated file passes the checker.
