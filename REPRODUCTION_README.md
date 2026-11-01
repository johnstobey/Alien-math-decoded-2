# Reproduction

Python 3.11+; NumPy required for the independent NumPy check during compilation.

From `proofs/` run:

```bash
python verify_math.py
python independent_replication.py
```

Expected: first tool produces 48 commuting checks, group order 24, 12 unique element-modality pairs, 7 undirected aspect classes; second prints status PASS and recomputes holdout correlations.

Original ZIP contents preserved under `original_extracted/`. The unmodified source ZIP can be compared with the manifest SHA. The original vortex image is not included. Thus the 72 TSV observations are reproducible as numerical calculations but not regenerable from image pixels within this package.
