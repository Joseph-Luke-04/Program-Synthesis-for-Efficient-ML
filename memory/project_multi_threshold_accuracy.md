---
name: Multi-threshold accuracy reporting for bitvector and flopoco sweeps
description: User wants within_X% accuracy reported at 6 thresholds from npz data for notebook analysis
type: project
---

Both bitvector_sweep and flopoco_bitvector_sweep produce `.npz` files per variant containing:
- `rel_err_pct`: float32 array of per-sample relative errors in percent (e.g. 0.0, 0.5, 12.3)
- `sample_mode`: string label for the sampling mode
- `rel_err_threshold_pct`: the single threshold used during the test run

The path to each npz is stored in the `error_samples_npz` column of the summary CSVs.

**Required thresholds to report:** 0.001%, 0.01%, 0.1%, 1%, 5%, 10%

These must be computed in the notebook from the raw npz arrays as:
```python
within_X = float(np.mean(rel_err_pct <= X))
```
and added as columns `within_0001pct`, `within_001pct`, `within_01pct`, `within_1pct`, `within_5pct`, `within_10pct` to `bv_df` after loading in Cell 19.

**Why:** The CSV only stores `within_rel_pct` at the single threshold used during the sweep run (e.g. 1.0 for flopoco small/wide, 0.01 for flopoco nf, 5.0 default for bitvector). All other thresholds must be derived from the npz.

**How to apply:** After Cell 19 builds `bv_df`, a new cell should load each npz via `error_samples_npz` column and compute all 6 columns. Both flopoco (sweep3 finished) and bitvector (bitvec_sweep running) produce compatible npz files.
