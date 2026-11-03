# Computational Notes

This directory contains numerical verification packages for the Chapter 3
mean-field, Landau, and finite-size block-relational models and the Chapter 6
reference-group orientational model.

## Scope

The current code covers:

- the refined two-block free energy from Sections 3.4 and 3.5,
- the local Hessian and Landau analysis near the critical threshold,
- finite-size random block-relational simulations with `N = 100`--`1000`,
- configurable block structures and coarse symmetry groups,
- the mean-field $XY$ prediction and finite-$N$ Metropolis measurements with
  global $SO(2)$ as the physical reference group,
- selected-phase relative-entropy estimates and exact global-versus-product
  deficit scaling,
- CSV output, summary tables, and diagnostic plots.

It does **not** yet include curvature or gauge-field numerics from the later
sections of Chapter 3.

## Layout

- `src/two_block_model.py`
  Core free-energy, gradient, Hessian, minimization, and scan code.
- `src/landau_model.py`
  Landau coefficients and predicted nonzero minimizer near `beta_c = 2/J`.
- `src/block_relational_model.py`
  Finite-size random block-relational ensembles, block observables, entropy,
  degree statistics, and coarse symmetry-deficit diagnostics.
- `src/large_scale_experiments.py`
  Parameter sweeps for two-block and three-block finite-size experiments and
  Landau-type fitting utilities.
- `src/reference_group_phase_model.py`
  Chapter 6 mean-field $XY$ prediction, Metropolis sampler, aligned
  relative-entropy estimator, and exact finite-window scaling comparison.
- `scripts/run_two_block_scan.py`
  Runs the beta scan and writes tables and a text summary.
- `scripts/plot_two_block_results.py`
  Builds the requested contour and line plots from the scan output.
- `scripts/run_large_scale_phase_scan.py`
  Runs the finite-size two-block and three-block experiments and writes the
  large-scale CSV summaries.
- `scripts/plot_large_scale_phase_results.py`
  Builds large-scale diagnostic plots from the saved summaries.
- `scripts/run_reference_group_phase_scan.py`
  Runs the seeded Chapter 6 orientational experiment and writes raw and
  aggregated measurements.
- `scripts/plot_reference_group_phase_results.py`
  Compares the Chapter 6 predictions and measurements in three figures.
- `results/data/`
  CSV and text summaries.
- `results/figures/`
  Generated figures.

## Requirements

Python 3 with:

- `numpy`
- `scipy`
- `pandas`
- `matplotlib`

## How To Run

From the repo root:

```bash
python3 scripts/run_two_block_scan.py
python3 scripts/plot_two_block_results.py
python3 scripts/run_large_scale_phase_scan.py
python3 scripts/plot_large_scale_phase_results.py
python3 scripts/run_reference_group_phase_scan.py
python3 scripts/plot_reference_group_phase_results.py
```

## Outputs

The scan script writes:

- `results/data/two_block_scan.csv`
- `results/data/two_block_summary.json`
- `results/data/two_block_summary.txt`
- `results/data/large_scale_two_block_summary.csv`
- `results/data/large_scale_three_block_summary.csv`
- `results/data/large_scale_landau_fit.csv`
- `results/data/large_scale_summary.json`
- `results/data/large_scale_summary.txt`
- `results/data/reference_group_xy_chains.csv`
- `results/data/reference_group_xy_summary.csv`
- `results/data/reference_group_xy_histograms.csv`
- `results/data/reference_group_xy_summary.json`
- `results/data/reference_group_xy_summary.txt`
- `results/data/reference_group_deficit_scaling.csv`

The plotting script writes:

- `results/figures/contour_beta_1.50.png`
- `results/figures/contour_beta_2.00.png`
- `results/figures/contour_beta_2.50.png`
- `results/figures/delta_vs_beta.png`
- `results/figures/antisymmetric_eigenvalue_vs_beta.png`
- `results/figures/d_star_exact_vs_landau.png`
- `results/figures/large_scale_block_contrast_vs_beta.png`
- `results/figures/large_scale_symmetry_deficit_vs_beta.png`
- `results/figures/large_scale_mean_field_error.png`
- `results/figures/large_scale_landau_fit.png`
- `results/figures/large_scale_three_block_symmetry_deficit.png`
- `results/figures/reference_group_xy_transition.png`
- `results/figures/reference_group_xy_distributions.png`
- `results/figures/reference_group_deficit_scaling.png`

## Validation Logic

The code checks agreement with the main Chapter 3 claims by comparing:

- the predicted local threshold `beta_c = 2/J`,
- the sign change of the antisymmetric Hessian curvature at the symmetric point,
- the onset of the numerically minimized order parameter `Delta = |p-q|`,
- the rise of a coarse symmetry-deficit diagnostic in finite-size block models,
- the agreement between finite-size block contrast and the Chapter 3 mean-field
  branch,
- the Chapter 6 prediction $\beta_cJ=2$ for orientational ordering,
- the agreement of finite-size order and aligned measure deficit with the
  selected-phase mean-field branch above the transition,
- the constant-versus-extensive scaling forced by global $\mathbb Z_2$ and
  product $(\mathbb Z_2)^N$ reference groups.

The first two are local/Landau diagnostics and should agree with the analytic
development. The finite-size simulations then test whether symmetry deficit
behaves like an order-parameter-type diagnostic in nontrivial relational
systems. If the numerics do not match the analytic picture, the summaries flag
that discrepancy rather than hiding it.

## Current Numerical Snapshot

For the present checked-in runs:

- the refined two-block scan uses `J = 1` and samples
  `beta = 1.5, 1.6, \ldots, 2.8` at system sizes `N = 100, 300, 1000`,
- the largest two-block system shows visible contrast at `beta = 2.1`, just
  above the analytic threshold `beta_c = 2`,
- the coarse two-block symmetry deficit rises from `0` to `log 2` once the
  within/cross sectors separate,
- the mean absolute contrast error against the mean-field branch is about
  `1.6 \times 10^{-3}` on the largest run,
- the three-block family is scanned for `gamma = 0, 0.02, \ldots, 0.18` at
  `N = 300, 900`,
- at `N = 900`, the three-block coarse symmetry deficit is `0` at `gamma = 0`
  and `log 3` throughout the visibly broken regime,
- the Chapter 6 scan uses `N = 64, 256`, four chains per point, and the fixed
  seed `20261003`,
- at `beta = 3` and `N = 256`, the measured order is `0.723995` versus the
  prediction `0.724159`,
- at the same point, the measured aligned measure deficit is `0.626140` versus
  the prediction `0.626545`,
- the positive aligned deficit below `beta_c = 2` decreases with system size
  and is reported as a finite-size selection bias rather than hidden.
