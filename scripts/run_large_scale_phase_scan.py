#!/usr/bin/env python3
"""Run larger-scale relational phase-structure experiments."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from large_scale_experiments import (
    FiniteBlockPhaseConfig,
    LatticePottsConfig,
    MonteCarloRelationalConfig,
    ThreeBlockScanConfig,
    TwoBlockScanConfig,
    build_large_scale_summary,
    run_finite_block_phase_scan,
    run_lattice_potts_scan,
    run_monte_carlo_relational_scan,
    run_three_block_scan,
    run_two_block_phase_scan,
    save_summary_text,
)


def parse_args() -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples-two-block", type=int, default=8)
    parser.add_argument("--samples-three-block", type=int, default=6)
    parser.add_argument("--samples-finite-block", type=int, default=24)
    parser.add_argument("--mc-burn-in", type=int, default=5000)
    parser.add_argument("--mc-sample-steps", type=int, default=10000)
    parser.add_argument("--mc-sample-every", type=int, default=100)
    parser.add_argument("--potts-burn-in-sweeps", type=int, default=100)
    parser.add_argument("--potts-measurement-sweeps", type=int, default=200)
    parser.add_argument("--potts-sample-every-sweeps", type=int, default=10)
    parser.add_argument("--seed", type=int, default=1729)
    return parser.parse_args()


def main() -> None:
    """Run the experiments and save data products."""
    args = parse_args()
    data_dir = ROOT / "results" / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    two_block_config = TwoBlockScanConfig(
        samples_per_beta=args.samples_two_block,
        seed=args.seed,
    )
    three_block_config = ThreeBlockScanConfig(
        samples_per_gamma=args.samples_three_block,
        seed=args.seed + 1,
    )
    finite_block_config = FiniteBlockPhaseConfig(
        samples_per_lambda=args.samples_finite_block,
        seed=args.seed + 2,
    )
    mc_config = MonteCarloRelationalConfig(
        burn_in_steps=args.mc_burn_in,
        sample_steps=args.mc_sample_steps,
        sample_every=args.mc_sample_every,
        seed=args.seed + 3,
    )
    lattice_config = LatticePottsConfig(
        burn_in_sweeps=args.potts_burn_in_sweeps,
        measurement_sweeps=args.potts_measurement_sweeps,
        sample_every_sweeps=args.potts_sample_every_sweeps,
        seed=args.seed + 4,
    )

    two_block_samples, two_block_summary, fit_df = run_two_block_phase_scan(two_block_config)
    three_block_samples, three_block_summary = run_three_block_scan(three_block_config)
    finite_block_samples, finite_block_summary = run_finite_block_phase_scan(finite_block_config)
    mc_samples, mc_summary = run_monte_carlo_relational_scan(mc_config)
    lattice_samples, lattice_summary = run_lattice_potts_scan(lattice_config)

    two_block_samples.to_csv(data_dir / "large_scale_two_block_samples.csv", index=False)
    two_block_summary.to_csv(data_dir / "large_scale_two_block_summary.csv", index=False)
    fit_df.to_csv(data_dir / "large_scale_landau_fit.csv", index=False)
    three_block_samples.to_csv(data_dir / "large_scale_three_block_samples.csv", index=False)
    three_block_summary.to_csv(data_dir / "large_scale_three_block_summary.csv", index=False)
    finite_block_samples.to_csv(data_dir / "finite_block_model_samples.csv", index=False)
    finite_block_summary.to_csv(data_dir / "finite_block_model_summary.csv", index=False)
    mc_samples.to_csv(data_dir / "finite_block_mc_samples.csv", index=False)
    mc_summary.to_csv(data_dir / "finite_block_mc_summary.csv", index=False)
    lattice_samples.to_csv(data_dir / "lattice_potts_samples.csv", index=False)
    lattice_summary.to_csv(data_dir / "lattice_potts_summary.csv", index=False)

    summary = build_large_scale_summary(
        two_block_summary,
        fit_df,
        three_block_summary,
        finite_block_summary,
        mc_summary,
        lattice_summary,
    )
    (data_dir / "large_scale_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n",
        encoding="utf-8",
    )
    save_summary_text(summary, data_dir / "large_scale_summary.txt")

    print(f"Saved data products under {data_dir}")
    print(summary["assessment"])


if __name__ == "__main__":
    main()
