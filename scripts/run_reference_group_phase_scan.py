#!/usr/bin/env python3
"""Run the Chapter 6 reference-group mean-field XY experiment."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from reference_group_phase_model import (
    XYSimulationConfig,
    predicted_measure_deficit,
    predicted_order,
    reference_group_scaling_table,
    run_xy_scan,
)


def main() -> None:
    """Run the reproducible scan and save data and summary products."""
    config = XYSimulationConfig()
    data_dir = ROOT / "results" / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    assert predicted_order(2.0, config.coupling) == 0.0
    assert predicted_order(3.0, config.coupling) > 0.0
    assert predicted_measure_deficit(1.5, config.coupling) == 0.0
    assert predicted_measure_deficit(3.0, config.coupling) > 0.0

    chain_df, summary_df, histogram_df = run_xy_scan(config)
    scaling_df = reference_group_scaling_table(
        np.asarray([8, 16, 32, 64, 128, 256, 512, 1024], dtype=float)
    )

    chain_path = data_dir / "reference_group_xy_chains.csv"
    summary_path = data_dir / "reference_group_xy_summary.csv"
    histogram_path = data_dir / "reference_group_xy_histograms.csv"
    scaling_path = data_dir / "reference_group_deficit_scaling.csv"
    chain_df.to_csv(chain_path, index=False)
    summary_df.to_csv(summary_path, index=False)
    histogram_df.to_csv(histogram_path, index=False)
    scaling_df.to_csv(scaling_path, index=False)

    largest_n = max(config.system_sizes)
    ordered_beta = 3.0
    ordered_row = summary_df.loc[
        (summary_df["n"] == largest_n) & (summary_df["beta"] == ordered_beta)
    ].iloc[0]
    ordered_rows = summary_df.loc[summary_df["beta"] > 2.0].copy()
    order_rmse = float(
        np.sqrt(
            np.mean(
                (ordered_rows["order_mean"] - ordered_rows["predicted_order"]) ** 2
            )
        )
    )
    deficit_rmse = float(
        np.sqrt(
            np.mean(
                (
                    ordered_rows["measure_deficit_mean"]
                    - ordered_rows["predicted_measure_deficit"]
                )
                ** 2
            )
        )
    )
    result_summary = {
        "model": "mean-field XY with global SO(2) reference symmetry",
        "coupling": config.coupling,
        "predicted_beta_c": 2.0 / config.coupling,
        "system_sizes": list(config.system_sizes),
        "betas": list(config.betas),
        "replicas": config.replicas,
        "burn_in_sweeps": config.burn_in_sweeps,
        "measurement_sweeps": config.measurement_sweeps,
        "sample_every_sweeps": config.sample_every_sweeps,
        "histogram_bins": config.histogram_bins,
        "seed": config.seed,
        "ordered_comparison_beta": ordered_beta,
        "largest_n": largest_n,
        "predicted_order_at_beta_3": float(ordered_row["predicted_order"]),
        "measured_order_at_beta_3": float(ordered_row["order_mean"]),
        "predicted_measure_deficit_at_beta_3": float(
            ordered_row["predicted_measure_deficit"]
        ),
        "measured_measure_deficit_at_beta_3": float(
            ordered_row["measure_deficit_mean"]
        ),
        "ordered_phase_order_rmse_all_sizes": order_rmse,
        "ordered_phase_measure_deficit_rmse_all_sizes": deficit_rmse,
        "interpretation": (
            "Finite-size Metropolis measurements approach the selected-phase "
            "mean-field branch above beta_c. Below beta_c, alignment of finite "
            "magnetization fluctuations creates a positive finite-N bias that "
            "decreases with system size."
        ),
    }
    json_path = data_dir / "reference_group_xy_summary.json"
    json_path.write_text(
        json.dumps(result_summary, indent=2) + "\n", encoding="utf-8"
    )

    text_lines = [
        "Reference-Group Mean-Field XY Summary",
        f"Predicted beta_c = {result_summary['predicted_beta_c']:.6f}",
        f"System sizes = {result_summary['system_sizes']}",
        f"Replicas per point = {result_summary['replicas']}",
        "Predicted r(beta=3) = "
        f"{result_summary['predicted_order_at_beta_3']:.6f}",
        f"Measured r(beta=3, N={largest_n}) = "
        f"{result_summary['measured_order_at_beta_3']:.6f}",
        "Predicted measure deficit(beta=3) = "
        f"{result_summary['predicted_measure_deficit_at_beta_3']:.6f}",
        f"Measured measure deficit(beta=3, N={largest_n}) = "
        f"{result_summary['measured_measure_deficit_at_beta_3']:.6f}",
        f"Ordered-phase order RMSE = {order_rmse:.6f}",
        f"Ordered-phase measure-deficit RMSE = {deficit_rmse:.6f}",
        "",
        str(result_summary["interpretation"]),
    ]
    (data_dir / "reference_group_xy_summary.txt").write_text(
        "\n".join(text_lines) + "\n", encoding="utf-8"
    )

    print(f"Saved chain data to {chain_path}")
    print(f"Saved aggregate data to {summary_path}")
    print(f"Saved histogram data to {histogram_path}")
    print(f"Saved scaling predictions to {scaling_path}")
    print(result_summary["interpretation"])


if __name__ == "__main__":
    main()
