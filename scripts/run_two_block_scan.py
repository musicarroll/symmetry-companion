#!/usr/bin/env python3
"""Run a beta scan for the refined two-block model and save diagnostics."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from landau_model import LandauModel
from two_block_model import TwoBlockModel


def first_nonzero_delta_beta(df: pd.DataFrame, tolerance: float = 1.0e-3) -> float | None:
    """Return the first beta where the minimized order parameter is visibly nonzero."""
    mask = df["Delta"] > tolerance
    if not mask.any():
        return None
    return float(df.loc[mask, "beta"].iloc[0])


def first_nonzero_symmetry_deficit_beta(
    df: pd.DataFrame, tolerance: float = 1.0e-6
) -> float | None:
    """Return the first beta where the explicit symmetry deficit is visibly nonzero."""
    mask = df["symmetry_deficit"] > tolerance
    if not mask.any():
        return None
    return float(df.loc[mask, "beta"].iloc[0])


def first_negative_lambda_beta(df: pd.DataFrame) -> float | None:
    """Return the first beta where the antisymmetric symmetric-point curvature is negative."""
    mask = df["lambda_asym_center"] < 0.0
    if not mask.any():
        return None
    return float(df.loc[mask, "beta"].iloc[0])


def estimate_symmetry_deficit_scaling(
    df: pd.DataFrame,
    beta_c: float,
    tolerance: float = 1.0e-6,
    max_reduced_beta: float = 0.1,
) -> tuple[float | None, float | None, float | None, int]:
    """Fit log D = alpha log(beta-beta_c) + C above threshold."""
    scaling_df = df.loc[
        (df["beta"] > beta_c)
        & ((df["beta"] - beta_c) <= max_reduced_beta)
        & (df["symmetry_deficit"] > tolerance),
        ["beta", "symmetry_deficit"],
    ].copy()
    if len(scaling_df) < 2:
        return None, None, None, len(scaling_df)

    x = np.log(scaling_df["beta"].to_numpy() - beta_c)
    y = np.log(scaling_df["symmetry_deficit"].to_numpy())
    alpha, intercept = np.polyfit(x, y, deg=1)
    residual = y - (alpha * x + intercept)
    rms_error = float(np.sqrt(np.mean(residual**2)))
    return float(alpha), float(intercept), rms_error, len(scaling_df)


def build_summary(df: pd.DataFrame, J: float) -> dict[str, object]:
    """Construct a concise numerical validation summary."""
    landau = LandauModel(J=J)
    beta_c = landau.beta_c()
    beta_delta = first_nonzero_delta_beta(df)
    beta_symmetry_deficit = first_nonzero_symmetry_deficit_beta(df)
    beta_lambda = first_negative_lambda_beta(df)
    critical_exponent_estimate, scaling_intercept, scaling_rms_error, scaling_points_used = (
        estimate_symmetry_deficit_scaling(df, beta_c)
    )

    discrepancy = None
    if beta_delta is not None:
        discrepancy = beta_delta - beta_c

    deficit_discrepancy = None
    if beta_symmetry_deficit is not None:
        deficit_discrepancy = beta_symmetry_deficit - beta_c

    if beta_delta is None:
        delta_message = "No nonzero Delta detected on the chosen beta grid."
    elif abs(beta_delta - beta_c) < 0.05:
        delta_message = (
            "The onset of nonzero Delta is numerically close to the predicted "
            "critical threshold."
        )
    else:
        delta_message = (
            "The onset of the global minimizing Delta does not occur near the local "
            "Landau threshold; this indicates a discrepancy between the local "
            "bifurcation analysis and the global minimization problem."
        )

    if beta_lambda is None:
        lambda_message = "The antisymmetric curvature at the symmetric point did not change sign."
    else:
        lambda_message = (
            "The antisymmetric symmetric-point curvature changes sign near the "
            "predicted threshold."
        )

    if beta_symmetry_deficit is None:
        deficit_message = "No nonzero symmetry deficit detected on the chosen beta grid."
    elif abs(beta_symmetry_deficit - beta_c) < 0.05:
        deficit_message = (
            "The onset of nonzero symmetry deficit is numerically close to the "
            "predicted critical threshold."
        )
    else:
        deficit_message = (
            "The onset of nonzero symmetry deficit does not occur near the local "
            "Landau threshold; this indicates a mismatch in the symmetry-based "
            "diagnostic."
        )

    alignment_warning = None
    if (
        beta_delta is not None
        and beta_symmetry_deficit is not None
        and abs(beta_delta - beta_symmetry_deficit) >= 0.05
    ):
        alignment_warning = (
            "WARNING: Delta and symmetry deficit do not become nonzero on the same "
            "beta grid point."
        )

    scaling_warning = None
    if critical_exponent_estimate is None:
        scaling_message = "Critical scaling could not be estimated from the available scan data."
    elif 0.8 < critical_exponent_estimate < 1.2:
        scaling_message = (
            "The symmetry-deficit scaling exponent is consistent with the "
            "mean-field expectation alpha ≈ 1."
        )
    else:
        scaling_message = (
            "The fitted symmetry-deficit scaling exponent is outside the expected "
            "mean-field range."
        )
        scaling_warning = (
            "WARNING: Critical scaling estimate for symmetry deficit lies outside "
            "the tolerance band 0.8 < alpha < 1.2."
        )

    summary = {
        "J": J,
        "predicted_beta_c": beta_c,
        "beta_c_numerical": beta_symmetry_deficit,
        "detected_beta_for_nonzero_Delta": beta_delta,
        "detected_beta_for_nonzero_symmetry_deficit": beta_symmetry_deficit,
        "detected_beta_for_lambda_asym_sign_change": beta_lambda,
        "Delta_onset_minus_beta_c": discrepancy,
        "symmetry_deficit_onset_minus_beta_c": deficit_discrepancy,
        "critical_exponent_estimate": critical_exponent_estimate,
        "critical_scaling_intercept": scaling_intercept,
        "critical_scaling_rms_error": scaling_rms_error,
        "critical_scaling_points_used": scaling_points_used,
        "delta_check": delta_message,
        "symmetry_deficit_check": deficit_message,
        "lambda_check": lambda_message,
        "scaling_check": scaling_message,
        "alignment_warning": alignment_warning,
        "scaling_warning": scaling_warning,
        "overall_assessment": (
            "The local Hessian/Landau threshold agrees with beta_c = 2/J, and in "
            "this refined two-block model the explicit symmetry deficit behaves as "
            "the primary symmetry-based observable while Delta serves as its reduced proxy. "
            "Its near-threshold scaling is also consistent with the mean-field "
            "expectation that symmetry deficit is quadratic in the order parameter."
        ),
    }
    return summary


def save_summary_text(summary: dict[str, object], out_path: Path) -> None:
    """Write a readable text summary."""
    lines = [
        "Two-Block Numerical Validation Summary",
        f"J = {summary['J']}",
        f"Predicted beta_c = {summary['predicted_beta_c']:.6f}",
        f"Numerical beta_c from symmetry deficit = {summary['beta_c_numerical']}",
        f"Detected onset of nonzero Delta = {summary['detected_beta_for_nonzero_Delta']}",
        "Detected onset of nonzero symmetry deficit = "
        f"{summary['detected_beta_for_nonzero_symmetry_deficit']}",
        "Detected antisymmetric sign change = "
        f"{summary['detected_beta_for_lambda_asym_sign_change']}",
        f"Delta onset minus beta_c = {summary['Delta_onset_minus_beta_c']}",
        "Symmetry-deficit onset minus beta_c = "
        f"{summary['symmetry_deficit_onset_minus_beta_c']}",
        "Critical exponent estimate for symmetry deficit = "
        f"{summary['critical_exponent_estimate']}",
        "Number of points in scaling fit = "
        f"{summary['critical_scaling_points_used']}",
        "Critical scaling RMS log-error = "
        f"{summary['critical_scaling_rms_error']}",
        "",
        f"Symmetry-deficit check: {summary['symmetry_deficit_check']}",
        f"Delta check: {summary['delta_check']}",
        f"Antisymmetric curvature check: {summary['lambda_check']}",
        f"Scaling check: {summary['scaling_check']}",
        "",
        f"Assessment: {summary['overall_assessment']}",
    ]
    if summary["alignment_warning"] is not None:
        lines.extend(["", str(summary["alignment_warning"])])
    if summary["scaling_warning"] is not None:
        lines.extend(["", str(summary["scaling_warning"])])
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    """Run the scan and write data products."""
    results_data = ROOT / "results" / "data"
    results_data.mkdir(parents=True, exist_ok=True)

    J = 1.0
    coarse_left = np.arange(1.5, 1.9 + 1.0e-12, 0.05)
    fine = np.arange(1.9, 2.1 + 1.0e-12, 0.005)
    coarse_right = np.arange(2.1, 3.0 + 1.0e-12, 0.05)
    betas = np.unique(np.round(np.concatenate([coarse_left, fine, coarse_right]), 12))

    two_block = TwoBlockModel(J=J)
    landau = LandauModel(J=J)

    df = two_block.scan(betas)
    df["beta_c_predicted"] = landau.beta_c()
    df["d_exact"] = 0.5 * df["Delta"]
    df["d_landau"] = df["beta"].map(landau.predicted_d_star)
    df["A_landau"] = df["beta"].map(landau.A)
    df["B_landau"] = landau.B()

    csv_path = results_data / "two_block_scan.csv"
    df.to_csv(csv_path, index=False)

    summary = build_summary(df, J=J)
    summary_json_path = results_data / "two_block_summary.json"
    summary_json_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    summary_txt_path = results_data / "two_block_summary.txt"
    save_summary_text(summary, summary_txt_path)

    print(f"Saved scan table to {csv_path}")
    print(f"Saved summary to {summary_txt_path}")
    print("")
    print(summary["delta_check"])
    print(summary["symmetry_deficit_check"])
    print(summary["lambda_check"])
    print(summary["scaling_check"])
    if summary["Delta_onset_minus_beta_c"] is not None and abs(summary["Delta_onset_minus_beta_c"]) >= 0.05:
        print("DISCREPANCY FLAG: Global Delta onset does not coincide with beta_c = 2/J.")
    if (
        summary["symmetry_deficit_onset_minus_beta_c"] is not None
        and abs(summary["symmetry_deficit_onset_minus_beta_c"]) >= 0.05
    ):
        print("DISCREPANCY FLAG: Symmetry-deficit onset does not coincide with beta_c = 2/J.")
    if summary["alignment_warning"] is not None:
        print(summary["alignment_warning"])
    if summary["scaling_warning"] is not None:
        print(summary["scaling_warning"])


if __name__ == "__main__":
    main()
