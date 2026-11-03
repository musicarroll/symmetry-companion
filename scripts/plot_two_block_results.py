#!/usr/bin/env python3
"""Generate plots for the refined two-block model scan."""

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from landau_model import LandauModel
from two_block_model import TwoBlockModel


def save_contour_plots(model: TwoBlockModel, figure_dir: Path, betas: list[float]) -> None:
    """Save contour plots of the free energy at representative beta values."""
    grid = np.linspace(1.0e-3, 1.0 - 1.0e-3, 200)
    P, Q = np.meshgrid(grid, grid)

    for beta in betas:
        F = model.free_energy(P, Q, beta)
        fig, ax = plt.subplots(figsize=(6, 5))
        contour = ax.contourf(P, Q, F, levels=40, cmap="viridis")
        ax.set_xlabel(r"$p$")
        ax.set_ylabel(r"$q$")
        ax.set_title(rf"$F_\beta(p,q)$ at $\beta={beta:.2f}$")
        fig.colorbar(contour, ax=ax, label=r"$F_\beta$")
        fig.tight_layout()
        out_path = figure_dir / f"contour_beta_{beta:.2f}.png"
        fig.savefig(out_path, dpi=200)
        plt.close(fig)


def save_scan_plots(df: pd.DataFrame, figure_dir: Path, J: float) -> None:
    """Save the main one-dimensional diagnostic plots."""
    landau = LandauModel(J=J)
    beta_c = landau.beta_c()

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(df["beta"], df["symmetry_deficit"], lw=2, label=r"Symmetry deficit $D=(p-q)^2$")
    ax.plot(df["beta"], df["Delta"], lw=2, ls="--", label=r"Reduced proxy $\Delta=|p-q|$")
    ax.axvline(beta_c, color="black", ls=":", lw=1, label=rf"$\beta_c={beta_c:.2f}$")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel("Observable value")
    ax.set_title("Primary Symmetry Deficit and Proxy Order Parameter")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "symmetry_deficit_vs_beta.png", dpi=200)
    plt.close(fig)

    scaling_df = df.loc[
        (df["beta"] > beta_c)
        & ((df["beta"] - beta_c) < 0.1)
        & (df["symmetry_deficit"] > 1.0e-6)
    ].copy()
    x = np.log(scaling_df["beta"] - beta_c)
    y = np.log(scaling_df["symmetry_deficit"])
    alpha, intercept = np.polyfit(x, y, deg=1)
    y_fit = alpha * x + intercept

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(x, y, "o", label="Raw data")
    ax.plot(x, y_fit, lw=2, label=rf"Refined fit: $\alpha={alpha:.3f}$")
    ax.set_xlabel(r"$\log(\beta-\beta_c)$")
    ax.set_ylabel(r"$\log D$")
    ax.set_title("Log-Log Scaling of the Symmetry Deficit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "scaling_symmetry_deficit.png", dpi=200)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(df["beta"], df["Delta"], lw=2)
    ax.axvline(beta_c, color="black", ls="--", lw=1, label=rf"$\beta_c={beta_c:.2f}$")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$\Delta(\beta)=|p-q|$")
    ax.set_title(r"Order Parameter $\Delta(\beta)$")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "delta_vs_beta.png", dpi=200)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(df["beta"], df["lambda_asym_center"], lw=2)
    ax.axhline(0.0, color="black", ls=":", lw=1)
    ax.axvline(beta_c, color="black", ls="--", lw=1, label=rf"$\beta_c={beta_c:.2f}$")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$\lambda_{\mathrm{asym}}$")
    ax.set_title("Antisymmetric Hessian Eigenvalue at the Symmetric Point")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "antisymmetric_eigenvalue_vs_beta.png", dpi=200)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(df["beta"], df["d_exact"], lw=2, label="Exact minimizer")
    ax.plot(df["beta"], df["d_landau"], lw=2, ls="--", label="Landau prediction")
    ax.axvline(beta_c, color="black", ls=":", lw=1)
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$d_*(\beta)$")
    ax.set_title(r"Exact vs. Landau-Predicted $d_*(\beta)$")
    ax.legend()
    fig.tight_layout()
    fig.savefig(figure_dir / "d_star_exact_vs_landau.png", dpi=200)
    plt.close(fig)


def main() -> None:
    """Load the scan output and generate the requested figures."""
    results_data = ROOT / "results" / "data"
    figure_dir = ROOT / "results" / "figures"
    figure_dir.mkdir(parents=True, exist_ok=True)

    csv_path = results_data / "two_block_scan.csv"
    if not csv_path.exists():
        raise FileNotFoundError(
            f"Missing {csv_path}. Run scripts/run_two_block_scan.py first."
        )

    df = pd.read_csv(csv_path)
    J = 1.0
    model = TwoBlockModel(J=J)

    save_contour_plots(model, figure_dir, betas=[1.50, 2.00, 2.50])
    save_scan_plots(df, figure_dir, J=J)

    print(f"Saved figures to {figure_dir}")


if __name__ == "__main__":
    main()
