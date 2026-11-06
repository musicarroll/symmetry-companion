#!/usr/bin/env python3
"""Plot large-scale relational phase-structure experiment outputs."""

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))


def plot_two_block_contrast(two_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot finite-size block contrast against beta."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for n, frame in two_block.groupby("n"):
        ax.plot(frame["beta"], frame["block_contrast_mean"], marker="o", ms=3, label=fr"$N={int(n)}$")
    beta_c = float(two_block["beta_c"].iloc[0])
    ax.axvline(beta_c, color="black", ls="--", lw=1, label=fr"$\beta_c={beta_c:.2f}$")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"mean block contrast")
    ax.set_title("Finite-Size Block Contrast")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "large_scale_block_contrast_vs_beta.png", dpi=200)
    plt.close(fig)


def plot_two_block_symmetry_deficit(two_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot coarse symmetry deficit against beta."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for n, frame in two_block.groupby("n"):
        ax.plot(
            frame["beta"],
            frame["symmetry_deficit_mean"],
            marker="o",
            ms=3,
            label=fr"$N={int(n)}$",
        )
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"mean coarse symmetry deficit")
    ax.set_title("Coarse Symmetry Deficit as a Phase Diagnostic")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "large_scale_symmetry_deficit_vs_beta.png", dpi=200)
    plt.close(fig)


def plot_mean_field_error(two_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot mean-field and Landau finite-size errors."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for n, frame in two_block.groupby("n"):
        ax.plot(
            frame["beta"],
            frame["abs_delta_error"],
            marker="o",
            ms=3,
            label=fr"$N={int(n)}$ mean-field",
        )
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"$|\Delta_{\mathrm{sim}}-\Delta_{\mathrm{MF}}|$")
    ax.set_title("Finite-Size Error Relative to Mean-Field Contrast")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "large_scale_mean_field_error.png", dpi=200)
    plt.close(fig)


def plot_landau_fit(two_block: pd.DataFrame, fit_df: pd.DataFrame, out_dir: Path) -> None:
    """Plot near-threshold simulation data against the polynomial Landau fit."""
    n_max = int(two_block["n"].max())
    frame = two_block[two_block["n"] == n_max]
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    ax.plot(frame["beta"], 0.5 * frame["block_contrast_mean"], marker="o", ms=3, label="simulation")
    if not fit_df.empty:
        ax.plot(fit_df["beta"], fit_df["landau_poly_fit"], lw=2, ls="--", label="polynomial fit")
        ax.plot(fit_df["beta"], fit_df["landau_d"], lw=2, ls=":", label="Landau prediction")
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"reduced scalar")
    ax.set_title(fr"Reduced Scalar Fit at $N={n_max}$")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "large_scale_landau_fit.png", dpi=200)
    plt.close(fig)


def plot_three_block_symmetry(three_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot three-block symmetry deficit against the control parameter gamma."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for n, frame in three_block.groupby("n"):
        ax.plot(frame["gamma"], frame["symmetry_deficit_mean"], marker="o", ms=3, label=fr"$N={int(n)}$")
    ax.set_xlabel(r"$\gamma$")
    ax.set_ylabel(r"mean coarse symmetry deficit")
    ax.set_title("Three-Block Symmetry Breaking")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "large_scale_three_block_symmetry_deficit.png", dpi=200)
    plt.close(fig)


def plot_finite_block_symmetry_deficit(finite_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot the variance-based symmetry deficit for the finite relational model."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for (k, n), frame in finite_block.groupby(["k", "n"]):
        label = fr"$k={int(k)},\,N={int(n)}$"
        ax.plot(
            frame["lambda_control"],
            frame["symmetry_deficit_mean"],
            marker="o",
            ms=3,
            label=label,
        )
    ax.set_xlabel(r"$\lambda=p-q$")
    ax.set_ylabel(r"mean block-variance proxy")
    ax.set_title("Finite Relational Symmetry Deficit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "symmetry_deficit_vs_lambda.png", dpi=200)
    plt.close(fig)


def plot_mean_field_finite_comparison(two_block: pd.DataFrame, finite_block: pd.DataFrame, out_dir: Path) -> None:
    """Compare mean-field-guided and finite relational symmetry-deficit curves."""
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 4.2))

    n_max = int(two_block["n"].max())
    frame_two = two_block[two_block["n"] == n_max]
    axes[0].plot(frame_two["beta"], frame_two["symmetry_deficit_mean"], marker="o", ms=3)
    axes[0].set_xlabel(r"$\beta$")
    axes[0].set_ylabel(r"mean structural proxy")
    axes[0].set_title(fr"Mean-Field-Guided Scan ($N={n_max}$)")

    finite_max = finite_block[
        (finite_block["k"] == finite_block["k"].max()) & (finite_block["n"] == finite_block["n"].max())
    ]
    axes[1].plot(
        finite_max["lambda_control"],
        finite_max["symmetry_deficit_mean"],
        marker="o",
        ms=3,
    )
    axes[1].set_xlabel(r"$\lambda=p-q$")
    axes[1].set_ylabel(r"mean structural proxy")
    axes[1].set_title(
        fr"Finite Relational Scan ($k={int(finite_max['k'].iloc[0])},\,N={int(finite_max['n'].iloc[0])}$)"
    )

    fig.tight_layout()
    fig.savefig(out_dir / "finite_vs_mean_field_symmetry_deficit.png", dpi=200)
    plt.close(fig)


def plot_monte_carlo_symmetry_deficit(mc_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot symmetry deficit from the energy-based Monte Carlo model."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for (k, n), frame in mc_block.groupby(["k", "n"]):
        ax.plot(
            frame["lambda_control"],
            frame["symmetry_deficit_mean"],
            marker="o",
            ms=3,
            label=fr"$k={int(k)},\,N={int(n)}$",
        )
    ax.set_xlabel(r"$\lambda$")
    ax.set_ylabel(r"mean structural proxy")
    ax.set_title("Monte Carlo Relational Symmetry Deficit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "symmetry_deficit_vs_lambda_mc.png", dpi=200)
    plt.close(fig)


def plot_monte_carlo_susceptibility(mc_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot symmetry-deficit susceptibility for the Monte Carlo model."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for (k, n), frame in mc_block.groupby(["k", "n"]):
        ax.plot(
            frame["lambda_control"],
            frame["symmetry_deficit_susceptibility"],
            marker="o",
            ms=3,
            label=fr"$k={int(k)},\,N={int(n)}$",
        )
    ax.set_xlabel(r"$\lambda$")
    ax.set_ylabel(r"variance of structural proxy")
    ax.set_title("Monte Carlo Symmetry-Deficit Susceptibility")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "susceptibility_vs_lambda_multiN.png", dpi=200)
    plt.close(fig)


def plot_monte_carlo_peak_scaling(mc_block: pd.DataFrame, out_dir: Path) -> None:
    """Plot susceptibility peak height against system size."""
    rows: list[dict[str, float]] = []
    for (k, n), frame in mc_block.groupby(["k", "n"]):
        peak = frame.loc[frame["symmetry_deficit_susceptibility"].idxmax()]
        rows.append(
            {
                "k": float(k),
                "n": float(n),
                "lambda_peak": float(peak["lambda_control"]),
                "chi_max": float(peak["symmetry_deficit_susceptibility"]),
            }
        )

    peak_df = pd.DataFrame(rows).sort_values(["k", "n"])
    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    for k, frame in peak_df.groupby("k"):
        ax.plot(
            frame["n"],
            frame["chi_max"],
            marker="o",
            ms=4,
            label=fr"$k={int(k)}$",
        )
    ax.set_xlabel(r"$N$")
    ax.set_ylabel(r"$\chi_{\max}$")
    ax.set_title("Monte Carlo Susceptibility Peak Height")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "susceptibility_peak_vs_N.png", dpi=200)
    plt.close(fig)


def plot_lattice_symmetry_deficit(lattice: pd.DataFrame, out_dir: Path) -> None:
    """Plot lattice Potts symmetry deficit versus beta."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for L, frame in lattice.groupby("L"):
        ax.plot(
            frame["beta"],
            frame["symmetry_deficit_mean"],
            marker="o",
            ms=3,
            label=fr"$L={int(L)}$",
        )
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"mean structural proxy")
    ax.set_title("Lattice Potts Symmetry Deficit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "lattice_symmetry_deficit.png", dpi=200)
    plt.close(fig)


def plot_lattice_susceptibility(lattice: pd.DataFrame, out_dir: Path) -> None:
    """Plot lattice Potts susceptibility versus beta."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for L, frame in lattice.groupby("L"):
        ax.plot(
            frame["beta"],
            frame["symmetry_deficit_susceptibility"],
            marker="o",
            ms=3,
            label=fr"$L={int(L)}$",
        )
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"variance of structural proxy")
    ax.set_title("Lattice Potts Symmetry-Deficit Susceptibility")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "lattice_susceptibility.png", dpi=200)
    plt.close(fig)


def plot_lattice_peak_scaling(lattice: pd.DataFrame, out_dir: Path) -> None:
    """Plot lattice susceptibility peak height against linear system size."""
    rows: list[dict[str, float]] = []
    for L, frame in lattice.groupby("L"):
        peak = frame.loc[frame["symmetry_deficit_susceptibility"].idxmax()]
        rows.append(
            {
                "L": float(L),
                "beta_peak": float(peak["beta"]),
                "chi_max": float(peak["symmetry_deficit_susceptibility"]),
            }
        )
    peak_df = pd.DataFrame(rows).sort_values("L")
    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    ax.plot(peak_df["L"], peak_df["chi_max"], marker="o", ms=4)
    ax.set_xlabel(r"$L$")
    ax.set_ylabel(r"$\chi_{\max}$")
    ax.set_title("Lattice Potts Peak Susceptibility")
    fig.tight_layout()
    fig.savefig(out_dir / "multi_L_scaling.png", dpi=200)
    plt.close(fig)


def plot_lattice_energy(lattice: pd.DataFrame, out_dir: Path) -> None:
    """Plot lattice Potts energy density versus beta."""
    fig, ax = plt.subplots(figsize=(6.5, 4.5))
    for L, frame in lattice.groupby("L"):
        ax.plot(
            frame["beta"],
            frame["energy_per_site_mean"],
            marker="o",
            ms=3,
            label=fr"$L={int(L)}$",
        )
    ax.set_xlabel(r"$\beta$")
    ax.set_ylabel(r"mean energy per site")
    ax.set_title("Lattice Potts Energy Density")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "lattice_energy.png", dpi=200)
    plt.close(fig)


def plot_lattice_susceptibility_scaling_D(lattice: pd.DataFrame, out_dir: Path) -> None:
    """Plot log chi_D,max against log L with the best-fit line."""
    rows: list[dict[str, float]] = []
    for L, frame in lattice.groupby("L"):
        peak = frame.loc[frame["symmetry_deficit_susceptibility"].idxmax()]
        rows.append(
            {
                "L": float(L),
                "chi_max": float(peak["symmetry_deficit_susceptibility"]),
            }
        )
    peak_df = pd.DataFrame(rows).sort_values("L")
    x = np.log(peak_df["L"].to_numpy(dtype=float))
    y = np.log(peak_df["chi_max"].to_numpy(dtype=float))
    coeffs = np.polyfit(x, y, deg=1)
    x_fit = np.linspace(x.min(), x.max(), 200)
    y_fit = np.polyval(coeffs, x_fit)

    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    ax.plot(x, y, "o", ms=5, label="peak data")
    ax.plot(x_fit, y_fit, lw=2, ls="--", label=fr"fit slope $={coeffs[0]:.3f}$")
    ax.set_xlabel(r"$\log L$")
    ax.set_ylabel(r"$\log V_{D,\max}$")
    ax.set_title("Raw structural variance fit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "susceptibility_D_scaling_loglog.png", dpi=200)
    plt.close(fig)


def plot_lattice_susceptibility_scaling_M(lattice_samples: pd.DataFrame, out_dir: Path) -> None:
    """Plot log chi_M,max against log L using the saved state-fraction samples."""
    frac_cols = [c for c in lattice_samples.columns if c.startswith("state_fraction_")]
    q = int(lattice_samples["q"].iloc[0])
    frame = lattice_samples.copy()
    frame["M"] = frame[frac_cols].max(axis=1) - 1.0 / q
    grouped = (
        frame.groupby(["L", "beta"], as_index=False)
        .agg(chi_M=("M", lambda s: float(s.var(ddof=0))))
    )

    rows: list[dict[str, float]] = []
    for L, subframe in grouped.groupby("L"):
        peak = subframe.loc[subframe["chi_M"].idxmax()]
        rows.append(
            {
                "L": float(L),
                "chi_M": float(peak["chi_M"]),
            }
        )
    peak_df = pd.DataFrame(rows).sort_values("L")
    x = np.log(peak_df["L"].to_numpy(dtype=float))
    y = np.log(peak_df["chi_M"].to_numpy(dtype=float))
    coeffs = np.polyfit(x, y, deg=1)
    x_fit = np.linspace(x.min(), x.max(), 200)
    y_fit = np.polyval(coeffs, x_fit)

    fig, ax = plt.subplots(figsize=(6.0, 4.2))
    ax.plot(x, y, "o", ms=5, label="peak data")
    ax.plot(x_fit, y_fit, lw=2, ls="--", label=fr"fit slope $={coeffs[0]:.3f}$")
    ax.set_xlabel(r"$\log L$")
    ax.set_ylabel(r"$\log V_{M,\max}$")
    ax.set_title("Raw order-parameter variance fit")
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_dir / "susceptibility_M_scaling_loglog.png", dpi=200)
    plt.close(fig)


def main() -> None:
    """Load large-scale outputs and save figures."""
    data_dir = ROOT / "results" / "data"
    out_dir = ROOT / "results" / "figures"
    out_dir.mkdir(parents=True, exist_ok=True)

    two_block = pd.read_csv(data_dir / "large_scale_two_block_summary.csv")
    fit_df = pd.read_csv(data_dir / "large_scale_landau_fit.csv")
    three_block = pd.read_csv(data_dir / "large_scale_three_block_summary.csv")
    finite_block = pd.read_csv(data_dir / "finite_block_model_summary.csv")
    mc_block = pd.read_csv(data_dir / "finite_block_mc_summary.csv")
    lattice = pd.read_csv(data_dir / "lattice_potts_summary.csv")
    lattice_samples = pd.read_csv(data_dir / "lattice_potts_samples.csv")

    plot_two_block_contrast(two_block, out_dir)
    plot_two_block_symmetry_deficit(two_block, out_dir)
    plot_mean_field_error(two_block, out_dir)
    plot_landau_fit(two_block, fit_df, out_dir)
    plot_three_block_symmetry(three_block, out_dir)
    plot_finite_block_symmetry_deficit(finite_block, out_dir)
    plot_mean_field_finite_comparison(two_block, finite_block, out_dir)
    plot_monte_carlo_symmetry_deficit(mc_block, out_dir)
    plot_monte_carlo_susceptibility(mc_block, out_dir)
    plot_monte_carlo_peak_scaling(mc_block, out_dir)
    plot_lattice_symmetry_deficit(lattice, out_dir)
    plot_lattice_susceptibility(lattice, out_dir)
    plot_lattice_peak_scaling(lattice, out_dir)
    plot_lattice_energy(lattice, out_dir)
    plot_lattice_susceptibility_scaling_D(lattice, out_dir)
    plot_lattice_susceptibility_scaling_M(lattice_samples, out_dir)

    print(f"Saved large-scale figures to {out_dir}")


if __name__ == "__main__":
    main()
