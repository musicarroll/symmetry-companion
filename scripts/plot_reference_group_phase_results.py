#!/usr/bin/env python3
"""Plot Chapter 6 reference-group predictions and simulated measurements."""

from __future__ import annotations

import sys
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT / "src") not in sys.path:
    sys.path.insert(0, str(ROOT / "src"))

from reference_group_phase_model import predicted_measure_deficit, predicted_order


def transition_plot(summary_df: pd.DataFrame, figure_dir: Path) -> None:
    """Plot analytic transition curves against finite-size measurements."""
    beta_grid = np.linspace(1.0, 4.0, 301)
    theory_order = np.asarray([predicted_order(beta) for beta in beta_grid])
    theory_deficit = np.asarray(
        [predicted_measure_deficit(beta) for beta in beta_grid]
    )

    fig, axes = plt.subplots(1, 2, figsize=(10, 4.1))
    axes[0].plot(
        beta_grid, theory_order, color="black", lw=2.2, label="mean-field prediction"
    )
    axes[1].plot(
        beta_grid,
        theory_deficit,
        color="black",
        lw=2.2,
        label="mean-field prediction",
    )

    markers = {64: "o", 256: "s"}
    colors = {64: "#2c7fb8", 256: "#d95f0e"}
    for n_value, frame in summary_df.groupby("n"):
        n = int(n_value)
        axes[0].errorbar(
            frame["beta"],
            frame["order_mean"],
            yerr=frame["order_between_replica_std"],
            fmt=markers.get(n, "o"),
            ms=4.5,
            capsize=2,
            color=colors.get(n),
            label=rf"Metropolis, $N={n}$",
        )
        axes[1].errorbar(
            frame["beta"],
            frame["measure_deficit_mean"],
            yerr=frame["measure_deficit_between_replica_std"],
            fmt=markers.get(n, "o"),
            ms=4.5,
            capsize=2,
            color=colors.get(n),
            label=rf"Metropolis, $N={n}$",
        )

    for ax in axes:
        ax.axvline(2.0, color="0.35", ls="--", lw=1.2, label=r"$\beta_c=2$")
        ax.set_xlabel(r"inverse temperature $\beta$")
        ax.grid(alpha=0.2)
    axes[0].set_ylabel(r"orientational order $r$")
    axes[0].set_title("Order parameter")
    axes[1].set_ylabel(r"aligned $D_{\mathrm{KL}}(\nu\Vert\mu_{S^1})$")
    axes[1].set_title("Measure symmetry deficit")
    handles, labels = axes[1].get_legend_handles_labels()
    unique = dict(zip(labels, handles))
    axes[1].legend(unique.values(), unique.keys(), fontsize=8, loc="upper left")
    fig.tight_layout()
    fig.savefig(figure_dir / "reference_group_xy_transition.png", dpi=220)
    plt.close(fig)


def distribution_plot(histogram_df: pd.DataFrame, figure_dir: Path) -> None:
    """Plot aligned angular laws against selected-phase predictions."""
    largest_n = int(histogram_df["n"].max())
    representative_betas = (1.5, 2.25, 3.0)
    fig, axes = plt.subplots(1, 3, figsize=(11, 3.4), sharey=True)

    for ax, beta in zip(axes, representative_betas):
        frame = histogram_df.loc[
            (histogram_df["n"] == largest_n) & np.isclose(histogram_df["beta"], beta)
        ].copy()
        grouped = frame.groupby("angle", as_index=False).agg(
            density=("density", "mean"),
            density_std=("density", "std"),
            predicted_density=("predicted_density", "first"),
        )
        ax.plot(
            grouped["angle"],
            grouped["predicted_density"],
            color="black",
            lw=2,
            label="mean-field prediction",
        )
        ax.fill_between(
            grouped["angle"],
            np.maximum(grouped["density"] - grouped["density_std"], 0.0),
            grouped["density"] + grouped["density_std"],
            color="#2c7fb8",
            alpha=0.2,
        )
        ax.plot(
            grouped["angle"],
            grouped["density"],
            color="#2c7fb8",
            lw=1.4,
            label=rf"aligned simulation, $N={largest_n}$",
        )
        ax.axhline(1.0 / (2.0 * np.pi), color="0.5", ls=":", lw=1, label="uniform")
        ax.set_title(rf"$\beta={beta:g}$")
        ax.set_xlabel(r"aligned angle $\theta-\arg M$")
        ax.set_xlim(-np.pi, np.pi)
        ax.grid(alpha=0.15)

    axes[0].set_ylabel("probability density")
    handles, labels = axes[-1].get_legend_handles_labels()
    unique = dict(zip(labels, handles))
    axes[-1].legend(unique.values(), unique.keys(), fontsize=7, loc="upper right")
    fig.tight_layout()
    fig.savefig(figure_dir / "reference_group_xy_distributions.png", dpi=220)
    plt.close(fig)


def scaling_plot(scaling_df: pd.DataFrame, figure_dir: Path) -> None:
    """Plot exact finite-window scaling for global and product reference groups."""
    fig, axes = plt.subplots(1, 2, figsize=(9.5, 3.8))
    axes[0].plot(
        scaling_df["n"],
        scaling_df["global_total_deficit"],
        "o-",
        label=r"global $\mathbb{Z}_2$",
    )
    axes[0].plot(
        scaling_df["n"],
        scaling_df["product_total_deficit"],
        "s-",
        label=r"product $(\mathbb{Z}_2)^N$",
    )
    axes[1].plot(
        scaling_df["n"],
        scaling_df["global_deficit_rate"],
        "o-",
        label=r"global $\mathbb{Z}_2$",
    )
    axes[1].plot(
        scaling_df["n"],
        scaling_df["product_deficit_rate"],
        "s-",
        label=r"product $(\mathbb{Z}_2)^N$",
    )
    for ax in axes:
        ax.set_xscale("log", base=2)
        ax.set_xlabel(r"window size $N$")
        ax.grid(alpha=0.2)
        ax.legend(fontsize=8)
    axes[0].set_ylabel(r"total deficit $I_N$")
    axes[0].set_title("Total symmetry loss")
    axes[1].set_ylabel(r"rate $I_N/N$")
    axes[1].set_title("Volume-normalized deficit")
    fig.tight_layout()
    fig.savefig(figure_dir / "reference_group_deficit_scaling.png", dpi=220)
    plt.close(fig)


def main() -> None:
    """Load generated data and create all Chapter 6 figures."""
    data_dir = ROOT / "results" / "data"
    figure_dir = ROOT / "results" / "figures"
    figure_dir.mkdir(parents=True, exist_ok=True)

    summary_df = pd.read_csv(data_dir / "reference_group_xy_summary.csv")
    histogram_df = pd.read_csv(data_dir / "reference_group_xy_histograms.csv")
    scaling_df = pd.read_csv(data_dir / "reference_group_deficit_scaling.csv")
    transition_plot(summary_df, figure_dir)
    distribution_plot(histogram_df, figure_dir)
    scaling_plot(scaling_df, figure_dir)
    print(f"Saved Chapter 6 figures under {figure_dir}")


if __name__ == "__main__":
    main()
