"""Reference-group diagnostics for a mean-field orientational phase model.

The model is the classical mean-field XY system

    E(theta) = -J / (2N) * |sum_j exp(i theta_j)|^2.

Its physical reference group is the global rotation group SO(2).  Above the
mean-field critical inverse temperature beta_c = 2 / J, a selected pure phase
has a preferred orientation.  After aligning each sampled configuration with
its instantaneous magnetization, the one-angle law can be compared with the
uniform invariant measure on SO(2) by relative entropy.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
import pandas as pd
from scipy.optimize import brentq
from scipy.special import i0e, i1e


TWO_PI = 2.0 * np.pi


def bessel_ratio(kappa: float | np.ndarray) -> float | np.ndarray:
    """Return I_1(kappa) / I_0(kappa) using exponentially scaled functions."""
    return i1e(kappa) / i0e(kappa)


def predicted_order(beta: float, coupling: float = 1.0) -> float:
    """Return the nonnegative thermodynamic mean-field order parameter."""
    beta_j = float(beta) * float(coupling)
    if beta_j <= 2.0:
        return 0.0

    def stationarity(r: float) -> float:
        return r - float(bessel_ratio(beta_j * r))

    return float(brentq(stationarity, 1.0e-8, 1.0 - 1.0e-12))


def predicted_measure_deficit(beta: float, coupling: float = 1.0) -> float:
    """Return D_KL(rho_beta || uniform) for the selected mean-field phase."""
    r = predicted_order(beta, coupling)
    if r == 0.0:
        return 0.0
    kappa = float(beta) * float(coupling) * r
    log_i0 = np.log(i0e(kappa)) + abs(kappa)
    return float(kappa * r - log_i0)


def predicted_aligned_density(
    angles: np.ndarray, beta: float, coupling: float = 1.0
) -> np.ndarray:
    """Return the selected-phase von Mises density on [-pi, pi)."""
    r = predicted_order(beta, coupling)
    kappa = float(beta) * float(coupling) * r
    weights = np.exp(kappa * np.cos(angles) - abs(kappa))
    normalization = TWO_PI * i0e(kappa)
    return weights / normalization


def wrap_angle(angle: np.ndarray | float) -> np.ndarray | float:
    """Wrap angles to the interval [-pi, pi)."""
    return (angle + np.pi) % TWO_PI - np.pi


def histogram_relative_entropy(counts: np.ndarray) -> float:
    """Return discrete KL divergence from the uniform histogram law."""
    total = int(np.sum(counts))
    if total == 0:
        return 0.0
    probabilities = counts.astype(float) / float(total)
    positive = probabilities > 0.0
    bins = len(probabilities)
    return float(
        np.sum(probabilities[positive] * np.log(bins * probabilities[positive]))
    )


@dataclass(frozen=True)
class XYSimulationConfig:
    """Configuration for finite-N mean-field XY Metropolis scans."""

    system_sizes: tuple[int, ...] = (64, 256)
    betas: tuple[float, ...] = (
        1.0,
        1.5,
        1.8,
        2.0,
        2.1,
        2.25,
        2.5,
        3.0,
        3.5,
        4.0,
    )
    coupling: float = 1.0
    replicas: int = 4
    burn_in_sweeps: int = 300
    measurement_sweeps: int = 500
    sample_every_sweeps: int = 5
    proposal_width: float = np.pi
    histogram_bins: int = 48
    seed: int = 20261003


def run_xy_chain(
    n: int,
    beta: float,
    coupling: float,
    burn_in_sweeps: int,
    measurement_sweeps: int,
    sample_every_sweeps: int,
    proposal_width: float,
    histogram_bins: int,
    rng: np.random.Generator,
) -> tuple[dict[str, float], np.ndarray]:
    """Run one Metropolis chain and return scalar and histogram diagnostics."""
    angles = rng.uniform(-np.pi, np.pi, size=n)
    cos_values = np.cos(angles)
    sin_values = np.sin(angles)
    magnetization_x = float(np.sum(cos_values))
    magnetization_y = float(np.sum(sin_values))
    accepted = 0
    attempted = 0
    order_samples: list[float] = []
    histogram_counts = np.zeros(histogram_bins, dtype=np.int64)
    bin_edges = np.linspace(-np.pi, np.pi, histogram_bins + 1)

    total_sweeps = burn_in_sweeps + measurement_sweeps
    for sweep in range(total_sweeps):
        for _ in range(n):
            i = int(rng.integers(0, n))
            old_angle = float(angles[i])
            new_angle = float(
                wrap_angle(old_angle + rng.uniform(-proposal_width, proposal_width))
            )
            new_cos = float(np.cos(new_angle))
            new_sin = float(np.sin(new_angle))
            delta_x = new_cos - float(cos_values[i])
            delta_y = new_sin - float(sin_values[i])
            new_magnetization_x = magnetization_x + delta_x
            new_magnetization_y = magnetization_y + delta_y
            delta_energy = -coupling / (2.0 * n) * (
                new_magnetization_x**2
                + new_magnetization_y**2
                - magnetization_x**2
                - magnetization_y**2
            )
            attempted += 1
            if delta_energy <= 0.0 or rng.random() < np.exp(-beta * delta_energy):
                angles[i] = new_angle
                cos_values[i] = new_cos
                sin_values[i] = new_sin
                magnetization_x = new_magnetization_x
                magnetization_y = new_magnetization_y
                accepted += 1

        if sweep < burn_in_sweeps:
            continue
        if (sweep - burn_in_sweeps) % sample_every_sweeps != 0:
            continue

        magnitude = float(np.hypot(magnetization_x, magnetization_y))
        order_samples.append(magnitude / float(n))
        orientation = float(np.arctan2(magnetization_y, magnetization_x))
        aligned_angles = np.asarray(wrap_angle(angles - orientation))
        histogram_counts += np.histogram(aligned_angles, bins=bin_edges)[0]

    order_array = np.asarray(order_samples, dtype=float)
    diagnostics = {
        "order_mean": float(np.mean(order_array)),
        "order_std": (
            float(np.std(order_array, ddof=1)) if len(order_array) > 1 else 0.0
        ),
        "measure_deficit": histogram_relative_entropy(histogram_counts),
        "acceptance_rate": accepted / float(attempted),
        "num_measurements": float(len(order_array)),
        "num_aligned_angles": float(np.sum(histogram_counts)),
    }
    return diagnostics, histogram_counts


def run_xy_scan(
    config: XYSimulationConfig,
) -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    """Run all finite-size scans and return chain, summary, and histogram tables."""
    chain_rows: list[dict[str, float]] = []
    histogram_rows: list[dict[str, float]] = []
    seed_sequence = np.random.SeedSequence(config.seed)
    child_seeds = iter(
        seed_sequence.spawn(
            len(config.system_sizes) * len(config.betas) * config.replicas
        )
    )
    bin_edges = np.linspace(-np.pi, np.pi, config.histogram_bins + 1)
    bin_centers = 0.5 * (bin_edges[:-1] + bin_edges[1:])
    bin_width = float(bin_edges[1] - bin_edges[0])

    for n in config.system_sizes:
        for beta in config.betas:
            for replica in range(config.replicas):
                rng = np.random.default_rng(next(child_seeds))
                diagnostics, counts = run_xy_chain(
                    n=n,
                    beta=beta,
                    coupling=config.coupling,
                    burn_in_sweeps=config.burn_in_sweeps,
                    measurement_sweeps=config.measurement_sweeps,
                    sample_every_sweeps=config.sample_every_sweeps,
                    proposal_width=config.proposal_width,
                    histogram_bins=config.histogram_bins,
                    rng=rng,
                )
                chain_rows.append(
                    {
                        "n": float(n),
                        "beta": float(beta),
                        "replica": float(replica),
                        "predicted_order": predicted_order(beta, config.coupling),
                        "predicted_measure_deficit": predicted_measure_deficit(
                            beta, config.coupling
                        ),
                        **diagnostics,
                    }
                )
                probabilities = counts.astype(float) / float(np.sum(counts))
                predicted_density = predicted_aligned_density(
                    bin_centers, beta, config.coupling
                )
                for center, probability, theory_density in zip(
                    bin_centers, probabilities, predicted_density
                ):
                    histogram_rows.append(
                        {
                            "n": float(n),
                            "beta": float(beta),
                            "replica": float(replica),
                            "angle": float(center),
                            "density": float(probability / bin_width),
                            "predicted_density": float(theory_density),
                        }
                    )

    chain_df = pd.DataFrame(chain_rows)
    summary_df = (
        chain_df.groupby(["n", "beta"], as_index=False)
        .agg(
            predicted_order=("predicted_order", "first"),
            predicted_measure_deficit=("predicted_measure_deficit", "first"),
            order_mean=("order_mean", "mean"),
            order_between_replica_std=("order_mean", "std"),
            measure_deficit_mean=("measure_deficit", "mean"),
            measure_deficit_between_replica_std=("measure_deficit", "std"),
            acceptance_rate_mean=("acceptance_rate", "mean"),
            num_measurements=("num_measurements", "sum"),
        )
        .sort_values(["n", "beta"])
        .reset_index(drop=True)
    )
    histogram_df = pd.DataFrame(histogram_rows)
    return chain_df, summary_df, histogram_df


def reference_group_scaling_table(system_sizes: np.ndarray) -> pd.DataFrame:
    """Return exact global and product-group scaling predictions."""
    sizes = np.asarray(system_sizes, dtype=float)
    return pd.DataFrame(
        {
            "n": sizes,
            "global_total_deficit": np.full_like(sizes, np.log(2.0)),
            "global_deficit_rate": np.log(2.0) / sizes,
            "product_total_deficit": sizes * np.log(2.0),
            "product_deficit_rate": np.full_like(sizes, np.log(2.0)),
        }
    )
