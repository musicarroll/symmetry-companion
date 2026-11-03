"""Large-scale finite-size experiments for relational phase structure."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import numpy as np
import pandas as pd

from block_relational_model import (
    BlockRelationalModel,
    block_observables,
    symmetric_group_permutations,
)
from finite_block_model import FiniteBlockModel
from landau_model import LandauModel
from lattice_potts_model import LatticePottsModel
from two_block_model import TwoBlockModel


@dataclass(frozen=True)
class TwoBlockScanConfig:
    """Configuration for finite-size two-block phase scans."""

    n_values: tuple[int, ...] = (100, 300, 1000)
    beta_values: tuple[float, ...] = tuple(np.linspace(1.5, 2.8, 14))
    samples_per_beta: int = 8
    seed: int = 1729
    tolerance_prefactor: float = 0.5


@dataclass(frozen=True)
class ThreeBlockScanConfig:
    """Configuration for a three-block symmetry-breaking scan."""

    n_values: tuple[int, ...] = (300, 900)
    gamma_values: tuple[float, ...] = tuple(np.linspace(0.0, 0.18, 10))
    samples_per_gamma: int = 6
    base_prob: float = 0.40
    seed: int = 2718
    tolerance_prefactor: float = 0.5


@dataclass(frozen=True)
class FiniteBlockPhaseConfig:
    """Configuration for the first non-toy finite relational phase scan."""

    n_values: tuple[int, ...] = (120, 240)
    k_values: tuple[int, ...] = (2, 3)
    lambda_values: tuple[float, ...] = tuple(np.linspace(0.0, 0.24, 13))
    q_base: float = 0.35
    samples_per_lambda: int = 24
    seed: int = 31415


@dataclass(frozen=True)
class MonteCarloRelationalConfig:
    """Configuration for the energy-based finite relational model."""

    n_values: tuple[int, ...] = (60, 120, 240, 360)
    k_values: tuple[int, ...] = (3,)
    lambda_values: tuple[float, ...] = tuple(np.linspace(0.0, 4.0, 17))
    burn_in_steps: int = 5000
    sample_steps: int = 10000
    sample_every: int = 100
    seed: int = 4242


@dataclass(frozen=True)
class LatticePottsConfig:
    """Configuration for the lattice Potts Monte Carlo model."""

    l_values: tuple[int, ...] = (20, 30, 40)
    q: int = 2
    J: float = 1.0
    beta_values: tuple[float, ...] = (
        0.10,
        0.30,
        0.40,
        0.42,
        0.44,
        0.46,
        0.50,
        1.00,
        2.00,
    )
    burn_in_sweeps: int = 100
    measurement_sweeps: int = 200
    sample_every_sweeps: int = 10
    seed: int = 5151


def binder_like_cumulant(values: pd.Series) -> float:
    """Return the Binder-like cumulant for the symmetry deficit samples."""
    d2 = float(np.mean(np.square(values.to_numpy(dtype=float))))
    if d2 <= 0.0:
        return 0.0
    d4 = float(np.mean(np.power(values.to_numpy(dtype=float), 4)))
    return float(1.0 - d4 / (3.0 * d2 * d2))


def peak_width_at_half_max(frame: pd.DataFrame) -> float:
    """Estimate the width of a susceptibility peak at half maximum."""
    y = frame["symmetry_deficit_susceptibility"].to_numpy(dtype=float)
    x = frame["lambda_control"].to_numpy(dtype=float)
    if len(y) == 0:
        return 0.0
    ymax = float(np.max(y))
    if ymax <= 0.0:
        return float(x[-1] - x[0]) if len(x) > 1 else 0.0
    mask = y >= 0.5 * ymax
    if not np.any(mask):
        return 0.0
    x_support = x[mask]
    return float(x_support[-1] - x_support[0])


def curve_width_at_half_max(frame: pd.DataFrame, x_col: str, y_col: str) -> float:
    """Estimate the support width above half maximum for a sampled curve."""
    y = frame[y_col].to_numpy(dtype=float)
    x = frame[x_col].to_numpy(dtype=float)
    if len(y) == 0:
        return 0.0
    ymax = float(np.max(y))
    if ymax <= 0.0:
        return float(x[-1] - x[0]) if len(x) > 1 else 0.0
    mask = y >= 0.5 * ymax
    if not np.any(mask):
        return 0.0
    support = x[mask]
    return float(support[-1] - support[0])


def weighted_peak_width(frame: pd.DataFrame, x_col: str, y_col: str) -> float:
    """Return the susceptibility-weighted width of a sampled peak."""
    x = frame[x_col].to_numpy(dtype=float)
    y = frame[y_col].to_numpy(dtype=float)
    total = float(np.sum(y))
    if total <= 0.0:
        return 0.0
    weights = y / total
    mean_x = float(np.sum(weights * x))
    variance = float(np.sum(weights * np.square(x - mean_x)))
    return float(np.sqrt(max(variance, 0.0)))


def susceptibility_scaling_fit(lattice_grouped: pd.DataFrame) -> dict[str, float]:
    """Fit chi_max(L) ~ L^(gamma/nu) from the lattice peak data."""
    peak_rows: list[dict[str, float]] = []
    for L, frame in lattice_grouped.groupby("L"):
        peak = frame.loc[frame["symmetry_deficit_susceptibility"].idxmax()]
        peak_rows.append(
            {
                "L": float(L),
                "chi_max": float(peak["symmetry_deficit_susceptibility"]),
                "beta_peak": float(peak["beta"]),
            }
        )
    peak_df = pd.DataFrame(peak_rows).sort_values("L").reset_index(drop=True)
    x = np.log(peak_df["L"].to_numpy(dtype=float))
    y = np.log(peak_df["chi_max"].to_numpy(dtype=float))
    coeffs = np.polyfit(x, y, deg=1)
    y_fit = np.polyval(coeffs, x)
    rms = float(np.sqrt(np.mean(np.square(y - y_fit))))
    ss_res = float(np.sum(np.square(y - y_fit)))
    ss_tot = float(np.sum(np.square(y - np.mean(y))))
    r2 = float(1.0 - ss_res / ss_tot) if ss_tot > 0.0 else 1.0
    expected = 1.75
    estimate = float(coeffs[0])
    percent_error = float(100.0 * abs(estimate - expected) / expected)
    consistent = bool(1.5 < estimate < 2.0)
    return {
        "gamma_over_nu_estimate": estimate,
        "fit_intercept": float(coeffs[1]),
        "fit_rms": rms,
        "fit_r2": r2,
        "expected_lower": 1.5,
        "expected_upper": 2.0,
        "expected_reference": expected,
        "percent_error_vs_ising": percent_error,
        "consistent_with_potts_range": consistent,
    }


def tolerance_for_size(n: int, prefactor: float) -> float:
    """Finite-size tolerance used for coarse block-symmetry tests."""
    return prefactor / np.sqrt(float(n))


def two_block_sector_symmetry_deficit(within_mean: float, cross_mean: float, tolerance: float) -> float:
    """Return the Chapter 3.11 coarse symmetry deficit for the reduced pair."""
    if abs(within_mean - cross_mean) <= tolerance:
        return 0.0
    return float(np.log(2.0))


def build_two_block_model_from_mean_field(n: int, beta: float, J: float = 1.0) -> tuple[BlockRelationalModel, dict[str, float]]:
    """Build a finite-size two-block graph model from the Chapter 3 minimizer."""
    mean_field = TwoBlockModel(J=J)
    minimizer = mean_field.minimize(beta)
    half = n // 2
    block_sizes = (half, n - half)
    p = float(minimizer["p_star"])
    q = float(minimizer["q_star"])
    probs = np.array([[p, q], [q, p]], dtype=float)
    model = BlockRelationalModel(block_sizes=block_sizes, edge_probs=probs)
    return model, minimizer


def run_two_block_phase_scan(config: TwoBlockScanConfig, J: float = 1.0) -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    """Run a finite-size scan based on mean-field two-block predictions."""
    rng = np.random.default_rng(config.seed)
    rows: list[dict[str, float]] = []
    group = [(0, 1), (1, 0)]
    landau = LandauModel(J=J)

    for n in config.n_values:
        tol = tolerance_for_size(n, config.tolerance_prefactor)
        for beta in config.beta_values:
            model, minimizer = build_two_block_model_from_mean_field(n=n, beta=float(beta), J=J)
            for sample_id in range(config.samples_per_beta):
                adj = model.sample_adjacency(rng)
                obs = block_observables(adj, model, group=group, tolerance=tol)
                obs["symmetry_deficit"] = two_block_sector_symmetry_deficit(
                    obs["within_density_mean"],
                    obs["cross_density_mean"],
                    tolerance=tol,
                )
                obs.update(
                    {
                        "experiment": "two_block_phase_scan",
                        "sample_id": float(sample_id),
                        "beta": float(beta),
                        "tolerance": tol,
                        "mean_field_p": float(minimizer["p_star"]),
                        "mean_field_q": float(minimizer["q_star"]),
                        "mean_field_delta": float(abs(minimizer["p_star"] - minimizer["q_star"])),
                        "mean_field_d": float(0.5 * abs(minimizer["p_star"] - minimizer["q_star"])),
                        "landau_d": float(landau.predicted_d_star(beta)),
                        "beta_c": float(landau.beta_c()),
                        "delta_error": float(obs["block_contrast"] - abs(minimizer["p_star"] - minimizer["q_star"])),
                    }
                )
                rows.append(obs)

    samples = pd.DataFrame(rows)
    grouped = (
        samples.groupby(["n", "beta"], as_index=False)
        .agg(
            symmetry_deficit_mean=("symmetry_deficit", "mean"),
            symmetry_deficit_std=("symmetry_deficit", "std"),
            entropy_density_mean=("entropy_density", "mean"),
            block_contrast_mean=("block_contrast", "mean"),
            block_contrast_std=("block_contrast", "std"),
            mean_field_delta=("mean_field_delta", "first"),
            mean_field_d=("mean_field_d", "first"),
            landau_d=("landau_d", "first"),
            beta_c=("beta_c", "first"),
            degree_mean=("degree_mean", "mean"),
            degree_std=("degree_std", "mean"),
        )
        .fillna(0.0)
    )
    grouped["abs_delta_error"] = np.abs(grouped["block_contrast_mean"] - grouped["mean_field_delta"])
    grouped["abs_landau_error"] = np.abs(0.5 * grouped["block_contrast_mean"] - grouped["landau_d"])

    fit_df = fit_landau_projection(grouped[grouped["n"] == max(config.n_values)].copy())
    fit_df["n"] = float(max(config.n_values))
    return samples, grouped, fit_df


def fit_landau_projection(grouped: pd.DataFrame) -> pd.DataFrame:
    """Fit a polynomial reduced model for the simulated order-parameter branch."""
    beta_c = float(grouped["beta_c"].iloc[0])
    fit_region = grouped[grouped["beta"] >= beta_c].copy()
    x = np.maximum(fit_region["beta"].to_numpy() - beta_c, 0.0)
    y = 0.5 * fit_region["block_contrast_mean"].to_numpy()
    if len(fit_region) >= 4:
        coeffs = np.polyfit(x, y, deg=3)
        fit_region["landau_poly_fit"] = np.polyval(coeffs, x)
    else:
        coeffs = np.zeros(4)
        fit_region["landau_poly_fit"] = y
    fit_region["reduced_variable"] = x
    fit_region["fit_error"] = fit_region["landau_poly_fit"] - y
    fit_region["fit_coeff_c3"] = coeffs[0]
    fit_region["fit_coeff_c2"] = coeffs[1]
    fit_region["fit_coeff_c1"] = coeffs[2]
    fit_region["fit_coeff_c0"] = coeffs[3]
    return fit_region


def three_block_probability_matrix(base_prob: float, gamma: float) -> np.ndarray:
    """Return a simple S_3-to-S_2 symmetry-breaking three-block profile."""
    probs = np.array(
        [
            [base_prob + gamma, base_prob, base_prob],
            [base_prob, base_prob + gamma, base_prob],
            [base_prob, base_prob, base_prob - gamma],
        ],
        dtype=float,
    )
    return np.clip(probs, 1.0e-3, 1.0 - 1.0e-3)


def run_three_block_scan(config: ThreeBlockScanConfig) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Run a finite-size multi-block symmetry scan."""
    rng = np.random.default_rng(config.seed)
    rows: list[dict[str, float]] = []
    group = symmetric_group_permutations(3)

    for n in config.n_values:
        block = n // 3
        block_sizes = (block, block, n - 2 * block)
        tol = tolerance_for_size(n, config.tolerance_prefactor)
        for gamma in config.gamma_values:
            probs = three_block_probability_matrix(config.base_prob, float(gamma))
            model = BlockRelationalModel(block_sizes=block_sizes, edge_probs=probs)
            for sample_id in range(config.samples_per_gamma):
                adj = model.sample_adjacency(rng)
                obs = block_observables(adj, model, group=group, tolerance=tol)
                obs.update(
                    {
                        "experiment": "three_block_symmetry_scan",
                        "sample_id": float(sample_id),
                        "gamma": float(gamma),
                        "tolerance": tol,
                    }
                )
                rows.append(obs)

    samples = pd.DataFrame(rows)
    grouped = (
        samples.groupby(["n", "gamma"], as_index=False)
        .agg(
            symmetry_deficit_mean=("symmetry_deficit", "mean"),
            symmetry_deficit_std=("symmetry_deficit", "std"),
            entropy_density_mean=("entropy_density", "mean"),
            block_contrast_mean=("block_contrast", "mean"),
            block_density_std_mean=("block_density_std", "mean"),
            degree_mean=("degree_mean", "mean"),
            degree_std=("degree_std", "mean"),
        )
        .fillna(0.0)
    )
    return samples, grouped


def run_finite_block_phase_scan(config: FiniteBlockPhaseConfig) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Run the first finite relational symmetry-breaking scan."""
    rng = np.random.default_rng(config.seed)
    rows: list[dict[str, float]] = []

    for k in config.k_values:
        for n in config.n_values:
            for lam in config.lambda_values:
                p = min(config.q_base + float(lam), 0.95)
                q = config.q_base
                model = FiniteBlockModel(n=n, k=k, p=p, q=q)
                for sample_id in range(config.samples_per_lambda):
                    adj = model.sample(rng)
                    obs = model.observables(adj)
                    obs.update(
                        {
                            "experiment": "finite_block_phase_scan",
                            "sample_id": float(sample_id),
                            "k": float(k),
                        }
                    )
                    rows.append(obs)

    samples = pd.DataFrame(rows)
    grouped = (
        samples.groupby(["k", "n", "lambda_control"], as_index=False)
        .agg(
            symmetry_deficit_mean=("symmetry_deficit", "mean"),
            symmetry_deficit_std=("symmetry_deficit", "std"),
            entropy_density_mean=("entropy_density", "mean"),
            block_contrast_mean=("block_contrast", "mean"),
            block_density_std_mean=("block_density_std", "mean"),
            degree_mean=("degree_mean", "mean"),
            degree_std=("degree_std", "mean"),
            q=("q", "first"),
            p=("p", "first"),
        )
        .fillna(0.0)
    )
    return samples, grouped


def run_monte_carlo_relational_scan(
    config: MonteCarloRelationalConfig,
) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Run the energy-based finite relational model with Metropolis sampling."""
    rng = np.random.default_rng(config.seed)
    rows: list[dict[str, float]] = []
    summary_rows: list[dict[str, float]] = []

    for k in config.k_values:
        for n in config.n_values:
            model = FiniteBlockModel(n=n, k=k, p=0.5, q=0.5)
            for lam in config.lambda_values:
                sample_rows, acceptance_rate = model.monte_carlo_observables(
                    lambda_control=float(lam),
                    rng=rng,
                    burn_in_steps=config.burn_in_steps,
                    sample_steps=config.sample_steps,
                    sample_every=config.sample_every,
                )
                for idx, obs in enumerate(sample_rows):
                    obs.update(
                        {
                            "experiment": "finite_block_monte_carlo",
                            "sample_id": float(idx),
                            "k": float(k),
                            "burn_in_steps": float(config.burn_in_steps),
                            "sample_steps": float(config.sample_steps),
                            "sample_every": float(config.sample_every),
                        }
                    )
                    rows.append(obs)

                sample_df = pd.DataFrame(sample_rows)
                summary_rows.append(
                    {
                        "k": float(k),
                        "n": float(n),
                        "lambda_control": float(lam),
                        "symmetry_deficit_mean": float(sample_df["symmetry_deficit"].mean()),
                        "symmetry_deficit_std": float(sample_df["symmetry_deficit"].std(ddof=0)),
                        "symmetry_deficit_susceptibility": float(sample_df["symmetry_deficit"].var(ddof=0)),
                        "binder_u": binder_like_cumulant(sample_df["symmetry_deficit"]),
                        "within_density_mean": float(sample_df["within_density_mean"].mean()),
                        "cross_density_mean": float(sample_df["cross_density_mean"].mean()),
                        "block_contrast_mean": float(sample_df["block_contrast"].mean()),
                        "entropy_density_mean": float(sample_df["entropy_density"].mean()),
                        "degree_mean": float(sample_df["degree_mean"].mean()),
                        "degree_std": float(sample_df["degree_std"].mean()),
                        "energy_mean": float(sample_df["energy"].mean()),
                        "acceptance_rate": acceptance_rate,
                    }
                )

    samples = pd.DataFrame(rows)
    grouped = pd.DataFrame(summary_rows)
    return samples, grouped


def run_lattice_potts_scan(
    config: LatticePottsConfig,
) -> tuple[pd.DataFrame, pd.DataFrame]:
    """Run a finite-size sweep of the two-dimensional lattice Potts model."""
    rng = np.random.default_rng(config.seed)
    rows: list[dict[str, float]] = []
    summary_rows: list[dict[str, float]] = []

    for L in config.l_values:
        model = LatticePottsModel(L=L, q=config.q, J=config.J)
        spins: np.ndarray | None = None
        for beta in config.beta_values:
            sample_rows, acceptance_rate, spins = model.monte_carlo_observables(
                beta=float(beta),
                rng=rng,
                burn_in_sweeps=config.burn_in_sweeps,
                measurement_sweeps=config.measurement_sweeps,
                sample_every_sweeps=config.sample_every_sweeps,
                initial_spins=spins,
            )
            for idx, obs in enumerate(sample_rows):
                obs.update(
                    {
                        "experiment": "lattice_potts",
                        "sample_id": float(idx),
                        "burn_in_sweeps": float(config.burn_in_sweeps),
                        "measurement_sweeps": float(config.measurement_sweeps),
                        "sample_every_sweeps": float(config.sample_every_sweeps),
                    }
                )
                rows.append(obs)

            sample_df = pd.DataFrame(sample_rows)
            energy_var = float(sample_df["energy_per_site"].var(ddof=0))
            summary_rows.append(
                {
                    "L": float(L),
                    "N": float(model.n),
                    "q": float(config.q),
                    "beta": float(beta),
                    "symmetry_deficit_mean": float(sample_df["symmetry_deficit"].mean()),
                    "symmetry_deficit_std": float(sample_df["symmetry_deficit"].std(ddof=0)),
                    "symmetry_deficit_susceptibility": float(sample_df["symmetry_deficit"].var(ddof=0)),
                    "energy_per_site_mean": float(sample_df["energy_per_site"].mean()),
                    "energy_per_site_std": float(sample_df["energy_per_site"].std(ddof=0)),
                    "specific_heat": float((beta**2) * model.n * energy_var),
                    "acceptance_rate": acceptance_rate,
                }
            )

    samples = pd.DataFrame(rows)
    grouped = pd.DataFrame(summary_rows)
    return samples, grouped


def build_large_scale_summary(
    two_block_grouped: pd.DataFrame,
    fit_df: pd.DataFrame,
    three_block_grouped: pd.DataFrame,
    finite_block_grouped: pd.DataFrame,
    mc_grouped: pd.DataFrame,
    lattice_grouped: pd.DataFrame,
) -> dict[str, object]:
    """Build a concise text/json summary for the large-scale experiments."""
    n_max = int(two_block_grouped["n"].max())
    near_threshold = two_block_grouped[
        (two_block_grouped["n"] == n_max) & (two_block_grouped["beta"] >= 2.0)
    ].copy()
    onset = near_threshold.loc[near_threshold["block_contrast_mean"] > 0.05, "beta"]
    beta_onset = float(onset.iloc[0]) if not onset.empty else None

    max_gamma_row = three_block_grouped.loc[three_block_grouped["gamma"].idxmax()]
    fit_row = fit_df.iloc[-1] if not fit_df.empty else None
    finite_kmax = int(finite_block_grouped["k"].max())
    finite_nmax = int(finite_block_grouped["n"].max())
    finite_frame = finite_block_grouped[
        (finite_block_grouped["k"] == finite_kmax) & (finite_block_grouped["n"] == finite_nmax)
    ].copy()
    finite_onset_candidates = finite_frame.loc[
        finite_frame["symmetry_deficit_mean"] > 1.0e-4, "lambda_control"
    ]
    finite_lambda_onset = (
        float(finite_onset_candidates.iloc[0]) if not finite_onset_candidates.empty else None
    )
    finite_terminal = finite_frame.iloc[-1]
    mc_frame = mc_grouped[
        (mc_grouped["k"] == mc_grouped["k"].max()) & (mc_grouped["n"] == mc_grouped["n"].max())
    ].copy()
    mc_peak = mc_frame.loc[mc_frame["symmetry_deficit_susceptibility"].idxmax()]
    mc_terminal = mc_frame.iloc[-1]
    mc_scaling_rows: list[dict[str, float]] = []
    for n, frame in mc_grouped.groupby("n"):
        frame = frame.sort_values("lambda_control").reset_index(drop=True)
        peak_idx = frame["symmetry_deficit_susceptibility"].idxmax()
        peak_row = frame.loc[peak_idx]
        mc_scaling_rows.append(
            {
                "n": float(n),
                "lambda_peak": float(peak_row["lambda_control"]),
                "chi_max": float(peak_row["symmetry_deficit_susceptibility"]),
                "peak_width": peak_width_at_half_max(frame),
                "binder_at_peak": float(peak_row["binder_u"]),
            }
        )
    mc_scaling = pd.DataFrame(mc_scaling_rows).sort_values("n").reset_index(drop=True)
    chi_values = mc_scaling["chi_max"].to_numpy(dtype=float)
    width_values = mc_scaling["peak_width"].to_numpy(dtype=float)
    chi_grows = bool(np.all(np.diff(chi_values) > 0.0)) if len(chi_values) > 1 else False
    width_sharpens = bool(np.all(np.diff(width_values) < 0.0)) if len(width_values) > 1 else False
    mc_conclusion = (
        "The growth and sharpening of the susceptibility peak with system size "
        "indicates behavior consistent with a second-order phase transition in the thermodynamic limit."
        if chi_grows and width_sharpens
        else "The observed peak suggests a crossover rather than a true phase transition."
    )
    lattice_scaling_rows: list[dict[str, float]] = []
    for L, frame in lattice_grouped.groupby("L"):
        frame = frame.sort_values("beta").reset_index(drop=True)
        peak_idx = frame["symmetry_deficit_susceptibility"].idxmax()
        peak_row = frame.loc[peak_idx]
        lattice_scaling_rows.append(
            {
                "L": float(L),
                "beta_peak": float(peak_row["beta"]),
                "chi_max": float(peak_row["symmetry_deficit_susceptibility"]),
                "peak_width": weighted_peak_width(frame, "beta", "symmetry_deficit_susceptibility"),
                "terminal_symmetry_deficit": float(frame.iloc[-1]["symmetry_deficit_mean"]),
            }
        )
    lattice_scaling = pd.DataFrame(lattice_scaling_rows).sort_values("L").reset_index(drop=True)
    lattice_chi = lattice_scaling["chi_max"].to_numpy(dtype=float)
    lattice_width = lattice_scaling["peak_width"].to_numpy(dtype=float)
    lattice_peak_grows = (
        bool(lattice_chi[-1] > lattice_chi[0] and lattice_chi[-1] >= np.max(lattice_chi[:-1]))
        if len(lattice_chi) > 1
        else False
    )
    lattice_peak_sharpens = bool(np.all(np.diff(lattice_width) < 0.0)) if len(lattice_width) > 1 else False
    lattice_conclusion = (
        "The growth and sharpening of the susceptibility peak with system size indicates behavior consistent with a second-order phase transition in the thermodynamic limit."
        if lattice_peak_grows and lattice_peak_sharpens
        else "The observed peak suggests a crossover rather than a true phase transition."
    )
    lattice_exponent = susceptibility_scaling_fit(lattice_grouped)
    lattice_universality = (
        "Results are consistent with 2D Potts universality class."
        if lattice_exponent["consistent_with_potts_range"]
        else "Finite-size effects or insufficient sampling may explain deviation."
    )

    return {
        "two_block_largest_n": n_max,
        "two_block_detected_beta_for_visible_contrast": beta_onset,
        "two_block_mean_abs_delta_error": float(two_block_grouped["abs_delta_error"].mean()),
        "two_block_mean_abs_landau_error": float(two_block_grouped["abs_landau_error"].mean()),
        "three_block_max_gamma_symmetry_deficit_mean": float(max_gamma_row["symmetry_deficit_mean"]),
        "three_block_max_gamma_block_contrast_mean": float(max_gamma_row["block_contrast_mean"]),
        "finite_block_largest_k": finite_kmax,
        "finite_block_largest_n": finite_nmax,
        "finite_block_detected_lambda_for_visible_deficit": finite_lambda_onset,
        "finite_block_terminal_symmetry_deficit_mean": float(finite_terminal["symmetry_deficit_mean"]),
        "finite_block_terminal_block_contrast_mean": float(finite_terminal["block_contrast_mean"]),
        "mc_largest_k": int(mc_frame["k"].iloc[0]),
        "mc_largest_n": int(mc_frame["n"].iloc[0]),
        "mc_peak_lambda": float(mc_peak["lambda_control"]),
        "mc_peak_susceptibility": float(mc_peak["symmetry_deficit_susceptibility"]),
        "mc_terminal_symmetry_deficit_mean": float(mc_terminal["symmetry_deficit_mean"]),
        "mc_peak_scaling": mc_scaling.to_dict(orient="records"),
        "mc_peak_height_grows_with_n": chi_grows,
        "mc_peak_width_sharpens_with_n": width_sharpens,
        "mc_finite_size_conclusion": mc_conclusion,
        "lattice_peak_scaling": lattice_scaling.to_dict(orient="records"),
        "lattice_peak_height_grows_with_l": lattice_peak_grows,
        "lattice_peak_width_sharpens_with_l": lattice_peak_sharpens,
        "lattice_finite_size_conclusion": lattice_conclusion,
        "lattice_gamma_over_nu_estimate": lattice_exponent["gamma_over_nu_estimate"],
        "lattice_gamma_over_nu_fit_rms": lattice_exponent["fit_rms"],
        "lattice_gamma_over_nu_fit_r2": lattice_exponent["fit_r2"],
        "lattice_expected_range": [lattice_exponent["expected_lower"], lattice_exponent["expected_upper"]],
        "lattice_percent_error_vs_ising": lattice_exponent["percent_error_vs_ising"],
        "lattice_universality_assessment": lattice_universality,
        "landau_fit_terminal_error": float(fit_row["fit_error"]) if fit_row is not None else None,
        "assessment": (
            "Finite-size relational simulations show that symmetry deficit rises "
            "from a nearly permutation-invariant regime to a visibly structured "
            "regime in both mean-field-guided block ensembles and the first "
            "fully finite block-relational model. In the energy-based Monte Carlo "
            "model, symmetry deficit also develops a broad susceptibility peak whose "
            "finite-size behavior can be tested directly across multiple system sizes. "
            "The lattice Potts model adds spatial locality and provides a separate "
            "test of whether symmetry deficit sharpens in step with genuine collective ordering."
        ),
    }


def save_summary_text(summary: dict[str, object], out_path: Path) -> None:
    """Write a readable summary of the large-scale experiments."""
    lines = [
        "Large-Scale Relational Phase-Structure Summary",
        f"Largest two-block system size = {summary['two_block_largest_n']}",
        "Detected visible two-block contrast at beta = "
        f"{summary['two_block_detected_beta_for_visible_contrast']}",
        "Mean absolute two-block contrast error vs. mean field = "
        f"{summary['two_block_mean_abs_delta_error']:.6f}",
        "Mean absolute two-block d-error vs. Landau = "
        f"{summary['two_block_mean_abs_landau_error']:.6f}",
        "Three-block symmetry-deficit mean at maximum gamma = "
        f"{summary['three_block_max_gamma_symmetry_deficit_mean']:.6f}",
        "Three-block contrast mean at maximum gamma = "
        f"{summary['three_block_max_gamma_block_contrast_mean']:.6f}",
        "Largest finite block model = "
        f"k={summary['finite_block_largest_k']}, N={summary['finite_block_largest_n']}",
        "Detected visible finite-model symmetry deficit at lambda = "
        f"{summary['finite_block_detected_lambda_for_visible_deficit']}",
        "Finite-model symmetry-deficit mean at maximum lambda = "
        f"{summary['finite_block_terminal_symmetry_deficit_mean']:.6f}",
        "Finite-model contrast mean at maximum lambda = "
        f"{summary['finite_block_terminal_block_contrast_mean']:.6f}",
        "Largest Monte Carlo model = "
        f"k={summary['mc_largest_k']}, N={summary['mc_largest_n']}",
        "Monte Carlo susceptibility peak at lambda = "
        f"{summary['mc_peak_lambda']}",
        "Monte Carlo peak susceptibility = "
        f"{summary['mc_peak_susceptibility']:.6f}",
        "Monte Carlo symmetry-deficit mean at maximum lambda = "
        f"{summary['mc_terminal_symmetry_deficit_mean']:.6f}",
        "Monte Carlo peak height grows with N = "
        f"{summary['mc_peak_height_grows_with_n']}",
        "Monte Carlo peak width sharpens with N = "
        f"{summary['mc_peak_width_sharpens_with_n']}",
        "Lattice susceptibility peak grows with L = "
        f"{summary['lattice_peak_height_grows_with_l']}",
        "Lattice susceptibility peak sharpens with L = "
        f"{summary['lattice_peak_width_sharpens_with_l']}",
        "Lattice gamma/nu estimate = "
        f"{summary['lattice_gamma_over_nu_estimate']:.6f}",
        "Lattice gamma/nu fit RMS = "
        f"{summary['lattice_gamma_over_nu_fit_rms']:.6f}",
        "Lattice percent error vs. 7/4 = "
        f"{summary['lattice_percent_error_vs_ising']:.3f}",
        "Terminal Landau polynomial fit error = "
        f"{summary['landau_fit_terminal_error']:.6f}",
        "",
        "Monte Carlo finite-size conclusion: "
        f"{summary['mc_finite_size_conclusion']}",
        "Lattice finite-size conclusion: "
        f"{summary['lattice_finite_size_conclusion']}",
        "Lattice universality assessment: "
        f"{summary['lattice_universality_assessment']}",
        "",
        f"Assessment: {summary['assessment']}",
    ]
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
