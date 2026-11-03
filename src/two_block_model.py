"""Numerics for the refined two-block free-energy model.

The model is the Chapter 3 refined two-block free energy

    F_beta(p, q) = -(beta * J / 2) * (p - q)^2 - h(p) - h(q),

where h(u) = -u log u - (1-u) log(1-u).

This module provides:
- entropy and free-energy evaluation
- analytic gradients and Hessians
- directional curvatures in the symmetric/antisymmetric directions
- numerical minimization on (0, 1)^2
- beta scans with summary diagnostics
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable

import numpy as np
import pandas as pd
from scipy.optimize import minimize


EPS = 1.0e-9


def clip_unit_interval(u: np.ndarray | float, eps: float = EPS) -> np.ndarray | float:
    """Clip values into the open unit interval."""
    return np.clip(u, eps, 1.0 - eps)


def binary_entropy(u: np.ndarray | float, eps: float = EPS) -> np.ndarray | float:
    """Return h(u) = -u log u - (1-u) log(1-u) on (0, 1)."""
    u = clip_unit_interval(u, eps=eps)
    return -u * np.log(u) - (1.0 - u) * np.log(1.0 - u)


def binary_entropy_prime(u: np.ndarray | float, eps: float = EPS) -> np.ndarray | float:
    """Return h'(u) = log((1-u)/u)."""
    u = clip_unit_interval(u, eps=eps)
    return np.log((1.0 - u) / u)


def binary_entropy_second(u: np.ndarray | float, eps: float = EPS) -> np.ndarray | float:
    """Return h''(u) = -1 / (u(1-u))."""
    u = clip_unit_interval(u, eps=eps)
    return -1.0 / (u * (1.0 - u))


@dataclass(frozen=True)
class TwoBlockModel:
    """Refined two-block free-energy model."""

    J: float = 1.0
    eps: float = EPS

    def free_energy(self, p: float, q: float, beta: float) -> float:
        """Evaluate F_beta(p, q)."""
        p = clip_unit_interval(p, self.eps)
        q = clip_unit_interval(q, self.eps)
        return -(beta * self.J / 2.0) * (p - q) ** 2 - binary_entropy(p) - binary_entropy(q)

    def free_energy_array(self, pq: np.ndarray, beta: float) -> float:
        """Free energy with packed vector input."""
        return self.free_energy(float(pq[0]), float(pq[1]), beta)

    def symmetry_deficit(self, p: float, q: float) -> float:
        """Return the explicit two-block symmetry-deficit observable D=(p-q)^2."""
        return (p - q) ** 2

    def symmetry_deficit_center(self) -> float:
        """Return the symmetry deficit at the distinguished symmetric point."""
        return 0.0

    def normalized_symmetry_deficit(self, p: float, q: float) -> float:
        """Return the normalized symmetry deficit D/(p+q)."""
        denom = p + q + 1.0e-12
        return (p - q) ** 2 / denom

    def gradient(self, p: float, q: float, beta: float) -> np.ndarray:
        """Return the analytic gradient of F_beta at (p, q)."""
        p = float(clip_unit_interval(p, self.eps))
        q = float(clip_unit_interval(q, self.eps))
        return np.array(
            [
                -beta * self.J * (p - q) - binary_entropy_prime(p),
                beta * self.J * (p - q) - binary_entropy_prime(q),
            ],
            dtype=float,
        )

    def gradient_array(self, pq: np.ndarray, beta: float) -> np.ndarray:
        """Gradient with packed vector input."""
        return self.gradient(float(pq[0]), float(pq[1]), beta)

    def hessian(self, p: float, q: float, beta: float) -> np.ndarray:
        """Return the analytic Hessian of F_beta at (p, q)."""
        p = float(clip_unit_interval(p, self.eps))
        q = float(clip_unit_interval(q, self.eps))
        return np.array(
            [
                [-beta * self.J - binary_entropy_second(p), beta * self.J],
                [beta * self.J, -beta * self.J - binary_entropy_second(q)],
            ],
            dtype=float,
        )

    def symmetric_point(self) -> tuple[float, float]:
        """Return the distinguished symmetric point of the Landau analysis."""
        return 0.5, 0.5

    def symmetric_hessian_eigenvalues(self, beta: float) -> tuple[float, float]:
        """Return the symmetric/antisymmetric eigenvalues at (1/2, 1/2).

        These coincide with the Chapter 3 local analysis:
        lambda_sym = 4
        lambda_asym = 4 - 2 beta J.
        """
        p, q = self.symmetric_point()
        hess = self.hessian(p, q, beta)
        vec_sym = np.array([1.0, 1.0]) / np.sqrt(2.0)
        vec_asym = np.array([1.0, -1.0]) / np.sqrt(2.0)
        lambda_sym = float(vec_sym @ hess @ vec_sym)
        lambda_asym = float(vec_asym @ hess @ vec_asym)
        return lambda_sym, lambda_asym

    def directional_curvatures(self, p: float, q: float, beta: float) -> tuple[float, float]:
        """Return Hessian quadratic forms in the symmetric/antisymmetric directions."""
        hess = self.hessian(p, q, beta)
        vec_sym = np.array([1.0, 1.0]) / np.sqrt(2.0)
        vec_asym = np.array([1.0, -1.0]) / np.sqrt(2.0)
        return float(vec_sym @ hess @ vec_sym), float(vec_asym @ hess @ vec_asym)

    def minimize(
        self,
        beta: float,
        starts: Iterable[tuple[float, float]] | None = None,
    ) -> dict[str, float]:
        """Compute a numerical minimizer of F_beta on [eps, 1-eps]^2.

        Multiple initial points are used because the model can have symmetry-related
        minima and local critical points.
        """
        if starts is None:
            starts = (
                (0.5, 0.5),
                (0.25, 0.75),
                (0.75, 0.25),
                (0.1, 0.9),
                (0.9, 0.1),
                (0.2, 0.2),
                (0.8, 0.8),
            )

        bounds = [(self.eps, 1.0 - self.eps), (self.eps, 1.0 - self.eps)]
        best = None

        for start in starts:
            result = minimize(
                self.free_energy_array,
                x0=np.array(start, dtype=float),
                args=(beta,),
                method="L-BFGS-B",
                jac=self.gradient_array,
                bounds=bounds,
            )
            if not result.success:
                continue
            if best is None or result.fun < best.fun:
                best = result

        if best is None:
            raise RuntimeError(f"Minimization failed for beta={beta}.")

        p_star, q_star = map(float, best.x)
        if q_star > p_star:
            p_star, q_star = q_star, p_star

        value = self.free_energy(p_star, q_star, beta)
        grad = self.gradient(p_star, q_star, beta)
        hess = self.hessian(p_star, q_star, beta)
        eigvals = np.linalg.eigvalsh(hess)
        dir_sym, dir_asym = self.directional_curvatures(p_star, q_star, beta)

        return {
            "beta": float(beta),
            "p_star": p_star,
            "q_star": q_star,
            "F_star": float(value),
            "Delta": abs(p_star - q_star),
            "symmetry_deficit": self.symmetry_deficit(p_star, q_star),
            "normalized_symmetry_deficit": self.normalized_symmetry_deficit(p_star, q_star),
            "grad_norm": float(np.linalg.norm(grad)),
            "eig_min": float(eigvals[0]),
            "eig_max": float(eigvals[1]),
            "dir_sym_min": dir_sym,
            "dir_asym_min": dir_asym,
        }

    def scan(self, betas: Iterable[float]) -> pd.DataFrame:
        """Scan the model over a list of beta values."""
        rows: list[dict[str, float]] = []
        for beta in betas:
            beta = float(beta)
            row = self.minimize(beta)
            lambda_sym_center, lambda_asym_center = self.symmetric_hessian_eigenvalues(beta)
            row["lambda_sym_center"] = lambda_sym_center
            row["lambda_asym_center"] = lambda_asym_center
            row["beta_c_predicted"] = 2.0 / self.J
            rows.append(row)
        return pd.DataFrame(rows)
