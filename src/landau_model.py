"""Landau approximation for the refined two-block model near the critical point."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class LandauModel:
    """Quartic Landau model from Chapter 3, Section 3.5."""

    J: float = 1.0

    def beta_c(self) -> float:
        """Return the predicted critical inverse temperature."""
        return 2.0 / self.J

    def A(self, beta: float) -> float:
        """Quadratic coefficient A(beta) = 4 - 2 beta J."""
        return 4.0 - 2.0 * beta * self.J

    def B(self) -> float:
        """Quartic coefficient at the symmetric point."""
        return 8.0 / 3.0

    def effective_free_energy(self, d: float, beta: float) -> float:
        """Quartic Landau effective free energy in the block-contrast variable."""
        return self.A(beta) * d**2 + self.B() * d**4

    def predicted_d_star(self, beta: float) -> float:
        """Return the positive nonzero minimizer predicted by the Landau theory."""
        if beta <= self.beta_c():
            return 0.0
        return float(np.sqrt((3.0 / 8.0) * (beta * self.J - 2.0)))
