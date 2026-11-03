"""Two-dimensional lattice Potts model with symmetry-deficit diagnostics.

This module adds a spatially local statistical-mechanical model to the
computational program. Spins live on an ``L x L`` periodic square lattice,
nearest-neighbor interactions favor aligned states, and the primary observable
is a symmetry deficit measuring deviation from the permutation-invariant state
distribution.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property

import numpy as np


@dataclass(frozen=True)
class LatticePottsModel:
    """Periodic two-dimensional Potts model."""

    L: int
    q: int
    J: float = 1.0

    def __post_init__(self) -> None:
        if self.L <= 1:
            raise ValueError("L must be at least 2.")
        if self.q <= 1:
            raise ValueError("q must be at least 2.")
        if self.J <= 0.0:
            raise ValueError("J must be positive.")

    @property
    def n(self) -> int:
        """Total number of sites."""
        return self.L * self.L

    @cached_property
    def neighbors(self) -> np.ndarray:
        """Nearest-neighbor table with periodic boundary conditions."""
        nbrs = np.zeros((self.n, 4), dtype=np.int32)
        for row in range(self.L):
            for col in range(self.L):
                idx = row * self.L + col
                nbrs[idx, 0] = row * self.L + ((col + 1) % self.L)
                nbrs[idx, 1] = row * self.L + ((col - 1) % self.L)
                nbrs[idx, 2] = ((row + 1) % self.L) * self.L + col
                nbrs[idx, 3] = ((row - 1) % self.L) * self.L + col
        return nbrs

    def random_spins(self, rng: np.random.Generator) -> np.ndarray:
        """Return a random spin configuration with values in ``{0, ..., q-1}``."""
        return rng.integers(0, self.q, size=self.n, dtype=np.int16)

    def state_fractions(self, spins: np.ndarray) -> np.ndarray:
        """Return the empirical fraction of sites in each state."""
        counts = np.bincount(spins, minlength=self.q).astype(float)
        return counts / float(self.n)

    def symmetry_deficit(self, spins: np.ndarray) -> float:
        """Return the variance of the state fractions about ``1/q``."""
        fractions = self.state_fractions(spins)
        target = 1.0 / float(self.q)
        return float(np.mean((fractions - target) ** 2))

    def energy(self, spins: np.ndarray) -> float:
        """Return the total Potts energy."""
        grid = spins.reshape(self.L, self.L)
        aligned_right = (grid == np.roll(grid, shift=-1, axis=1)).sum()
        aligned_down = (grid == np.roll(grid, shift=-1, axis=0)).sum()
        return -self.J * float(aligned_right + aligned_down)

    def delta_energy_for_flip(self, spins: np.ndarray, idx: int, new_state: int) -> float:
        """Return the local energy change for a single-site proposal."""
        old_state = int(spins[idx])
        if new_state == old_state:
            return 0.0
        nbr_states = spins[self.neighbors[idx]]
        old_matches = int(np.count_nonzero(nbr_states == old_state))
        new_matches = int(np.count_nonzero(nbr_states == new_state))
        return -self.J * float(new_matches - old_matches)

    def metropolis_step(
        self,
        spins: np.ndarray,
        beta: float,
        rng: np.random.Generator,
    ) -> bool:
        """Attempt one Metropolis single-site update."""
        idx = int(rng.integers(0, self.n))
        old_state = int(spins[idx])
        proposal = int(rng.integers(0, self.q - 1))
        if proposal >= old_state:
            proposal += 1
        delta_e = self.delta_energy_for_flip(spins, idx, proposal)
        if delta_e <= 0.0 or rng.random() < np.exp(-beta * delta_e):
            spins[idx] = proposal
            return True
        return False

    def sweep(self, spins: np.ndarray, beta: float, rng: np.random.Generator) -> float:
        """Perform one Monte Carlo sweep and return the acceptance rate."""
        accepted = 0
        for _ in range(self.n):
            accepted += int(self.metropolis_step(spins, beta, rng))
        return accepted / float(self.n)

    def observables(self, spins: np.ndarray) -> dict[str, float]:
        """Return observables for one Potts configuration."""
        fractions = self.state_fractions(spins)
        energy_total = self.energy(spins)
        return {
            "L": float(self.L),
            "N": float(self.n),
            "q": float(self.q),
            "symmetry_deficit": self.symmetry_deficit(spins),
            "energy_per_site": energy_total / float(self.n),
            **{f"state_fraction_{state}": float(frac) for state, frac in enumerate(fractions)},
        }

    def monte_carlo_observables(
        self,
        beta: float,
        rng: np.random.Generator,
        burn_in_sweeps: int,
        measurement_sweeps: int,
        sample_every_sweeps: int,
        initial_spins: np.ndarray | None = None,
    ) -> tuple[list[dict[str, float]], float, np.ndarray]:
        """Run a Metropolis chain and return sampled observables."""
        spins = self.random_spins(rng) if initial_spins is None else np.array(initial_spins, copy=True)
        acceptance_rates: list[float] = []
        rows: list[dict[str, float]] = []

        for _ in range(burn_in_sweeps):
            acceptance_rates.append(self.sweep(spins, beta, rng))

        for sweep_idx in range(measurement_sweeps):
            acceptance_rates.append(self.sweep(spins, beta, rng))
            if sweep_idx % sample_every_sweeps == 0:
                obs = self.observables(spins)
                obs.update(
                    {
                        "beta": float(beta),
                        "mc_sweep": float(sweep_idx),
                    }
                )
                rows.append(obs)

        acceptance_rate = float(np.mean(acceptance_rates)) if acceptance_rates else 0.0
        return rows, acceptance_rate, spins.copy()
