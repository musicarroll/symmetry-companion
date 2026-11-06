"""Finite block-relational models with variance-based symmetry deficit.

This module provides the first non-toy finite relational system used to test
symmetry deficit beyond the mean-field scalar setting. For equal-size blocks, the probability matrix preserves all block-label
permutations for both ``p = q`` and ``p != q``. Its entry variance measures
within/cross contrast, not loss of block-label symmetry or graph automorphisms.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from block_relational_model import BlockRelationalModel
from two_block_model import binary_entropy


def equal_block_sizes(n: int, k: int) -> tuple[int, ...]:
    """Split ``n`` nodes into ``k`` blocks as evenly as possible."""
    base = n // k
    remainder = n % k
    return tuple(base + (1 if i < remainder else 0) for i in range(k))


def probability_matrix(k: int, p: float, q: float) -> np.ndarray:
    """Return the symmetric ``k``-block probability matrix."""
    mat = np.full((k, k), q, dtype=float)
    np.fill_diagonal(mat, p)
    return np.clip(mat, 1.0e-6, 1.0 - 1.0e-6)


def generate_block_graph(
    n: int,
    k: int,
    p: float,
    q: float,
    rng: np.random.Generator,
) -> np.ndarray:
    """Generate one undirected block-relational graph realization."""
    model = BlockRelationalModel(
        block_sizes=equal_block_sizes(n, k),
        edge_probs=probability_matrix(k, p, q),
    )
    return model.sample_adjacency(rng)


@dataclass(frozen=True)
class FiniteBlockModel:
    """Finite ``k``-block relational model with permutation symmetry."""

    n: int
    k: int
    p: float
    q: float

    @property
    def block_assignment(self) -> np.ndarray:
        """Return the block label of each node."""
        labels: list[int] = []
        for block, size in enumerate(self.block_sizes):
            labels.extend([block] * size)
        return np.asarray(labels, dtype=int)

    @property
    def num_within_slots(self) -> int:
        """Return the number of potential within-block edges."""
        sizes = self.block_sizes
        return int(sum(size * (size - 1) // 2 for size in sizes))

    @property
    def block_sizes(self) -> tuple[int, ...]:
        """Equal-size block partition used by the model."""
        return equal_block_sizes(self.n, self.k)

    @property
    def block_model(self) -> BlockRelationalModel:
        """Underlying block-relational sampling model."""
        return BlockRelationalModel(
            block_sizes=self.block_sizes,
            edge_probs=probability_matrix(self.k, self.p, self.q),
        )

    def sample(self, rng: np.random.Generator) -> np.ndarray:
        """Sample one adjacency matrix."""
        return self.block_model.sample_adjacency(rng)

    def random_graph(self, rng: np.random.Generator, edge_prob: float = 0.5) -> np.ndarray:
        """Return an undirected random initial graph for Monte Carlo runs."""
        upper = (rng.random((self.n, self.n)) < edge_prob).astype(np.uint8)
        upper = np.triu(upper, k=1)
        adj = upper + upper.T
        return adj.astype(np.uint8)

    def block_density_matrix(self, adj: np.ndarray) -> np.ndarray:
        """Return the empirical block-density matrix."""
        return self.block_model.empirical_block_densities(adj)

    def symmetry_deficit(self, rho: np.ndarray) -> float:
        """Return the variance-based symmetry deficit of the density matrix."""
        global_mean = float(rho.mean())
        return float(np.mean((rho - global_mean) ** 2))

    def entropy_density(self, rho: np.ndarray) -> float:
        """Return an entropy-like density from the empirical block matrix."""
        return float(np.mean(binary_entropy(rho)))

    def degree_statistics(self, adj: np.ndarray) -> dict[str, float]:
        """Return degree-distribution statistics."""
        return self.block_model.degree_statistics(adj)

    def within_edge_count(self, adj: np.ndarray) -> int:
        """Return the number of within-block edges."""
        assignment = self.block_assignment
        total = 0
        for i in range(self.n):
            same = assignment[i + 1 :] == assignment[i]
            if same.any():
                total += int(adj[i, i + 1 :][same].sum())
        return total

    def energy(self, adj: np.ndarray, lambda_control: float) -> float:
        """Return the block-favoring Hamiltonian E = -lambda * N_within."""
        return -float(lambda_control) * float(self.within_edge_count(adj))

    def delta_energy_for_flip(self, adj: np.ndarray, i: int, j: int, lambda_control: float) -> float:
        """Return the energy change for flipping one edge."""
        if self.block_assignment[i] != self.block_assignment[j]:
            return 0.0
        delta_edge = 1.0 if adj[i, j] == 0 else -1.0
        return -float(lambda_control) * delta_edge

    def metropolis_step(
        self,
        adj: np.ndarray,
        lambda_control: float,
        rng: np.random.Generator,
    ) -> bool:
        """Attempt one Metropolis edge flip."""
        i = int(rng.integers(0, self.n - 1))
        j = int(rng.integers(i + 1, self.n))
        delta_e = self.delta_energy_for_flip(adj, i, j, lambda_control)
        if delta_e <= 0.0 or rng.random() < np.exp(-delta_e):
            new_value = np.uint8(1 - adj[i, j])
            adj[i, j] = new_value
            adj[j, i] = new_value
            return True
        return False

    def monte_carlo_observables(
        self,
        lambda_control: float,
        rng: np.random.Generator,
        burn_in_steps: int,
        sample_steps: int,
        sample_every: int,
        initial_edge_prob: float = 0.5,
    ) -> tuple[list[dict[str, float]], float]:
        """Run a Metropolis chain and return sampled observables and acceptance rate."""
        adj = self.random_graph(rng, edge_prob=initial_edge_prob)
        accepted = 0
        total_steps = burn_in_steps + sample_steps
        rows: list[dict[str, float]] = []

        for step in range(total_steps):
            accepted += int(self.metropolis_step(adj, lambda_control, rng))
            if step >= burn_in_steps and ((step - burn_in_steps) % sample_every == 0):
                obs = self.observables(adj)
                obs.update(
                    {
                        "lambda_control": float(lambda_control),
                        "energy": self.energy(adj, lambda_control),
                        "mc_step": float(step),
                    }
                )
                rows.append(obs)

        acceptance_rate = accepted / float(total_steps) if total_steps > 0 else 0.0
        return rows, float(acceptance_rate)

    def observables(self, adj: np.ndarray) -> dict[str, float]:
        """Collect observables for one finite relational realization."""
        rho = self.block_density_matrix(adj)
        block_stats = self.block_model.block_metrics(rho)
        degree_stats = self.degree_statistics(adj)
        return {
            "n": float(self.n),
            "num_blocks": float(self.k),
            "p": float(self.p),
            "q": float(self.q),
            "lambda_control": float(self.p - self.q),
            "symmetry_deficit": self.symmetry_deficit(rho),
            "entropy_density": self.entropy_density(rho),
            "rho_global_mean": float(rho.mean()),
            **block_stats,
            **degree_stats,
        }
