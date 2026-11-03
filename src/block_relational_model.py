"""Finite-size random block-relational models and coarse symmetry diagnostics.

This module extends the initial two-block / Landau numerics to larger random
relational graphs with configurable block structure and configurable symmetry
groups acting on the block labels.

The primary observable is a coarse-grained symmetry deficit computed from the
empirical block-density matrix relative to a chosen block symmetry group.
Entropy, degree statistics, and block metrics are logged as comparison
quantities.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations
from math import log
from typing import Iterable, Sequence

import numpy as np

from two_block_model import binary_entropy


def symmetric_group_permutations(k: int) -> list[tuple[int, ...]]:
    """Return the full symmetric group on ``k`` symbols as permutation tuples."""
    return [tuple(p) for p in permutations(range(k))]


def permutation_matrix(perm: Sequence[int]) -> np.ndarray:
    """Return the permutation matrix for ``perm``."""
    k = len(perm)
    mat = np.zeros((k, k), dtype=float)
    for i, j in enumerate(perm):
        mat[i, j] = 1.0
    return mat


def block_slot_matrix(block_sizes: Sequence[int]) -> np.ndarray:
    """Return the number of undirected simple-graph slots in each block sector."""
    sizes = np.asarray(block_sizes, dtype=int)
    k = len(sizes)
    slots = np.zeros((k, k), dtype=float)
    for a in range(k):
        for b in range(k):
            if a == b:
                slots[a, b] = sizes[a] * (sizes[a] - 1) / 2.0
            elif a < b:
                slots[a, b] = sizes[a] * sizes[b]
                slots[b, a] = slots[a, b]
    return slots


@dataclass(frozen=True)
class BlockRelationalModel:
    """Undirected multi-block random relational graph model."""

    block_sizes: tuple[int, ...]
    edge_probs: np.ndarray

    def __post_init__(self) -> None:
        probs = np.asarray(self.edge_probs, dtype=float)
        k = len(self.block_sizes)
        if probs.shape != (k, k):
            raise ValueError("edge_probs must be a square matrix matching block_sizes.")
        if not np.allclose(probs, probs.T):
            raise ValueError("edge_probs must be symmetric for the undirected model.")
        if np.any(probs < 0.0) or np.any(probs > 1.0):
            raise ValueError("edge probabilities must lie in [0, 1].")
        object.__setattr__(self, "edge_probs", probs)

    @property
    def n(self) -> int:
        """Total number of nodes."""
        return int(sum(self.block_sizes))

    @property
    def k(self) -> int:
        """Number of blocks."""
        return len(self.block_sizes)

    @property
    def slices(self) -> list[slice]:
        """Block slices inside the adjacency matrix."""
        offsets = np.cumsum((0,) + self.block_sizes)
        return [slice(int(offsets[i]), int(offsets[i + 1])) for i in range(self.k)]

    def sample_adjacency(self, rng: np.random.Generator) -> np.ndarray:
        """Sample an undirected adjacency matrix with zero diagonal."""
        adj = np.zeros((self.n, self.n), dtype=np.uint8)
        block_slices = self.slices
        for a in range(self.k):
            sa = block_slices[a]
            na = self.block_sizes[a]

            # Diagonal block: upper triangle only.
            p_aa = self.edge_probs[a, a]
            block = rng.random((na, na)) < p_aa
            block = np.triu(block, k=1)
            adj[sa, sa] = block.astype(np.uint8)
            adj[sa, sa] += block.T.astype(np.uint8)

            # Off-diagonal blocks.
            for b in range(a + 1, self.k):
                sb = block_slices[b]
                nb = self.block_sizes[b]
                p_ab = self.edge_probs[a, b]
                block_ab = (rng.random((na, nb)) < p_ab).astype(np.uint8)
                adj[sa, sb] = block_ab
                adj[sb, sa] = block_ab.T
        return adj

    def empirical_block_densities(self, adj: np.ndarray) -> np.ndarray:
        """Return the empirical symmetric block-density matrix."""
        block_slices = self.slices
        slots = block_slot_matrix(self.block_sizes)
        rho = np.zeros((self.k, self.k), dtype=float)
        for a in range(self.k):
            sa = block_slices[a]
            block = adj[sa, sa]
            rho[a, a] = block.sum() / 2.0 / slots[a, a] if slots[a, a] > 0 else 0.0
            for b in range(a + 1, self.k):
                sb = block_slices[b]
                count = adj[sa, sb].sum()
                rho[a, b] = count / slots[a, b]
                rho[b, a] = rho[a, b]
        return rho

    def degree_statistics(self, adj: np.ndarray) -> dict[str, float]:
        """Return simple degree-distribution statistics."""
        degrees = adj.sum(axis=1).astype(float)
        return {
            "degree_mean": float(degrees.mean()),
            "degree_std": float(degrees.std(ddof=0)),
            "degree_min": float(degrees.min()),
            "degree_max": float(degrees.max()),
        }

    def block_metrics(self, rho: np.ndarray) -> dict[str, float]:
        """Return coarse within/cross-block diagnostics."""
        diag = np.diag(rho)
        offdiag = rho[~np.eye(self.k, dtype=bool)]
        within_mean = float(diag.mean()) if diag.size else 0.0
        cross_mean = float(offdiag.mean()) if offdiag.size else 0.0
        return {
            "within_density_mean": within_mean,
            "cross_density_mean": cross_mean,
            "block_contrast": within_mean - cross_mean,
            "block_density_std": float(rho.std(ddof=0)),
        }

    def entropy_density(self, rho: np.ndarray) -> float:
        """Return a coarse block-entropy density based on empirical densities."""
        slots = block_slot_matrix(self.block_sizes)
        total = float(self.n**2)
        entropy = 0.0
        for a in range(self.k):
            entropy += slots[a, a] * float(binary_entropy(rho[a, a]))
            for b in range(a + 1, self.k):
                entropy += slots[a, b] * float(binary_entropy(rho[a, b]))
        return entropy / total


def stabilizer_size(
    rho: np.ndarray,
    group: Iterable[Sequence[int]],
    tolerance: float,
) -> int:
    """Return the size of the block-group stabilizer of ``rho``."""
    count = 0
    for perm in group:
        perm = tuple(perm)
        pmat = permutation_matrix(perm)
        permuted = pmat @ rho @ pmat.T
        if np.max(np.abs(permuted - rho)) <= tolerance:
            count += 1
    return count


def coarse_symmetry_deficit(
    rho: np.ndarray,
    group: Iterable[Sequence[int]],
    tolerance: float,
) -> float:
    """Return the coarse block symmetry deficit log(|G| / |Stab_G(rho)|)."""
    group_list = [tuple(g) for g in group]
    stab = stabilizer_size(rho, group_list, tolerance=tolerance)
    if stab <= 0:
        stab = 1
    return float(log(len(group_list) / stab))


def block_observables(
    adj: np.ndarray,
    model: BlockRelationalModel,
    group: Iterable[Sequence[int]],
    tolerance: float,
) -> dict[str, float]:
    """Collect the main observables for one sampled graph."""
    rho = model.empirical_block_densities(adj)
    block_stats = model.block_metrics(rho)
    degree_stats = model.degree_statistics(adj)
    return {
        "n": float(model.n),
        "num_blocks": float(model.k),
        "symmetry_deficit": coarse_symmetry_deficit(rho, group, tolerance=tolerance),
        "entropy_density": model.entropy_density(rho),
        "stabilizer_size": float(stabilizer_size(rho, group, tolerance=tolerance)),
        "rho_trace": float(np.trace(rho)),
        **block_stats,
        **degree_stats,
    }
