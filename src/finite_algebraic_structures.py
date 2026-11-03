"""Finite algebraic structure utilities.

This module enumerates binary operations on small finite sets and computes
basic algebraic and symmetry diagnostics.  It is intentionally elementary:
the point is to make the orbit-stabilizer statements in Chapter 4 directly
checkable for small operation tables.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations, product
from math import factorial, log
from typing import Dict, Iterable, List, Sequence, Tuple

Operation = Tuple[int, ...]
Permutation = Tuple[int, ...]


@dataclass(frozen=True)
class OperationDiagnostics:
    n: int
    aut_size: int
    multiplicity: int
    symmetry_deficit: float
    associative: bool
    commutative: bool
    has_identity: bool
    is_group: bool


def index(n: int, a: int, b: int) -> int:
    return a * n + b


def value(op: Operation, n: int, a: int, b: int) -> int:
    return op[index(n, a, b)]


def all_operations(n: int) -> Iterable[Operation]:
    return product(range(n), repeat=n * n)


def all_permutations(n: int) -> List[Permutation]:
    return list(permutations(range(n)))


def preserves_operation(op: Operation, n: int, perm: Permutation) -> bool:
    for a in range(n):
        for b in range(n):
            left = perm[value(op, n, a, b)]
            right = value(op, n, perm[a], perm[b])
            if left != right:
                return False
    return True


def automorphisms(op: Operation, n: int) -> List[Permutation]:
    return [perm for perm in all_permutations(n) if preserves_operation(op, n, perm)]


def is_associative(op: Operation, n: int) -> bool:
    for a in range(n):
        for b in range(n):
            for c in range(n):
                if value(op, n, value(op, n, a, b), c) != value(op, n, a, value(op, n, b, c)):
                    return False
    return True


def is_commutative(op: Operation, n: int) -> bool:
    for a in range(n):
        for b in range(n):
            if value(op, n, a, b) != value(op, n, b, a):
                return False
    return True


def identity_element(op: Operation, n: int) -> int | None:
    for e in range(n):
        ok = True
        for a in range(n):
            if value(op, n, e, a) != a or value(op, n, a, e) != a:
                ok = False
                break
        if ok:
            return e
    return None


def has_inverses(op: Operation, n: int, identity: int) -> bool:
    for a in range(n):
        found = False
        for b in range(n):
            if value(op, n, a, b) == identity and value(op, n, b, a) == identity:
                found = True
                break
        if not found:
            return False
    return True


def is_group(op: Operation, n: int) -> bool:
    e = identity_element(op, n)
    return e is not None and is_associative(op, n) and has_inverses(op, n, e)


def diagnose_operation(op: Operation, n: int) -> OperationDiagnostics:
    aut_size = len(automorphisms(op, n))
    multiplicity = factorial(n) // aut_size
    return OperationDiagnostics(
        n=n,
        aut_size=aut_size,
        multiplicity=multiplicity,
        symmetry_deficit=log(multiplicity),
        associative=is_associative(op, n),
        commutative=is_commutative(op, n),
        has_identity=identity_element(op, n) is not None,
        is_group=is_group(op, n),
    )


def summarize_operations(n: int) -> Dict[str, object]:
    total = 0
    aut_distribution: Dict[int, int] = {}
    multiplicity_distribution: Dict[int, int] = {}
    property_counts = {
        "associative": 0,
        "commutative": 0,
        "has_identity": 0,
        "is_group": 0,
        "rigid": 0,
    }

    for op in all_operations(n):
        total += 1
        diag = diagnose_operation(tuple(op), n)
        aut_distribution[diag.aut_size] = aut_distribution.get(diag.aut_size, 0) + 1
        multiplicity_distribution[diag.multiplicity] = (
            multiplicity_distribution.get(diag.multiplicity, 0) + 1
        )
        if diag.associative:
            property_counts["associative"] += 1
        if diag.commutative:
            property_counts["commutative"] += 1
        if diag.has_identity:
            property_counts["has_identity"] += 1
        if diag.is_group:
            property_counts["is_group"] += 1
        if diag.aut_size == 1:
            property_counts["rigid"] += 1

    return {
        "n": n,
        "total_operations": total,
        "aut_distribution": dict(sorted(aut_distribution.items())),
        "multiplicity_distribution": dict(sorted(multiplicity_distribution.items())),
        "property_counts": property_counts,
    }


def cyclic_group_operation(n: int) -> Operation:
    return tuple((a + b) % n for a in range(n) for b in range(n))
