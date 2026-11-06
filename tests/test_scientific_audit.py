"""Independent small-system and analytic checks added by the November audit."""
import itertools
import json
import math
from pathlib import Path
import sys
import unittest
from collections import Counter

import numpy as np
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from block_relational_model import stabilizer_size, symmetric_group_permutations
from finite_block_model import FiniteBlockModel, probability_matrix
from lattice_potts_model import LatticePottsModel
from two_block_model import TwoBlockModel


class ScientificAudit(unittest.TestCase):
    def test_all_three_point_binary_relations(self):
        perms = list(itertools.permutations(range(3)))
        classes = {}
        for mask in range(512):
            relation = {(i, j) for i in range(3) for j in range(3)
                        if mask & (1 << (3*i+j))}
            orbit = {sum(1 << (3*p[i]+p[j]) for i, j in relation) for p in perms}
            classes[min(orbit)] = 6 // len(orbit)
        self.assertEqual(Counter(classes.values()), {6: 4, 3: 2, 2: 28, 1: 70})

    def test_exhaustive_operation_counts_against_recorded_data(self):
        records = json.loads((ROOT/'results/data/finite_algebraic_operation_summary.json').read_text())
        for n in (2, 3):
            perms = list(itertools.permutations(range(n)))
            autos, properties = Counter(), Counter()
            for t in itertools.product(range(n), repeat=n*n):
                def op(a, b): return t[n*a+b]
                aut = sum(all(p[op(a,b)] == op(p[a],p[b])
                              for a in range(n) for b in range(n)) for p in perms)
                autos[aut] += 1
                assoc = all(op(op(a,b),c) == op(a,op(b,c))
                            for a,b,c in itertools.product(range(n), repeat=3))
                comm = all(op(a,b) == op(b,a) for a in range(n) for b in range(n))
                units = [e for e in range(n) if all(op(e,a)==a and op(a,e)==a for a in range(n))]
                group = assoc and any(all(any(op(a,b)==e and op(b,a)==e for b in range(n))
                                         for a in range(n)) for e in units)
                for key, val in [('associative',assoc),('commutative',comm),
                                 ('has_identity',bool(units)),('is_group',group),('rigid',aut==1)]:
                    properties[key] += int(val)
            record = next(r for r in records if r['n']==n)
            self.assertEqual(dict(autos), {int(k): v for k,v in record['aut_distribution'].items()})
            self.assertEqual(dict(properties), record['property_counts'])

    def test_edge_model_partition_function_and_flip_energy(self):
        model = FiniteBlockModel(n=4, k=2, p=.7, q=.5)
        edges = list(itertools.combinations(range(4), 2))
        for lam in (0., .8, 4.):
            total, weighted_within = 0., 0.
            for bits in itertools.product((0,1), repeat=len(edges)):
                adj = np.zeros((4,4), dtype=np.uint8)
                for (i,j),bit in zip(edges,bits): adj[i,j] = adj[j,i] = bit
                w = math.exp(-model.energy(adj,lam));total += w
                weighted_within += w * (adj[0,1] + int(adj[2,3]))
                for i,j in edges:
                    flipped = adj.copy();flipped[i,j] = flipped[j,i] = 1-adj[i,j]
                    self.assertAlmostEqual(model.delta_energy_for_flip(adj,i,j,lam),
                                           model.energy(flipped,lam)-model.energy(adj,lam))
            self.assertAlmostEqual(total, (1+math.exp(lam))**2 * 2**4, places=7)
            self.assertAlmostEqual(weighted_within/total, 2/(1+math.exp(-lam)))

    def test_potts_ising_convention_and_local_energy(self):
        model = LatticePottsModel(L=3, q=2)
        for bits in itertools.product((0,1), repeat=9):
            spins = np.array(bits);sigma = (2*spins-1).reshape(3,3)
            bonds = np.sum(sigma*np.roll(sigma,1,axis=0)+sigma*np.roll(sigma,1,axis=1))
            self.assertEqual(model.energy(spins), -9.-.5*bonds)
            m = float(np.mean(sigma))
            self.assertAlmostEqual(model.symmetry_deficit(spins), m*m/4)
            for i in range(9):
                changed = spins.copy();changed[i] = 1-spins[i]
                self.assertEqual(model.delta_energy_for_flip(spins,i,int(changed[i])),
                                 model.energy(changed)-model.energy(spins))

    def test_matrix_contrast_does_not_break_block_permutations(self):
        rho = probability_matrix(3,.8,.2)
        group = symmetric_group_permutations(3)
        self.assertEqual(stabilizer_size(rho,group,0),6)
        self.assertGreater(FiniteBlockModel(6,3,.8,.2).symmetry_deficit(rho),0)

    def test_approximate_preservers_need_not_be_subgroup(self):
        rho = np.diag([0.,.1,.2])
        # (01) and (12) pass, but their composition does not.
        group = symmetric_group_permutations(3)
        self.assertEqual(stabilizer_size(rho,group,.11),3)
        self.assertEqual(stabilizer_size(rho,[(1,0,2)],.11),1)
        self.assertEqual(stabilizer_size(rho,[(0,2,1)],.11),1)
        self.assertEqual(stabilizer_size(rho,[(1,2,0)],.11),0)

    def test_refined_minimizer_against_scalar_exact_equation(self):
        model = TwoBlockModel(J=1.)
        for beta in (1.5,2.005,2.025,2.5,3.):
            m = 0. if beta<=2 else brentq(lambda x: math.atanh(x)-beta*x/2,1e-7,1-1e-12)
            # Default L-BFGS-B is less accurate near the flat bifurcation.
            # This checks 1e-4 absolute contrast accuracy, not six digits.
            result = model.minimize(beta)
            self.assertAlmostEqual(abs(result['p_star']-result['q_star']),m,delta=1e-4)

if __name__ == '__main__': unittest.main()
