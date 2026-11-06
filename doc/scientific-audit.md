# Scientific audit — 6 November 2026

Companion 0.1.3 clarifies evidence scope without replacing historical raw data.

- Mean-field-guided graphs use fitted branch probabilities as inputs.
- The p/q matrix is invariant under simultaneous equal-block permutations even
  when its entry variance is positive. Variance is a structural proxy.
- Approximately preserving permutations need not be a subgroup.
- The edge Hamiltonian is exactly independent: Z=(1+exp(lambda))^M_w*2^M_c.
  No collective finite-coupling transition occurs. The archived N=360 run has
  15000 proposals for 64620 slots; mixing has not been established.
- The q=2 Potts energy uses Ising coupling J/2. Its critical beta*J is
  log(1+sqrt(2)) ~=0.881374. The archived grid skips from 0.5 to 1.0 and retains
  only twenty configurations per point. Critical scaling is unresolved.
- Raw Var(D) slopes are not magnetic gamma/nu. Legacy keys remain for data
  compatibility, but the summary generator no longer infers universality.
- Plot labels and slides now distinguish structural proxies and raw variances.

`tests/test_scientific_audit.py` contains seven independent enumeration,
energy/partition-function, counterexample, and scalar-root checks. Combined
with the ten pre-existing tests: 17 passing tests. The near-threshold numerical
contrast agrees with a scalar-root benchmark to 1e-4, not certified six-digit
accuracy (observed error about 4.8e-5 at beta=2.005).

Lean builds successfully and the ledger/axiom check passes: 57 numbered entries,
68 total, with 46 numbered entries complete within their declared scopes. The
external preprint statement was checked against its source, not independently
proved or assumed as a Lean axiom. No proof status was upgraded.

The raw CSV records are unchanged. Human specialist review, long-proof review,
and adequately equilibrated critical simulations remain separate tasks.
