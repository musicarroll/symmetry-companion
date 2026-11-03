# Companion repository rules

This repository contains the public Python experiments, Lean formalization,
numerical artifacts, and slides. The private AMS manuscript is normally checked
out beside it as `../symmetry-monograph`; it is optional for standalone builds.

- Keep manuscript chapters, cover artwork, manuscript PDF, and private session
  notes in the private repository. Do not copy its Git history here.
- Follow `SYNC.md` when changing mathematical claims, numerical results,
  bibliography, summaries, or proof status. Review both repositories when they
  are available and record any work that requires the private checkout.
- Run `lake build` for Lean changes, then the coverage checker. Use `--book PATH`
  for a live manuscript comparison; standalone CI validates the exported inventory.
- Keep statement labels stable and preserve the ledger's explicit proof scopes.
- Update affected slides and `slides/SOURCE_MAP.md` before refreshing snapshots.
  Never refresh a snapshot solely to silence a failed synchronization check.
- Public slide builds must work without any private checkout or absolute paths.
- Treat `references.bib` as an exported copy of the private book bibliography
  when coordinating the pair. Numerical results and figures originate here.
- Run the synchronization tests when changing repository coordination tools.
- Do not publish to GitHub unless the user requests it.
