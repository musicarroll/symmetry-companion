# First public GitHub push

The local repository has fresh history and is separate from the private book.
No remote is configured by the repository split.

1. On GitHub, create `musicarroll/symmetry-companion` with **Public** visibility.
   Leave README, `.gitignore`, and license initialization unchecked so the new
   remote is empty. If you choose another name, adjust the URL below.
2. From this directory, connect the existing local repository and push:

   ```bash
   git remote add origin git@github.com:musicarroll/symmetry-companion.git
   git remote -v
   git push -u origin main
   ```

   The existing `github-symmetry` SSH host alias can be used instead of
   `github.com` if that is the key configured for your GitHub account.
3. Confirm the GitHub page is public and the Lean workflow passes. The workflow
   validates the exported statement inventory; it has no private manuscript
   credentials or dependency.

Keep `symmetry-monograph` private with its existing remote and history. Commit
and push its file removals and coordination documentation separately through
the usual private workflow.

See [GitHub's instructions for adding locally hosted code](https://docs.github.com/en/migrations/importing-source-code/using-the-command-line-to-import-source-code/adding-locally-hosted-code-to-github).
