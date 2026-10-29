# Agent guidelines

## Code health

Family-wide rules live in the
[wazootech workspace constitution](https://github.com/wazootech/workspace/blob/main/AGENTS.md#code-health-standards);
this repo's specifics:

- Before pushing, run `deno task ci` (fmt, lint, check, test); CI runs it on
  every pull request and push to `main`.
- `deno lint` enforces `no-explicit-any` and `ban-ts-comment` (no `@ts-ignore`),
  and `deno.json` sets `strict: true`.
- `secret-scan.yml` runs gitleaks on every pull request and push to `main`;
  never commit credentials.
- Workflow actions are pinned to full commit SHAs with a version comment, Deno
  is pinned to `v2.9.8`, and CI installs with `deno install --frozen`, so commit
  any `deno.lock` change.
- `code-health.yml` only warns: files over 120 lines of code (300 for tests) and
  `TODO`/`FIXME` without an issue link. There are no exclusions.
- `.github/CODEOWNERS` routes review to the repo owner.
