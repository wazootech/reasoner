# Agent guidelines

## Code health

Family-wide rules live in the
[wazootech workspace constitution](https://github.com/wazootech/workspace/blob/main/AGENTS.md#code-health-standards);
this repo's specifics:

- Set up with `bun install`. Before pushing, run `bun run ci` (format, lint,
  type check, manifest check, tests); CI runs it on every pull request and push
  to `main`. Bun 1.4.5 or newer.
- Oxlint enforces `no-explicit-any` and `ban-ts-comment` (no `@ts-ignore`), and
  `tsconfig.json` sets `strict: true`.
- `secret-scan.yml` runs gitleaks on every pull request and push to `main`;
  never commit credentials.
- Workflow actions are pinned to full commit SHAs with a version comment, Bun
  floats on `1.x`, and CI installs with `--frozen-lockfile`, so commit any
  `bun.lock` change.
- `jsr.json` describes the published package and `package.json` the toolchain;
  `bun run check:manifests` fails when they disagree.
- `code-health.yml` only warns: files over 120 lines of code (300 for tests) and
  `TODO`/`FIXME` without an issue link. There are no exclusions.
- `.github/CODEOWNERS` routes review to the repo owner.
