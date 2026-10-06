# Public build receipt

Date: 2026-10-06 (Asia/Tokyo)

## Result

```text
FRESH PROJECT-LOCAL BUILD: PASS
FINAL NORMAL LAKE BUILD: PASS (8850 jobs)
MAIN-ONLY PUBLIC API TEST: PASS
```

The build was performed in the isolated public staging tree at
`C:\LeanProjects\NS-P23-Lean_BUILD\public`. The authoritative workspace
`C:\LeanProjects\Problem23Lean` and the pre-existing
`C:\LeanProjects\NS-P23-Lean` tree were not used as build-output locations.

The public staging tree had no project-local `.lake/build` directory when the
fresh build began. Only the frozen dependency package cache was copied into
`.lake/packages`; all project build output was produced locally from an empty
project build directory.

## Pinned environment

```text
Lean: 4.34.0-rc1
Lean commit: 3447a668783dbce1a8fdb97101dd067687b2b418
Lake: 5.0.0-src+3447a66
mathlib: v4.34.0-rc1
mathlib commit: de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
Lake configuration: lakefile.toml
```

## Build execution

The initial default-concurrency `lake build` and two resumptions were
terminated by the native launcher with exit code `-1` under peak memory
pressure. They emitted no Lean error, fatal error, or panic. The remaining
modules were then completed in dependency order with single-module Lake
targets. A final ordinary `lake build` over the completed fresh project-local
output passed:

```text
start: 2026-10-06T02:23:10.0398251+09:00
end: 2026-10-06T02:23:16.0024890+09:00
elapsed: 5.963 seconds
result: Build completed successfully (8850 jobs).
exit code: 0
```

This staged process compiled the project from fresh local output; the final
ordinary build is the release gate recorded above.

## Source and API coverage

```text
production Lean files: 143
P23/**/*.lean modules: 142
root P23.lean files: 1
```

`Tests/P23/Main.lean` contains exactly one import, `import P23.Main`, and
successfully elaborated consumers of all five stable public declarations plus
both fields of `P23.original_p23`. The OS process exit code was `0`, with no
stdout or stderr diagnostics.

