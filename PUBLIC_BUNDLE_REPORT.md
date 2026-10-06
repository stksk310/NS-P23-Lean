# Public bundle report

Release candidate: NS-P23-Lean v1.0.0  
Assembly date: 2026-10-06 (Asia/Tokyo)

## Status

| Gate | Result |
| --- | --- |
| Source authority SHA256 | `de12b67a6ca6525846f9aea38e58713baaf1719e932829927be2fdecc3a24e41` |
| Final public file count | 337 |
| Production Lean source count | 143 |
| Production byte identity | PASS — 143/143 MATCH |
| Fresh project-local Lake build | PASS — 8850 jobs |
| Main-only public API test | PASS |
| Public axiom audit | PASS — only `propext`, `Classical.choice`, `Quot.sound` |
| Project-local proof debt | PASS — 0 |
| Semantic-scope audit | PASS — 0 overclaims |
| License | COMPLETE — Apache-2.0 |
| Author metadata | COMPLETE |
| README | COMPLETE |
| CITATION.cff | COMPLETE |
| DOI | PENDING ZENODO PUBLICATION |
| GitHub readiness | **YES** |
| Zenodo readiness | **YES — DOI pending publication** |

## Authority and file-set policy

The only formal source authority is
`NS_P23_LEAN_FINAL_MAIN_RESULT_20261005.zip` with the SHA256 recorded above.
Every `P23/**/*.lean` file and root `P23.lean` in this bundle is byte-for-byte
identical to its corresponding authority member. The comparison is recorded
in `PUBLIC_PRODUCTION_SHA256.tsv`.

`PUBLIC_SHA256SUMS` covers exactly the files copied to the final public
candidate, except the manifest itself. The final candidate and source ZIP use
the same 337-file release set. `.lake/`, build output, compiled artifacts,
release-control scripts and logs, extraction content, and other staging-only
generated material are excluded.

The optional local file `P23_FINAL_INDEPENDENT_AUDIT_20261005.md` was not
available during assembly and is therefore neither included nor linked.

```text
INDEPENDENT AUDIT DOCUMENT: PENDING EXTERNAL COPY
```

## Publication follow-up

The repository metadata is complete for GitHub publication. The Zenodo DOI is
intentionally absent and must be added only after Zenodo publication creates
the record. If the independent audit Markdown is later supplied externally,
copy it byte-for-byte, add a non-broken README link, and regenerate the
manifest and source ZIP.

No GitHub repository creation, push, release creation, or Zenodo publication
was performed.

