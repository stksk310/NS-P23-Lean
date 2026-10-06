# Original P23 final certification

ORIGINAL P23 MATHEMATICS: CLOSED

LEAN IMPLEMENTATION: CLEAN_BUILD / FINAL INDEPENDENT AUDIT PENDING

SOLVER DEPENDENCY: NONE in production proof DAG

PROJECT-LOCAL AXIOMS / SORRY / ADMIT: 0

SEMANTIC SCOPE: PF NG-vector predicate

The original P23 branch theorem is Lean-certified under the project's
formal PF NG-vector predicate `SemigroupNearlyGorenstein`.

For a minimally four-generated numerical semigroup D satisfying that
predicate and not almost symmetric: type2 implies rho=4 or rho=5;
type3 implies rho=6. For type2/3 with rho>=type+4, D is almost symmetric.

Stable entry point: `import P23.Main`, namespace P23. Public theorems:
high_relation_number_forces_almost_symmetric;
type_two_nearly_gorenstein_not_almost_symmetric;
type_three_nearly_gorenstein_not_almost_symmetric;
original_p23 (OriginalP23Theorem package);
original_p23_of_type_two_or_three.

Accepted dependency chain: Run34 type3 lower bound -> Run37 AS forcing
-> Run37 original branches -> Run38 Main assembly. See the complete
LEAN_SOURCE_OF_TRUTH_LEDGER.md and LEAN_DEPENDENCY_DAG.md. All141 accepted
Run01--37 production modules are protected by the archive-derived freeze.
Main is one new production module, with no new mathematical argument.

## Semantic and external boundary

The predicate is the standard PF NG-vector criterion formalized in Run22.
The one-dimensional semigroup-ring trace equivalence has not been formalized.
No independent AS rho<=7 theorem or unconditional global e4 NG rho<=7
corollary is asserted. No external fact is inserted as a local postulate.

EXT-PF-NG-RING-TRACE-EQUIVALENCE: NOT_FORMALIZED
EXT-AS-RHO7-THEOREM: NOT_FORMALIZED_IN_THIS_PROJECT
COROLLARY-E4-NG-RHO7: PENDING EXT-AS-RHO7-THEOREM
GLOBAL_RHO7_COROLLARY: EXTERNAL_COROLLARY_PENDING_AS_THEOREM

## Final verification status

One fresh project-local build8850 jobs PASS; production142. Full Run01--38
typed119/119, repair positives/negative, controls16, tool-unit suites3,
historical/Main axiom files39, new Main public5/5, frozen141/141 and debt0 PASS.
All Main theorem dependencies are within propext/Classical.choice/Quot.sound.
Exact P146/T297 inputs are sealed in immutable Run38 receipts, with no P/T
changes after the accepted gate. Native gate UTC 2026-10-05T13:47:55 to
2026-10-05T14:48:54; precise timestamps and every hash are in the input JSONs.
Shared dependency caches and old result archives are preserved.

Final package SHA256 and actual last ZIP-byte audit are recorded externally
in RUN38_PACKAGE_RECEIPT.md, delivered alongside the ZIP; no self-hash cycle.
This internal report intentionally does not assert an independent audit.
Final Main remains CLEAN_BUILD / INDEPENDENT_AUDIT_PENDING, not self-FROZEN.
