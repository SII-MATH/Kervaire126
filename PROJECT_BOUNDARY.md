# Project Boundary

## Status

This document records the agreed scope and acceptance criteria for the Lean
formalization of:

> Weinan Lin, Guozhen Wang, and Zhouli Xu, *On the Last Kervaire Invariant
> Problem*, represented in this repository by `MainPaper/main.tex`,
> `MainPaper/112.tex`, and `MainPaper/2412.10879.pdf`.

The document is normative for the project. Any proposed extension or
relaxation of this boundary must be agreed explicitly and recorded here.

## Confirmed design decisions

1. **Homotopy-theoretic foundation.** We use an abstract stable homotopy
   context (option A), not a construction of a complete model of stable
   infinity-categories. The context must expose every operation and property
   needed by the paper's arguments: spectra, maps, homotopy classes,
   suspension, cofibers, distinguished triangles, smash products, homotopy
   groups, and Adams filtrations.

2. **Steenrod algebra and Ext.** We formalize the relevant algebraic
   interfaces and general theorems for the Steenrod algebra, graded objects,
   filtered objects, and Ext/Adams pages. We do not reimplement the large
   high-stem Ext calculations performed by Lin's programs. Concrete
   high-stem values, computer output, and table entries are external inputs
   represented by explicit mathematical hypotheses with provenance recorded
   in `docs/external-inputs.json`.

   For the statement of the permanent `h_6^2` target, the confirmed abstract
   foundation may include an explicit mod--2 Eilenberg--Mac Lane object and
   Milnor cooperation coordinates. These coordinates identify the constructed
   first Adams page with the explicitly defined normalized Milnor cobar
   cochains and intertwine the constructed first differential with the Milnor
   coproduct differential. This structural input is not inferred from the
   homotopy groups of the Eilenberg--Mac Lane object alone. The Adams tower,
   quotient pages, later differentials, page passage, standard `h_6`, its
   concatenation square, and pagewise nonzero permanence must be defined from
   these foundations; they must not be supplied as fields. Proof-route results
   such as C3, C4, and C5 are not part of the statement's defining data. This
   statement-only stage does not establish the conditional final theorem or
   relax the project's proof-completion and axiom-audit acceptance criteria.

   The next agreed stage retains the abstract background and moves the
   comparison foundation below the Adams pages: an associative unital
   structure on the specified `H`, its graded cooperations, and the tensor,
   exactness, and Künneth compatibility needed to construct the comparison.
   The first-page coordinates and their differential compatibility must be
   derived from those foundations. Until that derivation is implemented,
   the existing `MilnorCooperations` argument remains an explicit uneliminated
   dependency; merely renaming or rebundling it does not complete this stage.

3. **Appendix data.** Every entry in the Appendix tables is to be encoded,
   not only the entries used directly in the final proof. The encoding records
   the relevant stem, filtration, class names, differential length, target,
   permanence status, and any stated ambiguity.

4. **Examples, remarks, and questions.**
   - A mathematical assertion in an Example is formalized when it is used by
     a later argument or is needed as a regression test.
   - Expository Remarks are not required to become separate declarations.
   - Open Questions are represented as propositions/statements only; they are
     not assumed and are not required to be proved.
   - **Introduction excluded (2026-10-06).** The introduction's exposition,
     corollaries and open questions are outside the formalization plan.
     Results supporting only that introduction are removed from Challenge2
     and from active proof obligations. The standard `h_6^2` permanent-survival
     target and all results needed by the body’s proof or computation
     certification remain in scope, even when first mentioned in the
     introduction. This decision supersedes the earlier retention of May’s
     introductory low-dimensional square-survival family.

5. **Current endpoint and excluded geometry.** The current endpoint is
   nonzero permanent survival of the standard `h_6^2` in the classical Adams
   spectral sequence. Framed-manifold existence in dimension 126 and the exact
   geometric dimension list `2, 6, 14, 30, 62, 126` are outside the current
   scope and acceptance criteria. The classical `theta_5`/`h_5^2` results
   needed by the homotopy-theoretic proof remain in scope.

6. **Axiom policy.** The project may use Lean's foundational axioms and the
   axioms already intrinsic to Lean's standard foundational mechanisms.
   During development, an internal statement deliberately introduced with
   Lean's `axiom` command is limited to the single direct witness
   `Main.Axiom.challenge2 : KIP126.Challenge2`. No other project axioms may be
   declared, including under `Def/` or `Mathlib/`. The development axiom must
   record its intended meaning, source where applicable, intended construction
   or proof, and reason for being assumed. Its presence is not evidence that
   the statement or its downstream consequences are proved.

   An unfinished theorem remains in the appropriate proof file with `by sorry`;
   it must not be converted into an axiom merely to avoid `sorryAx`.
   Development CI does not run proof-debt audits or publish debt reports, and
   requires no debt-specific human approval for a compiling pull request.
   Development merging does not claim that the affected theorem or the project
   is complete; the final proof-completion checks below remain strict.

   Literature results and computational inputs remain explicit external
   premises as specified below. The single development axiom must be
   eliminated before final acceptance, while retained external results remain
   explicit hypotheses of the conditional theorem. Development compilation
   does not authorize retaining project axioms at final acceptance.

7. **Pinned toolchain.**
   - Lean: `4.32.2`
   - mathlib: `v4.32.2`

   The project must use the matching Lean/mathlib versions and must not depend
   on an unpinned `master` branch or a release candidate.

8. **Fixed, parameter-free standard h₆² statement (development-stage exception).**
   The standard `h_6^2` target fixes the stable foundation, H𝔽₂, Milnor
   coordinates and Adams tower once. Its signature has no model or
   external-evidence parameters. The standard sphere sequence and Milnor
   class reuse the tower construction; they are not supplied by a computation
   table. The target requires nonzero permanent survival of that standard
   class.

   The fixed Lin E₂ presentation (Zenodo 14875701, v126.3.cw49, internal degree
   at most 261) remains an explicitly recorded external computation input to
   the proof. Source hashes are recorded for the actual imported data in the
   external manifest. Unfinished fixed foundations and comparisons remain
   proof obligations under the axiom policy above. The target's survival
   conclusion is not assumed.

   A proof body without `sorry` is not a claim that its dependency cone is
   free of `sorryAx`, project axioms, or external computation assumptions.

## In-scope formalization

### 1. Algebraic and categorical foundations

The project must formalize the interfaces and required laws for:

- `\mathbb F_2`, graded groups, graded modules, and relevant additive
  structures;
- filtrations and filtered maps;
- chain complexes, homology, exactness, kernels, cokernels, and quotients;
- spectra, maps of spectra, homotopy classes, and homotopy groups;
- suspension and desuspension;
- cofibers, distinguished triangles, and the homotopy category;
- smash products and the naturality/compatibility used in the paper;
- Adams filtration of classes and maps.

The implementation may build on mathlib's category-theory, homological
algebra, homotopy-category, triangulated-category, and spectral-object
infrastructure, while supplying the paper-specific interfaces that mathlib
does not provide.

### 2. Classical Adams spectral sequences

The formalization must include:

- pages, bidegrees, cycles, boundaries, and page-to-page differentials;
- the `E_\infty` page and the relationship to filtered homotopy groups;
- convergence assumptions used by the paper;
- the classical Adams differential convention and degree shifts;
- the elements `h_j`, in particular `h_6^2`;
- the classical extension spectral sequence (ESS);
- essential and inessential extensions;
- crossings, no-crossing conditions, and the associated filtration criteria;
- the propositions and corollaries in Section 2, including naturality and
  composition results.

### 3. `H\mathbb F_2`-synthetic spectra

The abstract synthetic context must include:

- the synthetic category and the functor `\nu`;
- the deformation element `\lambda`;
- synthetic spheres and suspensions;
- `\lambda^n`-quotients;
- the maps `\rho` and `\delta`;
- synthetic Adams spectral sequences;
- the `\lambda`-Bockstein viewpoint;
- rigidity and the comparison interfaces needed by the paper;
- synthetic extension spectral sequences;
- the induced classical `(f, E_r)`-extensions;
- synthetic/classical crossing equivalences.

Foundational theorems imported from earlier papers (for example, the
Pstrągowski and BHS results used to justify these interfaces) are not reproved
here. Their statements are supplied as explicit mathematical hypotheses,
with provenance recorded in the external manifest described below.

### 4. The paper's new results

The following must be proved in Lean from the formalized interfaces and
explicit external inputs:

- Section 2 ESS definitions, propositions, and corollaries;
- synthetic extension results in Sections 3–5;
- the definition and properties of classical `(f, E_r)`-extensions;
- crossing and no-crossing lemmas;
- the Generalized Leibniz Rule;
- the Generalized Mahowald Trick;
- page-stretching and extension-propagation results;
- all logical reductions in Section 7 that do not themselves assert an
  external theorem or a computed table value;
- the conditional nonzero permanent-survival theorem for standard `h_6^2`.

The proofs must preserve the degree conventions in the paper, including the
third synthetic weight and the translation convention using `S^{1,0}`.

## External inputs

Results from earlier papers, published computations, Lin's program, and facts
read from the Appendix tables are outside the proof-development boundary.
They enter conditional theorems as explicit mathematical hypotheses. They
must not become untracked global facts or separate Lean `axiom` declarations.

Lean interfaces contain the mathematical statements, hypotheses and
conditions of those inputs. Source identities, locators, acquisition status,
artifact paths, versions and hashes are recorded outside Lean in the
canonical machine-readable manifest `docs/external-inputs.json`. Each
external input must be linked there to the Lean declarations that state or
consume it. There is no parallel Lean source registry or claim ledger.

The manifest must provide an auditable locator for each input, identifying a
theorem, lemma, proposition, equation, table, section, page or line. Unavailable
primary text must be marked explicitly, with the exact secondary locator used.
Computational evidence must identify the actual imported artifacts and their
versions and hashes. Source artifacts and acquisition records remain available
for review.

Checks of paths, artifact membership, hashes and declaration links establish
provenance consistency. They do not prove the recorded mathematical claim or
that a source entails the Lean statement.

Examples of external inputs include:

- Barratt--Jones--Mahowald and Burklund--Xu's inductive criterion;
- prior synthetic-spectrum and rigidity theorems;
- May's lemma and other prior-paper results used by the new arguments;
- all concrete Lin-program Ext groups, differentials, extensions, and
  disproofs;
- every entry of the Appendix tables, including entries not used in the final
  proof;
- cited `tmf` detection facts and other prior computational or
  homotopy-theoretic conclusions.

The final proof must make the dependency on these mathematical hypotheses
explicit, with their provenance linked in the external manifest.

## Conditional final theorem

Under the required external mathematical literature and computation
hypotheses, prove nonzero permanent survival of the standard `h_6^2` in the
classical Adams spectral sequence.

The retained external hypotheses have their provenance recorded in
`docs/external-inputs.json`. Framed-manifold existence, geometric dimension
classification and Browder/Pontryagin--Thom comparisons are outside the current
project scope.

## Acceptance criteria

The project is complete only when all of the following hold:

- `lake build` succeeds with the pinned Lean/mathlib versions;
- all canonical KIP126 source outside the intentional Challenge statement
  track contains no `sorry` or `admit`, and canonical KIP126 declares no project
  `axiom`; Challenge statements retain their required `by sorry` bodies and
  are excluded from proof-completion evidence, while the isolated historical
  KIPBase component remains subject to its separate migration audit;
- the single temporary development axiom has been eliminated;
- every external input is an explicit Lean mathematical hypothesis with a
  corresponding declaration and locator entry in `docs/external-inputs.json`;
- every Appendix table entry has a Lean encoding;
- the final theorem(s) pass a `#print axioms` audit with:
  - no `sorryAx`;
  - no project-defined or undeclared custom axiom;
  - Lean foundational axioms allowed by this boundary being the only
    remaining axioms.

The `#print axioms` audit is a hard completion requirement, not merely a
documentation check.

## Explicit non-goals

The project does not attempt to:

- formalize framed-manifold Kervaire invariants, Browder/Pontryagin--Thom
  comparisons, or geometric existence/nonexistence conclusions in the
  current scope;
- construct a complete model of stable infinity-categories;
- independently reproduce Lin's high-stem computer calculations;
- prove the cited prior-paper theorems;
- treat table values as trusted constants without provenance;
- turn the paper's open Questions into assumptions or claimed results;
- hide external dependencies behind untracked global instances or axioms.
