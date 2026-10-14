# Generalized paper rules

This Def module owns the generalized Leibniz rule (MainPaper Theorem 6.1),
the generalized Mahowald trick (Theorem 6.12), and the finite sufficient-condition
stretching law (Proposition 6.20 / Corollary 6.21).

- `Inputs/Data.lean`: the existing `EInftyInput`, `SyntheticInputs`, and
  `MayInput` mathematical premise packages, with unchanged fields and model
  correlations. Their construction and literature source bindings stay in Interface.
- `GeneralizedLeibniz/Predicates.lean`, `GeneralizedMahowald/Predicates.lean`,
  `PageExtensionStretching/Predicates.lean`: the public law definitions. Stretching retains develop's same-quotient
  sufficient condition described below.
- Each rule's `Proofs.lean`: the latest develop helper lemmas, proof, and
  any explicit unfinished obligations. Import this concrete module to use the rule.

All dependencies of these modules are in Def or the underlying libraries.
Interface certification and Main both use these proofs; LinProgram artifacts,
computation deliveries, and the consumer witness are not proof premises.
The public names `KIP126.Main.Solution.Tools.generalizedLeibniz`,
`generalizedMahowald`, and `finitePageExtensionStretching` are retained for
compatibility and do not identify the source directory or create a Main import.

Relocation does not complete a proof: the Leibniz and Mahowald implementations retain two
direct `sorry` obligations each. Finite stretching has no direct `sorry`,
but its model comparisons and other transitive dependencies remain proof
obligations; its Blueprint production node remains `notready`.
No theorem conclusion is added to a premise package or supplied as an axiom.

Stable Blueprint labels: `thm:generalized-leibniz`,
`thm:generalized-mahowald`, `cor:page-extension-stretch`.

The stretching exclusion is the actual `FiniteExtensionNonliftableCrossing`
predicate in `Extensions/Stretching/Predicates.lean`: it fixes the earlier
lambda quotient and synthetic weight, excludes sources outside the later
restriction map's E-infinity image, and covers nonzero targets of shorter
extensions even when they are nonessential. It includes length zero.
It is not identified with the previous ordinary-Adams-label candidate on a
smaller quotient. Any replay must supply the actual same-quotient exclusion;
no comparison with the old exclusion or the printed corollary is assumed.
