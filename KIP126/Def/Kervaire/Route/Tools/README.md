# Generalized paper rules

This Def module owns the generalized Leibniz rule (MainPaper Theorem 6.1),
the generalized Mahowald trick (Theorem 6.12), and the finite sufficient-condition
stretching law (Proposition 6.20 / Corollary 6.21).

- `Inputs/Data.lean`: the existing `EInftyInput`, `SyntheticInputs`, and
  `MayInput` mathematical premise packages, with unchanged fields and model
  correlations. Their construction and literature source bindings stay in Interface.
- `GeneralizedLeibniz/Predicates.lean`, `GeneralizedMahowald/Predicates.lean`,
  `PageExtensionStretching/Predicates.lean`: the unchanged public law definitions.
- Each rule's `Proofs.lean`: its existing helper lemmas, partial proof, and
  explicit unfinished obligations. Import this concrete module to use the rule.

All dependencies of these modules are in Def or the underlying libraries.
Interface certification and Main both use these proofs; LinProgram artifacts,
computation deliveries, and the consumer witness are not proof premises.
The public names `KIP126.Main.Solution.Tools.generalizedLeibniz`,
`generalizedMahowald`, and `finitePageExtensionStretching` are retained for
compatibility and do not identify the source directory or create a Main import.

Relocation does not complete a proof: the three implementations retain two,
two, and one direct `sorry` obligations respectively, and all three Blueprint
proof nodes remain `notready`. Dependencies have their own proof obligations.
No theorem conclusion is added to a premise package or supplied as an axiom.

Stable Blueprint labels: `thm:generalized-leibniz`,
`thm:generalized-mahowald`, `cor:page-extension-stretch`.
