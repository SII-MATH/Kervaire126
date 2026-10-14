import KIPBase.Synthetic.LambdaLiftESS

/-!
# Regression checks for the stable-model interface migration

Model-bound comparisons must carry the existing realization of the same
synthetic category. Generic finite-quotient and page algebra must not acquire
that premise merely by sharing a section with the comparisons. These checks
assert interface shape, not proof completion or freedom from inherited axioms.
-/

namespace KIPBase.Checks.ModelRealization

open Lean

private def mentionsRealization : Expr → Bool
  | .const name _ => name == ``KIPBase.Synthetic.SyntheticModelRealizationWitness
  | .app fn arg => mentionsRealization fn || mentionsRealization arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      mentionsRealization domain || mentionsRealization body
  | .letE _ type value body _ =>
      mentionsRealization type || mentionsRealization value || mentionsRealization body
  | .mdata _ body | .proj _ _ body => mentionsRealization body
  | _ => false

run_meta do
  for name in [
      ``KIPBase.Synthetic.lambdaBocksteinSource_boundaries_eq_initial,
      ``KIPBase.Synthetic.canonicalLambdaBocksteinSourceToE2Data,
      ``KIPBase.Synthetic.AffineReindexedSpectralSequenceMorphism.pageMap_isIso_of_initial,
      ``KIPBase.Synthetic.lambdaLiftBocksteinZ,
      ``KIPBase.Synthetic.lambdaLiftBocksteinRawDifferential,
      ``KIPBase.Synthetic.mahowaldQuotientLift_to_directBockstein_and_ess] do
    let info ← getConstInfo name
    if mentionsRealization info.type then
      throwError "Generic declaration acquired a model realization premise: {name}"
  for name in [
      ``KIPBase.Synthetic.NuSynAdamsGeometricComparison.adamsE2_geometricPageTwo_equiv,
      ``KIPBase.Synthetic.adamsDifferential_to_finiteBoundary_ess] do
    let info ← getConstInfo name
    unless mentionsRealization info.type do
      throwError "Model-bound comparison lost its realization premise: {name}"

-- The chosen category receives its witness from its actual selected model,
-- rather than from a universal instance postulating a model for every category.
noncomputable example : KIPBase.Synthetic.SyntheticModelRealizationWitness
    KIPBase.Synthetic.Syn.{0, 0} := inferInstance

end KIPBase.Checks.ModelRealization
