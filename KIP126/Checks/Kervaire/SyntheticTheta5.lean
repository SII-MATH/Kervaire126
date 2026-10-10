import KIP126.Def.Kervaire.Theta5.Synthetic.Predicates
import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
import Lean.Elab.Command

/-! No C(M), stage axiom or prototype operation may enter these definitions. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf m || (`KIP126.Interface).isPrefixOf m ||
        (`KIPBase).isPrefixOf m then
      throwError "actual-object theta5 definitions import a project input: {m}"
  for n in [``KIP126.Kervaire.BJMOriginalCriterion,
      ``KIP126.Kervaire.BJMSourceTotalBoundaryIdentity,
      ``KIP126.Comparison.ClassicalSynthetic.sphereFirstQuotientComparison,
      ``KIP126.Synthetic.Context.vanishesModLambda_iff_factors] do
    for a in ← liftCoreM (collectAxioms n) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "new definition or proof contains an admitted fact: {n}: {a}"

open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Comparison.ClassicalSynthetic
open KIP126.Kervaire KIP126.Kervaire.SyntheticTheta5 KIP126.Classical.Adams
open CategoryTheory
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)
  (comparison : SphereFirstQuotientComparison H Syn) (η : Eta Syn) (θ : Theta Syn)

noncomputable example : BiHom 124 128 (S_0_0 : Syn) := thetaSquare θ
noncomputable example : BiHom 125 130 (S_0_0 : Syn) := etaThetaSquare η θ
noncomputable example : BiHom 125 129 (S_0_0 : Syn) := lambdaEtaThetaSquare η θ
noncomputable example : BiHom 125 129 (S_0_0 : Syn) := deltaH6Square H M comparison

-- Reduction really is composition with the chosen cofiber inclusion.
example (r : ℕ) : VanishesModLambda r (etaThetaSquare η θ) ↔
    etaThetaSquare η θ ≫ XModLambdaN.incl S_0_0 r = 0 := Iff.rfl

-- θ₅ is detected by h₅² at (2,64), not an unrelated named generator.
example : DetectsTheta H M comparison θ ↔
    comparison 2 64 (quotientClass 1 θ) = Sphere.Internal.hiSquare H M 5 := Iff.rfl

-- The actual total boundary uses the same E₂ comparison and cofiber boundary.
example : deltaH6Square H M comparison = h6TotalBoundary
    ((comparison 2 128).symm (Sphere.Internal.hiSquare H M 6)) := rfl
