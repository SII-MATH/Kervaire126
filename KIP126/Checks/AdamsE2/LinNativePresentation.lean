import KIP126.Interface.Challenge.Computation.Presentation
import Lean.Elab.Command

/-! Contract regressions for the one untruncated global comparison.
These checks do not construct that comparison or discharge the explicitly
named actual E₂ ring-law obligations. Data-side trust is audited separately. -/
noncomputable section

namespace KIP126.Checks.LinNativePresentation
open KIP126.Core.Algebra KIP126.LinE2 KIP126.Classical.Adams
open Sphere.Internal

-- The new type alias names exactly the old actual page, not a replacement model.
example (s t : ℕ) : ActualE2At (s, t) =
    sphereAdamsData.Page 2 ((s : ℤ), (t : ℤ)) := rfl

-- All products, including those above the archive range, are preserved.
example (P : LinE2Presentation) (x y : NativeAlgebra) :
    P.toActual (x * y) = P.toActual x * P.toActual y := P.toActual.map_mul x y

-- The endpoint is inclusive, and every natural filtration remains in scope.
example (P : LinE2Presentation) (s : ℕ) :
    NativeAt s 261 ≃ₗ[F2] ActualE2At (s, 261) :=
  P.nativeComparison s 261 (by decide)

-- Components and degree preservation exist outside the bijectivity range.
example (P : LinE2Presentation) (s : ℕ) :
    NativeAt s 262 →ₗ[F2] ActualE2At (s, 262) :=
  P.component s 262

example (P : LinE2Presentation) (s : ℕ) (x : NativeAt s 262) :
    embed (s, 262) (P.component s 262 x) = P.toActual x.val :=
  P.embed_component s 262 x

-- Different presentations cannot choose different actual multiplications.
example (P Q : LinE2Presentation) (s t s' t' : ℕ) :
    P.product s t s' t' = Q.product s t s' t' := rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let fields := getStructureFields env ``LinE2Presentation
  unless fields == #[`toActual, `preservesDegree, `component_bijective] do
    throwError "global presentation field drift: {fields}"
  for name in [``LinE2Presentation.comparison, ``LinE2Presentation.product,
      ``LinE2Presentation.comparison_mul] do
    if (env.getProjectionFnInfo? name).isSome then
      throwError "compatibility API became an independent input again: {name}"
    let some info := env.find? name | throwError "missing derived API: {name}"
    let some value := info.value? (allowOpaque := true) |
      throwError "derived API has no definition/proof: {name}"
    if value.getUsedConstants.contains ``sorryAx then
      throwError "compatibility API hides a new direct placeholder: {name}"
  for module in env.allImportedModuleNames do
    if (`KIP126.Main).isPrefixOf module ||
        (`KIP126.Interface.Solution).isPrefixOf module then
      throwError "presentation depends on its own producer or consumer: {module}"

#print axioms LinE2Presentation.comparison_mul
end KIP126.Checks.LinNativePresentation
