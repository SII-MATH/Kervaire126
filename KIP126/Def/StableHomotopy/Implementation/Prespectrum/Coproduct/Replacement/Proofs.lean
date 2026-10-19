module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Lifting.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- Initial left lifting properties assemble over the actual strict
coproduct, without any stability assertion about coproducts. -/
theorem coproduct_initial_hasLiftingProperty {J : Type u} (X : J → Prespectrum.{u})
    {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hX : ∀ j, HasLiftingProperty (zeroMap zeroPrespectrum (X j)) q) :
    HasLiftingProperty (zeroMap zeroPrespectrum (∐ X)) q := by
  letI := hX
  constructor
  intro t b sq
  let sq' (j : J) : CommSq t (zeroMap zeroPrespectrum (X j)) q (Sigma.ι X j ≫ b) :=
    ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  refine CommSq.HasLift.mk' {
    l := Sigma.desc (fun j => (sq' j).lift)
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := ?_ }
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc_assoc]
  exact (sq' j).fac_right

/-- A small coproduct of the actual free-cell replacements has the same
left lifting property against all levelwise full-boundary lifting maps. -/
theorem coproduct_cubicalReplacement_initial_hasLiftingProperty
    {J : Type u} (X : J → Prespectrum.{u}) {E B : Prespectrum.{u}} (q : E ⟶ B)
    (hq : ∀ n, HasCubeBoundaryLifting (q.level n)) :
    HasLiftingProperty
      (zeroMap zeroPrespectrum (∐ fun j => cubicalReplacementFunctor.obj (X j))) q :=
  coproduct_initial_hasLiftingProperty _ q
    (fun j => cubicalReplacement_initial_hasLiftingProperty_of_level (X j) q hq)

/-- Replacing a coproduct of the constructed replacements admits an
actual strict section of the actual comparison. This allows mapping-class
statements with replacement source to apply to the coproduct itself. -/
theorem coproduct_cubicalReplacement_comparison_hasSection
    {J : Type u} (X : J → Prespectrum.{u}) :
    ∃ s : (∐ fun j => cubicalReplacementFunctor.obj (X j)) ⟶
        cubicalReplacementFunctor.obj (∐ fun j => cubicalReplacementFunctor.obj (X j)),
      s ≫ cubicalReplacementComparison.app
        (∐ fun j => cubicalReplacementFunctor.obj (X j)) = 𝟙 _ := by
  let Z := ∐ fun j => cubicalReplacementFunctor.obj (X j)
  let q := cubicalReplacementComparison.app Z
  letI := coproduct_cubicalReplacement_initial_hasLiftingProperty X q
    (cubicalReplacementComparison_level_hasCubeBoundaryLifting Z)
  let sq : CommSq (zeroMap zeroPrespectrum (cubicalReplacementFunctor.obj Z))
      (zeroMap zeroPrespectrum Z) q (𝟙 Z) := ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
