module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Predicates
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Endpoint.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual free-cell replacement satisfies the stated lifting
property by its proved attachment and countable-colimit construction. -/
theorem cubicalReplacement_isCubicallyCofibrant (X : Prespectrum.{u}) :
    IsCubicallyCofibrant (cubicalReplacementFunctor.obj X) :=
  cubicalReplacement_initial_hasLiftingProperty_of_level X

/-- The lifting property gives exact strict lifts of actual maps. -/
theorem IsCubicallyCofibrant.lift {X : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    {E B : Prespectrum.{u}} (p : E ⟶ B) (hp : ∀ n,HasCubeBoundaryLifting (p.level n))
    (b : X ⟶ B) : ∃ l : X ⟶ E, l ≫ p = b := by
  letI := hX p hp
  let sq : CommSq (zeroMap zeroPrespectrum E) (zeroMap zeroPrespectrum X) p b :=
    ⟨zeroPrespectrum_isZero.eq_of_src _ _⟩
  exact ⟨sq.lift,sq.fac_right⟩

/-- Actual endpoint comparison upgrades the same source property to
strict homotopy lifting with both prescribed endpoints retained. -/
theorem IsCubicallyCofibrant.lift_strictHomotopy {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) {E B : Prespectrum.{u}} (p : E ⟶ B)
    (hp : ∀ n,HasCubeBoundaryLifting (p.level n)) {a b : X ⟶ E}
    (H : StrictHomotopy (a ≫ p) (b ≫ p)) :
    ∃ G : StrictHomotopy a b, G.hom ≫ pathMap p = H.hom := by
  obtain ⟨l,hl⟩ := hX.lift (pathEndpointMap p) (pathEndpointMap_level_hasCubeBoundaryLifting p hp)
    (pathEndpointLift p a b H.hom H.zero H.one)
  have h0 : l ≫ pathEvaluation E 0 = a := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun k : X ⟶ pathEndpointPrespectrum p => (k.level n x).val.1.1) hl
  have h1 : l ≫ pathEvaluation E 1 = b := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun k : X ⟶ pathEndpointPrespectrum p => (k.level n x).val.1.2) hl
  refine ⟨⟨l,h0,h1⟩,?_⟩
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k : X ⟶ pathEndpointPrespectrum p => (k.level n x).val.2) hl

/-- A spectrum with actual left lifting is a strict retract of its
actual free-cell replacement. -/
theorem IsCubicallyCofibrant.replacement_hasSection {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) :
    ∃ s : X ⟶ cubicalReplacementFunctor.obj X,
      s ≫ cubicalReplacementComparison.app X = 𝟙 X :=
  hX.lift (cubicalReplacementComparison.app X)
    (cubicalReplacementComparison_level_hasCubeBoundaryLifting X) (𝟙 X)

end KIP126.StableHomotopy.Implementation.Prespectrum
