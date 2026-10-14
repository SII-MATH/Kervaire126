module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Endpoint.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Lifting.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Predicates
public import KIP126.Def.Topology.HomotopyLifting.Path.Endpoint.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual strict endpoint map inherits full cubical boundary lifting
at every level. -/
theorem pathEndpointMap_level_hasCubeBoundaryLifting {E B : Prespectrum.{u}}
    (f : E ⟶ B) (hf : ∀ n, HasCubeBoundaryLifting (f.level n)) (n : ℕ) :
    HasCubeBoundaryLifting ((pathEndpointMap f).level n) :=
  (hf n).pathEndpointComparison

/-- A strict homotopy of maps out of the actual cubical replacement lifts
through a levelwise boundary fibration, retaining both specified endpoints
and the whole base homotopy. -/
theorem cubicalReplacement_lift_strictHomotopy (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n, HasCubeBoundaryLifting (f.level n))
    {a b : cubicalReplacementFunctor.obj X ⟶ E}
    (H : StrictHomotopy (a ≫ f) (b ≫ f)) :
    ∃ G : StrictHomotopy a b, G.hom ≫ pathMap f = H.hom := by
  obtain ⟨l,hl⟩ := cubicalReplacement_lift_of_level_cubeBoundary X
    (pathEndpointMap f) (pathEndpointMap_level_hasCubeBoundaryLifting f hf)
    (pathEndpointLift f a b H.hom H.zero H.one)
  have h0 : l ≫ pathEvaluation E 0 = a := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun k : cubicalReplacementFunctor.obj X ⟶ pathEndpointPrespectrum f =>
      (k.level n x).val.1.1) hl
  have h1 : l ≫ pathEvaluation E 1 = b := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact congrArg (fun k : cubicalReplacementFunctor.obj X ⟶ pathEndpointPrespectrum f =>
      (k.level n x).val.1.2) hl
  refine ⟨⟨l,h0,h1⟩,?_⟩
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k : cubicalReplacementFunctor.obj X ⟶ pathEndpointPrespectrum f =>
    (k.level n x).val.2) hl

/-- Actual homotopy classes out of the constructed replacement are
reflected by every map with levelwise full boundary lifting. -/
theorem cubicalReplacement_pathHomotopic_of_postcomp (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n, HasCubeBoundaryLifting (f.level n))
    {a b : cubicalReplacementFunctor.obj X ⟶ E}
    (h : pathHomotopic (a ≫ f) (b ≫ f)) : pathHomotopic a b := by
  obtain ⟨H⟩ := h
  obtain ⟨G,_⟩ := cubicalReplacement_lift_strictHomotopy X f hf H
  exact ⟨G⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
