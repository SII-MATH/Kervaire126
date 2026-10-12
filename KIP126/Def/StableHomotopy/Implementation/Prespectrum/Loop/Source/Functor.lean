module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Equivalence.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual pointwise loop functor on the original stable localization. -/
noncomputable def sourceLoopFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (loopFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (loopMap_stableEquivalence _ hf))

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceLoopFunctor_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLoopFunctor.map (sourceLocalization.map f) = sourceLocalization.map (loopMap f) := by
  have h : sourceLocalization ⋙ sourceLoopFunctor = loopFunctor ⋙ sourceLocalization :=
    Localization.Construction.fac _ _
  have hh : ∀ (F G : Prespectrum.{u} ⥤ SourceCategory.{u}), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (hh _ _ h)

theorem sourceLoopFunctor_fac : sourceLocalization ⋙ sourceLoopFunctor.{u} =
    loopFunctor ⋙ sourceLocalization := Localization.Construction.fac _ _

end KIP126.StableHomotopy.Implementation.Prespectrum

end
