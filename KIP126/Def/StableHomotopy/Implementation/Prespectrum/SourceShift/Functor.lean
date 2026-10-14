module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Comparison.Naturality.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceDesuspensionFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (desuspensionFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (desuspensionMap_stableEquivalence _ hf))

noncomputable def sourceTailFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (levelTailFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (levelTailMap_stableEquivalence _ hf))

noncomputable def sourceSuspensionFunctor : SourceCategory.{u} ⥤ SourceCategory.{u} :=
  Localization.Construction.lift (suspensionFunctor ⋙ sourceLocalization)
    (fun _ _ _ hf => stableEquivalences.Q_inverts _ (suspensionMap_stableEquivalence _ hf))


end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceDesuspensionFunctor_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceDesuspensionFunctor.map (sourceLocalization.map f) = sourceLocalization.map (desuspensionMap f) := by
  have h : sourceLocalization ⋙ sourceDesuspensionFunctor = desuspensionFunctor ⋙ sourceLocalization :=
    Localization.Construction.fac _ _
  have hh : ∀ (F G : Prespectrum.{u} ⥤ SourceCategory.{u}), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (hh _ _ h)

@[simp] theorem sourceTailFunctor_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceTailFunctor.map (sourceLocalization.map f) = sourceLocalization.map (levelTailMap f) := by
  have h : sourceLocalization ⋙ sourceTailFunctor = levelTailFunctor ⋙ sourceLocalization :=
    Localization.Construction.fac _ _
  have hh : ∀ (F G : Prespectrum.{u} ⥤ SourceCategory.{u}), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (hh _ _ h)

@[simp] theorem sourceSuspensionFunctor_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceSuspensionFunctor.map (sourceLocalization.map f) = sourceLocalization.map (suspensionMap f) := by
  have h : sourceLocalization ⋙ sourceSuspensionFunctor = suspensionFunctor ⋙ sourceLocalization :=
    Localization.Construction.fac _ _
  have hh : ∀ (F G : Prespectrum.{u} ⥤ SourceCategory.{u}), F = G → HEq (F.map f) (G.map f) := by
    intro F G h
    cases h
    rfl
  exact eq_of_heq (hh _ _ h)


end KIP126.StableHomotopy.Implementation.Prespectrum

end
