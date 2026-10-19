module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Group.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceLoopAdd_map (X : Prespectrum.{u}) {A : Prespectrum.{u}}
    (f g : A ⟶ Prespectrum.loop X) :
    sourceLoopAdd X (sourceLocalization.map f) (sourceLocalization.map g) =
      sourceLocalization.map (loopAdd f g) := by
  unfold sourceLoopAdd
  have he : Fin.cases (sourceLocalization.map f) (fun _ : Fin 1 => sourceLocalization.map g) =
      fun j => sourceLocalization.map (Fin.cases f (fun _ : Fin 1 => g) j) := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> rfl
  rw [he, sourcePiLift_map, ← Functor.map_comp, loopConcat_lift]

@[reassoc] theorem comp_sourceLoopAdd (X : Prespectrum.{u}) {A B : SourceCategory.{u}}
    (k : A ⟶ B) (f g : B ⟶ sourceLocalization.obj (Prespectrum.loop X)) :
    k ≫ sourceLoopAdd X f g = sourceLoopAdd X (k ≫ f) (k ≫ g) := by
  unfold sourceLoopAdd
  rw [← Category.assoc, comp_sourcePiLift]
  congr 2
  funext j
  refine Fin.cases ?_ (fun _ => ?_) j <;> rfl

@[simp] theorem sourceLoopAdd_zero (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) : sourceLoopAdd X f 0 = f := by
  have h : sourceLoopAdd X (𝟙 (sourceLocalization.obj (Prespectrum.loop X))) 0 = 𝟙 _ := by
    have h := source_loopAdd_zero (𝟙 (Prespectrum.loop X))
    rw [← sourceLoopAdd_map] at h
    change sourceLoopAdd X (sourceLocalization.map (𝟙 _))
      (sourceLocalization.map (0 : Prespectrum.loop X ⟶ Prespectrum.loop X)) =
        sourceLocalization.map (𝟙 _) at h
    simpa only [sourceLocalization.map_id, Functor.map_zero] using h
  have hf := congrArg (fun k => f ≫ k) h
  simpa only [comp_sourceLoopAdd, Category.comp_id, CategoryTheory.Limits.comp_zero] using hf

@[simp] theorem zero_sourceLoopAdd (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) : sourceLoopAdd X 0 f = f := by
  have h : sourceLoopAdd X 0 (𝟙 (sourceLocalization.obj (Prespectrum.loop X))) = 𝟙 _ := by
    have h := source_zero_loopAdd (𝟙 (Prespectrum.loop X))
    rw [← sourceLoopAdd_map] at h
    change sourceLoopAdd X
      (sourceLocalization.map (0 : Prespectrum.loop X ⟶ Prespectrum.loop X))
      (sourceLocalization.map (𝟙 _)) = sourceLocalization.map (𝟙 _) at h
    simpa only [sourceLocalization.map_id, Functor.map_zero] using h
  have hf := congrArg (fun k => f ≫ k) h
  simpa only [comp_sourceLoopAdd, Category.comp_id, CategoryTheory.Limits.comp_zero] using hf

@[simp] theorem sourceLoopNeg_add (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) :
    sourceLoopAdd X (sourceLoopNeg X f) f = 0 := by
  have h : sourceLoopAdd X (sourceLocalization.map (loopInverse X)) (𝟙 _) = 0 := by
    have h := source_inverse_loopAdd (𝟙 (Prespectrum.loop X))
    rw [← sourceLoopAdd_map, Category.id_comp] at h
    change sourceLoopAdd X (sourceLocalization.map (loopInverse X))
      (sourceLocalization.map (𝟙 _)) =
        sourceLocalization.map (0 : Prespectrum.loop X ⟶ Prespectrum.loop X) at h
    simpa only [sourceLocalization.map_id, Functor.map_zero] using h
  have hf := congrArg (fun k => f ≫ k) h
  simpa only [comp_sourceLoopAdd, Category.comp_id, CategoryTheory.Limits.comp_zero,
    sourceLoopNeg] using hf

theorem sourceLoopAdd_assoc (X : Prespectrum.{u}) {A : SourceCategory.{u}}
    (f g h : A ⟶ sourceLocalization.obj (Prespectrum.loop X)) :
    sourceLoopAdd X (sourceLoopAdd X f g) h = sourceLoopAdd X f (sourceLoopAdd X g h) := by
  let Y : Fin 3 → Prespectrum.{u} := fun _ => Prespectrum.loop X
  let p : ∀ j : Fin 3, piPrespectrum Y ⟶ Prespectrum.loop X := piProjection Y
  have hp : sourceLoopAdd X (sourceLoopAdd X (sourceLocalization.map (p 0))
        (sourceLocalization.map (p 1))) (sourceLocalization.map (p 2)) =
      sourceLoopAdd X (sourceLocalization.map (p 0)) (sourceLoopAdd X
        (sourceLocalization.map (p 1)) (sourceLocalization.map (p 2))) := by
    simpa only [sourceLoopAdd_map] using source_loopAdd_assoc (p 0) (p 1) (p 2)
  let k := sourcePiLift Y (Fin.cases f (Fin.cases g (fun _ : Fin 1 => h)))
  have hk := congrArg (fun t => k ≫ t) hp
  simp only [comp_sourceLoopAdd, k, p, sourcePiLift_projection] at hk
  exact hk

end KIP126.StableHomotopy.Implementation.Prespectrum
