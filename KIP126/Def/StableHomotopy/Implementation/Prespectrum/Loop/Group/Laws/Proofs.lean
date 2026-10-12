module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Laws.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem loopAssocPath_zero {A X : Prespectrum.{u}} (f g h : A ⟶ Prespectrum.loop X) :
    loopAssocPath f g h ≫ pathEvaluation _ 0 = loopAdd (loopAdd f g) h := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (Path.Homotopy.transAssoc (f.level n x) (g.level n x) (h.level n x)).eval_zero

@[simp] theorem loopAssocPath_one {A X : Prespectrum.{u}} (f g h : A ⟶ Prespectrum.loop X) :
    loopAssocPath f g h ≫ pathEvaluation _ 1 = loopAdd f (loopAdd g h) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (Path.Homotopy.transAssoc (f.level n x) (g.level n x) (h.level n x)).eval_one

@[simp] theorem loopRightUnitPath_zero {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopRightUnitPath f ≫ pathEvaluation _ 0 = loopAdd f (zeroMap _ _) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Path.delayReflRight_zero (f.level n x)

@[simp] theorem loopRightUnitPath_one {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopRightUnitPath f ≫ pathEvaluation _ 1 = f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Path.delayReflRight_one (f.level n x)

@[simp] theorem loopLeftUnitPath_zero {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopLeftUnitPath f ≫ pathEvaluation _ 0 = loopAdd (zeroMap _ _) f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Path.delayReflLeft_zero (f.level n x)

@[simp] theorem loopLeftUnitPath_one {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopLeftUnitPath f ≫ pathEvaluation _ 1 = f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact Path.delayReflLeft_one (f.level n x)

@[simp] theorem loopRightInversePath_zero {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopRightInversePath f ≫ pathEvaluation _ 0 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (Path.Homotopy.reflTransSymm (f.level n x)).eval_zero

@[simp] theorem loopRightInversePath_one {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    loopRightInversePath f ≫ pathEvaluation _ 1 = loopAdd f (f ≫ loopInverse X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (Path.Homotopy.reflTransSymm (f.level n x)).eval_one

/-- Actual concatenation is associative in the original stable localization. -/
theorem source_loopAdd_assoc {A X : Prespectrum.{u}} (f g h : A ⟶ Prespectrum.loop X) :
    sourceLocalization.map (loopAdd (loopAdd f g) h) =
      sourceLocalization.map (loopAdd f (loopAdd g h)) := by
  rw [← loopAssocPath_zero,← loopAssocPath_one,Functor.map_comp,Functor.map_comp,
    source_pathEvaluation_eq (Prespectrum.loop X) 0 1]

theorem source_loopAdd_zero {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    sourceLocalization.map (loopAdd f (zeroMap _ _)) = sourceLocalization.map f := by
  calc
    _ = sourceLocalization.map (loopRightUnitPath f ≫ pathEvaluation _ 0) :=
      congrArg sourceLocalization.map (loopRightUnitPath_zero f).symm
    _ = sourceLocalization.map (loopRightUnitPath f ≫ pathEvaluation _ 1) := by
      rw [Functor.map_comp,Functor.map_comp,source_pathEvaluation_eq (Prespectrum.loop X) 0 1]
    _ = _ := congrArg sourceLocalization.map (loopRightUnitPath_one f)

theorem source_zero_loopAdd {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    sourceLocalization.map (loopAdd (zeroMap _ _) f) = sourceLocalization.map f := by
  calc
    _ = sourceLocalization.map (loopLeftUnitPath f ≫ pathEvaluation _ 0) :=
      congrArg sourceLocalization.map (loopLeftUnitPath_zero f).symm
    _ = sourceLocalization.map (loopLeftUnitPath f ≫ pathEvaluation _ 1) := by
      rw [Functor.map_comp,Functor.map_comp,source_pathEvaluation_eq (Prespectrum.loop X) 0 1]
    _ = _ := congrArg sourceLocalization.map (loopLeftUnitPath_one f)

theorem source_loopAdd_inverse {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    sourceLocalization.map (loopAdd f (f ≫ loopInverse X)) =
      sourceLocalization.map (zeroMap A (Prespectrum.loop X)) := by
  rw [← loopRightInversePath_one,← loopRightInversePath_zero f,Functor.map_comp,Functor.map_comp,
    source_pathEvaluation_eq (Prespectrum.loop X) 0 1]

@[simp] theorem loopInverse_twice (X : Prespectrum.{u}) : loopInverse X ≫ loopInverse X = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact x.symm_symm

theorem source_inverse_loopAdd {A X : Prespectrum.{u}} (f : A ⟶ Prespectrum.loop X) :
    sourceLocalization.map (loopAdd (f ≫ loopInverse X) f) =
      sourceLocalization.map (zeroMap A (Prespectrum.loop X)) := by
  simpa only [Category.assoc,loopInverse_twice,Category.comp_id] using
    source_loopAdd_inverse (f ≫ loopInverse X)

end KIP126.StableHomotopy.Implementation.Prespectrum
