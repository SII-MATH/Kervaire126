module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

variable {A X Y : Prespectrum.{u}} (f : X ⟶ Y)
  (u : A ⟶ mappingPath f) (H : A ⟶ pathPrespectrum Y)
  (h : u ≫ mappingPathProjection f = H ≫ pathEvaluation Y 0)

/-- At time zero the constructed lift is exactly the prescribed original lift. -/
@[simp] theorem mappingPathLift_zero :
    mappingPathLift f u H h ≫ pathEvaluation (mappingPath f) 0 = u := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    classical
    change (if (1+(0 : ℝ))*(t : ℝ) ≤ 1 then
      (u.level n a).val.2 (mappingPathLiftFirst (0,t)) else
        (H.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (0,t))) = (u.level n a).val.2 t
    simp only [add_zero,one_mul,t.property.2,ite_true,mappingPathLiftFirst_zero]

/-- At every time the lift projects exactly to the prescribed base homotopy. -/
@[simp] theorem mappingPathLift_projection (s : I) :
    mappingPathLift f u H h ≫ pathEvaluation (mappingPath f) s ≫ mappingPathProjection f =
      H ≫ pathEvaluation Y s := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  classical
  change (if (1+(s : ℝ))*(1 : ℝ) ≤ 1 then
    (u.level n a).val.2 (mappingPathLiftFirst (s,1)) else
      (H.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,1))) = (H.level n a : C(I,Y.level n)).toFun s
  split_ifs with hs
  · have hs0 : s = 0 := by
      apply Subtype.ext
      change (s : ℝ) = 0
      nlinarith [s.property.1]
    subst s
    rw [mappingPathLiftFirst_zero]
    exact congrArg (fun k : A ⟶ Y => k.level n a) h
  · rw [mappingPathLiftSecond_end]

/-- The source coordinate stays fixed throughout the lift. -/
@[simp] theorem mappingPathLift_retraction (s : I) :
    mappingPathLift f u H h ≫ pathEvaluation (mappingPath f) s ≫ mappingPathRetraction f =
      u ≫ mappingPathRetraction f := rfl

/-- The explicit lift commutes with strict precomposition. -/
theorem mappingPathLift_precomp {B : Prespectrum.{u}} (j : B ⟶ A) :
    j ≫ mappingPathLift f u H h =
      mappingPathLift f (j ≫ u) (j ≫ H) (by rw [Category.assoc,h,Category.assoc]) := rfl

/-- On a subobject whose original lift is a constant path and whose prescribed
base homotopy is stationary there, the entire lifted homotopy stays fixed. -/
theorem mappingPathLift_relative {B : Prespectrum.{u}} (j : B ⟶ A) (v : B ⟶ X)
    (hu : j ≫ u = v ≫ mappingPathInclusion f)
    (hH : j ≫ H = v ≫ f ≫ pathConstant Y) :
    j ≫ mappingPathLift f u H h = v ≫ mappingPathInclusion f ≫ pathConstant (mappingPath f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun k : B ⟶ mappingPath f => (k.level n a).val.1) hu
  · apply ContinuousMap.ext
    intro t
    classical
    change (if (1+(s : ℝ))*(t : ℝ) ≤ 1 then
      (u.level n (j.level n a)).val.2 (mappingPathLiftFirst (s,t)) else
        (H.level n (j.level n a) : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,t))) = f.level n (v.level n a)
    split_ifs
    · exact congrArg (fun k : B ⟶ mappingPath f => (k.level n a).val.2 (mappingPathLiftFirst (s,t))) hu
    · exact congrArg (fun k : B ⟶ pathPrespectrum Y =>
        (k.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,t))) hH

end KIP126.StableHomotopy.Implementation.Prespectrum
