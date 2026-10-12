module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Parameter.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {A X Y : Prespectrum.{u}} (f : X ⟶ Y)
  (u : A ⟶ mappingPath f) (H : A ⟶ pathPrespectrum Y)
  (h : u ≫ mappingPathProjection f = H ≫ pathEvaluation Y 0)

/-- Traverse the entire old path and then the specified initial segment of
the base homotopy, using continuous variable-length concatenation. -/
def mappingPathLiftFamily (n : ℕ) : C((A.level n × I) × I,Y.level n) := by
  classical
  refine ⟨fun z => if (1+(z.1.2 : ℝ))*(z.2 : ℝ) ≤ 1 then
    (u.level n z.1.1).val.2 (mappingPathLiftFirst (z.1.2,z.2)) else
      (H.level n z.1.1 : C(I,Y.level n)).toFun (mappingPathLiftSecond (z.1.2,z.2)),?_⟩
  apply Continuous.if_le
    (((u.level n).continuous.comp continuous_fst.fst).subtype_val.snd.eval
      (mappingPathLiftFirst.continuous.comp (continuous_fst.snd.prodMk continuous_snd)))
    (((show C(A.level n,C(I,Y.level n)) from H.level n).continuous.comp continuous_fst.fst).eval
      (mappingPathLiftSecond.continuous.comp (continuous_fst.snd.prodMk continuous_snd)))
    ((continuous_const.add continuous_fst.snd.subtype_val).mul continuous_snd.subtype_val)
    continuous_const
  intro z hz
  change (u.level n z.1.1).val.2 (mappingPathLiftFirst (z.1.2,z.2)) =
    (H.level n z.1.1 : C(I,Y.level n)).toFun (mappingPathLiftSecond (z.1.2,z.2))
  rw [mappingPathLiftFirst_join _ _ hz,mappingPathLiftSecond_join _ _ hz]
  exact congrArg (fun k : A ⟶ Y => k.level n z.1.1) h

/-- A levelwise lift retains the original source point and the constructed
extended path. -/
def mappingPathLiftLevel (n : ℕ) : C(A.level n × I,mappingPathLevel f n) := by
  refine ⟨fun z => ⟨((u.level n z.1).val.1,(mappingPathLiftFamily f u H h n).curry z),?_⟩,?_⟩
  · classical
    change (if (1+(z.2 : ℝ))*(0 : ℝ) ≤ 1 then
      (u.level n z.1).val.2 (mappingPathLiftFirst (z.2,0)) else
        (H.level n z.1 : C(I,Y.level n)).toFun (mappingPathLiftSecond (z.2,0))) = f.level n (u.level n z.1).val.1
    simp only [mul_zero,zero_le_one,ite_true,mappingPathLiftFirst_start]
    exact (u.level n z.1).property
  · exact (((u.level n).continuous.comp continuous_fst).subtype_val.fst.prodMk
      (mappingPathLiftFamily f u H h n).curry.continuous).subtype_mk _

/-- An actual strict lift of a prescribed strict prespectrum homotopy along
the endpoint projection of the mapping-path factorization. -/
def mappingPathLift : A ⟶ pathPrespectrum (mappingPath f) where
  level n := (mappingPathLiftLevel f u H h n).curry
  point n := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · change (u.level n (A.level n).point).val.1 = (X.level n).point
      exact congrArg (fun z : mappingPathLevel f n => z.val.1) (u.point n)
    · apply ContinuousMap.ext
      intro t
      classical
      change (if (1+(s : ℝ))*(t : ℝ) ≤ 1 then
        (u.level n (A.level n).point).val.2 (mappingPathLiftFirst (s,t)) else
          (H.level n (A.level n).point : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,t))) = (Y.level n).point
      split_ifs
      · exact congrArg (fun z : mappingPathLevel f n => z.val.2 (mappingPathLiftFirst (s,t))) (u.point n)
      · exact congrArg (fun q : C(I,Y.level n) => q (mappingPathLiftSecond (s,t))) (H.point n)
  bond n a t := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    apply Prod.ext
    · change (u.level (n+1) (A.bond n (a,t))).val.1 = X.bond n ((u.level n a).val.1,t)
      exact congrArg (fun z : mappingPathLevel f (n+1) => z.val.1) (u.bond n a t)
    · apply ContinuousMap.ext
      intro v
      classical
      change (if (1+(s : ℝ))*(v : ℝ) ≤ 1 then
        (u.level (n+1) (A.bond n (a,t))).val.2 (mappingPathLiftFirst (s,v)) else
          (H.level (n+1) (A.bond n (a,t)) : C(I,Y.level (n+1))).toFun (mappingPathLiftSecond (s,v))) =
        Y.bond n ((if (1+(s : ℝ))*(v : ℝ) ≤ 1 then
          (u.level n a).val.2 (mappingPathLiftFirst (s,v)) else
            (H.level n a : C(I,Y.level n)).toFun (mappingPathLiftSecond (s,v))),t)
      split_ifs
      · exact congrArg (fun z : mappingPathLevel f (n+1) => z.val.2 (mappingPathLiftFirst (s,v)))
          (u.bond n a t)
      · exact congrArg (fun q : C(I,Y.level (n+1)) => q (mappingPathLiftSecond (s,v))) (H.bond n a t)

end
end KIP126.StableHomotopy.Implementation.Prespectrum
