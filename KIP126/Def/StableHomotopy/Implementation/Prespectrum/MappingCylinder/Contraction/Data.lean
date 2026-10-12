module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Move a cylinder point towards its attached end, fixing the target. -/
noncomputable def mappingCylinderRawContraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingCylinderRaw f n,C(I,mappingCylinderLevel f n)) := by
  let a : C(X.level n × I,C(I,mappingCylinderLevel f n)) :=
    (⟨fun z => mappingCylinderMk f n (.inl (z.1.1,max z.1.2 z.2)),
      (mappingCylinderMk f n).continuous.comp
        (continuous_inl.comp (continuous_fst.fst.prodMk
          (continuous_fst.snd.max continuous_snd)))⟩ :
      C((X.level n × I) × I,mappingCylinderLevel f n)).curry
  let b : C(Y.level n,C(I,mappingCylinderLevel f n)) :=
    (⟨fun z => mappingCylinderMk f n (.inr z.1),
      (mappingCylinderMk f n).continuous.comp (continuous_inr.comp continuous_fst)⟩ :
      C(Y.level n × I,mappingCylinderLevel f n)).curry
  exact ⟨Sum.elim a b,a.continuous.sumElim b.continuous⟩

/-- The actual based deformation of the reduced mapping cylinder onto its target. -/
noncomputable def mappingCylinderContraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    C(mappingCylinderLevel f n × I,mappingCylinderLevel f n) :=
  (mappingCylinderLift f n (mappingCylinderRawContraction f n)
    (by
      intro s
      apply ContinuousMap.ext
      intro t
      change mappingCylinderMk f n (.inl ((X.level n).point,max s t)) = _
      exact mappingCylinderMk_point f n _)
    (by
      intro x
      apply ContinuousMap.ext
      intro t
      change mappingCylinderMk f n (.inl (x,max 1 t)) = _
      rw [max_eq_left (show t ≤ (1 : I) from t.property.2)]
      exact mappingCylinderMk_top f n x)).uncurry

end KIP126.StableHomotopy.Implementation.Prespectrum
