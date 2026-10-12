module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The original cylinder retains its entire path from the free source
inclusion to the attached target image. -/
noncomputable def mappingCylinderPath {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X ⟶ pathPrespectrum (mappingCylinder f) where
  level n := ((mappingCylinderMk f n).comp ⟨Sum.inl,continuous_inl⟩).curry
  point n := by
    apply ContinuousMap.ext
    intro t
    exact mappingCylinderMk_point f n t
  bond _ _ _ := rfl

/-- A strict target map and a retained path ending at its composite
descend through the actual reduced mapping-cylinder quotient. -/
noncomputable def mappingCylinderDesc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (H : X ⟶ pathPrespectrum Z)
    (h₁ : H ≫ pathEvaluation Z 1 = f ≫ a) : mappingCylinder f ⟶ Z := by
  let raw (n : ℕ) : C(mappingCylinderRaw f n,Z.level n) :=
    ⟨Sum.elim (show C(X.level n,C(I,Z.level n)) from H.level n).uncurry (a.level n),
      (show C(X.level n,C(I,Z.level n)) from H.level n).uncurry.continuous.sumElim
        (a.level n).continuous⟩
  have hp (n : ℕ) (t : I) : raw n (.inl ((X.level n).point,t)) =
      raw n (.inr (Y.level n).point) :=
    (congrArg (fun p : C(I,Z.level n) => p t) (H.point n)).trans (a.point n).symm
  have ht (n : ℕ) (x : X.level n) : raw n (.inl (x,1)) = raw n (.inr (f.level n x)) :=
    congrArg (fun e : X ⟶ Z => e.level n x) h₁
  refine {
    level n := mappingCylinderLift f n (raw n) (hp n) (ht n)
    point n := a.point n
    bond := ?_ }
  intro n z t
  obtain ⟨q,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases q with ⟨x,s⟩ | y
  · exact congrArg (fun p : C(I,Z.level (n+1)) => p s) (H.bond n x t)
  · exact a.bond n y t

end KIP126.StableHomotopy.Implementation.Prespectrum
