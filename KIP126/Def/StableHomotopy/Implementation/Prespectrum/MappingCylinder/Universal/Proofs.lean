module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Universal.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderPath_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderPath f ≫ pathEvaluation (mappingCylinder f) 0 =
      mappingCylinderInclusion f := rfl

@[simp] theorem mappingCylinderPath_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderPath f ≫ pathEvaluation (mappingCylinder f) 1 =
      f ≫ mappingCylinderSection f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  exact mappingCylinderMk_top f n

@[reassoc] theorem mappingCylinderSection_desc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (H : X ⟶ pathPrespectrum Z)
    (h₁ : H ≫ pathEvaluation Z 1 = f ≫ a) :
    mappingCylinderSection f ≫ mappingCylinderDesc f a H h₁ = a := rfl

@[reassoc] theorem mappingCylinderPath_desc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (H : X ⟶ pathPrespectrum Z)
    (h₁ : H ≫ pathEvaluation Z 1 = f ≫ a) :
    mappingCylinderPath f ≫ pathMap (mappingCylinderDesc f a H h₁) = H := rfl

@[reassoc] theorem mappingCylinderInclusion_desc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    (a : Y ⟶ Z) (H : X ⟶ pathPrespectrum Z)
    (h₁ : H ≫ pathEvaluation Z 1 = f ≫ a) :
    mappingCylinderInclusion f ≫ mappingCylinderDesc f a H h₁ =
      H ≫ pathEvaluation Z 0 := rfl

/-- The actual target and retained full cylinder path determine maps
out of the original point-set mapping cylinder. -/
theorem mappingCylinderHom_ext {X Y Z : Prespectrum.{u}} (f : X ⟶ Y)
    {a b : mappingCylinder f ⟶ Z}
    (h : mappingCylinderSection f ≫ a = mappingCylinderSection f ≫ b)
    (k : mappingCylinderPath f ≫ pathMap a = mappingCylinderPath f ≫ pathMap b) :
    a = b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨q,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases q with ⟨x,t⟩ | y
  · exact congrArg (fun e : X ⟶ pathPrespectrum Z =>
      (show C(I,Z.level n) from e.level n x) t) k
  · exact congrArg (fun e : Y ⟶ Z => e.level n y) h

end KIP126.StableHomotopy.Implementation.Prespectrum
