module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

@[simp] theorem pathMap_id (X : Prespectrum.{u}) : pathMap (𝟙 X) = 𝟙 (pathPrespectrum X) := rfl

@[simp] theorem pathMap_comp {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pathMap (f ≫ g) = pathMap f ≫ pathMap g := rfl

@[simp, reassoc] theorem pathMap_evaluation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (s : I) :
    pathMap f ≫ pathEvaluation Y s = pathEvaluation X s ≫ f := rfl

@[simp, reassoc] theorem pathConstant_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    pathConstant X ≫ pathMap f = f ≫ pathConstant Y := rfl

/-- All time evaluations together detect equality of strict path maps. -/
theorem pathHom_ext {A X : Prespectrum.{u}} (H K : A ⟶ pathPrespectrum X)
    (h : ∀ s : I, H ≫ pathEvaluation X s = K ≫ pathEvaluation X s) : H = K := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro s
  exact congrArg (fun f : A ⟶ X => f.level n a) (h s)

end KIP126.StableHomotopy.Implementation.Prespectrum
