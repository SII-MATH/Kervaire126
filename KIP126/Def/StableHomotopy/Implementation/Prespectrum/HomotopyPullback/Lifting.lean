module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Path.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Lifting.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Path.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- An actual strict homotopy lifting for the second homotopy-pullback
projection, obtained by lifting its image in the common target. -/
noncomputable def homotopyPullbackLiftHomotopy {A X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (u : A ⟶ homotopyPullback f g) (H : A ⟶ pathPrespectrum Z)
    (h : u ≫ homotopyPullbackSnd f g = H ≫ pathEvaluation Z 0) :
    A ⟶ pathPrespectrum (homotopyPullback f g) := by
  let v := u ≫ pullbackFst (mappingPathProjection f) g
  let G := H ≫ pathMap g
  have hv : v ≫ mappingPathProjection f = G ≫ pathEvaluation Y 0 := by
    dsimp only [v, G]
    rw [Category.assoc, pullbackFst_comp, ← Category.assoc]
    change (u ≫ homotopyPullbackSnd f g) ≫ g = (H ≫ pathMap g) ≫ pathEvaluation Y 0
    rw [h, Category.assoc, Category.assoc, pathMap_evaluation]
  exact pullbackPathLift (mappingPathLift f v G hv) H (fun s => by
    rw [mappingPathLift_projection]
    dsimp only [G]
    rw [Category.assoc, pathMap_evaluation])

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

@[simp] theorem homotopyPullbackLiftHomotopy_zero {A X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (u : A ⟶ homotopyPullback f g)
    (H : A ⟶ pathPrespectrum Z) (h : u ≫ homotopyPullbackSnd f g = H ≫ pathEvaluation Z 0) :
    homotopyPullbackLiftHomotopy f g u H h ≫ pathEvaluation (homotopyPullback f g) 0 = u := by
  apply pullbackHom_ext
  · dsimp only [homotopyPullbackLiftHomotopy]
    rw [Category.assoc, pullbackPathLift_fst, mappingPathLift_zero]
  · dsimp only [homotopyPullbackLiftHomotopy]
    rw [Category.assoc, pullbackPathLift_snd]
    exact h.symm

/-- The lifted homotopy has precisely the prescribed projection at every time. -/
@[simp] theorem homotopyPullbackLiftHomotopy_projection {A X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) (u : A ⟶ homotopyPullback f g)
    (H : A ⟶ pathPrespectrum Z) (h : u ≫ homotopyPullbackSnd f g = H ≫ pathEvaluation Z 0)
    (s : I) :
    (homotopyPullbackLiftHomotopy f g u H h ≫ pathEvaluation (homotopyPullback f g) s) ≫
        homotopyPullbackSnd f g = H ≫ pathEvaluation Z s := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum

end
