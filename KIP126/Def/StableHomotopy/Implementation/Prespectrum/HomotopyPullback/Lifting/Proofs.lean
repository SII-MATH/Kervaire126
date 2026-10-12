module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyPullback.Lifting.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Pullback.Path.Proofs

@[expose] public section

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
