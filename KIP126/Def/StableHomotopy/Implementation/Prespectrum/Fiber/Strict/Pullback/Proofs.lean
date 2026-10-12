module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Pullback.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[simp] theorem strictFiberPullbackTo_projection {A B Z : Prespectrum.{u}}
    (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiberPullbackTo p g ≫ pullbackFst p (zeroMap zeroPrespectrum B) =
      pullbackFst (pullbackSnd p g) (zeroMap zeroPrespectrum Z) ≫ pullbackFst p g := rfl

@[simp] theorem strictFiberPullbackFrom_projection {A B Z : Prespectrum.{u}}
    (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiberPullbackFrom p g ≫ pullbackFst (pullbackSnd p g) (zeroMap zeroPrespectrum Z) ≫
        pullbackFst p g = pullbackFst p (zeroMap zeroPrespectrum B) := rfl

@[simp] theorem strictFiberPullbackFrom_basepoint {A B Z : Prespectrum.{u}}
    (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiberPullbackFrom p g ≫ pullbackFst (pullbackSnd p g) (zeroMap zeroPrespectrum Z) ≫
      pullbackSnd p g = zeroMap (strictFiber p) Z := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
