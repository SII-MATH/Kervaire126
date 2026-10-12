module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Homotopy.Family.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval

@[simp] theorem spaceSmashPathMap_apply {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    (F : C(A × I,B)) (hF : ∀ t, F (A.point,t) = B.point)
    (H : X ⟶ pathPrespectrum Y) (n : ℕ) (a : A) (x : X.level n) (s : I) :
    (show C(I,(spaceSmash B Y).level n) from
      (spaceSmashPathMap F hF H).level n (BasedSpace.smashPoint A (X.level n) a x)) s =
      BasedSpace.smashPoint B (Y.level n) (F (a,s)) ((show C(I,Y.level n) from H.level n x) s) :=
  BasedSpace.smashFamily_apply F (show C(X.level n,C(I,Y.level n)) from H.level n).uncurry hF
    (fun t => congrArg (fun p : C(I,Y.level n) => p t) (H.point n)) a x s

end KIP126.StableHomotopy.Implementation.Prespectrum
