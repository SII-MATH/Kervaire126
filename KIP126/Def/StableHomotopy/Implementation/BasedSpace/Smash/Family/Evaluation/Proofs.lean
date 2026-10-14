module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Family.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open scoped unitInterval

@[simp] theorem smashFamily_apply {A B A' B' : BasedSpace.{0}}
    (f : C(A × I,A')) (g : C(B × I,B'))
    (hf : ∀ t, f (A.point,t) = A'.point)
    (hg : ∀ t, g (B.point,t) = B'.point) (a : A) (b : B) (t : I) :
    smashFamily f g hf hg (smashPoint A B a b,t) =
      smashPoint A' B' (f (a,t)) (g (b,t)) :=
  (smashFamily_exists f g hf hg).exists.choose_spec.1 a b t

@[simp] theorem smashFamily_point {A B A' B' : BasedSpace.{0}}
    (f : C(A × I,A')) (g : C(B × I,B'))
    (hf : ∀ t, f (A.point,t) = A'.point)
    (hg : ∀ t, g (B.point,t) = B'.point) (t : I) :
    smashFamily f g hf hg ((A.smash B).point,t) = (A'.smash B').point :=
  (smashFamily_exists f g hf hg).exists.choose_spec.2 t

end KIP126.StableHomotopy.Implementation.BasedSpace
