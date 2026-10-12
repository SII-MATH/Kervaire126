module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Family.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open scoped unitInterval

/-- The unique continuous family on the actual quotient smash. -/
noncomputable def smashFamily {A B A' B' : BasedSpace.{0}}
    (f : C(A × I,A')) (g : C(B × I,B'))
    (hf : ∀ t, f (A.point,t) = A'.point)
    (hg : ∀ t, g (B.point,t) = B'.point) : C((A.smash B) × I,A'.smash B') :=
  (smashFamily_exists f g hf hg).exists.choose

end KIP126.StableHomotopy.Implementation.BasedSpace
