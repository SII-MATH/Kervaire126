module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Smash an actual based family of space maps with an actual strict
path-valued spectrum map. The same homotopy parameter is retained at
every spectrum level. -/
noncomputable def spaceSmashPathMap {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    (F : C(A × I,B)) (hF : ∀ t, F (A.point,t) = B.point)
    (H : X ⟶ pathPrespectrum Y) : spaceSmash A X ⟶ pathPrespectrum (spaceSmash B Y) := by
  let K (n : ℕ) : C((A.smash (X.level n)) × I,B.smash (Y.level n)) :=
    BasedSpace.smashFamily F (show C(X.level n,C(I,Y.level n)) from H.level n).uncurry hF
      (fun t => congrArg (fun p : C(I,Y.level n) => p t) (H.point n))
  have hK (n : ℕ) (a : A) (x : X.level n) (s : I) :
      K n (BasedSpace.smashPoint A (X.level n) a x,s) =
        BasedSpace.smashPoint B (Y.level n) (F (a,s)) ((show C(I,Y.level n) from H.level n x) s) :=
    BasedSpace.smashFamily_apply F (show C(X.level n,C(I,Y.level n)) from H.level n).uncurry hF
      (fun t => congrArg (fun p : C(I,Y.level n) => p t) (H.point n)) a x s
  refine {
    level n := (K n).curry
    point n := ?_
    bond n z t := ?_ }
  · apply ContinuousMap.ext
    intro s
    exact BasedSpace.smashFamily_point F
      (show C(X.level n,C(I,Y.level n)) from H.level n).uncurry hF
      (fun t => congrArg (fun p : C(I,Y.level n) => p t) (H.point n)) s
  · apply ContinuousMap.ext
    intro s
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change K (n+1) ((spaceSmash A X).bond n (BasedSpace.smashPoint A (X.level n) a x,t),s) =
      (spaceSmash B Y).bond n (K n (BasedSpace.smashPoint A (X.level n) a x,s),t)
    rw [spaceSmash_bond,hK,hK,spaceSmash_bond]
    exact congrArg (fun y => BasedSpace.smashPoint B (Y.level (n+1)) (F (a,s)) y)
      (congrArg (fun p : C(I,Y.level (n+1)) => p s) (H.bond n x t))

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
