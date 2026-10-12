module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Homotopy.Family.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- Actual relative homotopies of the space factor and strict homotopies
of the spectrum factor smash to an actual strict homotopy. -/
noncomputable def spaceSmashHomotopy {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    {a b : A ⟶ B} {f g : X ⟶ Y}
    (H : ContinuousMap.HomotopyRel a.map b.map {A.point}) (K : StrictHomotopy f g) :
    StrictHomotopy (spaceSmashMap a f) (spaceSmashMap b g) := by
  let F : C(A × I,B) := ⟨fun p => H (p.2,p.1),H.continuous.comp continuous_swap⟩
  have hF (t : I) : F (A.point,t) = B.point :=
    (H.eq_fst t (Set.mem_singleton _)).trans a.point
  refine { hom := spaceSmashPathMap F hF K.hom, zero := ?_, one := ?_ }
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨c,x⟩
    change (show C(I,(spaceSmash B Y).level n) from
      (spaceSmashPathMap F hF K.hom).level n (BasedSpace.smashPoint A (X.level n) c x)) 0 =
      (spaceSmashMap a f).level n (BasedSpace.smashPoint A (X.level n) c x)
    rw [spaceSmashPathMap_apply,spaceSmashMap_apply]
    change BasedSpace.smashPoint B (Y.level n) (H (0,c)) ((show C(I,Y.level n) from K.hom.level n x) 0) = _
    rw [H.apply_zero]
    exact congrArg (BasedSpace.smashPoint B (Y.level n) (a.map c))
      (congrArg (fun e : X ⟶ Y => e.level n x) K.zero)
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨c,x⟩
    change (show C(I,(spaceSmash B Y).level n) from
      (spaceSmashPathMap F hF K.hom).level n (BasedSpace.smashPoint A (X.level n) c x)) 1 =
      (spaceSmashMap b g).level n (BasedSpace.smashPoint A (X.level n) c x)
    rw [spaceSmashPathMap_apply,spaceSmashMap_apply]
    change BasedSpace.smashPoint B (Y.level n) (H (1,c)) ((show C(I,Y.level n) from K.hom.level n x) 1) = _
    rw [H.apply_one]
    exact congrArg (BasedSpace.smashPoint B (Y.level n) (b.map c))
      (congrArg (fun e : X ⟶ Y => e.level n x) K.one)

end KIP126.StableHomotopy.Implementation.Prespectrum
