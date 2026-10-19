module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Equivalence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Last-coordinate uncurrying preserves concatenation in every original
cubical coordinate, with no coordinate switch or sign change. -/
theorem loopUncurryLast_transAt (A : BasedSpace.{u}) (r : ℕ) (i : Fin r)
    (p q : GenLoop (Fin r) (loopLevel A) (loopLevel A).point) :
    loopUncurryLast A r (GenLoop.transAt i p q) =
      GenLoop.transAt i.castSucc (loopUncurryLast A r p) (loopUncurryLast A r q) := by
  apply GenLoop.ext
  intro t
  have hupdate (a : I) : (fun j => (Function.update t i.castSucc a) j.castSucc) =
      Function.update (fun j => t j.castSucc) i a := by
    funext j
    simp [Function.update_apply]
  have hlast (a : I) : (Function.update t i.castSucc a) (Fin.last r) = t (Fin.last r) := by
    simp [(Fin.castSucc_ne_last i).symm]
  change (GenLoop.transAt i p q) (fun j => t j.castSucc) (t (Fin.last r)) = _
  simp only [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;>
    change _ = (loopUncurryLast A r _) (Function.update t i.castSucc _) <;>
    simp only [loopUncurryLast, GenLoop.mk_apply, ContinuousMap.coe_mk, hupdate, hlast]

@[simp] theorem stableLoopHomotopyMap_loopClass (X : Prespectrum.{u}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d + n)
    (p : GenLoop (Fin r) ((Prespectrum.loop X).level n) ((Prespectrum.loop X).level n).point) :
    stableLoopHomotopyMap X d (loopClass (Prespectrum.loop X) d n r h p) =
      loopClass X (d+1) n (r+1) (by omega) (loopUncurryLast (X.level n) r p) := rfl

/-- The actual stable loop-degree comparison preserves the original stable
abelian group operations. -/
theorem stableLoopHomotopyMap_add (X : Prespectrum.{u}) (d : ℤ)
    (x y : StableHomotopy (Prespectrum.loop X) d) :
    stableLoopHomotopyMap X d (x + y) =
      stableLoopHomotopyMap X d x + stableLoopHomotopyMap X d y := by
  obtain ⟨k,p,q,rfl,rfl⟩ := exists_stableLevelClass_pair (Prespectrum.loop X) d x y
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      change stableLoopHomotopyMap X d
        (loopClass (Prespectrum.loop X) d _ _ (stableGroup_degree d k) p +
          loopClass (Prespectrum.loop X) d _ _ (stableGroup_degree d k) q) = _
      rw [← loopClass_transAt _ _ _ _ _ (0 : Fin (stableGroupDimension d k)),
        stableLoopHomotopyMap_loopClass, loopUncurryLast_transAt, loopClass_transAt]
      rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
