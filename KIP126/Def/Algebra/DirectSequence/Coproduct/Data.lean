module

public import KIP126.Def.Algebra.DirectSequence.Category.Proofs
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits

universe u

/-- The coordinate cofan of the actual direct sum of the sequence. -/
def directSequenceSumCofan (F : ℕ ⥤ AddCommGrpCat.{u}) : Cofan F.obj :=
  Cofan.mk (directSequenceSum F) (directSequenceSumInclusion F)

section Cokernel

variable {C : Type*} [Category C] [Preadditive C]

/-- A cokernel of an adjacent difference has the specified compatible
maps from the original sequence. -/
def sequenceCokernelCocone (F : ℕ ⥤ C) (c : Cofan F.obj) (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ c.inj (n+1))
    (q : CokernelCofork d) : Cocone F where
  pt := q.pt
  ι := NatTrans.ofSequence (fun n => c.inj n ≫ q.π) (by
    intro n
    have h := congrArg (fun f => c.inj n ≫ f) q.condition
    rw [comp_zero, ← Category.assoc, hd, Preadditive.sub_comp] at h
    change F.map (homOfLE (Nat.le_succ n)) ≫ (c.inj (n+1) ≫ q.π) =
      (c.inj n ≫ q.π) ≫ 𝟙 q.pt
    simpa only [Category.assoc, Category.comp_id] using (sub_eq_zero.mp h).symm)

end Cokernel

end KIP126.Foundation
