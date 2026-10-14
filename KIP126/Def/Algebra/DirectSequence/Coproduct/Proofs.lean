module

public import KIP126.Def.Algebra.DirectSequence.Coproduct.Data

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

set_option backward.isDefEq.respectTransparency false

/-- The algebraic direct sum is the categorical coproduct, with the same
specified coordinate inclusions. -/
noncomputable def directSequenceSumCofan_isColimit (F : ℕ ⥤ AddCommGrpCat.{u}) :
    IsColimit (directSequenceSumCofan F) := by
  refine Cofan.IsColimit.mk _
    (fun c => AddCommGrpCat.ofHom
      (DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.inj n).hom))) ?_ ?_
  · intro c n
    apply AddCommGrpCat.ext
    intro x
    change DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.inj n).hom)
      (DirectSum.of (fun n => F.obj n) n x) = _
    rw [DirectSum.toAddMonoid_of]
  · intro c m hm
    apply AddCommGrpCat.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      change m (DirectSum.of (fun n => F.obj n) n x) =
        DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.inj n).hom)
          (DirectSum.of (fun n => F.obj n) n x)
      rw [DirectSum.toAddMonoid_of]
      exact ConcreteCategory.congr_hom (hm n) x
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual difference restricts to the expected adjacent difference
on each summand. -/
@[reassoc]
theorem directSequenceSumInclusion_difference (F : ℕ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    directSequenceSumInclusion F n ≫ directSequenceDifference F =
      directSequenceSumInclusion F n -
        F.map (homOfLE (Nat.le_succ n)) ≫ directSequenceSumInclusion F (n+1) := by
  apply AddCommGrpCat.ext
  intro x
  change directSequenceOneSubShift (fun n => (F.map (homOfLE (Nat.le_succ n))).hom)
    (DirectSum.of (fun n => F.obj n) n x) = _
  simp only [directSequenceOneSubShift, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    directSequenceShift, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
  rfl

/-- On any actual coproduct of an abelian-group sequence, a morphism having
the adjacent-difference coordinates is a monomorphism. -/
theorem sequenceDifference_mono_of_isColimit (F : ℕ ⥤ AddCommGrpCat.{u})
    (c : Cofan F.obj) (hc : IsColimit c) (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ c.inj (n+1)) : Mono d := by
  let e := hc.coconePointUniqueUpToIso (directSequenceSumCofan_isColimit F)
  have he (n : ℕ) : c.inj n ≫ e.hom = directSequenceSumInclusion F n :=
    hc.fac _ ⟨n⟩
  have h : d ≫ e.hom = e.hom ≫ directSequenceDifference F := by
    apply Cofan.IsColimit.hom_ext hc
    intro n
    rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc, he, he,
      ← Category.assoc, he, directSequenceSumInclusion_difference]
  haveI : Mono (d ≫ e.hom) := by
    rw [h]
    infer_instance
  exact mono_of_mono d e.hom

section Cokernel

variable {C : Type*} [Category C] [Preadditive C]

/-- The cokernel of the adjacent difference on an actual coproduct is the
colimit of the original sequence, in every preadditive category. -/
noncomputable def sequenceCokernelCocone_isColimit (F : ℕ ⥤ C)
    (c : Cofan F.obj) (hc : IsColimit c) (d : c.pt ⟶ c.pt)
    (hd : ∀ n, c.inj n ≫ d = c.inj n -
      F.map (homOfLE (Nat.le_succ n)) ≫ c.inj (n+1))
    (q : CokernelCofork d) (hq : IsColimit q) :
    IsColimit (sequenceCokernelCocone F c d hd q) := by
  let a (s : Cocone F) : c.pt ⟶ s.pt := hc.desc (Cofan.mk s.pt s.ι.app)
  have ha (s : Cocone F) : d ≫ a s = 0 := by
    apply Cofan.IsColimit.hom_ext hc
    intro n
    rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc]
    simp only [a, Cofan.IsColimit.inj_desc, comp_zero]
    exact sub_eq_zero.mpr (s.w (homOfLE (Nat.le_succ n))).symm
  refine {
    desc := fun s => hq.desc (CokernelCofork.ofπ (a s) (ha s))
    fac := ?_
    uniq := ?_ }
  · intro s n
    change (c.inj n ≫ q.π) ≫ _ = _
    rw [Category.assoc, Cofork.IsColimit.π_desc]
    exact hc.fac (Cofan.mk s.pt s.ι.app) ⟨n⟩
  · intro s m hm
    apply Cofork.IsColimit.hom_ext hq
    rw [Cofork.IsColimit.π_desc]
    apply Cofan.IsColimit.hom_ext hc
    intro n
    rw [← Category.assoc]
    change (sequenceCokernelCocone F c d hd q).ι.app n ≫ m = c.inj n ≫ a s
    rw [hm n]
    exact (hc.fac (Cofan.mk s.pt s.ι.app) ⟨n⟩).symm

end Cokernel

end KIP126.Foundation
