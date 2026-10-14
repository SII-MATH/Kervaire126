module

public import KIP126.Def.Algebra.DirectSequence.Category.Data

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual difference morphism is a monomorphism for every abelian-group sequence. -/
instance directSequenceDifference_mono (F : ℕ ⥤ AddCommGrpCat.{u}) :
    Mono (directSequenceDifference F) :=
  (AddCommGrpCat.mono_iff_injective _).mpr (directSequenceOneSubShift_injective _)

/-- The actual cokernel of `1 - shift` is the genuine colimit of the
original abelian-group sequence, with its specified coordinate maps. -/
noncomputable def directSequenceCokernelCocone_isColimit (F : ℕ ⥤ AddCommGrpCat.{u}) :
    IsColimit (directSequenceCokernelCocone F) := by
  let a (c : Cocone F) : directSequenceSum F ⟶ c.pt :=
    AddCommGrpCat.ofHom (DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.ι.app n).hom))
  have ha (c : Cocone F) : directSequenceDifference F ≫ a c = 0 := by
    apply AddCommGrpCat.ext
    intro x
    change (a c) (directSequenceOneSubShift
      (fun n => (F.map (homOfLE (Nat.le_succ n))).hom) x) = 0
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      simp only [directSequenceOneSubShift, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
        directSequenceShift, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, map_sub]
      apply sub_eq_zero.mpr
      change DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.ι.app n).hom)
          (DirectSum.of (fun n => F.obj n) n x) =
        DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.ι.app n).hom)
          (DirectSum.of (fun n => F.obj n) (n+1)
            (F.map (homOfLE (Nat.le_succ n)) x))
      rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
      exact (ConcreteCategory.congr_hom (c.w (homOfLE (Nat.le_succ n))) x).symm

    | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  let hq := AddCommGrpCat.cokernelIsColimit (directSequenceDifference F)
  refine {
    desc := fun c => hq.desc (CokernelCofork.ofπ (a c) (ha c))
    fac := ?_
    uniq := ?_ }
  · intro c n
    change (directSequenceSumInclusion F n ≫
      (AddCommGrpCat.cokernelCocone (directSequenceDifference F)).π) ≫ _ = _
    rw [Category.assoc, Cofork.IsColimit.π_desc]
    apply AddCommGrpCat.ext
    intro x
    change DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.ι.app n).hom)
      (DirectSum.of (fun n => F.obj n) n x) = _
    rw [DirectSum.toAddMonoid_of]
  · intro c m hm
    apply Cofork.IsColimit.hom_ext hq
    rw [Cofork.IsColimit.π_desc]
    apply AddCommGrpCat.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      change m ((AddCommGrpCat.cokernelCocone (directSequenceDifference F)).π
        (DirectSum.of (fun n => F.obj n) n x)) =
        DirectSum.toAddMonoid (γ := c.pt) (fun n => (c.ι.app n).hom)
          (DirectSum.of (fun n => F.obj n) n x)
      rw [DirectSum.toAddMonoid_of]
      exact ConcreteCategory.congr_hom (hm n) x
    | add x y hx hy => simp only [map_add, hx, hy]

end KIP126.Foundation
