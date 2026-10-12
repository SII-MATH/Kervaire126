module

public import KIP126.Def.Algebra.DirectSequence.Proofs
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

/-- The actual algebraic direct sum of the specified abelian-group sequence. -/
def directSequenceSum (F : ℕ ⥤ AddCommGrpCat.{u}) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (⨁ n, F.obj n)

/-- The actual coordinate inclusions into that algebraic direct sum. -/
def directSequenceSumInclusion (F : ℕ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    F.obj n ⟶ directSequenceSum F :=
  AddCommGrpCat.ofHom (DirectSum.of (fun n => F.obj n) n)

/-- The actual direct-sum difference morphism of the categorical sequence. -/
def directSequenceDifference (F : ℕ ⥤ AddCommGrpCat.{u}) :
    directSequenceSum F ⟶ directSequenceSum F :=
  AddCommGrpCat.ofHom (directSequenceOneSubShift
    (fun n => (F.map (homOfLE (Nat.le_succ n))).hom))

/-- The cokernel of the actual direct-sum difference, with its genuine
compatible maps from the original abelian groups. -/
def directSequenceCokernelCocone (F : ℕ ⥤ AddCommGrpCat.{u}) : Cocone F where
  pt := (AddCommGrpCat.cokernelCocone (directSequenceDifference F)).pt
  ι := NatTrans.ofSequence
    (fun n => directSequenceSumInclusion F n ≫
      (AddCommGrpCat.cokernelCocone (directSequenceDifference F)).π) (by
      intro n
      apply AddCommGrpCat.ext
      intro x
      have h := ConcreteCategory.congr_hom
        (CokernelCofork.condition (AddCommGrpCat.cokernelCocone (directSequenceDifference F)))
        (DirectSum.of (fun n => F.obj n) n x)
      change (AddCommGrpCat.cokernelCocone (directSequenceDifference F)).π
        (directSequenceOneSubShift (fun n => (F.map (homOfLE (Nat.le_succ n))).hom)
          (DirectSum.of (fun n => F.obj n) n x)) = 0 at h
      simp only [directSequenceOneSubShift, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
        directSequenceShift, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply] at h
      exact (sub_eq_zero.mp h).symm)

end KIP126.Foundation
