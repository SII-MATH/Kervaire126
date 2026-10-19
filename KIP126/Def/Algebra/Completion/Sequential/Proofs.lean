module

public import KIP126.Def.Algebra.Completion.Proofs
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Limits.Types.Limits

@[expose] public section

namespace KIP126.Core.Algebra.Filtration.CompletionWitness

open CategoryTheory CategoryTheory.Limits

universe u w

variable {ι : Type w} {A : CategoryTheory.GradedObject ι AddCommGrpCat.{u}}

/-- Unique lifts of compatible elements in the nonnegative quotient sequence
make the full integer-indexed canonical quotient cone limiting. It suffices
to check adjacent compatibility. The forgetful functor reflects the resulting
limit of sets, so no separate additivity proof for the inverse is required. -/
noncomputable def of_unique_nat_lifts (F : Filtration A) (i : ι)
    (hlift : ∀ q : ∀ n : ℕ, F.quotientAt (n : ℤ) i,
      (∀ n : ℕ, F.quotientTransition (show (n : ℤ) ≤ (n + 1 : ℕ) by omega) i
        (q (n + 1)) = q n) →
      ∃! a : A i, ∀ n : ℕ, F.quotientProjection (n : ℤ) i a = q n) :
    CompletionWitness F i := by
  classical
  refine ⟨isLimitOfReflects (forget AddCommGrpCat) ?_⟩
  apply Classical.choice
  apply (Types.isLimit_iff _).2
  intro q hq
  have hc {s t : ℤ} (hst : t ≤ s) :
      F.quotientTransition hst i (q (OrderDual.toDual s)) = q (OrderDual.toDual t) :=
    hq (homOfLE hst : OrderDual.toDual s ⟶ OrderDual.toDual t)
  obtain ⟨a, ha, hu⟩ := hlift (fun n => q (OrderDual.toDual (n : ℤ)))
    (fun n => hc (show (n : ℤ) ≤ (n + 1 : ℕ) by omega))
  refine ⟨a, ?_, ?_⟩
  · intro s
    let n : ℕ := (OrderDual.ofDual s).toNat
    have hs : OrderDual.ofDual s ≤ (n : ℤ) := by dsimp [n]; omega
    change F.quotientProjection (OrderDual.ofDual s) i a = q s
    calc
      F.quotientProjection (OrderDual.ofDual s) i a =
          F.quotientTransition hs i (F.quotientProjection (n : ℤ) i a) := by
        exact (congrArg (fun f : A i ⟶ F.quotientAt (OrderDual.ofDual s) i => f a)
          (F.quotientProjection_transition hs i)).symm
      _ = F.quotientTransition hs i (q (OrderDual.toDual (n : ℤ))) := by rw [ha n]
      _ = q s := hc hs
  · intro b hb
    exact hu b (fun n => hb (OrderDual.toDual (n : ℤ)))

section Module

universe v

variable {R : Type u} [Ring R]
variable {A : CategoryTheory.GradedObject ι (ModuleCat.{v} R)}

/-- Unique lifts of compatible elements in the nonnegative quotient sequence
make the full integer-indexed canonical quotient cone limiting. It suffices
to check adjacent compatibility. The forgetful functor reflects the resulting
limit of sets, so no separate additivity proof for the inverse is required. -/
noncomputable def of_unique_nat_module_lifts (F : Filtration A) (i : ι)
    (hlift : ∀ q : ∀ n : ℕ, F.quotientAt (n : ℤ) i,
      (∀ n : ℕ, F.quotientTransition (show (n : ℤ) ≤ (n + 1 : ℕ) by omega) i
        (q (n + 1)) = q n) →
      ∃! a : A i, ∀ n : ℕ, F.quotientProjection (n : ℤ) i a = q n) :
    CompletionWitness F i := by
  classical
  refine ⟨isLimitOfReflects (forget (ModuleCat R)) ?_⟩
  apply Classical.choice
  apply (Types.isLimit_iff _).2
  intro q hq
  have hc {s t : ℤ} (hst : t ≤ s) :
      F.quotientTransition hst i (q (OrderDual.toDual s)) = q (OrderDual.toDual t) :=
    hq (homOfLE hst : OrderDual.toDual s ⟶ OrderDual.toDual t)
  obtain ⟨a, ha, hu⟩ := hlift (fun n => q (OrderDual.toDual (n : ℤ)))
    (fun n => hc (show (n : ℤ) ≤ (n + 1 : ℕ) by omega))
  refine ⟨a, ?_, ?_⟩
  · intro s
    let n : ℕ := (OrderDual.ofDual s).toNat
    have hs : OrderDual.ofDual s ≤ (n : ℤ) := by dsimp [n]; omega
    change F.quotientProjection (OrderDual.ofDual s) i a = q s
    calc
      F.quotientProjection (OrderDual.ofDual s) i a =
          F.quotientTransition hs i (F.quotientProjection (n : ℤ) i a) := by
        exact (congrArg (fun f : A i ⟶ F.quotientAt (OrderDual.ofDual s) i => f a)
          (F.quotientProjection_transition hs i)).symm
      _ = F.quotientTransition hs i (q (OrderDual.toDual (n : ℤ))) := by rw [ha n]
      _ = q s := hc hs
  · intro b hb
    exact hu b (fun n => hb (OrderDual.toDual (n : ℤ)))

end Module

end KIP126.Core.Algebra.Filtration.CompletionWitness

namespace KIP126.Core.Algebra.Filtration

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {R : Type u} [Ring R]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι (ModuleCat.{v} R)}

/-- The canonical categorical quotient projection kills exactly the elements
of the specified filtration submodule. -/
lemma quotientProjection_eq_zero_iff (F : Filtration A) (s : ℤ) (i : ι) (a : A i) :
    F.quotientProjection s i a = 0 ↔
      a ∈ ModuleCat.subobjectModule (A i) (F.F s i) := by
  let e := ModuleCat.cokernelIsoRangeQuotient (F.F s i).arrow
  have hi : Function.Injective e.hom := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change cokernel.π (F.F s i).arrow a = 0 ↔
    a ∈ LinearMap.range (F.F s i).arrow.hom
  rw [← Submodule.Quotient.mk_eq_zero]
  have he : e.hom (cokernel.π (F.F s i).arrow a) =
      (Submodule.Quotient.mk a : A i ⧸ LinearMap.range (F.F s i).arrow.hom) :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply _ a
  rw [← he]
  exact ⟨fun h => by rw [h]; exact e.hom.hom.map_zero,
    fun h => hi (h.trans e.hom.hom.map_zero.symm)⟩

end KIP126.Core.Algebra.Filtration
