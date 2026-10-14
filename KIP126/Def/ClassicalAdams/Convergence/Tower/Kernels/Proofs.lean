module

public import KIP126.Def.StableHomotopy.FiniteType.Kernels.Proofs
public import KIP126.Def.ClassicalAdams.TowerLayer.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v

private theorem finite_ker_comp {A B D : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (f : A →+ B) (g : B →+ D) [Finite f.ker] [Finite g.ker] : Finite (g.comp f).ker := by
  classical
  let i : f.ker →+ (g.comp f).ker :=
    { toFun := fun a => ⟨a.val, by change g (f a.val) = 0; rw [a.property, map_zero]⟩
      map_zero' := rfl
      map_add' := by intros; rfl }
  let j : (g.comp f).ker →+ g.ker :=
    { toFun := fun a => ⟨f a.val, a.property⟩
      map_zero' := Subtype.ext f.map_zero
      map_add' := fun a b => Subtype.ext (f.map_add a.val b.val) }
  letI := Fintype.ofFinite f.ker
  letI := Fintype.ofFinite g.ker
  letI := AddGroup.fintypeOfKerLeRange i j (by
    intro a ha
    have hz : f a.val = 0 := congrArg Subtype.val ha
    exact ⟨⟨a.val, hz⟩, rfl⟩)
  infer_instance


variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- A finite homotopy group of the actual Adams layer makes the
corresponding tower-step kernel finite. -/
theorem finite_adamsTowerStep_kernel (n : ℤ) (k : ℕ)
    [Finite (HomotopyGroup (n + 1) (H ⊗ adamsTower unit X k))] :
    Finite (inducedMap (adamsTowerStep unit X k) n).ker := by
  let T := HoCofiberSequence.ofMorphism (adamsTowerStep unit X k)
  let e : T.Z ≅ H ⊗ adamsTower unit X k :=
    cofiberFiberIso (adamsUnit unit (adamsTower unit X k))
  letI : Finite (HomotopyGroup (n + 1) T.Z) :=
    Finite.of_injective (fun a : HomotopyGroup (n + 1) T.Z => a ≫ e.hom)
      (fun _ _ h => (cancel_mono e.hom).mp h)
  exact T.finite_homotopy_kernel n

/-- Finite homotopy groups in all actual Adams layers give finite kernels
for every residual-tower projection to the original spectrum. -/
theorem finite_adamsTowerMap_kernel (n : ℤ)
    [∀ k : ℕ, Finite (HomotopyGroup (n + 1) (H ⊗ adamsTower unit X k))] (k : ℕ) :
    Finite (inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n).ker := by
  induction k with
  | zero =>
      have hi : Function.Injective (inducedMap (adamsTowerMap unit X 0 0 (Nat.zero_le 0)) n) := by
        intro a b h
        simpa [adamsTowerMap_self, inducedMap] using h
      letI : Subsingleton (inducedMap (adamsTowerMap unit X 0 0 (Nat.zero_le 0)) n).ker :=
        ⟨fun a b => Subtype.ext (hi (a.property.trans b.property.symm))⟩
      infer_instance
  | succ k ih =>
      letI := ih
      letI := finite_adamsTowerStep_kernel unit X n k
      have he : inducedMap (adamsTowerMap unit X 0 (k + 1) (Nat.zero_le (k + 1))) n =
          (inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n).comp
            (inducedMap (adamsTowerStep unit X k) n) := by
        ext a
        change a ≫ adamsTowerMap unit X 0 (k + 1) _ =
          (a ≫ adamsTowerStep unit X k) ≫ adamsTowerMap unit X 0 k _
        rw [adamsTowerMap_succ, Category.assoc]
      rw [he]
      exact finite_ker_comp _ _

end KIP126.Classical.Adams
