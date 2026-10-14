module

public import KIP126.Def.StableHomotopy.InverseSequence.Predicates
public import KIP126.Def.StableHomotopy.Context.Proofs
public import KIP126.Def.Algebra.InverseSequence.Finite.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Adjunction.Limits

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

set_option backward.isDefEq.respectTransparency false

universe u v

section Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasProductsOfShape ℕ C]

/-- The projections of a Milnor triangle form a compatible cone. -/
theorem SequentialHomotopyLimit.π_step {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) (n : ℕ) :
    H.π (n + 1) ≫ D.step n = H.π n := by
  have h := CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ _ H.distinguished
  have hn := congrArg (fun f => f ≫ Pi.π D.obj n) h
  change (H.toProduct ≫ (𝟙 _ - D.shiftMap)) ≫ Pi.π D.obj n = _ at hn
  simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
    Category.assoc, InverseSequence.shiftMap, Pi.lift_π, zero_comp] at hn
  simpa only [SequentialHomotopyLimit.π, Category.assoc] using (sub_eq_zero.mp hn).symm

/-- The explicit `1 - shift` condition means that the homotopy-limit
object vanishes; it is not a condition on an ordinary inverse limit. -/
theorem SequentialHomotopyLimit.isZero_iff {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) : IsZero L ↔ D.IsAcyclic := by
  exact CategoryTheory.Pretriangulated.Triangle.isZero₁_iff_isIso₂
    (CategoryTheory.Pretriangulated.Triangle.mk H.toProduct D.oneSubShift H.boundary)
    H.distinguished

/-- A commuting family of stage isomorphisms conjugates the actual Milnor map. -/
theorem InverseSequence.oneSubShift_conjugate {D E : InverseSequence C}
    (e : ∀ n, D.obj n ≅ E.obj n)
    (h : ∀ n, (e (n + 1)).hom ≫ E.step n = D.step n ≫ (e n).hom) :
    E.oneSubShift = (Pi.mapIso e).inv ≫ D.oneSubShift ≫ (Pi.mapIso e).hom := by
  apply (cancel_epi (Pi.mapIso e).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply Pi.hom_ext
  intro n
  simp only [InverseSequence.oneSubShift, InverseSequence.shiftMap,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc, Pi.mapIso_hom_π,
    Pi.mapIso_hom_π_assoc]
  rw [h]

/-- Vanishing of a sequential homotopy limit is invariant under an actual
isomorphism of sequences, with the same specified products. -/
theorem InverseSequence.isAcyclic_iff_of_iso {D E : InverseSequence C}
    (e : ∀ n, D.obj n ≅ E.obj n)
    (h : ∀ n, (e (n + 1)).hom ≫ E.step n = D.step n ≫ (e n).hom) :
    D.IsAcyclic ↔ E.IsAcyclic := by
  have hc := oneSubShift_conjugate e h
  constructor
  · intro hD
    letI : IsIso D.oneSubShift := hD
    change IsIso E.oneSubShift
    rw [hc]
    infer_instance
  · intro hE
    letI : IsIso E.oneSubShift := hE
    have hd : D.oneSubShift =
        (Pi.mapIso e).hom ≫ E.oneSubShift ≫ (Pi.mapIso e).inv := by
      rw [hc]
      simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    change IsIso D.oneSubShift
    rw [hd]
    infer_instance

/-- An additive product-preserving functor carries the actual Milnor map to
the Milnor map of its image sequence through the canonical product comparison. -/
theorem InverseSequence.map_oneSubShift (D : InverseSequence C) (F : C ⥤ C)
    [F.Additive] [PreservesLimit (Discrete.functor D.obj) F] :
    (D.map F).oneSubShift =
      (PreservesProduct.iso F D.obj).inv ≫ F.map D.oneSubShift ≫
        (PreservesProduct.iso F D.obj).hom := by
  apply (cancel_epi (PreservesProduct.iso F D.obj).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  apply Pi.hom_ext
  intro n
  simp only [InverseSequence.oneSubShift, InverseSequence.shiftMap,
    InverseSequence.map,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc, Pi.lift_π,
    PreservesProduct.iso_hom, piComparison_comp_π, piComparison_comp_π_assoc,
    Functor.map_sub]
  change _ - F.map (Pi.π D.obj (n + 1)) ≫ F.map (D.step n) =
    _ - F.map (Pi.lift (fun n => Pi.π D.obj (n + 1) ≫ D.step n)) ≫
      F.map (Pi.π D.obj n)
  simp only [← F.map_comp, Pi.lift_π, Category.id_comp]

/-- Acyclicity is preserved by an additive functor preserving countable
products. This assertion uses the canonical comparison with those products. -/
theorem InverseSequence.IsAcyclic.map {D : InverseSequence C} (hD : D.IsAcyclic)
    (F : C ⥤ C) [F.Additive] [PreservesLimit (Discrete.functor D.obj) F] :
    (D.map F).IsAcyclic := by
  letI : IsIso D.oneSubShift := hD
  change IsIso (D.map F).oneSubShift
  rw [D.map_oneSubShift F]
  infer_instance

/-- If the functor also reflects isomorphisms, it reflects acyclicity. -/
theorem InverseSequence.map_isAcyclic_iff (D : InverseSequence C) (F : C ⥤ C)
    [F.Additive] [PreservesLimit (Discrete.functor D.obj) F] [F.ReflectsIsomorphisms] :
    (D.map F).IsAcyclic ↔ D.IsAcyclic := by
  refine ⟨fun hD => ?_, fun hD => hD.map F⟩
  letI : IsIso (D.map F).oneSubShift := hD
  have h : F.map D.oneSubShift =
      (PreservesProduct.iso F D.obj).hom ≫ (D.map F).oneSubShift ≫
        (PreservesProduct.iso F D.obj).inv := by
    rw [D.map_oneSubShift F]
    simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  haveI : IsIso (F.map D.oneSubShift) := by rw [h]; infer_instance
  exact isIso_of_reflects_iso D.oneSubShift F

/-- Every integer shift preserves and reflects vanishing of the actual
sequential homotopy limit. -/
theorem InverseSequence.shift_isAcyclic_iff (D : InverseSequence C) (k : ℤ) :
    (D.map (shiftFunctor C k)).IsAcyclic ↔ D.IsAcyclic :=
  D.map_isAcyclic_iff (shiftFunctor C k)

/-- A sequence with zero actual transition maps has zero homotopy limit. -/
theorem InverseSequence.isAcyclic_of_step_eq_zero (D : InverseSequence C)
    (h : ∀ n, D.step n = 0) : D.IsAcyclic := by
  have hs : D.shiftMap = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [InverseSequence.shiftMap, Pi.lift_π, h, comp_zero, zero_comp]
  change IsIso D.oneSubShift
  simp only [InverseSequence.oneSubShift, hs, sub_zero]
  infer_instance

/-- A conservative additive functor detects acyclicity when it commutes
with this particular product and sends every transition to zero. No global
preservation of products is required. -/
theorem InverseSequence.isAcyclic_of_map_step_eq_zero (D : InverseSequence C)
    (F : C ⥤ C) [F.Additive] [F.ReflectsIsomorphisms]
    [IsIso (piComparison F D.obj)] (h : ∀ n, F.map (D.step n) = 0) :
    D.IsAcyclic := by
  letI := PreservesProduct.of_iso_comparison F D.obj
  exact (D.map_isAcyclic_iff F).mp ((D.map F).isAcyclic_of_step_eq_zero h)

/-- Representing an acyclic sequence makes the actual difference operator
bijective, including its derived-limit surjectivity. -/
theorem InverseSequence.IsAcyclic.bijective_sub_shift {D : InverseSequence C}
    (hD : D.IsAcyclic) (W : C) :
    Function.Bijective (fun x : ∀ n, W ⟶ D.obj n =>
      fun n => x n - x (n + 1) ≫ D.step n) := by
  letI : IsIso D.oneSubShift := hD
  have hc (x : ∀ n, W ⟶ D.obj n) (n : ℕ) :
      (Pi.lift x ≫ D.oneSubShift) ≫ Pi.π D.obj n =
        x n - x (n + 1) ≫ D.step n := by
    simp [InverseSequence.oneSubShift, InverseSequence.shiftMap,
      Preadditive.comp_sub, Preadditive.sub_comp]
  constructor
  · intro x y hxy
    have hprod : Pi.lift x ≫ D.oneSubShift = Pi.lift y ≫ D.oneSubShift := by
      apply Pi.hom_ext
      intro n
      rw [hc, hc]
      exact congrFun hxy n
    have hxy' := (cancel_mono D.oneSubShift).mp hprod
    funext n
    simpa only [Pi.lift_π] using congrArg (fun f => f ≫ Pi.π D.obj n) hxy'
  · intro y
    let a := Pi.lift y ≫ inv D.oneSubShift
    refine ⟨fun n => a ≫ Pi.π D.obj n, ?_⟩
    funext n
    change (a ≫ Pi.π D.obj n) - (a ≫ Pi.π D.obj (n + 1)) ≫ D.step n = y n
    have ha : Pi.lift (fun n => a ≫ Pi.π D.obj n) = a := by
      apply Pi.hom_ext
      intro k
      simp only [Pi.lift_π]
    rw [← hc (fun k => a ≫ Pi.π D.obj k) n, ha]
    simp [a]

/-- Finite represented groups make the actual Milnor `1 - shift` map
surjective after applying the representable functor. -/
theorem InverseSequence.postcomp_oneSubShift_surjective_of_finite
    (D : InverseSequence C) (W : C) [∀ n, Finite (W ⟶ D.obj n)] :
    Function.Surjective (fun a : W ⟶ ∏ᶜ D.obj => a ≫ D.oneSubShift) := by
  intro b
  let f (n : ℕ) : (W ⟶ D.obj (n + 1)) →+ (W ⟶ D.obj n) :=
    { toFun := fun a => a ≫ D.step n
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.add_comp] }
  obtain ⟨a, ha⟩ := KIP126.Core.InverseSequence.surjective_sub_shift_of_finite
    (fun n => W ⟶ D.obj n) f (fun n => b ≫ Pi.π D.obj n)
  refine ⟨Pi.lift a, ?_⟩
  apply Pi.hom_ext
  intro n
  simpa only [InverseSequence.oneSubShift, InverseSequence.shiftMap,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    using congrFun ha n

/-- Every compatible family lifts through the actual Milnor projections. -/
theorem SequentialHomotopyLimit.exists_lift {D : InverseSequence C} {L : C}
    (H : SequentialHomotopyLimit D L) {W : C}
    (a : ∀ n, W ⟶ D.obj n) (ha : ∀ n, a (n + 1) ≫ D.step n = a n) :
    ∃ b : W ⟶ L, ∀ n, b ≫ H.π n = a n := by
  have hz : Pi.lift a ≫ D.oneSubShift = 0 := by
    apply Pi.hom_ext
    intro n
    simp [InverseSequence.oneSubShift, InverseSequence.shiftMap,
      Preadditive.comp_sub, Preadditive.sub_comp, ha]
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ H.distinguished (Pi.lift a) hz
  refine ⟨b, fun n => ?_⟩
  simpa only [SequentialHomotopyLimit.π, Category.assoc, Pi.lift_π, Triangle.mk_mor₁] using
    (congrArg (fun f => f ≫ Pi.π D.obj n) hb).symm

end Pretriangulated

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C]

/-- Finite homotopy groups in degree `n + 1` remove the ambiguity in
a degree-`n` homotopy-limit class with given projections. -/
theorem SequentialHomotopyLimit.homotopy_ext_of_finite
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L) (n : ℤ)
    [∀ k, Finite (HomotopyGroup (n + 1) (D.obj k))]
    {a b : HomotopyGroup n L} (hab : ∀ k, a ≫ H.π k = b ≫ H.π k) : a = b := by
  let T : HoCofiberSequence (C := C) :=
    ⟨L, ∏ᶜ D.obj, ∏ᶜ D.obj, H.toProduct, D.oneSubShift, H.boundary, H.distinguished⟩
  have hprod : (a - b) ≫ H.toProduct = 0 := by
    apply Pi.hom_ext
    intro k
    simpa only [Preadditive.sub_comp, Category.assoc, SequentialHomotopyLimit.π,
      zero_comp, sub_eq_zero] using hab k
  have hc (z : HomotopyGroup (n + 1) T.Z) : connectingHomomorphism T (n + 1) z = 0 := by
    apply (les_homotopy_exact_g T (n + 1) z).mpr
    exact D.postcomp_oneSubShift_surjective_of_finite (Sphere (n + 1)) z
  have hinj : Function.Injective (inducedMap T.f ((n + 1) - 1)) := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hzero : inducedMap T.f ((n + 1) - 1) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (lesHomotopyExactH T (n + 1) (x - y)).mp hzero
    exact hz.symm.trans (hc z)
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hinj
  have hi : Function.Injective (inducedMap H.toProduct n) := hinj
  have : a - b = 0 := hi (by simpa [inducedMap] using hprod)
  exact sub_eq_zero.mp this

/-- With finite groups in the next degree, compatible homotopy classes
have a unique lift through the actual Milnor projections. -/
theorem SequentialHomotopyLimit.existsUnique_homotopy_lift_of_finite
    {D : InverseSequence C} {L : C} (H : SequentialHomotopyLimit D L) (n : ℤ)
    [∀ k, Finite (HomotopyGroup (n + 1) (D.obj k))]
    (a : ∀ k, HomotopyGroup n (D.obj k))
    (ha : ∀ k, a (k + 1) ≫ D.step k = a k) :
    ∃! b : HomotopyGroup n L, ∀ k, b ≫ H.π k = a k := by
  obtain ⟨b, hb⟩ := H.exists_lift a ha
  refine ⟨b, hb, fun c hc => ?_⟩
  exact H.homotopy_ext_of_finite n (fun k => (hc k).trans (hb k).symm)

end KIP126.StableHomotopy
