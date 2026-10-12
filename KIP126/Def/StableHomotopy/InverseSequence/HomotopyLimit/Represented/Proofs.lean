module

public import KIP126.Def.StableHomotopy.InverseSequence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasProductsOfShape ℕ C]

/-- The actual next-shift difference operator measures the ambiguity of
maps with prescribed Milnor projections, in any pretriangulated category. -/
theorem SequentialHomotopyLimit.hom_ext_of_surjective
    {D : InverseSequence C} {L W : C} (H : SequentialHomotopyLimit D L)
    (hs : Function.Surjective
      (fun z : W⟦(1 : ℤ)⟧ ⟶ ∏ᶜ D.obj => z ≫ D.oneSubShift))
    {a b : W ⟶ L} (hab : ∀ k, a ≫ H.π k = b ≫ H.π k) : a = b := by
  let T := Triangle.mk H.toProduct D.oneSubShift H.boundary
  have hp : (a-b) ≫ H.toProduct = 0 := by
    apply Pi.hom_ext
    intro k
    simpa only [Preadditive.sub_comp, Category.assoc, SequentialHomotopyLimit.π,
      zero_comp, sub_eq_zero] using hab k
  have hp' : (a-b)⟦(1 : ℤ)⟧' ≫ H.toProduct⟦(1 : ℤ)⟧' = 0 := by
    rw [← Functor.map_comp, hp, Functor.map_zero]
  obtain ⟨z,hz⟩ := T.coyoneda_exact₁ H.distinguished ((a-b)⟦(1 : ℤ)⟧') hp'
  obtain ⟨y,hy⟩ := hs z
  have hm : (a-b)⟦(1 : ℤ)⟧' = 0 := by
    rw [hz, ← hy, Category.assoc]
    exact (congrArg (fun q => y ≫ q)
      (comp_distTriang_mor_zero₂₃ T H.distinguished)).trans (comp_zero)
  apply sub_eq_zero.mp
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simpa only [Functor.map_zero] using hm

/-- Finite next-shift represented groups eliminate the Milnor ambiguity. -/
theorem SequentialHomotopyLimit.hom_ext_of_finite
    {D : InverseSequence C} {L W : C} (H : SequentialHomotopyLimit D L)
    [∀ k, Finite (W⟦(1 : ℤ)⟧ ⟶ D.obj k)]
    {a b : W ⟶ L} (hab : ∀ k, a ≫ H.π k = b ≫ H.π k) : a = b :=
  H.hom_ext_of_surjective (D.postcomp_oneSubShift_surjective_of_finite _) hab

/-- Actual finite next-shift represented groups give a unique lift of every
compatible family through the specified Milnor triangle. -/
theorem SequentialHomotopyLimit.existsUnique_lift_of_finite
    {D : InverseSequence C} {L W : C} (H : SequentialHomotopyLimit D L)
    [∀ k, Finite (W⟦(1 : ℤ)⟧ ⟶ D.obj k)]
    (a : ∀ k, W ⟶ D.obj k) (ha : ∀ k, a (k+1) ≫ D.step k = a k) :
    ∃! b : W ⟶ L, ∀ k, b ≫ H.π k = a k := by
  obtain ⟨b,hb⟩ := H.exists_lift a ha
  exact ⟨b,hb,fun c hc => H.hom_ext_of_finite (fun k => (hc k).trans (hb k).symm)⟩

end KIP126.StableHomotopy
