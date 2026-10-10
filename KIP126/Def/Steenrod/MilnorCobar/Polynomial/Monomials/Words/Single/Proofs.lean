import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Single.Data

namespace KIP126.Steenrod.Milnor

/-- The single-word coordinate places the monomial in slot zero. -/
theorem singleMilnorWord_exponents (t : ℤ) (a : PositiveMonomial t) :
    (slotExponentsEquiv 1).symm (singleMilnorWordEquiv t a).val =
      a.val.mapDomain (fun j => ((0 : Fin 1), j)) := by
  have hi : Function.Injective (fun j : ℕ => ((0 : Fin 1), j)) := fun _ _ h =>
    congrArg Prod.snd h
  apply (slotExponentsEquiv 1).injective
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i
  ext j
  simp [slotExponentsEquiv, singleMilnorWordEquiv, Finsupp.mapDomain_apply hi]

/-- Concatenating with any degree-zero empty word gives the single-slot word. -/
theorem wordConsEquiv_zero (t : ℤ) (a : PositiveMonomial t) (d : MilnorWord 0 (t - t)) :
    wordConsEquiv 0 t ⟨t, a, d⟩ = singleMilnorWordEquiv t a := by
  apply Subtype.ext
  funext i
  fin_cases i
  rfl

end KIP126.Steenrod.Milnor
