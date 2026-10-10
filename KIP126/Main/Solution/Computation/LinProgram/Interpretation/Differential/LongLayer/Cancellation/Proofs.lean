import KIP126.Main.Solution.Computation.LinProgram.Interpretation.Differential.Proofs

namespace KIP126.Classical.Adams

noncomputable section

/-- In the covered target degree, the two cross products cancel by the Lin
quotient's commutativity and characteristic two. No differential rule is
used: the first input may in particular be the actual differential of h₆. -/
theorem LinE2Presentation.h6_cross_products_add_eq_zero (P : LinE2Presentation)
    (x : sphereAdamsData.Page 2 (3, 65)) (y : sphereAdamsData.Page 2 (1, 64)) :
    P.product 3 65 1 64 x y + P.product 1 64 3 65 y x = 0 := by
  let a := (P.comparison 3 65 (by decide)).symm x
  let b := (P.comparison 1 64 (by decide)).symm y
  have ha : P.comparison 3 65 (by decide) a = x := LinearEquiv.apply_symm_apply _ _
  have hb : P.comparison 1 64 (by decide) b = y := LinearEquiv.apply_symm_apply _ _
  have hab := P.comparison_mul 3 65 1 64 (by decide) a b (KIP126.LinE2.mulAt a b) rfl
  rw [ha, hb] at hab
  have hba := P.comparison_mul 1 64 3 65 (by decide) b a (KIP126.LinE2.mulAt b a) rfl
  rw [hb, ha] at hba
  have hz : KIP126.LinE2.mulAt a b + KIP126.LinE2.mulAt b a = 0 := by
    apply Subtype.ext
    change a.val * b.val + b.val * a.val = 0
    rw [mul_comm b.val a.val]
    exact linE2_add_self_eq_zero _
  exact (congrArg₂ (fun x y : sphereAdamsData.Page 2 (4, 129) => x + y)
    hab.symm hba.symm).trans
      (((P.comparison 4 129 (by decide)).map_add _ _).symm.trans
        ((congrArg (P.comparison 4 129 (by decide)) hz).trans
          (P.comparison 4 129 (by decide)).map_zero))

end
end KIP126.Classical.Adams
