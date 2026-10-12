module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Abelian.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open scoped Topology.Homotopy
set_option backward.isDefEq.respectTransparency false
universe u

/-- Reversing any actual cube coordinate gives the negative of the
same original stable class, at every allowable representative stage. -/
theorem loopClass_symmAt (X : Prespectrum.{u}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d + n) (i : Fin r)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    loopClass X d n r h (GenLoop.symmAt i p) = -loopClass X d n r h p := by
  letI : Nonempty (Fin r) := ⟨i⟩
  have hh : (⟦GenLoop.transAt i p (GenLoop.symmAt i p)⟧ :
      HomotopyGroup (Fin r) (X.level n) (X.level n).point) = ⟦GenLoop.const⟧ := by
    rw [← HomotopyGroup.mul_spec (p := GenLoop.symmAt i p) (q := p),
      ← HomotopyGroup.inv_spec (i := i)]
    exact (@inv_mul_cancel (_root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point)
      inferInstance ⟦p⟧).trans
      HomotopyGroup.one_def
  have hs : loopClass X d n r h (GenLoop.transAt i p (GenLoop.symmAt i p)) =
      loopClass X d n r h GenLoop.const :=
    Quot.sound (StableRelation.homotopy
      ⟨n, r, h, GenLoop.transAt i p (GenLoop.symmAt i p)⟩ GenLoop.const (Quotient.exact hh))
  rw [loopClass_transAt, loopClass_const] at hs
  apply eq_neg_iff_add_eq_zero.mpr
  rwa [add_comm]

end KIP126.StableHomotopy.Implementation.Prespectrum
