module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Cofinal.Even.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open _root_.Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- Both generators of the even-stage quotient give equal original
stable classes; the double step uses both actual structure maps. -/
theorem EvenStableRelation.forget_sound {P : Prespectrum.{u}} {d : ℤ}
    {a b : EvenRepresentative P d} (h : EvenStableRelation P d a b) :
    (Quot.mk _ a.val : StableHomotopy P d) = Quot.mk _ b.val := by
  cases h with
  | homotopy p hp => exact Quot.sound (StableRelation.homotopy a.val p hp)
  | stabilization =>
      exact (Quot.sound (StableRelation.stabilization a.val)).trans
        (Quot.sound (StableRelation.stabilization a.val.next))

/-- Even-stage normalization respects every original stable generator. -/
theorem Representative.toEven_relation {P : Prespectrum.{u}} {d : ℤ}
    {a b : Representative P d} (h : StableRelation P d a b) :
    (Quot.mk _ a.toEven : EvenStableHomotopy P d) = Quot.mk _ b.toEven := by
  cases h with
  | homotopy p hp =>
      by_cases he : a.stage % 2 = 0
      · simp only [Representative.toEven,dif_pos he]
        exact Quot.sound (EvenStableRelation.homotopy ⟨a,he⟩ p hp)
      · have he' : a.next.stage % 2 = 0 := by change (a.stage+1)%2=0; omega
        simp only [Representative.toEven,dif_neg he]
        exact Quot.sound (EvenStableRelation.homotopy ⟨a.next,he'⟩ _
          (stabilizeLoop_homotopic P _ _ _ _ hp))
  | stabilization =>
      by_cases he : a.stage % 2 = 0
      · have ho : a.next.stage % 2 ≠ 0 := by change (a.stage+1)%2≠0; omega
        simp only [Representative.toEven,dif_pos he,dif_neg ho]
        exact Quot.sound (EvenStableRelation.stabilization ⟨a,he⟩)
      · have he' : a.next.stage % 2 = 0 := by change (a.stage+1)%2=0; omega
        simp only [Representative.toEven,dif_neg he,dif_pos he']

/-- On an original even representative normalization is literally
that same subtype element. -/
@[simp] theorem EvenRepresentative.toEven_val {P : Prespectrum.{u}} {d : ℤ}
    (a : EvenRepresentative P d) : a.val.toEven = a := by
  simp only [Representative.toEven,dif_pos a.property]
  rfl

/-- Normalization retains the original stable class, also at odd stages. -/
theorem Representative.toEven_forget {P : Prespectrum.{u}} {d : ℤ}
    (a : Representative P d) :
    (Quot.mk _ a.toEven.val : StableHomotopy P d) = Quot.mk _ a := by
  by_cases he : a.stage % 2 = 0
  · simp only [Representative.toEven,dif_pos he]
  · simp only [Representative.toEven,dif_neg he]
    exact (Quot.sound (StableRelation.stabilization a)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
