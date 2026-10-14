module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Loop.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

private theorem apply_heq {A B C D : Type} (hA : A = B) (hC : C = D)
    {f : A → C} {g : B → D} (hf : HEq f g) {a : A} {b : B} (ha : HEq a b) :
    HEq (f a) (g b) := by
  subst B
  subst D
  cases eq_of_heq hf
  cases eq_of_heq ha
  rfl

private theorem genLoop_apply_heq {A B : BasedSpace} (h : A = B) {r : ℕ}
    {p : GenLoop (Fin r) A A.point} {q : GenLoop (Fin r) B B.point}
    (hp : HEq p q) (t : Fin r → I) : HEq (p t) (q t) := by
  subst B
  cases eq_of_heq hp
  rfl

private theorem genLoop_ext_heq {A B : BasedSpace} (h : A = B) {r : ℕ}
    {p : GenLoop (Fin r) A A.point} {q : GenLoop (Fin r) B B.point}
    (hp : ∀ t, HEq (p t) (q t)) : HEq p q := by
  subst B
  apply heq_of_eq
  apply GenLoop.ext
  intro t
  exact eq_of_heq (hp t)

/-- The even-level identification preserves and reflects actual based homotopies. -/
theorem diagonalEvenLoopEquiv_homotopic_iff (X Y : Prespectrum.{0}) (n r : ℕ)
    (p q : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) :
    GenLoop.Homotopic (diagonalEvenLoopEquiv X Y n r p)
      (diagonalEvenLoopEquiv X Y n r q) ↔ GenLoop.Homotopic p q := by
  have aux {A B : BasedSpace} (h : A = B)
      (p q : GenLoop (Fin r) A A.point) :
      GenLoop.Homotopic (Equiv.cast (congrArg
        (fun C : BasedSpace => ↥(GenLoop (Fin r) C C.point)) h) p)
        (Equiv.cast (congrArg (fun C : BasedSpace => ↥(GenLoop (Fin r) C C.point)) h) q) ↔
      GenLoop.Homotopic p q := by subst B; rfl
  exact aux (diagonalLevel_even X Y n) p q

/-- Two original diagonal stabilizations are exactly the signed grid's
horizontal-then-vertical transition, after identifying the actual levels. -/
theorem diagonalEvenLoopEquiv_stabilize_pair_heq (X Y : Prespectrum.{0}) (n r : ℕ)
    (p : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) :
    HEq (stabilizeLoop (diagonalSmash X Y) (n+n+1) (r+1)
      (stabilizeLoop (diagonalSmash X Y) (n+n) r p))
      (diagonalGridLoopVertical X Y (n+1) n (r+1)
        (diagonalGridLoopHorizontal X Y n n r (diagonalEvenLoopEquiv X Y n r p))) := by
  have hout : (diagonalSmash X Y).level (n+n+1+1) =
      (X.level (n+1)).smash (Y.level (n+1)) := by
    change diagonalLevel X Y (n+n+1+1) = _
    rw [show n+n+1+1 = (n+1)+(n+1) by omega,diagonalLevel_even]
  apply genLoop_ext_heq hout
  intro t
  have hp : HEq p (diagonalEvenLoopEquiv X Y n r p) :=
    (cast_heq _ p).symm
  have hpt := genLoop_apply_heq (diagonalLevel_even X Y n) hp (fun i => t i.succ.succ)
  have hb := diagonalBond_pair_heq X Y n
  have h1 := apply_heq
    (congrArg (fun A : BasedSpace => (A : Type)) (diagonalLevel_even X Y n))
    (congrArg (fun A : BasedSpace => I → I → A) hout) hb hpt
  have h2 := apply_heq rfl (congrArg (fun A : BasedSpace => I → A) hout) h1
    (HEq.rfl : HEq (t 1) (t 1))
  have h3 := apply_heq rfl (congrArg (fun A : BasedSpace => (A : Type)) hout) h2
    (HEq.rfl : HEq (t 0) (t 0))
  convert h3 using 1
  · rfl
  · change (spaceSmash (X.level (n+1)) Y).bond n
      (diagonalGridBondLeft X Y n n
        ((diagonalEvenLoopEquiv X Y n r p) (fun i => t i.succ.succ),
          suspensionDesuspensionSign (n+n) (t 1)),t 0) = _
    rw [suspensionDesuspensionSign_double]

end KIP126.StableHomotopy.Implementation.Prespectrum
