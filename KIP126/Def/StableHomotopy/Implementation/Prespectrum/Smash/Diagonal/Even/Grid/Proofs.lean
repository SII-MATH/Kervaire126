module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Grid.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

private theorem grid_class_ext {X Y : Prespectrum.{0}} {d : ℤ}
    {n k r n' k' r' : ℕ} (hn : n = n') (hk : k = k') (hr : r = r')
    (h : (r : ℤ) = d+n+k) (h' : (r' : ℤ) = d+n'+k')
    (p : _root_.HomotopyGroup (Fin r) ((X.level n).smash (Y.level k))
      ((X.level n).smash (Y.level k)).point)
    (q : _root_.HomotopyGroup (Fin r') ((X.level n').smash (Y.level k'))
      ((X.level n').smash (Y.level k')).point) (hp : HEq p q) :
    (⟨n,k,r,h,p⟩ : DiagonalGridClass X Y d) = ⟨n',k',r',h',q⟩ := by
  subst n'
  subst k'
  subst r'
  cases eq_of_heq hp
  rfl

private theorem homotopy_mk_heq {A B : BasedSpace.{0}} (hA : A = B) {r : ℕ}
    (p : GenLoop (Fin r) A A.point) (q : GenLoop (Fin r) B B.point) (hp : HEq p q) :
    HEq (⟦p⟧ : _root_.HomotopyGroup (Fin r) A A.point)
      (⟦q⟧ : _root_.HomotopyGroup (Fin r) B B.point) := by
  subst B
  cases eq_of_heq hp
  rfl

private theorem even_loop_heq (X Y : Prespectrum.{0}) {m n r : ℕ} (hm : m = n)
    (p : GenLoop (Fin r) ((diagonalSmash X Y).level (m+m))
      ((diagonalSmash X Y).level (m+m)).point)
    (q : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) (hp : HEq p q) :
    HEq (diagonalEvenLoopEquiv X Y m r p) (diagonalEvenLoopEquiv X Y n r q) := by
  subst n
  cases eq_of_heq hp
  rfl

private theorem grid_pair_loop_heq (X Y : Prespectrum.{0}) {m n r : ℕ} (hm : m = n)
    (p : GenLoop (Fin r) ((diagonalSmash X Y).level (m+m))
      ((diagonalSmash X Y).level (m+m)).point)
    (q : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) (hp : HEq p q) :
    HEq (diagonalGridLoopVertical X Y (m+1) m (r+1)
      (diagonalGridLoopHorizontal X Y m m r (diagonalEvenLoopEquiv X Y m r p)))
      (diagonalGridLoopVertical X Y (n+1) n (r+1)
        (diagonalGridLoopHorizontal X Y n n r (diagonalEvenLoopEquiv X Y n r q))) := by
  subst n
  cases eq_of_heq hp
  rfl

/-- The comparison evaluates on an original representative at stage `n+n`. -/
theorem diagonalGridOfEvenRepresentative_mk (X Y : Prespectrum.{0}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d+(n+n))
    (p : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) :
    diagonalGridOfEvenRepresentative
      (⟨⟨n+n,r,by omega,p⟩,by change (n+n)%2=0; omega⟩ : EvenRepresentative (diagonalSmash X Y) d) =
      ⟨⟨n,n,r,by omega,⟦diagonalEvenLoopEquiv X Y n r p⟧⟩,rfl⟩ := by
  apply Subtype.ext
  apply grid_class_ext (by change (n+n)/2=n; omega) (by change (n+n)/2=n; omega) rfl
  apply homotopy_mk_heq
    (show (X.level ((n+n)/2)).smash (Y.level ((n+n)/2)) =
      (X.level n).smash (Y.level n) by congr 2 <;> omega)
  exact even_loop_heq X Y (show (n+n)/2 = n by omega) _ p (cast_heq _ p)

/-- The actual even-to-grid comparison preserves the original doubled bond. -/
theorem diagonalGridOfEvenRepresentative_nextNext {X Y : Prespectrum.{0}} {d : ℤ}
    (a : EvenRepresentative (diagonalSmash X Y) d) :
    diagonalGridOfEvenRepresentative a.nextNext =
      (diagonalGridOfEvenRepresentative a).next := by
  rcases a with ⟨⟨k,r,hd,p⟩,he⟩
  change k % 2 = 0 at he
  have hk : k = k/2+k/2 := by omega
  generalize hk2 : k/2 = n at hk
  subst k
  apply Subtype.ext
  apply grid_class_ext (by change (n+n+1+1)/2=(n+n)/2+1; omega)
    (by change (n+n+1+1)/2=(n+n)/2+1; omega) rfl
  apply homotopy_mk_heq
    (show (X.level ((n+n+1+1)/2)).smash (Y.level ((n+n+1+1)/2)) =
      (X.level ((n+n)/2+1)).smash (Y.level ((n+n)/2+1)) by congr 2 <;> omega)
  exact (cast_heq _ _).trans ((cast_heq _ _).trans
    ((diagonalEvenLoopEquiv_stabilize_pair_heq X Y n r p).trans
      (grid_pair_loop_heq X Y (show (n+n)/2 = n by omega) _ p (cast_heq _ p)).symm))

/-- The comparison respects each actual even-stage quotient generator. -/
theorem diagonalGridOfEvenRepresentative_relation {X Y : Prespectrum.{0}} {d : ℤ}
    {a b : EvenRepresentative (diagonalSmash X Y) d}
    (h : EvenStableRelation (diagonalSmash X Y) d a b) :
    (Quot.mk _ (diagonalGridOfEvenRepresentative a) : DiagonalGridDiagonalStable X Y d) =
      Quot.mk _ (diagonalGridOfEvenRepresentative b) := by
  cases h with
  | homotopy q h =>
      apply congrArg (Quot.mk _)
      rcases a with ⟨⟨k,r,hd,p⟩,he⟩
      change k % 2 = 0 at he
      have hk : k = k/2+k/2 := by omega
      generalize hk2 : k/2 = n at hk
      subst k
      rw [diagonalGridOfEvenRepresentative_mk X Y d n r (by omega) p,
        diagonalGridOfEvenRepresentative_mk X Y d n r (by omega) q]
      exact congrArg (fun z : _root_.HomotopyGroup (Fin r)
        ((X.level n).smash (Y.level n)) ((X.level n).smash (Y.level n)).point =>
          (⟨⟨n,n,r,by omega,z⟩,rfl⟩ : DiagonalGridDiagonalClass X Y d))
        (Quotient.sound ((diagonalEvenLoopEquiv_homotopic_iff X Y n r p q).mpr h))
  | stabilization =>
      rw [diagonalGridOfEvenRepresentative_nextNext]
      exact Quot.sound (DiagonalGridDiagonalRelation.step _)

end KIP126.StableHomotopy.Implementation.Prespectrum
