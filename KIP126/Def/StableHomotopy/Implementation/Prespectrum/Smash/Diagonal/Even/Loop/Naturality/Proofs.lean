module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Loop.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory _root_.Topology
set_option backward.isDefEq.respectTransparency false

/-- At each actual even level, the original recursively defined map is
the original smash map on the corresponding two retained spectrum levels. -/
theorem diagonalMapLevel_even_heq {X Y X' Y' : Prespectrum.{0}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    HEq (diagonalMapLevel f g (n+n))
      (BasedSpace.smashMap ⟨f.level n,f.point n⟩ ⟨g.level n,g.point n⟩) := by
  induction n generalizing X Y X' Y' with
  | zero => rfl
  | succ n ih =>
      rw [show n+1+(n+1) = n+n+2 by omega]
      exact ih (tailMap f) (tailMap g)

/-- The even-level loop identification strictly intertwines the
original diagonal right-spectrum map with the original fixed-space map. -/
theorem diagonalEvenLoopEquiv_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (n r : ℕ)
    (p : GenLoop (Fin r) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point) :
    diagonalEvenLoopEquiv X Z n r
        ((diagonalSmashMap (𝟙 X) f).levelLoop (n+n) r p) =
      (spaceSmashMap (𝟙 (X.level n)) f).levelLoop n r
        (diagonalEvenLoopEquiv X Y n r p) := by
  let loopMap {A B : BasedSpace.{0}} (g : A ⟶ B)
      (q : GenLoop (Fin r) A A.point) : GenLoop (Fin r) B B.point :=
    ⟨g.map.comp q.val,fun t ht =>
      (congrArg g.map (q.property t ht)).trans g.point⟩
  have aux {A B C D : BasedSpace.{0}} (hA : A = B) (hC : C = D)
      (g : A ⟶ C) (h : B ⟶ D) (hg : HEq g h)
      (p : GenLoop (Fin r) A A.point) (q : GenLoop (Fin r) B B.point)
      (hp : HEq p q) : HEq (loopMap g p) (loopMap h q) := by
    subst B
    subst D
    cases eq_of_heq hg
    cases eq_of_heq hp
    rfl
  apply (Equiv.cast_eq_iff_heq _).mpr
  exact aux (diagonalLevel_even X Y n) (diagonalLevel_even X Z n)
    (diagonalMapLevel (𝟙 X) f (n+n))
    (BasedSpace.smashMap (𝟙 (X.level n)) ⟨f.level n,f.point n⟩)
    (diagonalMapLevel_even_heq (𝟙 X) f n) p (diagonalEvenLoopEquiv X Y n r p)
    (cast_heq _ p).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
