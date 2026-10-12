module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Grid.Equivalence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Loop.Naturality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The original even-representative comparison preserves the original
map of the right spectrum before either stable quotient is taken. -/
theorem diagonalGridOfEvenRepresentative_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ)
    (a : EvenRepresentative (diagonalSmash X Y) d) :
    diagonalGridOfEvenRepresentative
      (⟨a.val.map (diagonalSmashMap (𝟙 X) f),a.property⟩ :
        EvenRepresentative (diagonalSmash X Z) d) =
      (diagonalGridOfEvenRepresentative a).mapRight f := by
  rcases a with ⟨⟨k,r,hd,p⟩,he⟩
  change k % 2 = 0 at he
  have hk : k = k/2+k/2 := by omega
  generalize hk2 : k/2 = n at hk
  subst k
  change diagonalGridOfEvenRepresentative
    (⟨⟨n+n,r,hd,(diagonalSmashMap (𝟙 X) f).levelLoop (n+n) r p⟩,he⟩ :
      EvenRepresentative (diagonalSmash X Z) d) = _
  rw [diagonalGridOfEvenRepresentative_mk X Z d n r (by omega)
    ((diagonalSmashMap (𝟙 X) f).levelLoop (n+n) r p),
    diagonalGridOfEvenRepresentative_mk X Y d n r (by omega) p]
  apply Subtype.ext
  change (DiagonalGridClass.mk n n r _ _ : DiagonalGridClass X Z d) =
    DiagonalGridClass.mk n n r _ _
  congr 1
  exact congrArg Quotient.mk' (diagonalEvenLoopEquiv_natural_right X f n r p)

/-- The comparison of original stable diagonal homotopy with the
actual equal-index grid is natural for the original spectrum map. -/
theorem diagonalStableHomotopyDiagonalGridEquiv_natural_right (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z) (d : ℤ)
    (x : StableHomotopy (diagonalSmash X Y) d) :
    diagonalStableHomotopyDiagonalGridEquiv X Z d
      (stableHomotopyMap (diagonalSmashMap (𝟙 X) f) d x) =
      diagonalGridDiagonalStableMap X f d (diagonalStableHomotopyDiagonalGridEquiv X Y d x) := by
  obtain ⟨x,rfl⟩ := (evenStableHomotopyEquiv (diagonalSmash X Y) d).surjective x
  induction x using Quot.inductionOn with
  | h a =>
      let b : EvenRepresentative (diagonalSmash X Z) d :=
        ⟨a.val.map (diagonalSmashMap (𝟙 X) f),a.property⟩
      change diagonalEvenStableGridEquiv X Z d
        ((evenStableHomotopyEquiv (diagonalSmash X Z) d).symm (Quot.mk _ b.val)) =
        diagonalGridDiagonalStableMap X f d (diagonalEvenStableGridEquiv X Y d
          ((evenStableHomotopyEquiv (diagonalSmash X Y) d).symm (Quot.mk _ a.val)))
      rw [evenStableHomotopyEquiv_symm_mk_even,evenStableHomotopyEquiv_symm_mk_even]
      exact congrArg (Quot.mk _) (diagonalGridOfEvenRepresentative_natural_right X f d a)

/-- Stable equivalences on every actual fixed-space row induce a
stable equivalence on the original recursive diagonal spectrum. -/
theorem diagonalSmashMap_stableEquivalence_of_rows (X : Prespectrum.{0})
    {Y Z : Prespectrum.{0}} (f : Y ⟶ Z)
    (hf : ∀ n, stableEquivalences (spaceSmashMap (𝟙 (X.level n)) f)) :
    stableEquivalences (diagonalSmashMap (𝟙 X) f) := by
  intro d
  have hm : stableHomotopyMap (diagonalSmashMap (𝟙 X) f) d =
      (diagonalStableHomotopyDiagonalGridEquiv X Z d).symm ∘
        diagonalGridDiagonalStableMap X f d ∘
          diagonalStableHomotopyDiagonalGridEquiv X Y d := by
    funext a
    apply (diagonalStableHomotopyDiagonalGridEquiv X Z d).injective
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
    exact diagonalStableHomotopyDiagonalGridEquiv_natural_right X f d a
  rw [hm]
  exact (diagonalStableHomotopyDiagonalGridEquiv X Z d).symm.bijective.comp
    ((diagonalGridDiagonalStableMap_bijective_of_rows X f d (fun n => hf n (d+n))).comp
      (diagonalStableHomotopyDiagonalGridEquiv X Y d).bijective)

end KIP126.StableHomotopy.Implementation.Prespectrum
