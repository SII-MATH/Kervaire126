module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Grid.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- An original even representative is recovered in the original even
stable quotient by the inverse comparison. -/
theorem diagonalEvenStableOfGridClass_ofEven {X Y : Prespectrum.{0}} {d : ℤ}
    (a : EvenRepresentative (diagonalSmash X Y) d) :
    diagonalEvenStableOfGridClass (diagonalGridOfEvenRepresentative a) = Quot.mk _ a := by
  rcases a with ⟨⟨k,r,hd,p⟩,he⟩
  change k % 2 = 0 at he
  have hk : k = k/2+k/2 := by omega
  generalize hk2 : k/2 = n at hk
  subst k
  rw [diagonalGridOfEvenRepresentative_mk X Y d n r (by omega) p]
  change Quot.mk _ (diagonalEvenRepresentativeOfGridLoop X Y d n r _
    (diagonalEvenLoopEquiv X Y n r p)) = _
  unfold diagonalEvenRepresentativeOfGridLoop
  rw [Equiv.symm_apply_apply]

/-- Every actual equal-index grid homotopy class has an original even
representative. This chooses only a representative of its homotopy quotient. -/
theorem diagonalGridOfEvenRepresentative_surjective (X Y : Prespectrum.{0}) (d : ℤ) :
    Function.Surjective (diagonalGridOfEvenRepresentative (X := X) (Y := Y) (d := d)) := by
  rintro ⟨⟨n,k,r,hd,p⟩,hn⟩
  change n = k at hn
  subst k
  induction p using Quotient.inductionOn with
  | h p =>
      refine ⟨diagonalEvenRepresentativeOfGridLoop X Y d n r hd p,?_⟩
      unfold diagonalEvenRepresentativeOfGridLoop
      rw [diagonalGridOfEvenRepresentative_mk X Y d n r (by omega)
        ((diagonalEvenLoopEquiv X Y n r).symm p)]
      simp only [Equiv.apply_symm_apply]

/-- The inverse map respects the actual two-bond diagonal relation. -/
theorem diagonalEvenStableOfGridClass_relation {X Y : Prespectrum.{0}} {d : ℤ}
    {a b : DiagonalGridDiagonalClass X Y d}
    (h : DiagonalGridDiagonalRelation X Y d a b) :
    diagonalEvenStableOfGridClass a = diagonalEvenStableOfGridClass b := by
  cases h with
  | step =>
      obtain ⟨a,rfl⟩ := diagonalGridOfEvenRepresentative_surjective X Y d a
      rw [← diagonalGridOfEvenRepresentative_nextNext,
        diagonalEvenStableOfGridClass_ofEven,diagonalEvenStableOfGridClass_ofEven]
      exact Quot.sound (EvenStableRelation.stabilization a)

end KIP126.StableHomotopy.Implementation.Prespectrum
