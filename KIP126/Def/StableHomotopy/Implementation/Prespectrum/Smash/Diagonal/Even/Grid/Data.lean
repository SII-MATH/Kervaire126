module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Even.Loop.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Diagonal.Grid.Stable.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Cofinal.Even.Equivalence.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
set_option backward.isDefEq.respectTransparency false

/-- An actual equal-index grid loop gives an original even representative. -/
noncomputable def diagonalEvenRepresentativeOfGridLoop (X Y : Prespectrum.{0}) (d : ℤ)
    (n r : ℕ) (h : (r : ℤ) = d+n+n)
    (p : GenLoop (Fin r) ((X.level n).smash (Y.level n))
      ((X.level n).smash (Y.level n)).point) :
    EvenRepresentative (diagonalSmash X Y) d :=
  ⟨{ stage := n+n, dimension := r, degree := by omega,
      loop := (diagonalEvenLoopEquiv X Y n r).symm p },by change (n+n)%2=0; omega⟩

/-- An original even representative determines its actual equal-index
smash homotopy class. The half-stage is the arithmetic quotient by two. -/
noncomputable def diagonalGridOfEvenRepresentative {X Y : Prespectrum.{0}} {d : ℤ}
    (a : EvenRepresentative (diagonalSmash X Y) d) : DiagonalGridDiagonalClass X Y d := by
  let n := a.val.stage / 2
  have hn : a.val.stage = n+n := by have := a.property; dsimp only [n]; omega
  let p : GenLoop (Fin a.val.dimension) ((diagonalSmash X Y).level (n+n))
      ((diagonalSmash X Y).level (n+n)).point :=
    cast (congrArg (fun k => ↥(GenLoop (Fin a.val.dimension)
      ((diagonalSmash X Y).level k) ((diagonalSmash X Y).level k).point)) hn) a.val.loop
  exact ⟨{ left := n
           right := n
           dimension := a.val.dimension
           degree := by have := a.val.degree; omega
           homotopy := ⟦diagonalEvenLoopEquiv X Y n a.val.dimension p⟧ },rfl⟩

/-- The inverse comparison on a grid class descends actual loop homotopy,
using the equality of the original based spaces at each even level. -/
noncomputable def diagonalEvenStableOfGridClass {X Y : Prespectrum.{0}} {d : ℤ}
    (a : DiagonalGridDiagonalClass X Y d) : EvenStableHomotopy (diagonalSmash X Y) d := by
  rcases a with ⟨⟨n,k,r,h,p⟩,hn⟩
  change n = k at hn
  subst k
  refine Quotient.lift (fun p => Quot.mk _ (diagonalEvenRepresentativeOfGridLoop X Y d n r h p))
    (fun p q hp => ?_) p
  change GenLoop.Homotopic p q at hp
  apply Quot.sound
  apply EvenStableRelation.homotopy
  change GenLoop.Homotopic ((diagonalEvenLoopEquiv X Y n r).symm p)
    ((diagonalEvenLoopEquiv X Y n r).symm q)
  apply (diagonalEvenLoopEquiv_homotopic_iff X Y n r _ _).mp
  simpa only [Equiv.apply_symm_apply] using hp

end KIP126.StableHomotopy.Implementation.Prespectrum
