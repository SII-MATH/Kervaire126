module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Cofinal.Even.Equivalence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open _root_.Topology
universe u

@[simp] theorem evenStableHomotopyEquiv_mk (P : Prespectrum.{u}) (d : ℤ)
    (a : EvenRepresentative P d) :
    evenStableHomotopyEquiv P d (Quot.mk _ a) = Quot.mk _ a.val := rfl

@[simp] theorem evenStableHomotopyEquiv_symm_mk (P : Prespectrum.{u}) (d : ℤ)
    (a : Representative P d) :
    (evenStableHomotopyEquiv P d).symm (Quot.mk _ a) = Quot.mk _ a.toEven := rfl

@[simp] theorem evenStableHomotopyEquiv_symm_mk_even (P : Prespectrum.{u}) (d : ℤ)
    (a : EvenRepresentative P d) :
    (evenStableHomotopyEquiv P d).symm (Quot.mk _ a.val) = Quot.mk _ a := by
  rw [evenStableHomotopyEquiv_symm_mk,a.toEven_val]

theorem evenStableHomotopy_mk_nextNext {P : Prespectrum.{u}} {d : ℤ}
    (a : EvenRepresentative P d) :
    (Quot.mk _ a.nextNext : EvenStableHomotopy P d) = Quot.mk _ a :=
  (Quot.sound (EvenStableRelation.stabilization a)).symm

theorem evenStableHomotopy_mk_homotopy {P : Prespectrum.{u}} {d : ℤ}
    (a : EvenRepresentative P d)
    (p : GenLoop (Fin a.val.dimension) (P.level a.val.stage) (P.level a.val.stage).point)
    (h : GenLoop.Homotopic a.val.loop p) :
    (Quot.mk _ a : EvenStableHomotopy P d) = Quot.mk _ ⟨{a.val with loop := p},a.property⟩ :=
  Quot.sound (EvenStableRelation.homotopy a p h)

end KIP126.StableHomotopy.Implementation.Prespectrum
