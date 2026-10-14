module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open _root_.Topology
universe u

/-- Original cubical representatives whose actual spectrum stage is even. -/
def EvenRepresentative (P : Prespectrum.{u}) (d : ℤ) :=
  {a : Representative P d // a.stage % 2 = 0}

/-- Advance an even representative by the two original structure maps. -/
def EvenRepresentative.nextNext {P : Prespectrum.{u}} {d : ℤ}
    (a : EvenRepresentative P d) : EvenRepresentative P d :=
  ⟨a.val.next.next,by
    change (a.val.stage + 1 + 1) % 2 = 0
    have := a.property
    omega⟩

/-- The even-stage relation uses actual based homotopies and exactly
two successive original stabilizations. -/
inductive EvenStableRelation (P : Prespectrum.{u}) (d : ℤ) :
    EvenRepresentative P d → EvenRepresentative P d → Prop
  | homotopy (a : EvenRepresentative P d)
      (p : GenLoop (Fin a.val.dimension) (P.level a.val.stage) (P.level a.val.stage).point)
      (h : GenLoop.Homotopic a.val.loop p) :
      EvenStableRelation P d a ⟨{a.val with loop := p},a.property⟩
  | stabilization (a : EvenRepresentative P d) :
      EvenStableRelation P d a a.nextNext

/-- The quotient of actual even-stage representatives by their
homotopies and double stabilization, before any comparison is proved. -/
def EvenStableHomotopy (P : Prespectrum.{u}) (d : ℤ) := Quot (EvenStableRelation P d)

/-- An original odd-stage representative advances once; an even one
retains its original stage, dimension and loop. -/
def Representative.toEven {P : Prespectrum.{u}} {d : ℤ}
    (a : Representative P d) : EvenRepresentative P d :=
  if h : a.stage % 2 = 0 then ⟨a,h⟩ else
    ⟨a.next,by change (a.stage+1)%2=0; omega⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
