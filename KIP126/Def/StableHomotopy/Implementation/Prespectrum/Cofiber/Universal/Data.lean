module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal quotient cofiber universally receives an actual strict
map whose composite with f is the actual zero map. -/
def cofiberDesc {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (a : Y ⟶ Z)
    (h : f ≫ a = zeroMap X Z) : pointSetCofiber f ⟶ Z := by
  have ha (n : ℕ) (x : X.level n) : a.level n (f.level n x) = (Z.level n).point :=
    congrArg (fun e : X ⟶ Z => e.level n x) h
  have hr (n : ℕ) : ∀ y z, CofiberRelation f n y z → a.level n y = a.level n z := by
    rintro y z ⟨⟨x,rfl⟩,⟨x',rfl⟩⟩
    exact (ha n x).trans (ha n x').symm
  refine {
    level n := ⟨Quot.lift (a.level n) (hr n),continuous_quot_lift (hr n) (a.level n).continuous⟩
    point n := a.point n
    bond := ?_ }
  intro n z t
  refine Quot.inductionOn z ?_
  intro y
  exact a.bond n y t
end KIP126.StableHomotopy.Implementation.Prespectrum
