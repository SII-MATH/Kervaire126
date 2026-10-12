module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The ordinary quotient relation collapsing the entire actual image
of the displayed level map. -/
def CofiberRelation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (y z : Y.level n) : Prop := y ∈ Set.range (f.level n) ∧ z ∈ Set.range (f.level n)

def cofiberLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of (Quot (CofiberRelation f n))
  point := Quot.mk _ (Y.level n).point

/-- The literal level quotient B/f(A), with its induced strict bonds. -/
def pointSetCofiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} := by
  have hr (n : ℕ) (t : I) : ∀ y z, CofiberRelation f n y z →
      Quot.mk (CofiberRelation f (n+1)) (Y.bond n (y,t)) =
        Quot.mk (CofiberRelation f (n+1)) (Y.bond n (z,t)) := by
    rintro y z ⟨⟨x,rfl⟩,⟨x',rfl⟩⟩
    apply Quot.sound
    exact ⟨⟨X.bond n (x,t),f.bond n x t⟩,⟨X.bond n (x',t),f.bond n x' t⟩⟩
  refine {
    level := cofiberLevel f
    bond n := ⟨fun p => Quot.lift (fun y => Quot.mk (CofiberRelation f (n+1)) (Y.bond n (y,p.2)))
      (hr n p.2) p.1,?_⟩
    bond_point := ?_
    bond_zero := ?_
    bond_one := ?_ }
  · apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact continuous_quot_mk.comp (Y.bond n).continuous
  · intro n t
    change Quot.mk (CofiberRelation f (n+1)) (Y.bond n ((Y.level n).point,t)) = _
    rw [Y.bond_point]
    rfl
  · intro n z
    refine Quot.inductionOn z ?_
    intro y
    change Quot.mk (CofiberRelation f (n+1)) (Y.bond n (y,0)) = _
    rw [Y.bond_zero]
    rfl
  · intro n z
    refine Quot.inductionOn z ?_
    intro y
    change Quot.mk (CofiberRelation f (n+1)) (Y.bond n (y,1)) = _
    rw [Y.bond_one]
    rfl

def cofiberProjection {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Y ⟶ pointSetCofiber f where
  level n := ⟨Quot.mk _,continuous_quot_mk⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- Collapse the retained cone cylinder to the image point in the
literal quotient cofiber. -/
def coneToCofiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) : cone f ⟶ pointSetCofiber f :=
  coneLift f (cofiberProjection f) (zeroMap X (pathPrespectrum (pointSetCofiber f))) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact Quot.sound ⟨⟨(X.level n).point,f.point n⟩,⟨x,rfl⟩⟩) rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
