module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Product.Infinite.Proofs
public import KIP126.Def.StableHomotopy.InverseSequence.HomotopyLimit.Represented.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Compatible families in the actual abelian stable homotopy groups of
the specified inverse sequence, with its original adjacent maps. -/
noncomputable def sourceHomotopyCompatible (D : InverseSequence SourceCategory.{u}) (d : ℤ) :
    AddSubgroup (∀ k, (sourceStableHomotopyAddFunctor d).obj (D.obj k)) where
  carrier := {x | ∀ k, (sourceStableHomotopyAddFunctor d).map (D.step k) (x (k+1)) = x k}
  zero_mem' k := map_zero _
  add_mem' {a b} ha hb k := by
    change (sourceStableHomotopyAddFunctor d).map (D.step k) (a (k+1) + b (k+1)) = a k+b k
    rw [map_add, ha k, hb k]
  neg_mem' {a} ha k := by
    change (sourceStableHomotopyAddFunctor d).map (D.step k) (-a (k+1)) = -a k
    rw [map_neg, ha k]

/-- The actual Milnor projections give an additive comparison to the
compatible families of stable homotopy classes. -/
noncomputable def sourceHomotopyLimitComparison (D : InverseSequence SourceCategory.{u}) (d : ℤ) :
    (sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D) →+
      sourceHomotopyCompatible D d where
  toFun x := ⟨fun k => (sourceStableHomotopyAddFunctor d).map
    ((sourceHomotopyLimitWitness D).π k) x, fun k => by
      have h := congrArg ((sourceStableHomotopyAddFunctor d).map)
        ((sourceHomotopyLimitWitness D).π_step k)
      rw [Functor.map_comp] at h
      exact ConcreteCategory.congr_hom h x⟩
  map_zero' := Subtype.ext (funext (fun k => map_zero _))
  map_add' x y := Subtype.ext (funext (fun k => map_add _ x y))

end KIP126.StableHomotopy.Implementation
