module

public import KIP126.Def.Topology.Coproduct.Wedge.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} (X : J → Type v) [∀ j, TopologicalSpace (X j)] (x₀ : ∀ j, X j)

/-- Include an actual subfamily wedge by the original summand maps. -/
def wedgeSubfamilyInclusion (s : Set J) :
    C(Wedge (fun j : s => X j.val) (fun j => x₀ j.val),Wedge X x₀) :=
  wedgeDesc _ _ (wedgePoint X x₀) (fun j => wedgeInclusion X x₀ j.val)
    (fun j => wedgeInclusion_point j.val)

/-- The continuous retraction which collapses every omitted summand to
the common point of the subfamily wedge. -/
noncomputable def wedgeSubfamilyRetraction (s : Set J) :
    C(Wedge X x₀,Wedge (fun j : s => X j.val) (fun j => x₀ j.val)) := by
  classical
  exact wedgeDesc X x₀ (wedgePoint (fun j : s => X j.val) (fun j => x₀ j.val))
    (fun j => if h : j ∈ s then
      wedgeInclusion (fun j : s => X j.val) (fun j => x₀ j.val) ⟨j,h⟩ else
        ContinuousMap.const _ (wedgePoint (fun j : s => X j.val) (fun j => x₀ j.val)))
    (fun j => by split_ifs <;> simp)

end KIP126.Topology
