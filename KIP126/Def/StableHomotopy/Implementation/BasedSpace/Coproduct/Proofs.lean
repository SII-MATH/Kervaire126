module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Coproduct.Data
public import KIP126.Def.Topology.Coproduct.Wedge.Compact.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits

universe u

@[simp] theorem wedgeι_desc {J : Type u} {X : J → BasedSpace.{u}}
    {Y : BasedSpace.{u}} (f : ∀ j, X j ⟶ Y) (j : J) :
    wedgeι X j ≫ wedgeDesc f = f j := rfl

/-- The actual quotient wedge satisfies the based coproduct universal
property, including the empty indexing family. -/
def wedgeCofan_isColimit {J : Type u} (X : J → BasedSpace.{u}) :
    IsColimit (wedgeCofan X) := by
  refine Cofan.IsColimit.mk _ (fun c => wedgeDesc c.inj) (fun _ _ => rfl) ?_
  intro c m hm
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quotient.inductionOn z ?_
  rintro (⟨j,x⟩ | ⟨⟩)
  · exact congrArg (fun f : X j ⟶ c.pt => f.map x) (hm j)
  · exact m.point

/-- The common-point quotient identifies with the actual chosen based
coproduct via its genuine universal property. -/
noncomputable def wedgeCoproductIso {J : Type u} (X : J → BasedSpace.{u}) :
    wedge X ≅ ∐ X :=
  (wedgeCofan_isColimit X).coconePointUniqueUpToIso (coproductIsCoproduct X)

@[simp] theorem wedgeι_coproductIso_hom {J : Type u} (X : J → BasedSpace.{u}) (j : J) :
    wedgeι X j ≫ (wedgeCoproductIso X).hom = Sigma.ι X j :=
  (wedgeCofan_isColimit X).comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct X) ⟨j⟩

/-- Compact subsets of the explicit based wedge meet finitely many
summands away from their actual basepoints. -/
theorem wedge_compact_finite_support {J : Type u} (X : J → BasedSpace.{u})
    [∀ j, T1Space (X j)] {K : Set (wedge X)} (hK : IsCompact K) :
    {j | ∃ x : X j, x ≠ (X j).point ∧ (wedgeι X j).map x ∈ K}.Finite :=
  KIP126.Topology.isCompact_wedge_finite_support hK

end KIP126.StableHomotopy.Implementation.BasedSpace
