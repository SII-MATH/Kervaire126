module

public import KIP126.Def.Topology.SmallObject.Cubical.Proofs
public import KIP126.Def.Topology.SmallObject.CompactlyGenerated.Proofs
public import KIP126.Def.Topology.SmallObject.HomotopyExtension.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Extension.Proofs

@[expose] public section

namespace KIP126.Topology.SmallObject

open CategoryTheory CategoryTheory.Limits HomotopyLifting
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cubical replacement has its original compactly generated
colimit topology. -/
theorem cubicalReplacement_uCompactlyGeneratedSpace (S : TopCat.{u}) (s : S) :
    UCompactlyGeneratedSpace.{u} (cubicalReplacement S s) := by
  letI : UCompactlyGeneratedSpace.{u} (pointOver S s).left :=
    inferInstanceAs (UCompactlyGeneratedSpace.{u} (ULift.{u} PUnit))
  letI (n : ℕ) : UCompactlyGeneratedSpace.{u} (cubeObject.{u} n) :=
    inferInstanceAs (UCompactlyGeneratedSpace.{u} (ULift.{u} (Fin n → I)))
  exact cellularReplacement_uCompactlyGeneratedSpace cubeBoundaryInclusion (pointOver S s)

/-- The specified point in the constructed replacement is actually closed. -/
theorem cubicalReplacementPoint_isClosed (S : TopCat.{u}) (s : S) :
    IsClosed ({cubicalReplacementPoint S s} : Set (cubicalReplacement S s)) := by
  let i := colimit.ι (cellularSequence cubeBoundaryInclusion (pointOver S s)) 0
  have hi := cellularStageInclusion_isClosedEmbedding cubeBoundaryInclusion (pointOver S s)
    cubeBoundaryInclusion_isClosedEmbedding 0
  letI : T1Space ((cellularSequence cubeBoundaryInclusion (pointOver S s)).obj 0) :=
    inferInstanceAs (T1Space (ULift.{u} PUnit))
  have h := hi.isClosedMap ({ULift.up PUnit.unit} : Set ((cellularStage
    cubeBoundaryInclusion (pointOver S s) 0).left)) isClosed_singleton
  simp only [Set.image_singleton] at h
  exact h

/-- The point in the constructed replacement has the genuine Hurewicz
homotopy-extension property, with the entire specified path retained. -/
theorem cubicalReplacementPoint_homotopy_extension (S : TopCat.{u}) (s : S)
    (Y : TopCat.{u}) (f : C(cubicalReplacement S s,Y)) (p : C(I,Y))
    (hp : p 0 = f (cubicalReplacementPoint S s)) :
    ∃ H : C(cubicalReplacement S s × I,Y),
      (∀ x, H (x,0) = f x) ∧ (∀ t, H (cubicalReplacementPoint S s,t) = p t) := by
  have he := cellularInitialInclusion_hasHomotopyExtension cubeBoundaryInclusion (pointOver S s)
    cubeBoundaryInclusion_hasHomotopyExtension
  obtain ⟨H,hH₀,hHb⟩ := he Y f
    (p.comp ⟨Prod.snd,continuous_snd⟩) (by
      intro x
      have hx : x = ULift.up PUnit.unit :=
        @Subsingleton.elim (ULift.{u} PUnit) inferInstance _ _
      change p 0 = f (colimit.ι (cellularSequence cubeBoundaryInclusion (pointOver S s)) 0 x)
      rw [hx]
      exact hp)
  exact ⟨H,hH₀,fun t => hHb (ULift.up PUnit.unit) t⟩

end KIP126.Topology.SmallObject
