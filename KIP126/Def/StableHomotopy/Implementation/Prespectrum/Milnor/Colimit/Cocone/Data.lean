module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Colimit.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe u

/-- The actual Milnor object together with its compatible maps from the
specified sequence. This is a cocone, without an ordinary colimit assertion. -/
noncomputable def sourceHomotopyColimitCocone (F : ℕ ⥤ SourceCategory.{u}) : Cocone F where
  pt := sourceHomotopyColimit F
  ι := NatTrans.ofSequence (sourceHomotopyColimitInclusion F) (by
    intro n
    change F.map (homOfLE (Nat.le_succ n)) ≫ sourceHomotopyColimitInclusion F (n+1) =
      sourceHomotopyColimitInclusion F n ≫ 𝟙 _
    rw [Category.comp_id]
    exact sourceHomotopyColimitInclusion_step F n)

end KIP126.StableHomotopy.Implementation
