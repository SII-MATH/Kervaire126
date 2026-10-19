module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Derived.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Cofiber.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

/-- The actual forward shift on the proved countable source coproduct. -/
noncomputable def sourceSequentialShiftMap (F : ℕ ⥤ SourceCategory.{u}) :
    (∐ F.obj) ⟶ ∐ F.obj :=
  Sigma.desc (fun n => F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n+1))

/-- The actual Milnor map for the specified source sequence. -/
noncomputable def sourceSequentialOneSubShift (F : ℕ ⥤ SourceCategory.{u}) :
    (∐ F.obj) ⟶ ∐ F.obj :=
  𝟙 _ - sourceSequentialShiftMap F

/-- The actual sequential homotopy colimit in the original source category,
constructed as the chosen distinguished cofiber of its actual Milnor map. -/
noncomputable def sourceHomotopyColimit (F : ℕ ⥤ SourceCategory.{u}) : SourceCategory.{u} :=
  HasFunctorialCofiber.cofib (sourceSequentialOneSubShift F)

/-- The original coproduct-to-cofiber arrow of the constructed Milnor triangle. -/
noncomputable def sourceHomotopyColimitFromCoproduct (F : ℕ ⥤ SourceCategory.{u}) :
    (∐ F.obj) ⟶ sourceHomotopyColimit F :=
  HasFunctorialCofiber.cofibι (sourceSequentialOneSubShift F)

/-- The original connecting arrow of the actual Milnor cofiber triangle. -/
noncomputable def sourceHomotopyColimitBoundary (F : ℕ ⥤ SourceCategory.{u}) :
    sourceHomotopyColimit F ⟶ (∐ F.obj)⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (sourceSequentialOneSubShift F)

/-- The specified stage inclusions into this particular constructed
homotopy colimit, retaining the actual coproduct and cofiber maps. -/
noncomputable def sourceHomotopyColimitInclusion (F : ℕ ⥤ SourceCategory.{u}) (n : ℕ) :
    F.obj n ⟶ sourceHomotopyColimit F :=
  Sigma.ι F.obj n ≫ sourceHomotopyColimitFromCoproduct F

end KIP126.StableHomotopy.Implementation
