module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The homotopy category of strict prespectra, quotienting precisely by
actual based homotopies compatible with all bonding maps. -/
abbrev HomotopyCategory := CategoryTheory.Quotient pathHomotopic.{u}

/-- The identity-on-objects quotient by the proved actual homotopy congruence. -/
def homotopyQuotient : Prespectrum.{u} ⥤ HomotopyCategory.{u} :=
  CategoryTheory.Quotient.functor pathHomotopic

/-- The original ordinary stable localization factors through actual homotopy. -/
noncomputable def homotopyToSource : HomotopyCategory.{u} ⥤ SourceCategory.{u} :=
  CategoryTheory.Quotient.lift pathHomotopic sourceLocalization
    (fun _ _ _ _ h => source_map_eq_of_pathHomotopic h)

/-- Actual stable equivalences descended through the proved homotopy congruence. -/
def homotopyStableEquivalences : MorphismProperty HomotopyCategory.{u} :=
  stableEquivalences.quotient pathHomotopic

end KIP126.StableHomotopy.Implementation.Prespectrum
