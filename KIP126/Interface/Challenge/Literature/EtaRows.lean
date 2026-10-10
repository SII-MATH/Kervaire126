import KIP126.Def.ClassicalESS.Eta.Data


/-!
# Typed data for the classical eta extension spectral sequence

This module isolates the finite, source-backed Adams data used to construct
the classical eta-ESS.  It intentionally contains no eta map, row map, page
differential, or nonvanishing witness; those belong to the downstream
construction.
-/

namespace KIP126.Classical.ExtensionSS

open KIP126.Classical.Adams


/-- Stable identities for the five rows in the eta-ESS regression table. -/
inductive EtaRowId
  | d₁
  | d₂
  | d₃
  | d₄
  | d₂Inessential
  deriving DecidableEq, Repr, Inhabited

namespace EtaRowId

/-- The canonical existing differential selected by a stable row identity. -/
def row : EtaRowId → EtaDifferential
  | .d₁ => etaD₁
  | .d₂ => etaD₂
  | .d₃ => etaD₃
  | .d₄ => etaD₄
  | .d₂Inessential => etaD₂Inessential

/-- The five row identities in their canonical table order. -/
def all : List EtaRowId := [.d₁, .d₂, .d₃, .d₄, .d₂Inessential]

/-- The row identities form a closed finite type. -/
instance : Fintype EtaRowId where
  elems := {.d₁, .d₂, .d₃, .d₄, .d₂Inessential}
  complete id := by cases id <;> simp

end EtaRowId

/-- Typed Adams representatives for one canonically identified eta-ESS row. -/
structure EtaTypedRow {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y)
    (id : EtaRowId) where
  sourceClass : AdamsClass source
  targetClass : AdamsClass target
  sourceClass_degree : sourceClass.degree = id.row.sourceDegree
  targetClass_degree : targetClass.degree = id.row.targetDegree

/-- Complete upstream data for the classical eta-ESS construction.

The source and target Adams systems are fixed by the structure parameters.
Rows can only be requested through `EtaRowId`, so callers cannot inject an
uncatalogued row. The evidence states the existing eta regression directly. -/
structure EtaData {stable : StableHomotopyContext}
    {X Y : stable.Spectrum}
    (source : ClassicalAdamsSS stable X)
    (target : ClassicalAdamsSS stable Y) where
  eta : AdamsClass source
  eta_degree : eta.degree = (1, 2)
  typedRow : (id : EtaRowId) → EtaTypedRow source target id
  evidence :
    (KIP126.Classical.Regression.etaEss etaESSDifferentials)

namespace EtaData

variable {stable : StableHomotopyContext} {X Y : stable.Spectrum}
  {source : ClassicalAdamsSS stable X} {target : ClassicalAdamsSS stable Y}

/-- The typed source representative of a canonical row. -/
def sourceClass (data : EtaData source target) (id : EtaRowId) :
    AdamsClass source :=
  (data.typedRow id).sourceClass

/-- The typed target representative of a canonical row. -/
def targetClass (data : EtaData source target) (id : EtaRowId) :
    AdamsClass target :=
  (data.typedRow id).targetClass

end EtaData

end KIP126.Classical.ExtensionSS
