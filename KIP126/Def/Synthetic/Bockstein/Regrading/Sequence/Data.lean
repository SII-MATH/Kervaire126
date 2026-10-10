import KIP126.Def.Synthetic.Bockstein.Regrading.Proofs

/-!
# The λ-tower construction with synthetic Adams conventions

This assembles the explicitly constructed regraded maps with their laws.
It does not identify the result with a separately supplied synthetic Adams
family or assert convergence, vertical-shift exactness, or quotient-layer
comparisons.  Those are separate mathematical obligations.
-/

namespace KIP126.Synthetic.Bockstein

open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The actual λ-tower spectral sequence, regraded and renumbered so that
raw `E₁,d₁` appear as synthetic `E₂,d₂`. -/
noncomputable def normalizedSequence (A : Syn) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree where
  toPreSS := normalizedPreSS A
  d_comp_d := normalizedPreSS_d_comp_d A
  Z_succ := normalizedPreSS_Z_succ A
  B_succ := normalizedPreSS_B_succ A

/-- The same constructed sequence packaged by its actual first page and
differential degrees.  This makes no additional choice of a sequence. -/
noncomputable def normalizedAdamsSS (A : Syn) : SyntheticAdamsSS.{v} where
  sequence := normalizedSequence A
  firstPage := rfl
  differentialDegree _ := rfl

end KIP126.Synthetic.Bockstein
