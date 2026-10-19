module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Layer.Scalar.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Orthogonality.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- Every actual single-degree layer of every actual Moore stage retains
the proved square-power scalar annihilator, without a coefficient-locality assumption. -/
theorem sourceMoorePowerSequence_postnikovLayer_scalarSquare (p : ℕ)
    (X : SourceCategory.{0}) (k : ℕ) (n : ℤ) :
    (p^k)^2 • 𝟙 (sourcePostnikovLayer ((moorePowerSequence p X).obj k) n) = 0 :=
  sourcePostnikovLayer_nsmul_id_eq_zero _ n ((p^k)^2)
    (sourceMoorePowerSequence_scalarSquare p X k)

end KIP126.StableHomotopy.Implementation
