module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Heart.Locality.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Postnikov.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Connectivity.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Every original dyadic Moore stage of a bounded-below source is
HF2-local, conditional on the specified Moore-heart comparison. -/
theorem sourceMoorePowerSequence_isHF2Local_of_boundedBelow
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X))
    (k : ℕ) : SourceIsHF2Local ((moorePowerSequence 2 X).obj k) := by
  apply sourceIsHF2Local_of_boundedBelow_layers _ N
    (sourceMoorePowerSequence_homotopy_subsingleton 2 X N hX k)
  intro d _
  apply sourceIsHF2Local_of_two_power_singleDegree
    (sourcePostnikovLayer ((moorePowerSequence 2 X).obj k) d) d
    (sourcePostnikovLayer_homotopy_subsingleton _ d) (k*2)
  simpa only [pow_mul] using sourceMoorePowerSequence_postnikovLayer_scalarSquare 2 X k d

/-- The original dyadic Moore output on every bounded-below source is
HF2-local under the specified coefficient comparison. This is the actual
Milnor limit of the original Moore tower, not an independently chosen local
replacement. -/
theorem sourceMooreCompletion_isHF2Local_of_boundedBelow
    [IsIso sourceModTwoMooreHeartToHF2]
    (X : SourceCategory.{0}) (N : ℤ)
    (hX : ∀ d : ℤ, d < N → Subsingleton ((sourceStableHomotopyAddFunctor d).obj X)) :
    SourceIsHF2Local (sourceMooreCompletion 2 X) :=
  SourceIsHF2Local.sourceHomotopyLimit (moorePowerSequence 2 X)
    (fun k => @sourceMoorePowerSequence_isHF2Local_of_boundedBelow _ X N hX k)

end KIP126.StableHomotopy.Implementation
