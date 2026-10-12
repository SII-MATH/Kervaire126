module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Order.Initial.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Simplicial KIP126.Topology.SimplicialRealization

universe u

/-- The actual cone vertex represents the specified initial basepoint. -/
theorem zeroPrespectrumLevelOrderHomeomorph_vertex (n : ℕ) :
    zeroPrespectrumLevelOrderHomeomorph.{u} n
      (orderVertex _ (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1))))) =
        (zeroPrespectrum.{u}.level n).point := by
  letI : Subsingleton (zeroPrespectrum.{u}.level n) := inferInstanceAs (Subsingleton PUnit)
  exact Subsingleton.elim _ _

/-- The inverse initial model sends the original basepoint to that same
actual cone vertex, retaining the point needed for later based comparisons. -/
theorem zeroPrespectrumLevelOrderHomeomorph_symm_point (n : ℕ) :
    (zeroPrespectrumLevelOrderHomeomorph.{u} n).symm
      (zeroPrespectrum.{u}.level n).point =
        orderVertex _ (⊤ : WithTop (orderProperChains (ULift.{u} (Fin 1)))) := by
  apply (zeroPrespectrumLevelOrderHomeomorph n).injective
  rw [(zeroPrespectrumLevelOrderHomeomorph n).apply_symm_apply,
    zeroPrespectrumLevelOrderHomeomorph_vertex]

end KIP126.StableHomotopy.Implementation.Prespectrum
