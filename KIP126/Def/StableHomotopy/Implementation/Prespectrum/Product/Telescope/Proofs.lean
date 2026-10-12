module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Telescope.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Stabilized.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Separation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

variable {J : Type}

/-- The constructed product of telescopes preserves pointwise stable equivalences
between actual families with T₁ levels, for arbitrary index type. -/
theorem piTelescopeFunctor_map_stableEquivalence {X Y : J → Prespectrum.{u}}
    [∀ j n, T1Space ((X j).level n)] [∀ j n, T1Space ((Y j).level n)]
    (f : X ⟶ Y) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences ((piTelescopeFunctor J).map f) :=
  piMap_stableEquivalence_of_stabilization
    (fun j => spectrificationTelescope_hasBijectiveStabilization (X j))
    (fun j => spectrificationTelescope_hasBijectiveStabilization (Y j))
    (fun j => spectrificationTelescopeMap (f j))
    (fun j => spectrificationTelescopeMap_stableEquivalence (f j) (hf j))

theorem piTelescopeFunctor_obj_hasBijectiveStabilization (X : J → Prespectrum.{u})
    [∀ j n, T1Space ((X j).level n)] : HasBijectiveStabilization ((piTelescopeFunctor J).obj X) :=
  hasBijectiveStabilization_pi _ (fun j => spectrificationTelescope_hasBijectiveStabilization (X j))

instance piTelescopeFunctor_level_t1Space (X : J → Prespectrum.{u})
    [∀ j n, T1Space ((X j).level n)] (n : ℕ) :
    T1Space (((piTelescopeFunctor J).obj X).level n) :=
  inferInstanceAs (T1Space (∀ j, (spectrificationTelescope (X j)).level n))

end KIP126.StableHomotopy.Implementation.Prespectrum
