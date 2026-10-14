module

public import KIP126.Def.StableHomotopy.Context.Proofs
public import Mathlib.GroupTheory.QuotientGroup.Finite

@[expose] public section

namespace KIP126.StableHomotopy
open CategoryTheory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The next homotopy group of a cofiber surjects onto the kernel of the
first map; finiteness of that group therefore makes the kernel finite. -/
theorem HoCofiberSequence.finite_homotopy_kernel (T : HoCofiberSequence (C := C)) (n : ℤ)
    [Finite (HomotopyGroup (n + 1) T.Z)] : Finite (inducedMap T.f n).ker := by
  have hfinite : Finite (inducedMap T.f ((n + 1) - 1)).ker := by
    let g : HomotopyGroup (n + 1) T.Z → (inducedMap T.f ((n + 1) - 1)).ker :=
      fun z => ⟨connectingHomomorphism T (n + 1) z,
        (lesHomotopyExactH T (n + 1) _).mpr ⟨z, rfl⟩⟩
    apply Finite.of_surjective g
    intro a
    obtain ⟨z, hz⟩ := (lesHomotopyExactH T (n + 1) a.val).mp a.property
    exact ⟨z, Subtype.ext hz⟩
  have hn : n + 1 - 1 = n := by omega
  rw [hn] at hfinite
  exact hfinite

end KIP126.StableHomotopy
