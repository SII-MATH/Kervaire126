module

public import KIP126.Def.StableHomotopy.FiniteType.Proofs

@[expose] public section

/-! The other two directions of finite-type and lower-bound closure in
an actual distinguished cofiber triangle. -/

namespace KIP126.StableHomotopy

open CategoryTheory MonoidalCategory Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

/-- The first term of a cofiber triangle is bounded below when the second
and third terms are bounded below. -/
theorem BoundedBelow.of_cofiber_left (T : HoCofiberSequence (C := C))
    (hY : BoundedBelow T.Y) (hZ : BoundedBelow T.Z) : BoundedBelow T.X := by
  obtain ⟨NY, hNY⟩ := hY
  obtain ⟨NZ, hNZ⟩ := hZ
  refine ⟨min NY (NZ - 1), fun n hn => ?_⟩
  letI := hNY ((n + 1) - 1) (by have := min_le_left NY (NZ - 1); omega)
  letI := hNZ (n + 1) (by have := min_le_right NY (NZ - 1); omega)
  have hz (x : HomotopyGroup ((n + 1) - 1) T.X) : x = 0 := by
    obtain ⟨z, hz⟩ := (lesHomotopyExactH T (n + 1) x).mp (Subsingleton.elim _ _)
    rw [show z = 0 from Subsingleton.elim _ _] at hz
    simpa using hz.symm
  have hs : Subsingleton (HomotopyGroup ((n + 1) - 1) T.X) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  simpa using hs

/-- The middle term of a cofiber triangle is bounded below when both
outside terms are bounded below. -/
theorem BoundedBelow.of_cofiber_middle (T : HoCofiberSequence (C := C))
    (hX : BoundedBelow T.X) (hZ : BoundedBelow T.Z) : BoundedBelow T.Y := by
  obtain ⟨NX, hNX⟩ := hX
  obtain ⟨NZ, hNZ⟩ := hZ
  refine ⟨min NX NZ, fun n hn => ?_⟩
  letI := hNX n (lt_of_lt_of_le hn (min_le_left _ _))
  letI := hNZ n (lt_of_lt_of_le hn (min_le_right _ _))
  have hz (y : HomotopyGroup n T.Y) : y = 0 := by
    obtain ⟨x, hx⟩ := (les_homotopy_exact_f T n y).mp (Subsingleton.elim _ _)
    rw [show x = 0 from Subsingleton.elim _ _] at hx
    simpa using hx.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- The first term has finite mod-two homology when the other two terms do. -/
theorem FiniteMod2Type.of_cofiber_left {H : Mod2EilenbergMacLane (C := C)}
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (T : HoCofiberSequence (C := C)) (hY : FiniteMod2Type H T.Y)
    (hZ : FiniteMod2Type H T.Z) : FiniteMod2Type H T.X := by
  classical
  intro n
  let U := T.map (tensorLeft H.HF2)
  letI : Finite (HomotopyGroup ((n + 1) - 1) U.Y) := hY _
  letI : Finite (HomotopyGroup (n + 1) U.Z) := hZ _
  letI := Fintype.ofFinite (HomotopyGroup ((n + 1) - 1) U.Y)
  letI := Fintype.ofFinite (HomotopyGroup (n + 1) U.Z)
  letI := AddGroup.fintypeOfKerLeRange (connectingHomomorphism U (n + 1))
    (inducedMap U.f ((n + 1) - 1)) (by
      intro x hx
      exact (lesHomotopyExactH U (n + 1) x).mp hx)
  change Finite (HomotopyGroup n U.X)
  simpa using (inferInstance : Finite (HomotopyGroup ((n + 1) - 1) U.X))

/-- The middle term has finite mod-two homology when both outside terms do. -/
theorem FiniteMod2Type.of_cofiber_middle {H : Mod2EilenbergMacLane (C := C)}
    [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
    (T : HoCofiberSequence (C := C)) (hX : FiniteMod2Type H T.X)
    (hZ : FiniteMod2Type H T.Z) : FiniteMod2Type H T.Y := by
  classical
  intro n
  let U := T.map (tensorLeft H.HF2)
  letI : Finite (HomotopyGroup n U.X) := hX _
  letI : Finite (HomotopyGroup n U.Z) := hZ _
  letI := Fintype.ofFinite (HomotopyGroup n U.X)
  letI := Fintype.ofFinite (HomotopyGroup n U.Z)
  letI := AddGroup.fintypeOfKerLeRange (inducedMap U.f n) (inducedMap U.g n) (by
    intro y hy
    exact (les_homotopy_exact_f U n y).mp hy)
  change Finite (HomotopyGroup n U.Y)
  infer_instance

end KIP126.StableHomotopy
