module

public import KIP126.Interface.Challenge.Computation.Delivery
public import KIP126.Def.SpectralSequence.Computation.Proofs
public import KIP126.LinProgram.Certificates.Differentials.Row5432Coordinates

@[expose] public section


/-!
# Interface/Solution/LinProgram/Differentials/VanishingD2

Fixed-model Interface construction or conditional theorem. A supplied presentation is not constructed by its use.
Public Lean declaration names are preserved; the path identifies this module's
mathematical subject and role. See `KIP126/LinProgram/README.md` for contracts,
remaining comparison obligations and the module migration table.
-/

/-! Producer-side differential certification from the supplied literature delivery.
No Main witness, total Interface producer, or table-soundness result is used. -/
namespace KIP126.Interface.Solution.LinProgram

open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.LinE2

/-- The empty CSV coordinate vector is the zero element of the data quotient. -/
theorem zero_hasCoordinates (s t : ℕ) :
    KIP126.Challenge2.HasCoordinates (0 : E2At s t) [] := by
  exact ⟨[], rfl, by simp, rfl⟩

set_option maxHeartbeats 2000000 in
/-- Certify an exported d₂ row whose target lies in the already specified
literature vanishing region. Source coordinates must be checked independently;
no CSV basis exhaustion or recorded differential is assumed. -/
theorem d2_zero_of_vanishingLine
    (literature : KIP126.Challenge2.LiteratureInterface)
    (P : LinE2Presentation) (row : KIP126.Computation.LinProofs.DifferentialRow)
    (hr : row.r = 2) (hzero : row.dx = [])
    (ht : row.t + 1 ≤ 261)
    (hpositive : (0 : ℤ) < (row.t + 1 : ℕ) - (row.s + 2 : ℕ))
    (hvanish : ((row.t + 1 : ℕ) : ℤ) - (row.s + 2 : ℕ) <
      2 * ((row.s + 2 : ℕ) : ℤ) - 3)
    (x : E2At row.s row.t) (hx : KIP126.Challenge2.HasCoordinates x row.x) :
    KIP126.Challenge2.DifferentialStatement P row := by
  rcases row with ⟨id, reason, s, t, r, xs, ys⟩
  dsimp only at hr hzero ht hpositive hvanish x hx ⊢
  subst r
  subst ys
  have ht' : t + 2 - 1 = t + 1 := by omega
  have hdeg : ((s : ℤ), (t : ℤ)) + sphereAdamsData.diffDeg 2 =
      (((s + 2 : ℕ) : ℤ), ((t + 2 - 1 : ℕ) : ℤ)) := by
    rw [sphereAdamsModel.differentialDegree]
    ext <;> simp
  letI : Subsingleton (sphereAdamsData.Page 2
      (((s + 2 : ℕ) : ℤ), ((t + 2 - 1 : ℕ) : ℤ))) := by
    rw [ht']
    exact literature.results.sphereVanishing _ _ hpositive hvanish
  have hd := hasDifferential_two_of_subsingleton_target hdeg
    (P.comparison s t (by omega) x)
  obtain ⟨h, xr, yr, hxr, hyr, hd⟩ := hd
  dsimp only [KIP126.Challenge2.DifferentialStatement]
  refine ⟨(show t ≤ 261 by omega), (show t + 2 - 1 ≤ 261 by omega),
    x, 0, hx, zero_hasCoordinates _ _, h, xr, yr,
    hxr, ?_, hd⟩
  simpa only [map_zero, Nat.cast_ofNat] using hyr

/-- Original CSV coordinate zero at (5,14), without basis certification. -/
theorem ph1_hasCoordinates : KIP126.Challenge2.HasCoordinates LowStem.ph1 [0] := by
  refine ⟨[LowStem.ph1Row], rfl, ?_, ?_⟩
  · intro row hrow
    obtain rfl := List.mem_singleton.mp hrow
    exact ⟨LowStem.ph1Row_mem, rfl, rfl⟩
  · simpa only [List.map_singleton, List.sum_singleton] using LowStem.ph1_value

/-- Producer proof of the full mathematical meaning of proofs.db record 5432.
The literature and presentation are explicit inputs; this theorem does not
consume the Main witness or the database soundness field being constructed. -/
theorem row5432 (literature : KIP126.Challenge2.LiteratureInterface)
    (P : LinE2Presentation) :
    KIP126.Challenge2.DifferentialStatement P ⟨5432, "d2", 5, 14, 2, [0], []⟩ := by
  exact d2_zero_of_vanishingLine literature P _ rfl rfl (by decide)
    (by norm_num) (by norm_num) LowStem.ph1 ph1_hasCoordinates

end KIP126.Interface.Solution.LinProgram
