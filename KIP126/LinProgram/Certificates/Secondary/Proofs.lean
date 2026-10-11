module

public import KIP126.LinProgram.Certificates.Secondary.Data

@[expose] public section

namespace KIP126.Computation.Secondary
open MilnorCertificates

theorem coefficient_append (a b : Polynomial) (m : Monomial) :
    coefficient (a ++ b) m = xor (coefficient a m) (coefficient b m) := by
  simp only [coefficient, List.filter_append, List.length_append]
  have ha : (a.filter (· == m)).length % 2 < 2 := Nat.mod_lt _ (by decide)
  have hb : (b.filter (· == m)).length % 2 < 2 := Nat.mod_lt _ (by decide)
  have hab := Nat.add_mod (a.filter (· == m)).length (b.filter (· == m)).length 2
  by_cases ha0 : (a.filter (· == m)).length % 2 = 0
  · by_cases hb0 : (b.filter (· == m)).length % 2 = 0
    · simp [ha0, hb0, hab]
    · have hb1 : (b.filter (· == m)).length % 2 = 1 := by omega
      simp [ha0, hb1, hab]
  · have ha1 : (a.filter (· == m)).length % 2 = 1 := by omega
    by_cases hb0 : (b.filter (· == m)).length % 2 = 0
    · simp [ha1, hb0, hab]
    · have hb1 : (b.filter (· == m)).length % 2 = 1 := by omega
      simp [ha1, hb1, hab]
end KIP126.Computation.Secondary
