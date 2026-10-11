module

public import KIP126.LinProgram.Certificates.Secondary.Seed5487.Input
public import KIP126.LinProgram.Certificates.Secondary.Milnor.Products

@[expose] public section


/-! Five checked products from the selected native paths. Rank stability
proves their coefficients at every original eight-coordinate monomial. -/

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace KIP126.Computation.Secondary.Seed5487
open MilnorCertificates

private theorem product01_10 : IsMilnorProductAll 2 [[0,1]] [[1,0]] [[1,1]] := by
  exact fastSingletonProductCheck_sound 2 [0,1] [1,0] [[1,1]] (by decide +kernel)

private theorem product20_20 : IsMilnorProductAll 2 [[2,0]] [[2,0]] [[1,1]] := by
  exact fastSingletonProductCheck_sound 2 [2,0] [2,0] [[1,1]] (by decide +kernel)

private theorem product001_200 : IsMilnorProductAll 3 [[0,0,1]] [[2,0,0]] [[2,0,1]] := by
  exact fastSingletonProductCheck_sound 3 [0,0,1] [2,0,0] [[2,0,1]] (by decide +kernel)

private theorem product800_100 : IsMilnorProductAll 3 [[8,0,0]] [[1,0,0]] [[6,1,0],[9,0,0]] := by
  exact fastSingletonProductCheck_sound 3 [8,0,0] [1,0,0] [[6,1,0],[9,0,0]]
    (by decide +kernel)

theorem product01_10_rank8 : IsMilnorProductAll 8
    [[0,1,0,0,0,0,0,0]] [[1,0,0,0,0,0,0,0]] [[1,1,0,0,0,0,0,0]] := by
  exact stable_product 2 6 3 1 _ _ _ product01_10
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by decide)

theorem product20_20_rank8 : IsMilnorProductAll 8
    [[2,0,0,0,0,0,0,0]] [[2,0,0,0,0,0,0,0]] [[1,1,0,0,0,0,0,0]] := by
  exact stable_product 2 6 2 2 _ _ _ product20_20
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by decide)

theorem product001_200_rank8 : IsMilnorProductAll 8
    [[0,0,1,0,0,0,0,0]] [[2,0,0,0,0,0,0,0]] [[2,0,1,0,0,0,0,0]] := by
  exact stable_product 3 5 7 2 _ _ _ product001_200
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by decide)

theorem product800_100_rank8 : IsMilnorProductAll 8
    [[8,0,0,0,0,0,0,0]] [[1,0,0,0,0,0,0,0]] [[6,1,0,0,0,0,0,0],[9,0,0,0,0,0,0,0]] := by
  exact stable_product 3 5 8 1 _ _ _ product800_100
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> decide)
    (by decide)

private theorem product401_100 : IsMilnorProductAll 3
    [[4,0,1]] [[1,0,0]] [[2,1,1],[5,0,1]] := by
  exact fastSingletonProductCheck_sound 3 [4,0,1] [1,0,0] [[2,1,1],[5,0,1]]
    (by decide +kernel)

/-- The single native path for row3145729 expands into two distinct terms.
Rank stability retains all eight-coordinate monomials, without a degree cutoff. -/
theorem product401_100_rank8 : IsMilnorProductAll 8
    [[4,0,1,0,0,0,0,0]] [[1,0,0,0,0,0,0,0]]
    [[2,1,1,0,0,0,0,0],[5,0,1,0,0,0,0,0]] := by
  exact stable_product 3 5 11 1 _ _ _ product401_100
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_singleton] at hm; subst m; decide)
    (by intro m hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> decide)
    (by decide)

end KIP126.Computation.Secondary.Seed5487
