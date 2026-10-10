import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.Boundary.Proofs
import KIP126.Def.ClassicalAdams.TowerHomology.MilnorCoordinates.SphereTensor.Proofs
import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Monomials.Words.Single.Proofs

namespace KIP126.Classical.Adams

noncomputable section
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Steenrod.Milnor
open scoped TensorProduct DirectSum

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] (H : Mod2EilenbergMacLane (C := C))
  (R : Mod2RingStructure H) (K : Mod2CooperationKunneth H R)
  (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- Every reduced Milnor basis vector, tensored with the already normalized
sphere unit, becomes exactly its one-slot word under the actual boundary. -/
theorem sphereTowerHomologyWordEquiv_firstBoundary_basis (n : ℤ)
    (a : PositiveMonomial (n + 1)) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
      (show n = (n + 1) - 1 by omega)
    sphereTowerHomologyWordEquiv H R K B 1 n
      (e.symm (adamsTensorBoundary H R K SphereSpectrum (n + 1)
        ((sphereCooperationTensorEquiv H R (n + 1)).symm (B.basis (n + 1) a).val))) =
      Finsupp.single (singleMilnorWordEquiv (n + 1) a) 1 := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  let d : MilnorWord 0 (n + 1 - (n + 1)) :=
    ⟨Fin.elim0, by simp [wordDegree], fun i => Fin.elim0 i⟩
  have hx : (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord 0 t →₀ ZMod 2)
      (show n + 1 - (n + 1) + (0 : ℕ) = n + (0 + 1 : ℕ) - (n + 1) by omega))
      (sphereTowerHomologyWordEquiv H R K B 0 (n + 1 - (n + 1))
        ((sphereHomologyScalarEquiv H R (n + 1 - (n + 1)) (by omega)).symm 1)) =
        Finsupp.single d 1 := by
    have hbase (j : ℤ) (hj : j = 0) (d' : MilnorWord 0 (j + (0 : ℕ))) :
        sphereTowerHomologyWordEquiv H R K B 0 j
          ((sphereHomologyScalarEquiv H R j hj).symm 1) = Finsupp.single d' 1 := by
      subst j
      have hd' : d' = emptyMilnorWord := Subsingleton.elim _ _
      rw [hd']
      change (sphereHomologyEmptyWordEquiv H R 0)
        ((sphereHomologyEmptyWordEquiv H R 0).symm _) = _
      exact LinearEquiv.apply_symm_apply _ _
    have hcast {j l : ℤ} (hj : j = l) (d₁ : MilnorWord 0 j) (d₂ : MilnorWord 0 l) :
        (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord 0 t →₀ ZMod 2) hj)
          (Finsupp.single d₁ 1) = Finsupp.single d₂ 1 := by
      subst l
      have hd : d₁ = d₂ := Subsingleton.elim _ _
      subst d₂
      rfl
    let d' : MilnorWord 0 (n + 1 - (n + 1) + (0 : ℕ)) :=
      ⟨Fin.elim0, by simp [wordDegree], fun i => Fin.elim0 i⟩
    exact (congrArg (LinearEquiv.cast (R := ZMod 2) (M := fun t => MilnorWord 0 t →₀ ZMod 2)
      (show n + 1 - (n + 1) + (0 : ℕ) = n + (0 + 1 : ℕ) - (n + 1) by omega))
        (hbase _ (by omega) d')).trans (hcast _ d' d)
  dsimp only
  rw [sphereCooperationTensorEquiv_symm_apply]
  have h := sphereTowerHomologyWordEquiv_boundary_basis_single H R K B 0 n (n + 1) a
    ((sphereHomologyScalarEquiv H R (n + 1 - (n + 1)) (by omega)).symm 1) d 1 hx
  have hd : wordConsEquiv 0 (n + (0 + 1 : ℕ)) ⟨n + 1, a, d⟩ =
      singleMilnorWordEquiv (n + 1) a := by
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  rw [hd] at h
  exact h

/-- The entire first-stage boundary on reduced cooperations is the
one-slot basis-coordinate map, not merely its values on selected classes. -/
theorem sphereTowerHomologyWordEquiv_firstBoundary_reduced (n : ℤ) :
    letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
      fun i => mod2HomologyModule H R i H.HF2
    letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
      fun i => mod2HF2HomotopyModule H R i
    ∀ a : LinearMap.ker (cooperationCounitF2 H R (n + 1)),
    let e := LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
      (show n = (n + 1) - 1 by omega)
    sphereTowerHomologyWordEquiv H R K B 1 n
      (e.symm (adamsTensorBoundary H R K SphereSpectrum (n + 1)
        ((sphereCooperationTensorEquiv H R (n + 1)).symm a.val))) =
      Finsupp.domLCongr (R := ZMod 2) (singleMilnorWordEquiv (n + 1))
        ((B.basis (n + 1)).repr a) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  intro a
  let e := LinearEquiv.cast (R := ZMod 2)
    (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit SphereSpectrum 1))
    (show n = (n + 1) - 1 by omega)
  let f := (sphereTowerHomologyWordEquiv H R K B 1 n).toLinearMap.comp
    (e.symm.toLinearMap.comp ((adamsTensorBoundary H R K SphereSpectrum (n + 1)).comp
      ((sphereCooperationTensorEquiv H R (n + 1)).symm.toLinearMap.comp
        (LinearMap.ker (cooperationCounitF2 H R (n + 1))).subtype)))
  let g := (Finsupp.domLCongr (R := ZMod 2) (singleMilnorWordEquiv (n + 1))).toLinearMap.comp
    (B.basis (n + 1)).repr.toLinearMap
  have hfg : f = g := by
    apply (B.basis (n + 1)).ext
    intro d
    change f (B.basis (n + 1) d) =
      Finsupp.domLCongr (R := ZMod 2) (singleMilnorWordEquiv (n + 1))
        ((B.basis (n + 1)).repr (B.basis (n + 1) d))
    rw [Module.Basis.repr_self, Finsupp.domLCongr_single]
    exact sphereTowerHomologyWordEquiv_firstBoundary_basis H R K B n d
  exact LinearMap.congr_fun hfg a

end
end KIP126.Classical.Adams
