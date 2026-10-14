module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory Simplicial Opposite
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

theorem singularPrespectrumBond_evaluation (X : Prespectrum.{u}) (n : ℕ)
    (x : singularRealization (X.level n)) (t : I) :
    singularEvaluation (X.level (n+1)) (singularPrespectrumBond X n (x,t)) =
      X.bond n (singularEvaluation (X.level n) x,t) :=
  singularCylinder_evaluation _ _ _ _

theorem singularPrespectrumBond_point (X : Prespectrum.{u}) (n : ℕ) (t : I) :
    singularPrespectrumBond X n ((singularRealization (X.level n)).point,t) =
      (singularRealization (X.level (n+1))).point := by
  let K := TopCat.toSSet.obj (X.level n).space
  let φ : (Δ[0] : SSet.{u}) ⟶ K :=
    SSet.const (TopCat.toSSetObj₀Equiv.symm (X.level n).point)
  have h := singularCylinder_precomp φ (X.level (n+1)).space
    (singularBondDomain X n) default t
  have hc : (singularBondDomain X n).comp
      ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id I)) =
      ContinuousMap.const _ (X.level (n+1)).point := by
    apply ContinuousMap.ext
    rintro ⟨x,s⟩
    change X.bond n (singularEvaluation (X.level n) (SSet.toTop.map φ x),s) = _
    rw [show φ = SSet.const (TopCat.toSSetObj₀Equiv.symm (X.level n).point) from rfl,
      realization_const_apply]
    change X.bond n (singularEvaluation (X.level n) (singularRealization (X.level n)).point,s) = _
    rw [singularEvaluation_point,X.bond_point]
    rfl
  rw [hc,singularCylinder_const] at h
  rw [show φ = SSet.const (TopCat.toSSetObj₀Equiv.symm (X.level n).point) from rfl,
    realization_const_apply] at h
  exact h

private theorem singularPrespectrumBond_end (X : Prespectrum.{u}) (n : ℕ)
    (i : Fin 2) (x : singularRealization (X.level n)) :
    singularPrespectrumBond X n
      (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      (singularRealization (X.level (n+1))).point := by
  have h := singularCylinder_endpoint (TopCat.toSSet.obj (X.level n).space)
    (X.level (n+1)).space (singularBondDomain X n) i x
  have he : TopCat.ofHom (Y := (X.level (n+1)).space)
      ((singularBondDomain X n).comp ((ContinuousMap.id _).prodMk
        (ContinuousMap.const _ (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))) =
      TopCat.const (X.level (n+1)).point := by
    apply ConcreteCategory.hom_ext
    intro y
    fin_cases i
    · exact X.bond_zero n (singularEvaluation (X.level n) y)
    · exact X.bond_one n (singularEvaluation (X.level n) y)
  have h' := h.trans (congrArg (fun a : SSet.toTop.obj
      (TopCat.toSSet.obj (X.level n).space) ⟶ (X.level (n+1)).space =>
    SSet.toTop.map (sSetTopAdj.homEquiv _ _ a) x) he)
  have hc : sSetTopAdj.homEquiv _ _ (TopCat.const (X.level (n+1)).point) =
      SSet.const (X := TopCat.toSSet.obj (X.level n).space)
        (TopCat.toSSetObj₀Equiv.symm (X.level (n+1)).point) := by
    simp [Adjunction.homEquiv_unit]
  rw [hc,realization_const_apply] at h'
  exact h'

theorem singularPrespectrumBond_zero (X : Prespectrum.{u}) (n : ℕ)
    (x : singularRealization (X.level n)) :
    singularPrespectrumBond X n (x,0) = (singularRealization (X.level (n+1))).point :=
  singularPrespectrumBond_end X n 0 x

theorem singularPrespectrumBond_one (X : Prespectrum.{u}) (n : ℕ)
    (x : singularRealization (X.level n)) :
    singularPrespectrumBond X n (x,1) = (singularRealization (X.level (n+1))).point :=
  singularPrespectrumBond_end X n 1 x

theorem singularPrespectrumBond_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : singularRealization (X.level n)) (t : I) :
    singularRealizationMap (⟨f.level (n+1),f.point (n+1)⟩ : X.level (n+1) ⟶ Y.level (n+1))
      (singularPrespectrumBond X n (x,t)) =
      singularPrespectrumBond Y n
        (singularRealizationMap (⟨f.level n,f.point n⟩ : X.level n ⟶ Y.level n) x,t) := by
  let φ := TopCat.toSSet.map (TopCat.ofHom (X := (X.level n).space) (Y := (Y.level n).space)
    (f.level n))
  have hpost := singularCylinder_postcomp (TopCat.toSSet.obj (X.level n).space)
    (TopCat.ofHom (X := (X.level (n+1)).space) (Y := (Y.level (n+1)).space) (f.level (n+1)))
    (singularBondDomain X n) (x,t)
  have hpre := singularCylinder_precomp φ (Y.level (n+1)).space (singularBondDomain Y n) x t
  have hc : (f.level (n+1)).comp (singularBondDomain X n) =
      (singularBondDomain Y n).comp ((SSet.toTop.map φ).hom.prodMap (ContinuousMap.id I)) := by
    apply ContinuousMap.ext
    rintro ⟨z,s⟩
    change f.level (n+1) (X.bond n (singularEvaluation (X.level n) z,s)) =
      Y.bond n (singularEvaluation (Y.level n) (singularRealizationMap
        (⟨f.level n,f.point n⟩ : X.level n ⟶ Y.level n) z),s)
    rw [singularEvaluation_natural,f.bond]
  exact hpost.trans ((congrArg (fun c => singularCylinder
    (TopCat.toSSet.obj (X.level n).space) (Y.level (n+1)).space c (x,t)) hc).trans hpre.symm)

end KIP126.StableHomotopy.Implementation
