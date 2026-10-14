module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.Data

@[expose] public section

/-! Maps of sequential prespectra commuting with bonding maps up to a
specified based homotopy, and their strict mapping-path replacement. -/

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

noncomputable section

/-- Homotopy compatibility is explicit and constant whenever the bonding
cylinder is collapsed. This is data for constructing a strict zigzag. -/
structure HomotopyMap (X Y : Prespectrum.{u}) where
  level : ∀ n, C(X.level n, Y.level n)
  point : ∀ n, level n (X.level n).point = (Y.level n).point
  bondHomotopy : ∀ n, C(I × (X.level n × I), Y.level (n + 1))
  bondHomotopy_zero : ∀ n x t,
    bondHomotopy n (0, (x, t)) = level (n + 1) (X.bond n (x, t))
  bondHomotopy_one : ∀ n x t,
    bondHomotopy n (1, (x, t)) = Y.bond n (level n x, t)
  bondHomotopy_collapsed : ∀ n s x t,
    x = (X.level n).point ∨ t = 0 ∨ t = 1 →
      bondHomotopy n (s, (x, t)) = (Y.level (n + 1)).point

namespace HomotopyMap

variable {X Y : Prespectrum.{u}} (f : HomotopyMap X Y)

/-- A point in the replacement carries a path starting at its specified
image. Its other endpoint is the strict map to the target. -/
def pathLevel (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of {p : X.level n × C(I, Y.level n) // p.2 0 = f.level n p.1}
  point := ⟨((X.level n).point, ContinuousMap.const _ (Y.level n).point), (f.point n).symm⟩

/-- First concatenate the bonding comparison homotopy. -/
def bondFirstPath (n : ℕ) (z : f.pathLevel n × I) :
    Path (f.level (n + 1) (X.bond n (z.1.val.1, z.2)))
      (Y.bond n (f.level n z.1.val.1, z.2)) where
  toFun s := f.bondHomotopy n (s, (z.1.val.1, z.2))
  continuous_toFun := (f.bondHomotopy n).continuous.comp (continuous_id.prodMk continuous_const)
  source' := f.bondHomotopy_zero n _ _
  target' := f.bondHomotopy_one n _ _

/-- Then apply the target bonding map to the carried path. -/
def bondSecondPath (n : ℕ) (z : f.pathLevel n × I) :
    Path (Y.bond n (f.level n z.1.val.1, z.2))
      (Y.bond n (z.1.val.2 1, z.2)) where
  toFun s := Y.bond n (z.1.val.2 s, z.2)
  continuous_toFun := (Y.bond n).continuous.comp (z.1.val.2.continuous.prodMk continuous_const)
  source' := congrArg (fun y => Y.bond n (y, z.2)) z.1.property
  target' := rfl

/-- The mapping-path bonding operation is an actual continuous map. -/
def pathBond (n : ℕ) : C(f.pathLevel n × I, f.pathLevel (n + 1)) := by
  have hfirst : Continuous (fun z : (f.pathLevel n × I) × I =>
      f.bondFirstPath n z.1 z.2) :=
    (f.bondHomotopy n).continuous.comp
      (continuous_snd.prodMk
        (continuous_fst.fst.subtype_val.fst.prodMk continuous_fst.snd))
  have hsecond : Continuous (fun z : (f.pathLevel n × I) × I =>
      f.bondSecondPath n z.1 z.2) :=
    (Y.bond n).continuous.comp
      ((continuous_fst.fst.subtype_val.snd.eval continuous_snd).prodMk continuous_fst.snd)
  have hpath : Continuous (fun z : (f.pathLevel n × I) × I =>
      (f.bondFirstPath n z.1 |>.trans (f.bondSecondPath n z.1)) z.2) :=
    Path.trans_continuous_family _ hfirst _ hsecond
  let paths : C(f.pathLevel n × I, C(I, Y.level (n + 1))) :=
    (⟨_, hpath⟩ : C((f.pathLevel n × I) × I, Y.level (n + 1))).curry
  exact ⟨fun z => ⟨(X.bond n (z.1.val.1, z.2), paths z),
    (f.bondFirstPath n z |>.trans (f.bondSecondPath n z)).source⟩,
    (((X.bond n).continuous.comp
      (continuous_fst.subtype_val.fst.prodMk continuous_snd)).prodMk paths.continuous).subtype_mk _⟩

/-- The replacement has strict bonding maps to both source and target. -/
def pathSpectrum : Prespectrum.{u} where
  level := f.pathLevel
  bond := f.pathBond
  bond_point := by
    intro n t
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_point n t
    · apply ContinuousMap.ext
      intro s
      change (f.bondFirstPath n ((f.pathLevel n).point, t) |>.trans
        (f.bondSecondPath n ((f.pathLevel n).point, t))) s = (Y.level (n + 1)).point
      rw [Path.trans_apply]
      split_ifs
      · exact f.bondHomotopy_collapsed n _ _ _ (Or.inl rfl)
      · exact Y.bond_point n t
  bond_zero := by
    intro n x
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_zero n x.val.1
    · apply ContinuousMap.ext
      intro s
      change (f.bondFirstPath n (x, 0) |>.trans (f.bondSecondPath n (x, 0))) s =
        (Y.level (n + 1)).point
      rw [Path.trans_apply]
      split_ifs
      · exact f.bondHomotopy_collapsed n _ _ _ (Or.inr (Or.inl rfl))
      · exact Y.bond_zero n _
  bond_one := by
    intro n x
    apply Subtype.ext
    apply Prod.ext
    · exact X.bond_one n x.val.1
    · apply ContinuousMap.ext
      intro s
      change (f.bondFirstPath n (x, 1) |>.trans (f.bondSecondPath n (x, 1))) s =
        (Y.level (n + 1)).point
      rw [Path.trans_apply]
      split_ifs
      · exact f.bondHomotopy_collapsed n _ _ _ (Or.inr (Or.inr rfl))
      · exact Y.bond_one n _

/-- The strict source projection forgets the carried path. -/
def sourceProjection : f.pathSpectrum ⟶ X where
  level _n := ⟨fun z => z.val.1, continuous_subtype_val.fst⟩
  point _n := rfl
  bond _ _ _ := rfl

/-- The strict target projection evaluates the carried path at its endpoint. -/
def targetProjection : f.pathSpectrum ⟶ Y where
  level _n := ⟨fun z => z.val.2 1, continuous_subtype_val.snd.eval continuous_const⟩
  point _n := rfl
  bond n z t := (f.bondFirstPath n (z, t) |>.trans (f.bondSecondPath n (z, t))).target

/-- The levelwise section carries the constant path at the specified image. -/
def sourceSection (n : ℕ) : C(X.level n, f.pathLevel n) :=
  ⟨fun x => ⟨(x, ContinuousMap.const _ (f.level n x)), rfl⟩,
    (continuous_id.prodMk ((ContinuousMap.const' (X := ↥I) (Y := Y.level n)).continuous.comp (f.level n).continuous)).subtype_mk _⟩

/-- A level map acts on the actual based cubical loops. -/
def mapLoop (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop (Fin r) (Y.level n) (Y.level n).point :=
  ⟨(f.level n).comp p.val, fun t ht =>
    (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩

/-- The same operation on stable representatives retains their actual stage. -/
def mapRepresentative {d : ℤ} (a : Representative X d) : Representative Y d where
  stage := a.stage
  dimension := a.dimension
  degree := a.degree
  loop := f.mapLoop a.stage a.dimension a.loop

end HomotopyMap
end
end KIP126.StableHomotopy.Implementation.Prespectrum
