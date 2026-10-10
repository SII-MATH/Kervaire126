import KIP126.LinProgram.Model.E2.Data
import Mathlib.LinearAlgebra.Basis.Basic

/-! Raw additive-basis catalogue from PR #110, ff39e951, Zenodo 14875701.
Rows are not yet a certified `Module.Basis`. The strict parser reports malformed
input; `basisRows` has an explicit empty fallback, checked in executable tests.
CSV indices are local to a bidegree and are not algebra-generator IDs. -/
namespace KIP126.LinE2

structure BasisRow where
  s : ℕ
  t : ℕ
  index : ℕ
  monomial : String
  deriving Inhabited, Repr, BEq, DecidableEq

def decodeBasisRow (line : String) : Except String BasisRow := do
  let [s, t, index, code] := line.splitOn "|"
    | throw "malformed basis row"
  let some s := s.toNat? | throw "invalid basis filtration"
  let some t := t.toNat? | throw "invalid basis internal degree"
  let some index := index.toNat? | throw "invalid basis index"
  return ⟨s, t, index, code⟩

def parseBasisRows : Except String (List BasisRow) :=
  (RawData.basisChunks.toList.flatMap (·.splitOn "\n")).mapM decodeBasisRow

def basisRows : List BasisRow := parseBasisRows.toOption.getD []

/-- The catalogue in CSV order, in Adams (s,t), not (stem,s), coordinates. -/
def basisRowsAt (s t : ℕ) : Array BasisRow :=
  (basisRows.filter (fun row => row.s == s && row.t == t)).toArray

abbrev BasisIndex (s t : ℕ) := Fin (basisRowsAt s t).size

def basisRowAt (s t : ℕ) (i : BasisIndex s t) : BasisRow :=
  (basisRowsAt s t)[i]

/-- Lookup by the original CSV index; absent coordinates return `none`. -/
def findBasisIndex? (s t index : ℕ) : Option (BasisIndex s t) :=
  (List.finRange (basisRowsAt s t).size).find?
    (fun i => (basisRowAt s t i).index == index)

noncomputable def basisValue (row : BasisRow) : E2 :=
  projection (monomialOfString row.monomial)

noncomputable def basisElements (s t : ℕ) : List E2 :=
  (basisRowsAt s t).toList.map basisValue

end KIP126.LinE2
