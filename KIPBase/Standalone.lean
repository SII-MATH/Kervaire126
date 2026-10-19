import KIPBase.Basic
import KIPBase.multiplicativeSS.Adams
import KIPBase.multiplicativeSS.AdamsDetection
import KIPBase.multiplicativeSS.AdamsEnriched
import KIPBase.multiplicativeSS.AdamsMasseyProduct
import KIPBase.multiplicativeSS.Basic
import KIPBase.multiplicativeSS.CategoricalTodaBracket
import KIPBase.multiplicativeSS.DGA
import KIPBase.multiplicativeSS.MasseyProduct
import KIPBase.multiplicativeSS.ModuleCat
import KIPBase.multiplicativeSS.Monoidal
import KIPBase.multiplicativeSS.Moss
import KIPBase.multiplicativeSS.MossCrossing
import KIPBase.multiplicativeSS.TodaBracket
import KIPBase.multiplicativeSS.TriangulatedTodaBracket
import KIPBase.multiplicativeSS.adamsdata.adamsE2
import KIPBase.multiplicativeSS.adamsdata.homotopy

/-!
# KIPBase standalone build root

This module is the root of the standalone `KIPBase` Lake project.  It imports
the historical KIP base itself, including the multiplicative spectral-sequence
development, but intentionally does not import `KIPBase.Compatibility`: that
namespace is an adapter to `KIP126.Core` and is therefore built only by the
parent KIP126 project.
-/
