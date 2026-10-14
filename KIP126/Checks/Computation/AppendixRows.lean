module

public import KIP126.Checks.SourceMetadata.AppendixTable.Rows.Catalogue.Proofs

@[expose] public section

namespace KIP126.Checks.Computation

open KIP126.Computation

example : appendixRows.length = 401 := appendixRows_length
example : (appendixRows.map AppendixRow.key).Nodup := appendixRows_keys_nodup
example : appendixRowsValid = true := appendixRows_valid
example : appendixZeroBands.length = 9 := appendixZeroBands_length
example : appendixZeroBandsValid = true := appendixZeroBands_valid

end KIP126.Checks.Computation
