import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 224 through 226.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk224 :
    chunksCheck ((RawData.relationChunks.toList.drop 224).take 1) = true := by
  lin_square_chunks 224 1

private theorem archivedChunk225 :
    chunksCheck ((RawData.relationChunks.toList.drop 225).take 1) = true := by
  lin_square_chunks 225 1

private theorem archivedChunk226 :
    chunksCheck ((RawData.relationChunks.toList.drop 226).take 1) = true := by
  lin_square_chunks 226 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch7 :
    chunksCheck ((RawData.relationChunks.toList.drop 224).take 3) = true := by
  lin_square_compose
    archivedChunk224 archivedChunk225 archivedChunk226

end KIP126.LinE2.SquareDetection
