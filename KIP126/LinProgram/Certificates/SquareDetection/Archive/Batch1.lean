import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 32 through 63.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk32 :
    chunksCheck ((RawData.relationChunks.toList.drop 32).take 1) = true := by
  lin_square_chunks 32 1

private theorem archivedChunk33 :
    chunksCheck ((RawData.relationChunks.toList.drop 33).take 1) = true := by
  lin_square_chunks 33 1

private theorem archivedChunk34 :
    chunksCheck ((RawData.relationChunks.toList.drop 34).take 1) = true := by
  lin_square_chunks 34 1

private theorem archivedChunk35 :
    chunksCheck ((RawData.relationChunks.toList.drop 35).take 1) = true := by
  lin_square_chunks 35 1

private theorem archivedChunk36 :
    chunksCheck ((RawData.relationChunks.toList.drop 36).take 1) = true := by
  lin_square_chunks 36 1

private theorem archivedChunk37 :
    chunksCheck ((RawData.relationChunks.toList.drop 37).take 1) = true := by
  lin_square_chunks 37 1

private theorem archivedChunk38 :
    chunksCheck ((RawData.relationChunks.toList.drop 38).take 1) = true := by
  lin_square_chunks 38 1

private theorem archivedChunk39 :
    chunksCheck ((RawData.relationChunks.toList.drop 39).take 1) = true := by
  lin_square_chunks 39 1

private theorem archivedChunk40 :
    chunksCheck ((RawData.relationChunks.toList.drop 40).take 1) = true := by
  lin_square_chunks 40 1

private theorem archivedChunk41 :
    chunksCheck ((RawData.relationChunks.toList.drop 41).take 1) = true := by
  lin_square_chunks 41 1

private theorem archivedChunk42 :
    chunksCheck ((RawData.relationChunks.toList.drop 42).take 1) = true := by
  lin_square_chunks 42 1

private theorem archivedChunk43 :
    chunksCheck ((RawData.relationChunks.toList.drop 43).take 1) = true := by
  lin_square_chunks 43 1

private theorem archivedChunk44 :
    chunksCheck ((RawData.relationChunks.toList.drop 44).take 1) = true := by
  lin_square_chunks 44 1

private theorem archivedChunk45 :
    chunksCheck ((RawData.relationChunks.toList.drop 45).take 1) = true := by
  lin_square_chunks 45 1

private theorem archivedChunk46 :
    chunksCheck ((RawData.relationChunks.toList.drop 46).take 1) = true := by
  lin_square_chunks 46 1

private theorem archivedChunk47 :
    chunksCheck ((RawData.relationChunks.toList.drop 47).take 1) = true := by
  lin_square_chunks 47 1

private theorem archivedChunk48 :
    chunksCheck ((RawData.relationChunks.toList.drop 48).take 1) = true := by
  lin_square_chunks 48 1

private theorem archivedChunk49 :
    chunksCheck ((RawData.relationChunks.toList.drop 49).take 1) = true := by
  lin_square_chunks 49 1

private theorem archivedChunk50 :
    chunksCheck ((RawData.relationChunks.toList.drop 50).take 1) = true := by
  lin_square_chunks 50 1

private theorem archivedChunk51 :
    chunksCheck ((RawData.relationChunks.toList.drop 51).take 1) = true := by
  lin_square_chunks 51 1

private theorem archivedChunk52 :
    chunksCheck ((RawData.relationChunks.toList.drop 52).take 1) = true := by
  lin_square_chunks 52 1

private theorem archivedChunk53 :
    chunksCheck ((RawData.relationChunks.toList.drop 53).take 1) = true := by
  lin_square_chunks 53 1

private theorem archivedChunk54 :
    chunksCheck ((RawData.relationChunks.toList.drop 54).take 1) = true := by
  lin_square_chunks 54 1

private theorem archivedChunk55 :
    chunksCheck ((RawData.relationChunks.toList.drop 55).take 1) = true := by
  lin_square_chunks 55 1

private theorem archivedChunk56 :
    chunksCheck ((RawData.relationChunks.toList.drop 56).take 1) = true := by
  lin_square_chunks 56 1

private theorem archivedChunk57 :
    chunksCheck ((RawData.relationChunks.toList.drop 57).take 1) = true := by
  lin_square_chunks 57 1

private theorem archivedChunk58 :
    chunksCheck ((RawData.relationChunks.toList.drop 58).take 1) = true := by
  lin_square_chunks 58 1

private theorem archivedChunk59 :
    chunksCheck ((RawData.relationChunks.toList.drop 59).take 1) = true := by
  lin_square_chunks 59 1

private theorem archivedChunk60 :
    chunksCheck ((RawData.relationChunks.toList.drop 60).take 1) = true := by
  lin_square_chunks 60 1

private theorem archivedChunk61 :
    chunksCheck ((RawData.relationChunks.toList.drop 61).take 1) = true := by
  lin_square_chunks 61 1

private theorem archivedChunk62 :
    chunksCheck ((RawData.relationChunks.toList.drop 62).take 1) = true := by
  lin_square_chunks 62 1

private theorem archivedChunk63 :
    chunksCheck ((RawData.relationChunks.toList.drop 63).take 1) = true := by
  lin_square_chunks 63 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch1 :
    chunksCheck ((RawData.relationChunks.toList.drop 32).take 32) = true := by
  lin_square_compose
    archivedChunk32 archivedChunk33 archivedChunk34 archivedChunk35
    archivedChunk36 archivedChunk37 archivedChunk38 archivedChunk39
    archivedChunk40 archivedChunk41 archivedChunk42 archivedChunk43
    archivedChunk44 archivedChunk45 archivedChunk46 archivedChunk47
    archivedChunk48 archivedChunk49 archivedChunk50 archivedChunk51
    archivedChunk52 archivedChunk53 archivedChunk54 archivedChunk55
    archivedChunk56 archivedChunk57 archivedChunk58 archivedChunk59
    archivedChunk60 archivedChunk61 archivedChunk62 archivedChunk63

end KIP126.LinE2.SquareDetection
