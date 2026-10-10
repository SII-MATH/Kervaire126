import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 64 through 95.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk64 :
    chunksCheck ((RawData.relationChunks.toList.drop 64).take 1) = true := by
  lin_square_chunks 64 1

private theorem archivedChunk65 :
    chunksCheck ((RawData.relationChunks.toList.drop 65).take 1) = true := by
  lin_square_chunks 65 1

private theorem archivedChunk66 :
    chunksCheck ((RawData.relationChunks.toList.drop 66).take 1) = true := by
  lin_square_chunks 66 1

private theorem archivedChunk67 :
    chunksCheck ((RawData.relationChunks.toList.drop 67).take 1) = true := by
  lin_square_chunks 67 1

private theorem archivedChunk68 :
    chunksCheck ((RawData.relationChunks.toList.drop 68).take 1) = true := by
  lin_square_chunks 68 1

private theorem archivedChunk69 :
    chunksCheck ((RawData.relationChunks.toList.drop 69).take 1) = true := by
  lin_square_chunks 69 1

private theorem archivedChunk70 :
    chunksCheck ((RawData.relationChunks.toList.drop 70).take 1) = true := by
  lin_square_chunks 70 1

private theorem archivedChunk71 :
    chunksCheck ((RawData.relationChunks.toList.drop 71).take 1) = true := by
  lin_square_chunks 71 1

private theorem archivedChunk72 :
    chunksCheck ((RawData.relationChunks.toList.drop 72).take 1) = true := by
  lin_square_chunks 72 1

private theorem archivedChunk73 :
    chunksCheck ((RawData.relationChunks.toList.drop 73).take 1) = true := by
  lin_square_chunks 73 1

private theorem archivedChunk74 :
    chunksCheck ((RawData.relationChunks.toList.drop 74).take 1) = true := by
  lin_square_chunks 74 1

private theorem archivedChunk75 :
    chunksCheck ((RawData.relationChunks.toList.drop 75).take 1) = true := by
  lin_square_chunks 75 1

private theorem archivedChunk76 :
    chunksCheck ((RawData.relationChunks.toList.drop 76).take 1) = true := by
  lin_square_chunks 76 1

private theorem archivedChunk77 :
    chunksCheck ((RawData.relationChunks.toList.drop 77).take 1) = true := by
  lin_square_chunks 77 1

private theorem archivedChunk78 :
    chunksCheck ((RawData.relationChunks.toList.drop 78).take 1) = true := by
  lin_square_chunks 78 1

private theorem archivedChunk79 :
    chunksCheck ((RawData.relationChunks.toList.drop 79).take 1) = true := by
  lin_square_chunks 79 1

private theorem archivedChunk80 :
    chunksCheck ((RawData.relationChunks.toList.drop 80).take 1) = true := by
  lin_square_chunks 80 1

private theorem archivedChunk81 :
    chunksCheck ((RawData.relationChunks.toList.drop 81).take 1) = true := by
  lin_square_chunks 81 1

private theorem archivedChunk82 :
    chunksCheck ((RawData.relationChunks.toList.drop 82).take 1) = true := by
  lin_square_chunks 82 1

private theorem archivedChunk83 :
    chunksCheck ((RawData.relationChunks.toList.drop 83).take 1) = true := by
  lin_square_chunks 83 1

private theorem archivedChunk84 :
    chunksCheck ((RawData.relationChunks.toList.drop 84).take 1) = true := by
  lin_square_chunks 84 1

private theorem archivedChunk85 :
    chunksCheck ((RawData.relationChunks.toList.drop 85).take 1) = true := by
  lin_square_chunks 85 1

private theorem archivedChunk86 :
    chunksCheck ((RawData.relationChunks.toList.drop 86).take 1) = true := by
  lin_square_chunks 86 1

private theorem archivedChunk87 :
    chunksCheck ((RawData.relationChunks.toList.drop 87).take 1) = true := by
  lin_square_chunks 87 1

private theorem archivedChunk88 :
    chunksCheck ((RawData.relationChunks.toList.drop 88).take 1) = true := by
  lin_square_chunks 88 1

private theorem archivedChunk89 :
    chunksCheck ((RawData.relationChunks.toList.drop 89).take 1) = true := by
  lin_square_chunks 89 1

private theorem archivedChunk90 :
    chunksCheck ((RawData.relationChunks.toList.drop 90).take 1) = true := by
  lin_square_chunks 90 1

private theorem archivedChunk91 :
    chunksCheck ((RawData.relationChunks.toList.drop 91).take 1) = true := by
  lin_square_chunks 91 1

private theorem archivedChunk92 :
    chunksCheck ((RawData.relationChunks.toList.drop 92).take 1) = true := by
  lin_square_chunks 92 1

private theorem archivedChunk93 :
    chunksCheck ((RawData.relationChunks.toList.drop 93).take 1) = true := by
  lin_square_chunks 93 1

private theorem archivedChunk94 :
    chunksCheck ((RawData.relationChunks.toList.drop 94).take 1) = true := by
  lin_square_chunks 94 1

private theorem archivedChunk95 :
    chunksCheck ((RawData.relationChunks.toList.drop 95).take 1) = true := by
  lin_square_chunks 95 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch2 :
    chunksCheck ((RawData.relationChunks.toList.drop 64).take 32) = true := by
  lin_square_compose
    archivedChunk64 archivedChunk65 archivedChunk66 archivedChunk67
    archivedChunk68 archivedChunk69 archivedChunk70 archivedChunk71
    archivedChunk72 archivedChunk73 archivedChunk74 archivedChunk75
    archivedChunk76 archivedChunk77 archivedChunk78 archivedChunk79
    archivedChunk80 archivedChunk81 archivedChunk82 archivedChunk83
    archivedChunk84 archivedChunk85 archivedChunk86 archivedChunk87
    archivedChunk88 archivedChunk89 archivedChunk90 archivedChunk91
    archivedChunk92 archivedChunk93 archivedChunk94 archivedChunk95

end KIP126.LinE2.SquareDetection
