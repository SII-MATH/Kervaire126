import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 96 through 127.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk96 :
    chunksCheck ((RawData.relationChunks.toList.drop 96).take 1) = true := by
  lin_square_chunks 96 1

private theorem archivedChunk97 :
    chunksCheck ((RawData.relationChunks.toList.drop 97).take 1) = true := by
  lin_square_chunks 97 1

private theorem archivedChunk98 :
    chunksCheck ((RawData.relationChunks.toList.drop 98).take 1) = true := by
  lin_square_chunks 98 1

private theorem archivedChunk99 :
    chunksCheck ((RawData.relationChunks.toList.drop 99).take 1) = true := by
  lin_square_chunks 99 1

private theorem archivedChunk100 :
    chunksCheck ((RawData.relationChunks.toList.drop 100).take 1) = true := by
  lin_square_chunks 100 1

private theorem archivedChunk101 :
    chunksCheck ((RawData.relationChunks.toList.drop 101).take 1) = true := by
  lin_square_chunks 101 1

private theorem archivedChunk102 :
    chunksCheck ((RawData.relationChunks.toList.drop 102).take 1) = true := by
  lin_square_chunks 102 1

private theorem archivedChunk103 :
    chunksCheck ((RawData.relationChunks.toList.drop 103).take 1) = true := by
  lin_square_chunks 103 1

private theorem archivedChunk104 :
    chunksCheck ((RawData.relationChunks.toList.drop 104).take 1) = true := by
  lin_square_chunks 104 1

private theorem archivedChunk105 :
    chunksCheck ((RawData.relationChunks.toList.drop 105).take 1) = true := by
  lin_square_chunks 105 1

private theorem archivedChunk106 :
    chunksCheck ((RawData.relationChunks.toList.drop 106).take 1) = true := by
  lin_square_chunks 106 1

private theorem archivedChunk107 :
    chunksCheck ((RawData.relationChunks.toList.drop 107).take 1) = true := by
  lin_square_chunks 107 1

private theorem archivedChunk108 :
    chunksCheck ((RawData.relationChunks.toList.drop 108).take 1) = true := by
  lin_square_chunks 108 1

private theorem archivedChunk109 :
    chunksCheck ((RawData.relationChunks.toList.drop 109).take 1) = true := by
  lin_square_chunks 109 1

private theorem archivedChunk110 :
    chunksCheck ((RawData.relationChunks.toList.drop 110).take 1) = true := by
  lin_square_chunks 110 1

private theorem archivedChunk111 :
    chunksCheck ((RawData.relationChunks.toList.drop 111).take 1) = true := by
  lin_square_chunks 111 1

private theorem archivedChunk112 :
    chunksCheck ((RawData.relationChunks.toList.drop 112).take 1) = true := by
  lin_square_chunks 112 1

private theorem archivedChunk113 :
    chunksCheck ((RawData.relationChunks.toList.drop 113).take 1) = true := by
  lin_square_chunks 113 1

private theorem archivedChunk114 :
    chunksCheck ((RawData.relationChunks.toList.drop 114).take 1) = true := by
  lin_square_chunks 114 1

private theorem archivedChunk115 :
    chunksCheck ((RawData.relationChunks.toList.drop 115).take 1) = true := by
  lin_square_chunks 115 1

private theorem archivedChunk116 :
    chunksCheck ((RawData.relationChunks.toList.drop 116).take 1) = true := by
  lin_square_chunks 116 1

private theorem archivedChunk117 :
    chunksCheck ((RawData.relationChunks.toList.drop 117).take 1) = true := by
  lin_square_chunks 117 1

private theorem archivedChunk118 :
    chunksCheck ((RawData.relationChunks.toList.drop 118).take 1) = true := by
  lin_square_chunks 118 1

private theorem archivedChunk119 :
    chunksCheck ((RawData.relationChunks.toList.drop 119).take 1) = true := by
  lin_square_chunks 119 1

private theorem archivedChunk120 :
    chunksCheck ((RawData.relationChunks.toList.drop 120).take 1) = true := by
  lin_square_chunks 120 1

private theorem archivedChunk121 :
    chunksCheck ((RawData.relationChunks.toList.drop 121).take 1) = true := by
  lin_square_chunks 121 1

private theorem archivedChunk122 :
    chunksCheck ((RawData.relationChunks.toList.drop 122).take 1) = true := by
  lin_square_chunks 122 1

private theorem archivedChunk123 :
    chunksCheck ((RawData.relationChunks.toList.drop 123).take 1) = true := by
  lin_square_chunks 123 1

private theorem archivedChunk124 :
    chunksCheck ((RawData.relationChunks.toList.drop 124).take 1) = true := by
  lin_square_chunks 124 1

private theorem archivedChunk125 :
    chunksCheck ((RawData.relationChunks.toList.drop 125).take 1) = true := by
  lin_square_chunks 125 1

private theorem archivedChunk126 :
    chunksCheck ((RawData.relationChunks.toList.drop 126).take 1) = true := by
  lin_square_chunks 126 1

private theorem archivedChunk127 :
    chunksCheck ((RawData.relationChunks.toList.drop 127).take 1) = true := by
  lin_square_chunks 127 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch3 :
    chunksCheck ((RawData.relationChunks.toList.drop 96).take 32) = true := by
  lin_square_compose
    archivedChunk96 archivedChunk97 archivedChunk98 archivedChunk99
    archivedChunk100 archivedChunk101 archivedChunk102 archivedChunk103
    archivedChunk104 archivedChunk105 archivedChunk106 archivedChunk107
    archivedChunk108 archivedChunk109 archivedChunk110 archivedChunk111
    archivedChunk112 archivedChunk113 archivedChunk114 archivedChunk115
    archivedChunk116 archivedChunk117 archivedChunk118 archivedChunk119
    archivedChunk120 archivedChunk121 archivedChunk122 archivedChunk123
    archivedChunk124 archivedChunk125 archivedChunk126 archivedChunk127

end KIP126.LinE2.SquareDetection
