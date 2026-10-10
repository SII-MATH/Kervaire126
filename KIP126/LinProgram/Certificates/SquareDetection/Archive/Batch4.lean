import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 128 through 159.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk128 :
    chunksCheck ((RawData.relationChunks.toList.drop 128).take 1) = true := by
  lin_square_chunks 128 1

private theorem archivedChunk129 :
    chunksCheck ((RawData.relationChunks.toList.drop 129).take 1) = true := by
  lin_square_chunks 129 1

private theorem archivedChunk130 :
    chunksCheck ((RawData.relationChunks.toList.drop 130).take 1) = true := by
  lin_square_chunks 130 1

private theorem archivedChunk131 :
    chunksCheck ((RawData.relationChunks.toList.drop 131).take 1) = true := by
  lin_square_chunks 131 1

private theorem archivedChunk132 :
    chunksCheck ((RawData.relationChunks.toList.drop 132).take 1) = true := by
  lin_square_chunks 132 1

private theorem archivedChunk133 :
    chunksCheck ((RawData.relationChunks.toList.drop 133).take 1) = true := by
  lin_square_chunks 133 1

private theorem archivedChunk134 :
    chunksCheck ((RawData.relationChunks.toList.drop 134).take 1) = true := by
  lin_square_chunks 134 1

private theorem archivedChunk135 :
    chunksCheck ((RawData.relationChunks.toList.drop 135).take 1) = true := by
  lin_square_chunks 135 1

private theorem archivedChunk136 :
    chunksCheck ((RawData.relationChunks.toList.drop 136).take 1) = true := by
  lin_square_chunks 136 1

private theorem archivedChunk137 :
    chunksCheck ((RawData.relationChunks.toList.drop 137).take 1) = true := by
  lin_square_chunks 137 1

private theorem archivedChunk138 :
    chunksCheck ((RawData.relationChunks.toList.drop 138).take 1) = true := by
  lin_square_chunks 138 1

private theorem archivedChunk139 :
    chunksCheck ((RawData.relationChunks.toList.drop 139).take 1) = true := by
  lin_square_chunks 139 1

private theorem archivedChunk140 :
    chunksCheck ((RawData.relationChunks.toList.drop 140).take 1) = true := by
  lin_square_chunks 140 1

private theorem archivedChunk141 :
    chunksCheck ((RawData.relationChunks.toList.drop 141).take 1) = true := by
  lin_square_chunks 141 1

private theorem archivedChunk142 :
    chunksCheck ((RawData.relationChunks.toList.drop 142).take 1) = true := by
  lin_square_chunks 142 1

private theorem archivedChunk143 :
    chunksCheck ((RawData.relationChunks.toList.drop 143).take 1) = true := by
  lin_square_chunks 143 1

private theorem archivedChunk144 :
    chunksCheck ((RawData.relationChunks.toList.drop 144).take 1) = true := by
  lin_square_chunks 144 1

private theorem archivedChunk145 :
    chunksCheck ((RawData.relationChunks.toList.drop 145).take 1) = true := by
  lin_square_chunks 145 1

private theorem archivedChunk146 :
    chunksCheck ((RawData.relationChunks.toList.drop 146).take 1) = true := by
  lin_square_chunks 146 1

private theorem archivedChunk147 :
    chunksCheck ((RawData.relationChunks.toList.drop 147).take 1) = true := by
  lin_square_chunks 147 1

private theorem archivedChunk148 :
    chunksCheck ((RawData.relationChunks.toList.drop 148).take 1) = true := by
  lin_square_chunks 148 1

private theorem archivedChunk149 :
    chunksCheck ((RawData.relationChunks.toList.drop 149).take 1) = true := by
  lin_square_chunks 149 1

private theorem archivedChunk150 :
    chunksCheck ((RawData.relationChunks.toList.drop 150).take 1) = true := by
  lin_square_chunks 150 1

private theorem archivedChunk151 :
    chunksCheck ((RawData.relationChunks.toList.drop 151).take 1) = true := by
  lin_square_chunks 151 1

private theorem archivedChunk152 :
    chunksCheck ((RawData.relationChunks.toList.drop 152).take 1) = true := by
  lin_square_chunks 152 1

private theorem archivedChunk153 :
    chunksCheck ((RawData.relationChunks.toList.drop 153).take 1) = true := by
  lin_square_chunks 153 1

private theorem archivedChunk154 :
    chunksCheck ((RawData.relationChunks.toList.drop 154).take 1) = true := by
  lin_square_chunks 154 1

private theorem archivedChunk155 :
    chunksCheck ((RawData.relationChunks.toList.drop 155).take 1) = true := by
  lin_square_chunks 155 1

private theorem archivedChunk156 :
    chunksCheck ((RawData.relationChunks.toList.drop 156).take 1) = true := by
  lin_square_chunks 156 1

private theorem archivedChunk157 :
    chunksCheck ((RawData.relationChunks.toList.drop 157).take 1) = true := by
  lin_square_chunks 157 1

private theorem archivedChunk158 :
    chunksCheck ((RawData.relationChunks.toList.drop 158).take 1) = true := by
  lin_square_chunks 158 1

private theorem archivedChunk159 :
    chunksCheck ((RawData.relationChunks.toList.drop 159).take 1) = true := by
  lin_square_chunks 159 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch4 :
    chunksCheck ((RawData.relationChunks.toList.drop 128).take 32) = true := by
  lin_square_compose
    archivedChunk128 archivedChunk129 archivedChunk130 archivedChunk131
    archivedChunk132 archivedChunk133 archivedChunk134 archivedChunk135
    archivedChunk136 archivedChunk137 archivedChunk138 archivedChunk139
    archivedChunk140 archivedChunk141 archivedChunk142 archivedChunk143
    archivedChunk144 archivedChunk145 archivedChunk146 archivedChunk147
    archivedChunk148 archivedChunk149 archivedChunk150 archivedChunk151
    archivedChunk152 archivedChunk153 archivedChunk154 archivedChunk155
    archivedChunk156 archivedChunk157 archivedChunk158 archivedChunk159

end KIP126.LinE2.SquareDetection
