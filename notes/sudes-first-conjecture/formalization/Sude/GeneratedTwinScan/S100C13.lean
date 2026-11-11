import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14541)) 211419181 211451949 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211419181 211451949).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14541 211419181 211451949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14542)) 211451949 211484717 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211451949 211484717).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14542 211451949 211484717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14543)) 211484717 211517485 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211484717 211517485).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14543 211484717 211517485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14544)) 211517485 211550253 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211517485 211550253).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14544 211517485 211550253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211419181 211484717).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 211419181 ≤ 211451949)
    (by decide : 211451949 ≤ 211484717) block0 block1

theorem join_0_1 : (twinPrimeSegment 211484717 211550253).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 211484717 ≤ 211517485)
    (by decide : 211517485 ≤ 211550253) block2 block3

theorem join_1_0 : (twinPrimeSegment 211419181 211550253).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 211419181 ≤ 211484717)
    (by decide : 211484717 ≤ 211550253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211419181 211550253).card = 466 := join_1_0

end S100C13
end Sude.GeneratedTwinScan
