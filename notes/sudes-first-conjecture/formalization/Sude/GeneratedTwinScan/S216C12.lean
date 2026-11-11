import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21321)) 454557741 454590509 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454557741 454590509).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21321 454557741 454590509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21321)) 454590509 454623277 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454590509 454623277).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21321 454590509 454623277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21322)) 454623277 454656045 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 454623277 454656045).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21322 454623277 454656045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21323)) 454656045 454688813 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454656045 454688813).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21323 454656045 454688813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454557741 454623277).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 454557741 ≤ 454590509)
    (by decide : 454590509 ≤ 454623277) block0 block1

theorem join_0_1 : (twinPrimeSegment 454623277 454688813).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 454623277 ≤ 454656045)
    (by decide : 454656045 ≤ 454688813) block2 block3

theorem join_1_0 : (twinPrimeSegment 454557741 454688813).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 454557741 ≤ 454623277)
    (by decide : 454623277 ≤ 454688813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454557741 454688813).card = 451 := join_1_0

end S216C12
end Sude.GeneratedTwinScan
