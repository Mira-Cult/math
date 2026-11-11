import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18875)) 356253741 356286509 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356253741 356286509).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18875 356253741 356286509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18876)) 356286509 356319277 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356286509 356319277).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18876 356286509 356319277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18877)) 356319277 356352045 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356319277 356352045).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18877 356319277 356352045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18878)) 356352045 356384813 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356352045 356384813).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18878 356352045 356384813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356253741 356319277).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 356253741 ≤ 356286509)
    (by decide : 356286509 ≤ 356319277) block0 block1

theorem join_0_1 : (twinPrimeSegment 356319277 356384813).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 356319277 ≤ 356352045)
    (by decide : 356352045 ≤ 356384813) block2 block3

theorem join_1_0 : (twinPrimeSegment 356253741 356384813).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 356253741 ≤ 356319277)
    (by decide : 356319277 ≤ 356384813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356253741 356384813).card = 470 := join_1_0

end S169C14
end Sude.GeneratedTwinScan
