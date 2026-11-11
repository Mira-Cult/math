import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22849)) 522059821 522092589 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522059821 522092589).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22849 522059821 522092589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22850)) 522092589 522125357 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522092589 522125357).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22850 522092589 522125357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22850)) 522125357 522158125 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522125357 522158125).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22850 522125357 522158125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22851)) 522158125 522190893 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522158125 522190893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22851 522158125 522190893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522059821 522125357).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 522059821 ≤ 522092589)
    (by decide : 522092589 ≤ 522125357) block0 block1

theorem join_0_1 : (twinPrimeSegment 522125357 522190893).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 522125357 ≤ 522158125)
    (by decide : 522158125 ≤ 522190893) block2 block3

theorem join_1_0 : (twinPrimeSegment 522059821 522190893).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 522059821 ≤ 522125357)
    (by decide : 522125357 ≤ 522190893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522059821 522190893).card = 449 := join_1_0

end S248C15
end Sude.GeneratedTwinScan
