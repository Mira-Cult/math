import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20889)) 436338733 436371501 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436338733 436371501).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20889 436338733 436371501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20890)) 436371501 436404269 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436371501 436404269).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20890 436371501 436404269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20891)) 436404269 436437037 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436404269 436437037).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20891 436404269 436437037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20891)) 436437037 436469805 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436437037 436469805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20891 436437037 436469805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436338733 436404269).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 436338733 ≤ 436371501)
    (by decide : 436371501 ≤ 436404269) block0 block1

theorem join_0_1 : (twinPrimeSegment 436404269 436469805).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 436404269 ≤ 436437037)
    (by decide : 436437037 ≤ 436469805) block2 block3

theorem join_1_0 : (twinPrimeSegment 436338733 436469805).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 436338733 ≤ 436404269)
    (by decide : 436404269 ≤ 436469805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436338733 436469805).card = 429 := join_1_0

end S208C01
end Sude.GeneratedTwinScan
