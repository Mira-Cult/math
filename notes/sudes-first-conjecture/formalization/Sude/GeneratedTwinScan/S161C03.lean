import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18386)) 338034733 338067501 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338034733 338067501).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18386 338034733 338067501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18387)) 338067501 338100269 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338067501 338100269).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18387 338067501 338100269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18388)) 338100269 338133037 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338100269 338133037).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18388 338100269 338133037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18389)) 338133037 338165805 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338133037 338165805).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18389 338133037 338165805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338034733 338100269).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 338034733 ≤ 338067501)
    (by decide : 338067501 ≤ 338100269) block0 block1

theorem join_0_1 : (twinPrimeSegment 338100269 338165805).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 338100269 ≤ 338133037)
    (by decide : 338133037 ≤ 338165805) block2 block3

theorem join_1_0 : (twinPrimeSegment 338034733 338165805).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 338034733 ≤ 338100269)
    (by decide : 338100269 ≤ 338165805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338034733 338165805).card = 480 := join_1_0

end S161C03
end Sude.GeneratedTwinScan
