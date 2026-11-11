import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21098)) 445120557 445153325 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445120557 445153325).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21098 445120557 445153325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21099)) 445153325 445186093 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445153325 445186093).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21099 445153325 445186093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21100)) 445186093 445218861 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445186093 445218861).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21100 445186093 445218861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21100)) 445218861 445251629 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445218861 445251629).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21100 445218861 445251629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445120557 445186093).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 445120557 ≤ 445153325)
    (by decide : 445153325 ≤ 445186093) block0 block1

theorem join_0_1 : (twinPrimeSegment 445186093 445251629).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 445186093 ≤ 445218861)
    (by decide : 445218861 ≤ 445251629) block2 block3

theorem join_1_0 : (twinPrimeSegment 445120557 445251629).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 445120557 ≤ 445186093)
    (by decide : 445186093 ≤ 445251629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445120557 445251629).card = 415 := join_1_0

end S212C04
end Sude.GeneratedTwinScan
