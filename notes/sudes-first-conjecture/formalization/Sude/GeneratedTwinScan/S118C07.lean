import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15761)) 248381485 248414253 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248381485 248414253).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15761 248381485 248414253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15762)) 248414253 248447021 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248414253 248447021).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15762 248414253 248447021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15763)) 248447021 248479789 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248447021 248479789).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15763 248447021 248479789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15764)) 248479789 248512557 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 248479789 248512557).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15764 248479789 248512557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248381485 248447021).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 248381485 ≤ 248414253)
    (by decide : 248414253 ≤ 248447021) block0 block1

theorem join_0_1 : (twinPrimeSegment 248447021 248512557).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 248447021 ≤ 248479789)
    (by decide : 248479789 ≤ 248512557) block2 block3

theorem join_1_0 : (twinPrimeSegment 248381485 248512557).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 248381485 ≤ 248447021)
    (by decide : 248447021 ≤ 248512557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248381485 248512557).card = 447 := join_1_0

end S118C07
end Sude.GeneratedTwinScan
