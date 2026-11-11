import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18830)) 354549805 354582573 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354549805 354582573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18830 354549805 354582573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18831)) 354582573 354615341 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354582573 354615341).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18831 354582573 354615341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18832)) 354615341 354648109 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 354615341 354648109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18832 354615341 354648109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18832)) 354648109 354680877 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 354648109 354680877).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18832 354648109 354680877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354549805 354615341).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 354549805 ≤ 354582573)
    (by decide : 354582573 ≤ 354615341) block0 block1

theorem join_0_1 : (twinPrimeSegment 354615341 354680877).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 354615341 ≤ 354648109)
    (by decide : 354648109 ≤ 354680877) block2 block3

theorem join_1_0 : (twinPrimeSegment 354549805 354680877).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 354549805 ≤ 354615341)
    (by decide : 354615341 ≤ 354680877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354549805 354680877).card = 425 := join_1_0

end S169C01
end Sude.GeneratedTwinScan
