import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18052)) 325845037 325877805 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325845037 325877805).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18052 325845037 325877805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18052)) 325877805 325910573 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325877805 325910573).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18052 325877805 325910573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18053)) 325910573 325943341 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325910573 325943341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18053 325910573 325943341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18054)) 325943341 325976109 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325943341 325976109).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18054 325943341 325976109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325845037 325910573).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 325845037 ≤ 325877805)
    (by decide : 325877805 ≤ 325910573) block0 block1

theorem join_0_1 : (twinPrimeSegment 325910573 325976109).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 325910573 ≤ 325943341)
    (by decide : 325943341 ≤ 325976109) block2 block3

theorem join_1_0 : (twinPrimeSegment 325845037 325976109).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 325845037 ≤ 325910573)
    (by decide : 325910573 ≤ 325976109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325845037 325976109).card = 479 := join_1_0

end S155C06
end Sude.GeneratedTwinScan
