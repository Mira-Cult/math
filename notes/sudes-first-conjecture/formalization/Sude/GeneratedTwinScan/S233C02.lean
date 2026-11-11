import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22111)) 488898605 488931373 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488898605 488931373).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22111 488898605 488931373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22112)) 488931373 488964141 = 90 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488931373 488964141).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22112 488931373 488964141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22113)) 488964141 488996909 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488964141 488996909).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22113 488964141 488996909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22114)) 488996909 489029677 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488996909 489029677).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22114 488996909 489029677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488898605 488964141).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 488898605 ≤ 488931373)
    (by decide : 488931373 ≤ 488964141) block0 block1

theorem join_0_1 : (twinPrimeSegment 488964141 489029677).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 488964141 ≤ 488996909)
    (by decide : 488996909 ≤ 489029677) block2 block3

theorem join_1_0 : (twinPrimeSegment 488898605 489029677).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 488898605 ≤ 488964141)
    (by decide : 488964141 ≤ 489029677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488898605 489029677).card = 435 := join_1_0

end S233C02
end Sude.GeneratedTwinScan
