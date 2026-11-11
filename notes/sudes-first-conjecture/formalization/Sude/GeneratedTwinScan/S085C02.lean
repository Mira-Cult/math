import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13362)) 178520109 178552877 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178520109 178552877).card = 151 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13362 178520109 178552877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13363)) 178552877 178585645 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178552877 178585645).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13363 178552877 178585645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13364)) 178585645 178618413 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178585645 178618413).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13364 178585645 178618413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13366)) 178618413 178651181 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178618413 178651181).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13366 178618413 178651181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178520109 178585645).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 178520109 ≤ 178552877)
    (by decide : 178552877 ≤ 178585645) block0 block1

theorem join_0_1 : (twinPrimeSegment 178585645 178651181).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 178585645 ≤ 178618413)
    (by decide : 178618413 ≤ 178651181) block2 block3

theorem join_1_0 : (twinPrimeSegment 178520109 178651181).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 178520109 ≤ 178585645)
    (by decide : 178585645 ≤ 178651181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178520109 178651181).card = 509 := join_1_0

end S085C02
end Sude.GeneratedTwinScan
