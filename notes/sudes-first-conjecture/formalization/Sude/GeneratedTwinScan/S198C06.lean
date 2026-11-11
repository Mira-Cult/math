import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20397)) 416022573 416055341 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416022573 416055341).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20397 416022573 416055341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20398)) 416055341 416088109 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416055341 416088109).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20398 416055341 416088109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20399)) 416088109 416120877 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416088109 416120877).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20399 416088109 416120877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20399)) 416120877 416153645 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416120877 416153645).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20399 416120877 416153645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416022573 416088109).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 416022573 ≤ 416055341)
    (by decide : 416055341 ≤ 416088109) block0 block1

theorem join_0_1 : (twinPrimeSegment 416088109 416153645).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 416088109 ≤ 416120877)
    (by decide : 416120877 ≤ 416153645) block2 block3

theorem join_1_0 : (twinPrimeSegment 416022573 416153645).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 416022573 ≤ 416088109)
    (by decide : 416088109 ≤ 416153645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416022573 416153645).card = 416 := join_1_0

end S198C06
end Sude.GeneratedTwinScan
