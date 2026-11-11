import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22082)) 487587885 487620653 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487587885 487620653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22082 487587885 487620653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22082)) 487620653 487653421 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487620653 487653421).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22082 487620653 487653421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22083)) 487653421 487686189 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487653421 487686189).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22083 487653421 487686189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22084)) 487686189 487718957 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487686189 487718957).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22084 487686189 487718957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487587885 487653421).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 487587885 ≤ 487620653)
    (by decide : 487620653 ≤ 487653421) block0 block1

theorem join_0_1 : (twinPrimeSegment 487653421 487718957).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 487653421 ≤ 487686189)
    (by decide : 487686189 ≤ 487718957) block2 block3

theorem join_1_0 : (twinPrimeSegment 487587885 487718957).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 487587885 ≤ 487653421)
    (by decide : 487653421 ≤ 487718957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487587885 487718957).card = 416 := join_1_0

end S232C08
end Sude.GeneratedTwinScan
