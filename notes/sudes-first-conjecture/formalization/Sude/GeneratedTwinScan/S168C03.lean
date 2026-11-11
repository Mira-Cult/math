import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18781)) 352714797 352747565 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352714797 352747565).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18781 352714797 352747565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18782)) 352747565 352780333 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352747565 352780333).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18782 352747565 352780333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18783)) 352780333 352813101 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352780333 352813101).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18783 352780333 352813101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18784)) 352813101 352845869 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352813101 352845869).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18784 352813101 352845869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352714797 352780333).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 352714797 ≤ 352747565)
    (by decide : 352747565 ≤ 352780333) block0 block1

theorem join_0_1 : (twinPrimeSegment 352780333 352845869).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 352780333 ≤ 352813101)
    (by decide : 352813101 ≤ 352845869) block2 block3

theorem join_1_0 : (twinPrimeSegment 352714797 352845869).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 352714797 ≤ 352780333)
    (by decide : 352780333 ≤ 352845869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352714797 352845869).card = 428 := join_1_0

end S168C03
end Sude.GeneratedTwinScan
