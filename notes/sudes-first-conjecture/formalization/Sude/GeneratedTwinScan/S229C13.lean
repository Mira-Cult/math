import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21954)) 481951789 481984557 = 83 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481951789 481984557).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21954 481951789 481984557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21954)) 481984557 482017325 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481984557 482017325).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21954 481984557 482017325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21955)) 482017325 482050093 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482017325 482050093).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21955 482017325 482050093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21956)) 482050093 482082861 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482050093 482082861).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21956 482050093 482082861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481951789 482017325).card = 187 := by
  simpa using combineTwinPrimeSegments (by decide : 481951789 ≤ 481984557)
    (by decide : 481984557 ≤ 482017325) block0 block1

theorem join_0_1 : (twinPrimeSegment 482017325 482082861).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 482017325 ≤ 482050093)
    (by decide : 482050093 ≤ 482082861) block2 block3

theorem join_1_0 : (twinPrimeSegment 481951789 482082861).card = 400 := by
  simpa using combineTwinPrimeSegments (by decide : 481951789 ≤ 482017325)
    (by decide : 482017325 ≤ 482082861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481951789 482082861).card = 400 := join_1_0

end S229C13
end Sude.GeneratedTwinScan
