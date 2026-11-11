import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22794)) 519569453 519602221 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519569453 519602221).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22794 519569453 519602221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22795)) 519602221 519634989 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519602221 519634989).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22795 519602221 519634989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22796)) 519634989 519667757 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519634989 519667757).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22796 519634989 519667757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22796)) 519667757 519700525 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519667757 519700525).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22796 519667757 519700525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519569453 519634989).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 519569453 ≤ 519602221)
    (by decide : 519602221 ≤ 519634989) block0 block1

theorem join_0_1 : (twinPrimeSegment 519634989 519700525).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 519634989 ≤ 519667757)
    (by decide : 519667757 ≤ 519700525) block2 block3

theorem join_1_0 : (twinPrimeSegment 519569453 519700525).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 519569453 ≤ 519634989)
    (by decide : 519634989 ≤ 519700525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519569453 519700525).card = 460 := join_1_0

end S247C12
end Sude.GeneratedTwinScan
