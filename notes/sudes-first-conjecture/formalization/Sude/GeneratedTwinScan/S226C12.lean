import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21807)) 475529261 475562029 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475529261 475562029).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21807 475529261 475562029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21808)) 475562029 475594797 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475562029 475594797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21808 475562029 475594797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21808)) 475594797 475627565 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475594797 475627565).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21808 475594797 475627565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21809)) 475627565 475660333 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475627565 475660333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21809 475627565 475660333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475529261 475594797).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 475529261 ≤ 475562029)
    (by decide : 475562029 ≤ 475594797) block0 block1

theorem join_0_1 : (twinPrimeSegment 475594797 475660333).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 475594797 ≤ 475627565)
    (by decide : 475627565 ≤ 475660333) block2 block3

theorem join_1_0 : (twinPrimeSegment 475529261 475660333).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 475529261 ≤ 475594797)
    (by decide : 475594797 ≤ 475660333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475529261 475660333).card = 456 := join_1_0

end S226C12
end Sude.GeneratedTwinScan
