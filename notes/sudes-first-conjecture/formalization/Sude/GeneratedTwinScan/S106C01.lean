import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14915)) 222429229 222461997 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222429229 222461997).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14915 222429229 222461997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14916)) 222461997 222494765 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222461997 222494765).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14916 222461997 222494765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14917)) 222494765 222527533 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222494765 222527533).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14917 222494765 222527533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14918)) 222527533 222560301 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222527533 222560301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14918 222527533 222560301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222429229 222494765).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 222429229 ≤ 222461997)
    (by decide : 222461997 ≤ 222494765) block0 block1

theorem join_0_1 : (twinPrimeSegment 222494765 222560301).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 222494765 ≤ 222527533)
    (by decide : 222527533 ≤ 222560301) block2 block3

theorem join_1_0 : (twinPrimeSegment 222429229 222560301).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 222429229 ≤ 222494765)
    (by decide : 222494765 ≤ 222560301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222429229 222560301).card = 452 := join_1_0

end S106C01
end Sude.GeneratedTwinScan
