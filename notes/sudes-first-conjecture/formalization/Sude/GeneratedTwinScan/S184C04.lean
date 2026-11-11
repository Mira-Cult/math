import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19657)) 386400301 386433069 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386400301 386433069).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19657 386400301 386433069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19658)) 386433069 386465837 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386433069 386465837).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19658 386433069 386465837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19659)) 386465837 386498605 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386465837 386498605).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19659 386465837 386498605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19660)) 386498605 386531373 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386498605 386531373).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19660 386498605 386531373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386400301 386465837).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 386400301 ≤ 386433069)
    (by decide : 386433069 ≤ 386465837) block0 block1

theorem join_0_1 : (twinPrimeSegment 386465837 386531373).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 386465837 ≤ 386498605)
    (by decide : 386498605 ≤ 386531373) block2 block3

theorem join_1_0 : (twinPrimeSegment 386400301 386531373).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 386400301 ≤ 386465837)
    (by decide : 386465837 ≤ 386531373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386400301 386531373).card = 465 := join_1_0

end S184C04
end Sude.GeneratedTwinScan
