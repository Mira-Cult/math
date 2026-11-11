import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13169)) 173408301 173441069 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173408301 173441069).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13169 173408301 173441069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13170)) 173441069 173473837 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173441069 173473837).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13170 173441069 173473837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13172)) 173473837 173506605 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173473837 173506605).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13172 173473837 173506605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13173)) 173506605 173539373 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173506605 173539373).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13173 173506605 173539373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173408301 173473837).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 173408301 ≤ 173441069)
    (by decide : 173441069 ≤ 173473837) block0 block1

theorem join_0_1 : (twinPrimeSegment 173473837 173539373).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 173473837 ≤ 173506605)
    (by decide : 173506605 ≤ 173539373) block2 block3

theorem join_1_0 : (twinPrimeSegment 173408301 173539373).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 173408301 ≤ 173473837)
    (by decide : 173473837 ≤ 173539373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173408301 173539373).card = 482 := join_1_0

end S082C11
end Sude.GeneratedTwinScan
