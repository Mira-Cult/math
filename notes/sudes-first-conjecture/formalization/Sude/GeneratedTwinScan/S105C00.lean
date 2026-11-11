import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14840)) 220201005 220233773 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220201005 220233773).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14840 220201005 220233773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14841)) 220233773 220266541 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220233773 220266541).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14841 220233773 220266541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14842)) 220266541 220299309 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220266541 220299309).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14842 220266541 220299309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14843)) 220299309 220332077 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220299309 220332077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14843 220299309 220332077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220201005 220266541).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 220233773)
    (by decide : 220233773 ≤ 220266541) block0 block1

theorem join_0_1 : (twinPrimeSegment 220266541 220332077).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 220266541 ≤ 220299309)
    (by decide : 220299309 ≤ 220332077) block2 block3

theorem join_1_0 : (twinPrimeSegment 220201005 220332077).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 220201005 ≤ 220266541)
    (by decide : 220266541 ≤ 220332077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220201005 220332077).card = 466 := join_1_0

end S105C00
end Sude.GeneratedTwinScan
