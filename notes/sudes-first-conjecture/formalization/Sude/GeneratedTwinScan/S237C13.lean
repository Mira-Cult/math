import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22332)) 498729005 498761773 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 498729005 498761773).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22332 498729005 498761773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22333)) 498761773 498794541 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 498761773 498794541).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22333 498761773 498794541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22334)) 498794541 498827309 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 498794541 498827309).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22334 498794541 498827309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22335)) 498827309 498860077 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 498827309 498860077).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22335 498827309 498860077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 498729005 498794541).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 498729005 ≤ 498761773)
    (by decide : 498761773 ≤ 498794541) block0 block1

theorem join_0_1 : (twinPrimeSegment 498794541 498860077).card = 182 := by
  simpa using combineTwinPrimeSegments (by decide : 498794541 ≤ 498827309)
    (by decide : 498827309 ≤ 498860077) block2 block3

theorem join_1_0 : (twinPrimeSegment 498729005 498860077).card = 383 := by
  simpa using combineTwinPrimeSegments (by decide : 498729005 ≤ 498794541)
    (by decide : 498794541 ≤ 498860077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 498729005 498860077).card = 383 := join_1_0

end S237C13
end Sude.GeneratedTwinScan
