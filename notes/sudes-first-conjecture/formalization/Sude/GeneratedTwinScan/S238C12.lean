import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22376)) 500695085 500727853 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500695085 500727853).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22376 500695085 500727853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22377)) 500727853 500760621 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500727853 500760621).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22377 500727853 500760621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22378)) 500760621 500793389 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500760621 500793389).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22378 500760621 500793389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22379)) 500793389 500826157 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500793389 500826157).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22379 500793389 500826157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500695085 500760621).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 500695085 ≤ 500727853)
    (by decide : 500727853 ≤ 500760621) block0 block1

theorem join_0_1 : (twinPrimeSegment 500760621 500826157).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 500760621 ≤ 500793389)
    (by decide : 500793389 ≤ 500826157) block2 block3

theorem join_1_0 : (twinPrimeSegment 500695085 500826157).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 500695085 ≤ 500760621)
    (by decide : 500760621 ≤ 500826157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500695085 500826157).card = 415 := join_1_0

end S238C12
end Sude.GeneratedTwinScan
