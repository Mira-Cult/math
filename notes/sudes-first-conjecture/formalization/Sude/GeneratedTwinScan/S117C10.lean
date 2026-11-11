import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15707)) 246677549 246710317 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246677549 246710317).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15707 246677549 246710317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15708)) 246710317 246743085 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246710317 246743085).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15708 246710317 246743085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15709)) 246743085 246775853 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246743085 246775853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15709 246743085 246775853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15710)) 246775853 246808621 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246775853 246808621).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15710 246775853 246808621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246677549 246743085).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 246677549 ≤ 246710317)
    (by decide : 246710317 ≤ 246743085) block0 block1

theorem join_0_1 : (twinPrimeSegment 246743085 246808621).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 246743085 ≤ 246775853)
    (by decide : 246775853 ≤ 246808621) block2 block3

theorem join_1_0 : (twinPrimeSegment 246677549 246808621).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 246677549 ≤ 246743085)
    (by decide : 246743085 ≤ 246808621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246677549 246808621).card = 443 := join_1_0

end S117C10
end Sude.GeneratedTwinScan
