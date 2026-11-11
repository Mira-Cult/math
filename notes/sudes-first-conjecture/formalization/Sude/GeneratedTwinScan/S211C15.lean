import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21083)) 444465197 444497965 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444465197 444497965).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21083 444465197 444497965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21083)) 444497965 444530733 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444497965 444530733).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21083 444497965 444530733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21084)) 444530733 444563501 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444530733 444563501).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21084 444530733 444563501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21085)) 444563501 444596269 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444563501 444596269).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21085 444563501 444596269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444465197 444530733).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 444465197 ≤ 444497965)
    (by decide : 444497965 ≤ 444530733) block0 block1

theorem join_0_1 : (twinPrimeSegment 444530733 444596269).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 444530733 ≤ 444563501)
    (by decide : 444563501 ≤ 444596269) block2 block3

theorem join_1_0 : (twinPrimeSegment 444465197 444596269).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 444465197 ≤ 444530733)
    (by decide : 444530733 ≤ 444596269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444465197 444596269).card = 411 := join_1_0

end S211C15
end Sude.GeneratedTwinScan
