import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20031)) 401211437 401244205 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401211437 401244205).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20031 401211437 401244205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20031)) 401244205 401276973 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401244205 401276973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20031 401244205 401276973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20032)) 401276973 401309741 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401276973 401309741).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20032 401276973 401309741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20033)) 401309741 401342509 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401309741 401342509).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20033 401309741 401342509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401211437 401276973).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 401211437 ≤ 401244205)
    (by decide : 401244205 ≤ 401276973) block0 block1

theorem join_0_1 : (twinPrimeSegment 401276973 401342509).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 401276973 ≤ 401309741)
    (by decide : 401309741 ≤ 401342509) block2 block3

theorem join_1_0 : (twinPrimeSegment 401211437 401342509).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 401211437 ≤ 401276973)
    (by decide : 401276973 ≤ 401342509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401211437 401342509).card = 444 := join_1_0

end S191C05
end Sude.GeneratedTwinScan
