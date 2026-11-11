import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17405)) 302907437 302940205 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302907437 302940205).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17405 302907437 302940205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17406)) 302940205 302972973 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302940205 302972973).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17406 302940205 302972973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17407)) 302972973 303005741 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302972973 303005741).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17407 302972973 303005741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17408)) 303005741 303038509 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303005741 303038509).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17408 303005741 303038509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302907437 302972973).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 302907437 ≤ 302940205)
    (by decide : 302940205 ≤ 302972973) block0 block1

theorem join_0_1 : (twinPrimeSegment 302972973 303038509).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 302972973 ≤ 303005741)
    (by decide : 303005741 ≤ 303038509) block2 block3

theorem join_1_0 : (twinPrimeSegment 302907437 303038509).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 302907437 ≤ 302972973)
    (by decide : 302972973 ≤ 303038509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302907437 303038509).card = 468 := join_1_0

end S144C07
end Sude.GeneratedTwinScan
