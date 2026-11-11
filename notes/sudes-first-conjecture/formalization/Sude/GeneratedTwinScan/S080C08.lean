import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12994)) 168820781 168853549 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168820781 168853549).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12994 168820781 168853549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12995)) 168853549 168886317 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168853549 168886317).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12995 168853549 168886317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12996)) 168886317 168919085 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168886317 168919085).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12996 168886317 168919085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12998)) 168919085 168951853 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168919085 168951853).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12998 168919085 168951853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168820781 168886317).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 168820781 ≤ 168853549)
    (by decide : 168853549 ≤ 168886317) block0 block1

theorem join_0_1 : (twinPrimeSegment 168886317 168951853).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 168886317 ≤ 168919085)
    (by decide : 168919085 ≤ 168951853) block2 block3

theorem join_1_0 : (twinPrimeSegment 168820781 168951853).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 168820781 ≤ 168886317)
    (by decide : 168886317 ≤ 168951853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168820781 168951853).card = 471 := join_1_0

end S080C08
end Sude.GeneratedTwinScan
