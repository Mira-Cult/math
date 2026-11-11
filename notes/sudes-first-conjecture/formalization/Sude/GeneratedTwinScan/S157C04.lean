import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18160)) 329777197 329809965 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329777197 329809965).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18160 329777197 329809965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18161)) 329809965 329842733 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329809965 329842733).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18161 329809965 329842733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18162)) 329842733 329875501 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329842733 329875501).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18162 329842733 329875501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18163)) 329875501 329908269 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329875501 329908269).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18163 329875501 329908269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329777197 329842733).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 329777197 ≤ 329809965)
    (by decide : 329809965 ≤ 329842733) block0 block1

theorem join_0_1 : (twinPrimeSegment 329842733 329908269).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 329842733 ≤ 329875501)
    (by decide : 329875501 ≤ 329908269) block2 block3

theorem join_1_0 : (twinPrimeSegment 329777197 329908269).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 329777197 ≤ 329842733)
    (by decide : 329842733 ≤ 329908269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329777197 329908269).card = 436 := join_1_0

end S157C04
end Sude.GeneratedTwinScan
