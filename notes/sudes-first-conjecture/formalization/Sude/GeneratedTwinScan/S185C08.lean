import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19724)) 389021741 389054509 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389021741 389054509).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19724 389021741 389054509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19725)) 389054509 389087277 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389054509 389087277).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19725 389054509 389087277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19726)) 389087277 389120045 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 389087277 389120045).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19726 389087277 389120045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19726)) 389120045 389152813 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 389120045 389152813).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19726 389120045 389152813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389021741 389087277).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 389021741 ≤ 389054509)
    (by decide : 389054509 ≤ 389087277) block0 block1

theorem join_0_1 : (twinPrimeSegment 389087277 389152813).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 389087277 ≤ 389120045)
    (by decide : 389120045 ≤ 389152813) block2 block3

theorem join_1_0 : (twinPrimeSegment 389021741 389152813).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 389021741 ≤ 389087277)
    (by decide : 389087277 ≤ 389152813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389021741 389152813).card = 419 := join_1_0

end S185C08
end Sude.GeneratedTwinScan
