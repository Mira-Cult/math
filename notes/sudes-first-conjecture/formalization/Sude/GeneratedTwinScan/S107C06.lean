import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S107C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15007)) 225181741 225214509 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 225181741 225214509).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15007 225181741 225214509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15008)) 225214509 225247277 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 225214509 225247277).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15008 225214509 225247277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15009)) 225247277 225280045 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 225247277 225280045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15009 225247277 225280045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15010)) 225280045 225312813 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 225280045 225312813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15010 225280045 225312813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 225181741 225247277).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 225181741 ≤ 225214509)
    (by decide : 225214509 ≤ 225247277) block0 block1

theorem join_0_1 : (twinPrimeSegment 225247277 225312813).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 225247277 ≤ 225280045)
    (by decide : 225280045 ≤ 225312813) block2 block3

theorem join_1_0 : (twinPrimeSegment 225181741 225312813).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 225181741 ≤ 225247277)
    (by decide : 225247277 ≤ 225312813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 225181741 225312813).card = 446 := join_1_0

end S107C06
end Sude.GeneratedTwinScan
