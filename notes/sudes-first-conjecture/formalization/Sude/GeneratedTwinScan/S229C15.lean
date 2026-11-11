import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21960)) 482213933 482246701 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482213933 482246701).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21960 482213933 482246701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21960)) 482246701 482279469 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482246701 482279469).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21960 482246701 482279469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21961)) 482279469 482312237 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482279469 482312237).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21961 482279469 482312237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21962)) 482312237 482345005 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482312237 482345005).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21962 482312237 482345005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482213933 482279469).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 482213933 ≤ 482246701)
    (by decide : 482246701 ≤ 482279469) block0 block1

theorem join_0_1 : (twinPrimeSegment 482279469 482345005).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 482279469 ≤ 482312237)
    (by decide : 482312237 ≤ 482345005) block2 block3

theorem join_1_0 : (twinPrimeSegment 482213933 482345005).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 482213933 ≤ 482279469)
    (by decide : 482279469 ≤ 482345005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482213933 482345005).card = 443 := join_1_0

end S229C15
end Sude.GeneratedTwinScan
