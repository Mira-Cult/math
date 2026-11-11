import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15141)) 229244973 229277741 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 229244973 229277741).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15141 229244973 229277741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15143)) 229277741 229310509 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 229277741 229310509).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15143 229277741 229310509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15144)) 229310509 229343277 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 229310509 229343277).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15144 229310509 229343277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15145)) 229343277 229376045 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 229343277 229376045).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15145 229343277 229376045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 229244973 229310509).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 229244973 ≤ 229277741)
    (by decide : 229277741 ≤ 229310509) block0 block1

theorem join_0_1 : (twinPrimeSegment 229310509 229376045).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 229310509 ≤ 229343277)
    (by decide : 229343277 ≤ 229376045) block2 block3

theorem join_1_0 : (twinPrimeSegment 229244973 229376045).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 229244973 ≤ 229310509)
    (by decide : 229310509 ≤ 229376045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 229244973 229376045).card = 474 := join_1_0

end S109C05
end Sude.GeneratedTwinScan
