import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19514)) 380764205 380796973 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380764205 380796973).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19514 380764205 380796973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19514)) 380796973 380829741 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380796973 380829741).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19514 380796973 380829741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19515)) 380829741 380862509 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380829741 380862509).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19515 380829741 380862509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19516)) 380862509 380895277 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380862509 380895277).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19516 380862509 380895277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380764205 380829741).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 380764205 ≤ 380796973)
    (by decide : 380796973 ≤ 380829741) block0 block1

theorem join_0_1 : (twinPrimeSegment 380829741 380895277).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 380829741 ≤ 380862509)
    (by decide : 380862509 ≤ 380895277) block2 block3

theorem join_1_0 : (twinPrimeSegment 380764205 380895277).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 380764205 ≤ 380829741)
    (by decide : 380829741 ≤ 380895277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380764205 380895277).card = 457 := join_1_0

end S181C09
end Sude.GeneratedTwinScan
