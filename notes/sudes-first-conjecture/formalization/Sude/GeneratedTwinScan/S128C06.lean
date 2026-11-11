import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16408)) 269221933 269254701 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269221933 269254701).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16408 269221933 269254701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16409)) 269254701 269287469 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269254701 269287469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16409 269254701 269287469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16410)) 269287469 269320237 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269287469 269320237).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16410 269287469 269320237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16411)) 269320237 269353005 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269320237 269353005).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16411 269320237 269353005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269221933 269287469).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 269221933 ≤ 269254701)
    (by decide : 269254701 ≤ 269287469) block0 block1

theorem join_0_1 : (twinPrimeSegment 269287469 269353005).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 269287469 ≤ 269320237)
    (by decide : 269320237 ≤ 269353005) block2 block3

theorem join_1_0 : (twinPrimeSegment 269221933 269353005).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 269221933 ≤ 269287469)
    (by decide : 269287469 ≤ 269353005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269221933 269353005).card = 468 := join_1_0

end S128C06
end Sude.GeneratedTwinScan
