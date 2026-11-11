import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15407)) 237371437 237404205 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237371437 237404205).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15407 237371437 237404205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15408)) 237404205 237436973 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237404205 237436973).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15408 237404205 237436973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15410)) 237436973 237469741 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237436973 237469741).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15410 237436973 237469741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15411)) 237469741 237502509 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237469741 237502509).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15411 237469741 237502509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237371437 237436973).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 237371437 ≤ 237404205)
    (by decide : 237404205 ≤ 237436973) block0 block1

theorem join_0_1 : (twinPrimeSegment 237436973 237502509).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 237436973 ≤ 237469741)
    (by decide : 237469741 ≤ 237502509) block2 block3

theorem join_1_0 : (twinPrimeSegment 237371437 237502509).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 237371437 ≤ 237436973)
    (by decide : 237436973 ≤ 237502509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237371437 237502509).card = 472 := join_1_0

end S113C03
end Sude.GeneratedTwinScan
