import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18764)) 352059437 352092205 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352059437 352092205).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18764 352059437 352092205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18764)) 352092205 352124973 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352092205 352124973).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18764 352092205 352124973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18765)) 352124973 352157741 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352124973 352157741).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18765 352124973 352157741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18766)) 352157741 352190509 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352157741 352190509).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18766 352157741 352190509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352059437 352124973).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 352059437 ≤ 352092205)
    (by decide : 352092205 ≤ 352124973) block0 block1

theorem join_0_1 : (twinPrimeSegment 352124973 352190509).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 352124973 ≤ 352157741)
    (by decide : 352157741 ≤ 352190509) block2 block3

theorem join_1_0 : (twinPrimeSegment 352059437 352190509).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 352059437 ≤ 352124973)
    (by decide : 352124973 ≤ 352190509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352059437 352190509).card = 469 := join_1_0

end S167C14
end Sude.GeneratedTwinScan
