import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20974)) 439877677 439910445 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439877677 439910445).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20974 439877677 439910445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20974)) 439910445 439943213 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439910445 439943213).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20974 439910445 439943213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20975)) 439943213 439975981 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439943213 439975981).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20975 439943213 439975981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20976)) 439975981 440008749 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439975981 440008749).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20976 439975981 440008749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439877677 439943213).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 439877677 ≤ 439910445)
    (by decide : 439910445 ≤ 439943213) block0 block1

theorem join_0_1 : (twinPrimeSegment 439943213 440008749).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 439943213 ≤ 439975981)
    (by decide : 439975981 ≤ 440008749) block2 block3

theorem join_1_0 : (twinPrimeSegment 439877677 440008749).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 439877677 ≤ 439943213)
    (by decide : 439943213 ≤ 440008749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439877677 440008749).card = 436 := join_1_0

end S209C12
end Sude.GeneratedTwinScan
