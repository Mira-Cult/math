import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22502)) 506331181 506363949 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506331181 506363949).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22502 506331181 506363949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22503)) 506363949 506396717 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506363949 506396717).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22503 506363949 506396717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22503)) 506396717 506429485 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506396717 506429485).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22503 506396717 506429485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22504)) 506429485 506462253 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506429485 506462253).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22504 506429485 506462253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506331181 506396717).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 506331181 ≤ 506363949)
    (by decide : 506363949 ≤ 506396717) block0 block1

theorem join_0_1 : (twinPrimeSegment 506396717 506462253).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 506396717 ≤ 506429485)
    (by decide : 506429485 ≤ 506462253) block2 block3

theorem join_1_0 : (twinPrimeSegment 506331181 506462253).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 506331181 ≤ 506396717)
    (by decide : 506396717 ≤ 506462253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506331181 506462253).card = 431 := join_1_0

end S241C07
end Sude.GeneratedTwinScan
