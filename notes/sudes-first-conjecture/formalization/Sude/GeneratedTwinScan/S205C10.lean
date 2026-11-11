import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20766)) 431226925 431259693 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431226925 431259693).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20766 431226925 431259693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20767)) 431259693 431292461 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431259693 431292461).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20767 431259693 431292461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20768)) 431292461 431325229 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431292461 431325229).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20768 431292461 431325229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20769)) 431325229 431357997 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431325229 431357997).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20769 431325229 431357997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431226925 431292461).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 431226925 ≤ 431259693)
    (by decide : 431259693 ≤ 431292461) block0 block1

theorem join_0_1 : (twinPrimeSegment 431292461 431357997).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 431292461 ≤ 431325229)
    (by decide : 431325229 ≤ 431357997) block2 block3

theorem join_1_0 : (twinPrimeSegment 431226925 431357997).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 431226925 ≤ 431292461)
    (by decide : 431292461 ≤ 431357997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431226925 431357997).card = 429 := join_1_0

end S205C10
end Sude.GeneratedTwinScan
