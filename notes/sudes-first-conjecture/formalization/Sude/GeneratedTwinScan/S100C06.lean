import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14509)) 210501677 210534445 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 210501677 210534445).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14509 210501677 210534445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14510)) 210534445 210567213 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 210534445 210567213).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14510 210534445 210567213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14512)) 210567213 210599981 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 210567213 210599981).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14512 210567213 210599981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14513)) 210599981 210632749 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 210599981 210632749).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14513 210599981 210632749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 210501677 210567213).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 210501677 ≤ 210534445)
    (by decide : 210534445 ≤ 210567213) block0 block1

theorem join_0_1 : (twinPrimeSegment 210567213 210632749).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 210567213 ≤ 210599981)
    (by decide : 210599981 ≤ 210632749) block2 block3

theorem join_1_0 : (twinPrimeSegment 210501677 210632749).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 210501677 ≤ 210567213)
    (by decide : 210567213 ≤ 210632749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 210501677 210632749).card = 466 := join_1_0

end S100C06
end Sude.GeneratedTwinScan
