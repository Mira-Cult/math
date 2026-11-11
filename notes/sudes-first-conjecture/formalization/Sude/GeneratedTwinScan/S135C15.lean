import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16885)) 285081645 285114413 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285081645 285114413).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16885 285081645 285114413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16886)) 285114413 285147181 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 285114413 285147181).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16886 285114413 285147181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16887)) 285147181 285179949 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285147181 285179949).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16887 285147181 285179949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16888)) 285179949 285212717 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285179949 285212717).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16888 285179949 285212717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285081645 285147181).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 285081645 ≤ 285114413)
    (by decide : 285114413 ≤ 285147181) block0 block1

theorem join_0_1 : (twinPrimeSegment 285147181 285212717).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 285147181 ≤ 285179949)
    (by decide : 285179949 ≤ 285212717) block2 block3

theorem join_1_0 : (twinPrimeSegment 285081645 285212717).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 285081645 ≤ 285147181)
    (by decide : 285147181 ≤ 285212717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285081645 285212717).card = 450 := join_1_0

end S135C15
end Sude.GeneratedTwinScan
