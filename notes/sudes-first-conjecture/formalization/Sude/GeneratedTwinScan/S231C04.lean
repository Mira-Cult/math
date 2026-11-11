import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22022)) 484966445 484999213 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484966445 484999213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22022 484966445 484999213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22023)) 484999213 485031981 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484999213 485031981).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22023 484999213 485031981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22024)) 485031981 485064749 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485031981 485064749).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22024 485031981 485064749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22024)) 485064749 485097517 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485064749 485097517).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22024 485064749 485097517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484966445 485031981).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 484966445 ≤ 484999213)
    (by decide : 484999213 ≤ 485031981) block0 block1

theorem join_0_1 : (twinPrimeSegment 485031981 485097517).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 485031981 ≤ 485064749)
    (by decide : 485064749 ≤ 485097517) block2 block3

theorem join_1_0 : (twinPrimeSegment 484966445 485097517).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 484966445 ≤ 485031981)
    (by decide : 485031981 ≤ 485097517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484966445 485097517).card = 415 := join_1_0

end S231C04
end Sude.GeneratedTwinScan
