import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21677)) 469893165 469925933 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 469893165 469925933).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21677 469893165 469925933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21678)) 469925933 469958701 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469925933 469958701).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21678 469925933 469958701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21679)) 469958701 469991469 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469958701 469991469).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21679 469958701 469991469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21680)) 469991469 470024237 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469991469 470024237).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21680 469991469 470024237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 469893165 469958701).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 469893165 ≤ 469925933)
    (by decide : 469925933 ≤ 469958701) block0 block1

theorem join_0_1 : (twinPrimeSegment 469958701 470024237).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 469958701 ≤ 469991469)
    (by decide : 469991469 ≤ 470024237) block2 block3

theorem join_1_0 : (twinPrimeSegment 469893165 470024237).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 469893165 ≤ 469958701)
    (by decide : 469958701 ≤ 470024237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 469893165 470024237).card = 456 := join_1_0

end S224C01
end Sude.GeneratedTwinScan
