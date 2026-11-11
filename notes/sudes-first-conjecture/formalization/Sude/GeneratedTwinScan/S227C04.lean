import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21831)) 476577837 476610605 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476577837 476610605).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21831 476577837 476610605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21832)) 476610605 476643373 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476610605 476643373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21832 476610605 476643373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21832)) 476643373 476676141 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476643373 476676141).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21832 476643373 476676141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21833)) 476676141 476708909 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476676141 476708909).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21833 476676141 476708909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476577837 476643373).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 476577837 ≤ 476610605)
    (by decide : 476610605 ≤ 476643373) block0 block1

theorem join_0_1 : (twinPrimeSegment 476643373 476708909).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 476643373 ≤ 476676141)
    (by decide : 476676141 ≤ 476708909) block2 block3

theorem join_1_0 : (twinPrimeSegment 476577837 476708909).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 476577837 ≤ 476643373)
    (by decide : 476643373 ≤ 476708909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476577837 476708909).card = 450 := join_1_0

end S227C04
end Sude.GeneratedTwinScan
