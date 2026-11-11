import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20895)) 436600877 436633645 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436600877 436633645).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20895 436600877 436633645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20896)) 436633645 436666413 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436633645 436666413).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20896 436633645 436666413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20897)) 436666413 436699181 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436666413 436699181).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20897 436666413 436699181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20898)) 436699181 436731949 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436699181 436731949).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20898 436699181 436731949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436600877 436666413).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 436600877 ≤ 436633645)
    (by decide : 436633645 ≤ 436666413) block0 block1

theorem join_0_1 : (twinPrimeSegment 436666413 436731949).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 436666413 ≤ 436699181)
    (by decide : 436699181 ≤ 436731949) block2 block3

theorem join_1_0 : (twinPrimeSegment 436600877 436731949).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 436600877 ≤ 436666413)
    (by decide : 436666413 ≤ 436731949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436600877 436731949).card = 414 := join_1_0

end S208C03
end Sude.GeneratedTwinScan
