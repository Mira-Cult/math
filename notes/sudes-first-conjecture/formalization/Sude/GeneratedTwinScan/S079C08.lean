import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12913)) 166723629 166756397 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166723629 166756397).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12913 166723629 166756397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12914)) 166756397 166789165 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166756397 166789165).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12914 166756397 166789165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12915)) 166789165 166821933 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166789165 166821933).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12915 166789165 166821933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12917)) 166821933 166854701 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166821933 166854701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12917 166821933 166854701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166723629 166789165).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 166723629 ≤ 166756397)
    (by decide : 166756397 ≤ 166789165) block0 block1

theorem join_0_1 : (twinPrimeSegment 166789165 166854701).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 166789165 ≤ 166821933)
    (by decide : 166821933 ≤ 166854701) block2 block3

theorem join_1_0 : (twinPrimeSegment 166723629 166854701).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 166723629 ≤ 166789165)
    (by decide : 166789165 ≤ 166854701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166723629 166854701).card = 474 := join_1_0

end S079C08
end Sude.GeneratedTwinScan
