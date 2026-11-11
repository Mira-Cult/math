import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14959)) 223739949 223772717 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223739949 223772717).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14959 223739949 223772717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14960)) 223772717 223805485 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223772717 223805485).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14960 223772717 223805485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14961)) 223805485 223838253 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223805485 223838253).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14961 223805485 223838253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14962)) 223838253 223871021 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223838253 223871021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14962 223838253 223871021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223739949 223805485).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 223739949 ≤ 223772717)
    (by decide : 223772717 ≤ 223805485) block0 block1

theorem join_0_1 : (twinPrimeSegment 223805485 223871021).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 223805485 ≤ 223838253)
    (by decide : 223838253 ≤ 223871021) block2 block3

theorem join_1_0 : (twinPrimeSegment 223739949 223871021).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 223739949 ≤ 223805485)
    (by decide : 223805485 ≤ 223871021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223739949 223871021).card = 448 := join_1_0

end S106C11
end Sude.GeneratedTwinScan
