import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15288)) 233701421 233734189 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233701421 233734189).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15288 233701421 233734189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15289)) 233734189 233766957 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233734189 233766957).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15289 233734189 233766957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15290)) 233766957 233799725 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233766957 233799725).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15290 233766957 233799725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15291)) 233799725 233832493 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233799725 233832493).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15291 233799725 233832493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233701421 233766957).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 233701421 ≤ 233734189)
    (by decide : 233734189 ≤ 233766957) block0 block1

theorem join_0_1 : (twinPrimeSegment 233766957 233832493).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 233766957 ≤ 233799725)
    (by decide : 233799725 ≤ 233832493) block2 block3

theorem join_1_0 : (twinPrimeSegment 233701421 233832493).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 233701421 ≤ 233766957)
    (by decide : 233766957 ≤ 233832493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233701421 233832493).card = 446 := join_1_0

end S111C07
end Sude.GeneratedTwinScan
