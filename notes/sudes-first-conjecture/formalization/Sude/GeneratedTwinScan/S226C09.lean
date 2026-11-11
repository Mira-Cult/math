import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21798)) 475136045 475168813 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475136045 475168813).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21798 475136045 475168813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21799)) 475168813 475201581 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475168813 475201581).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21799 475168813 475201581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21799)) 475201581 475234349 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475201581 475234349).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21799 475201581 475234349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21800)) 475234349 475267117 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475234349 475267117).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21800 475234349 475267117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475136045 475201581).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 475136045 ≤ 475168813)
    (by decide : 475168813 ≤ 475201581) block0 block1

theorem join_0_1 : (twinPrimeSegment 475201581 475267117).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 475201581 ≤ 475234349)
    (by decide : 475234349 ≤ 475267117) block2 block3

theorem join_1_0 : (twinPrimeSegment 475136045 475267117).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 475136045 ≤ 475201581)
    (by decide : 475201581 ≤ 475267117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475136045 475267117).card = 452 := join_1_0

end S226C09
end Sude.GeneratedTwinScan
