import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22572)) 509476909 509509677 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509476909 509509677).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22572 509476909 509509677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22573)) 509509677 509542445 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509509677 509542445).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22573 509509677 509542445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22573)) 509542445 509575213 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509542445 509575213).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22573 509542445 509575213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22574)) 509575213 509607981 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509575213 509607981).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22574 509575213 509607981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509476909 509542445).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 509476909 ≤ 509509677)
    (by decide : 509509677 ≤ 509542445) block0 block1

theorem join_0_1 : (twinPrimeSegment 509542445 509607981).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 509542445 ≤ 509575213)
    (by decide : 509575213 ≤ 509607981) block2 block3

theorem join_1_0 : (twinPrimeSegment 509476909 509607981).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 509476909 ≤ 509542445)
    (by decide : 509542445 ≤ 509607981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509476909 509607981).card = 429 := join_1_0

end S242C15
end Sude.GeneratedTwinScan
