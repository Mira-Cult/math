import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19935)) 397410349 397443117 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397410349 397443117).card = 142 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19935 397410349 397443117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19936)) 397443117 397475885 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397443117 397475885).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19936 397443117 397475885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19937)) 397475885 397508653 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397475885 397508653).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19937 397475885 397508653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19938)) 397508653 397541421 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397508653 397541421).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19938 397508653 397541421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397410349 397475885).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 397410349 ≤ 397443117)
    (by decide : 397443117 ≤ 397475885) block0 block1

theorem join_0_1 : (twinPrimeSegment 397475885 397541421).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 397475885 ≤ 397508653)
    (by decide : 397508653 ≤ 397541421) block2 block3

theorem join_1_0 : (twinPrimeSegment 397410349 397541421).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 397410349 ≤ 397475885)
    (by decide : 397475885 ≤ 397541421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397410349 397541421).card = 453 := join_1_0

end S189C08
end Sude.GeneratedTwinScan
