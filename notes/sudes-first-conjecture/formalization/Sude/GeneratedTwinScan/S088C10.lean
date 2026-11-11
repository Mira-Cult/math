import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13634)) 185860141 185892909 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185860141 185892909).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13634 185860141 185892909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13635)) 185892909 185925677 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185892909 185925677).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13635 185892909 185925677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13636)) 185925677 185958445 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185925677 185958445).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13636 185925677 185958445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13637)) 185958445 185991213 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185958445 185991213).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13637 185958445 185991213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185860141 185925677).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 185860141 ≤ 185892909)
    (by decide : 185892909 ≤ 185925677) block0 block1

theorem join_0_1 : (twinPrimeSegment 185925677 185991213).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 185925677 ≤ 185958445)
    (by decide : 185958445 ≤ 185991213) block2 block3

theorem join_1_0 : (twinPrimeSegment 185860141 185991213).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 185860141 ≤ 185925677)
    (by decide : 185925677 ≤ 185991213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185860141 185991213).card = 470 := join_1_0

end S088C10
end Sude.GeneratedTwinScan
