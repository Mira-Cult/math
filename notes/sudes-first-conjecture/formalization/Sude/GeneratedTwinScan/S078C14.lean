import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12862)) 165412909 165445677 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165412909 165445677).card = 143 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12862 165412909 165445677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12863)) 165445677 165478445 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165445677 165478445).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12863 165445677 165478445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12865)) 165478445 165511213 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165478445 165511213).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12865 165478445 165511213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12866)) 165511213 165543981 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165511213 165543981).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12866 165511213 165543981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165412909 165478445).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 165412909 ≤ 165445677)
    (by decide : 165445677 ≤ 165478445) block0 block1

theorem join_0_1 : (twinPrimeSegment 165478445 165543981).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 165478445 ≤ 165511213)
    (by decide : 165511213 ≤ 165543981) block2 block3

theorem join_1_0 : (twinPrimeSegment 165412909 165543981).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 165412909 ≤ 165478445)
    (by decide : 165478445 ≤ 165543981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165412909 165543981).card = 525 := join_1_0

end S078C14
end Sude.GeneratedTwinScan
