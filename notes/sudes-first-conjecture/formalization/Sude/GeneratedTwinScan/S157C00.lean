import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18146)) 329252909 329285677 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329252909 329285677).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18146 329252909 329285677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18147)) 329285677 329318445 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329285677 329318445).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18147 329285677 329318445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18148)) 329318445 329351213 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329318445 329351213).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18148 329318445 329351213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18148)) 329351213 329383981 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329351213 329383981).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18148 329351213 329383981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329252909 329318445).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 329285677)
    (by decide : 329285677 ≤ 329318445) block0 block1

theorem join_0_1 : (twinPrimeSegment 329318445 329383981).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 329318445 ≤ 329351213)
    (by decide : 329351213 ≤ 329383981) block2 block3

theorem join_1_0 : (twinPrimeSegment 329252909 329383981).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 329252909 ≤ 329318445)
    (by decide : 329318445 ≤ 329383981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329252909 329383981).card = 440 := join_1_0

end S157C00
end Sude.GeneratedTwinScan
