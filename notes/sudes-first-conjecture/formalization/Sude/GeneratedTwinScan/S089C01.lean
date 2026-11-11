import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13667)) 186777645 186810413 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186777645 186810413).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13667 186777645 186810413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13669)) 186810413 186843181 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186810413 186843181).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13669 186810413 186843181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13670)) 186843181 186875949 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186843181 186875949).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13670 186843181 186875949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13671)) 186875949 186908717 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186875949 186908717).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13671 186875949 186908717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186777645 186843181).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 186777645 ≤ 186810413)
    (by decide : 186810413 ≤ 186843181) block0 block1

theorem join_0_1 : (twinPrimeSegment 186843181 186908717).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 186843181 ≤ 186875949)
    (by decide : 186875949 ≤ 186908717) block2 block3

theorem join_1_0 : (twinPrimeSegment 186777645 186908717).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 186777645 ≤ 186843181)
    (by decide : 186843181 ≤ 186908717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186777645 186908717).card = 476 := join_1_0

end S089C01
end Sude.GeneratedTwinScan
