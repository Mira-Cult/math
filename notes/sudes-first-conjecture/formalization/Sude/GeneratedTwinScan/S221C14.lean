import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21571)) 465305645 465338413 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465305645 465338413).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21571 465305645 465338413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21572)) 465338413 465371181 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465338413 465371181).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21572 465338413 465371181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21573)) 465371181 465403949 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465371181 465403949).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21573 465371181 465403949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21573)) 465403949 465436717 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465403949 465436717).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21573 465403949 465436717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465305645 465371181).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 465305645 ≤ 465338413)
    (by decide : 465338413 ≤ 465371181) block0 block1

theorem join_0_1 : (twinPrimeSegment 465371181 465436717).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 465371181 ≤ 465403949)
    (by decide : 465403949 ≤ 465436717) block2 block3

theorem join_1_0 : (twinPrimeSegment 465305645 465436717).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 465305645 ≤ 465371181)
    (by decide : 465371181 ≤ 465436717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465305645 465436717).card = 441 := join_1_0

end S221C14
end Sude.GeneratedTwinScan
