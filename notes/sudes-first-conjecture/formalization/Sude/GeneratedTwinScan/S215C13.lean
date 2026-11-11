import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21274)) 452591661 452624429 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 452591661 452624429).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21274 452591661 452624429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21275)) 452624429 452657197 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 452624429 452657197).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21275 452624429 452657197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21276)) 452657197 452689965 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 452657197 452689965).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21276 452657197 452689965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21277)) 452689965 452722733 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 452689965 452722733).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21277 452689965 452722733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 452591661 452657197).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 452591661 ≤ 452624429)
    (by decide : 452624429 ≤ 452657197) block0 block1

theorem join_0_1 : (twinPrimeSegment 452657197 452722733).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 452657197 ≤ 452689965)
    (by decide : 452689965 ≤ 452722733) block2 block3

theorem join_1_0 : (twinPrimeSegment 452591661 452722733).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 452591661 ≤ 452657197)
    (by decide : 452657197 ≤ 452722733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 452591661 452722733).card = 414 := join_1_0

end S215C13
end Sude.GeneratedTwinScan
