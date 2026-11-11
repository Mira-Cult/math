import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16862)) 284295213 284327981 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284295213 284327981).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16862 284295213 284327981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16862)) 284327981 284360749 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284327981 284360749).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16862 284327981 284360749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16863)) 284360749 284393517 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284360749 284393517).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16863 284360749 284393517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16864)) 284393517 284426285 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284393517 284426285).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16864 284393517 284426285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284295213 284360749).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 284295213 ≤ 284327981)
    (by decide : 284327981 ≤ 284360749) block0 block1

theorem join_0_1 : (twinPrimeSegment 284360749 284426285).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 284360749 ≤ 284393517)
    (by decide : 284393517 ≤ 284426285) block2 block3

theorem join_1_0 : (twinPrimeSegment 284295213 284426285).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 284295213 ≤ 284360749)
    (by decide : 284360749 ≤ 284426285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284295213 284426285).card = 470 := join_1_0

end S135C09
end Sude.GeneratedTwinScan
