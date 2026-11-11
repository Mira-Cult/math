import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20323)) 413007917 413040685 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 413007917 413040685).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20323 413007917 413040685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20324)) 413040685 413073453 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 413040685 413073453).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20324 413040685 413073453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20325)) 413073453 413106221 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 413073453 413106221).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20325 413073453 413106221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20325)) 413106221 413138989 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 413106221 413138989).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20325 413106221 413138989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 413007917 413073453).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 413007917 ≤ 413040685)
    (by decide : 413040685 ≤ 413073453) block0 block1

theorem join_0_1 : (twinPrimeSegment 413073453 413138989).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 413073453 ≤ 413106221)
    (by decide : 413106221 ≤ 413138989) block2 block3

theorem join_1_0 : (twinPrimeSegment 413007917 413138989).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 413007917 ≤ 413073453)
    (by decide : 413073453 ≤ 413138989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 413007917 413138989).card = 434 := join_1_0

end S196C15
end Sude.GeneratedTwinScan
