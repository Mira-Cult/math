import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16016)) 256507949 256540717 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256507949 256540717).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16016 256507949 256540717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16017)) 256540717 256573485 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256540717 256573485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16017 256540717 256573485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16018)) 256573485 256606253 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256573485 256606253).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16018 256573485 256606253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16019)) 256606253 256639021 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256606253 256639021).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16019 256606253 256639021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256507949 256573485).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 256507949 ≤ 256540717)
    (by decide : 256540717 ≤ 256573485) block0 block1

theorem join_0_1 : (twinPrimeSegment 256573485 256639021).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 256573485 ≤ 256606253)
    (by decide : 256606253 ≤ 256639021) block2 block3

theorem join_1_0 : (twinPrimeSegment 256507949 256639021).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 256507949 ≤ 256573485)
    (by decide : 256573485 ≤ 256639021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256507949 256639021).card = 420 := join_1_0

end S122C05
end Sude.GeneratedTwinScan
