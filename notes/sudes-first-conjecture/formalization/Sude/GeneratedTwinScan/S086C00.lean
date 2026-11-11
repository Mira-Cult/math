import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13430)) 180355117 180387885 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180355117 180387885).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13430 180355117 180387885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13432)) 180387885 180420653 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180387885 180420653).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13432 180387885 180420653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13433)) 180420653 180453421 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180420653 180453421).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13433 180420653 180453421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13434)) 180453421 180486189 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180453421 180486189).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13434 180453421 180486189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180355117 180420653).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 180387885)
    (by decide : 180387885 ≤ 180420653) block0 block1

theorem join_0_1 : (twinPrimeSegment 180420653 180486189).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 180420653 ≤ 180453421)
    (by decide : 180453421 ≤ 180486189) block2 block3

theorem join_1_0 : (twinPrimeSegment 180355117 180486189).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 180420653)
    (by decide : 180420653 ≤ 180486189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180355117 180486189).card = 458 := join_1_0

end S086C00
end Sude.GeneratedTwinScan
