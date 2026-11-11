import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20435)) 417595437 417628205 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417595437 417628205).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20435 417595437 417628205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20436)) 417628205 417660973 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417628205 417660973).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20436 417628205 417660973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20437)) 417660973 417693741 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417660973 417693741).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20437 417660973 417693741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20438)) 417693741 417726509 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417693741 417726509).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20438 417693741 417726509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417595437 417660973).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 417595437 ≤ 417628205)
    (by decide : 417628205 ≤ 417660973) block0 block1

theorem join_0_1 : (twinPrimeSegment 417660973 417726509).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 417660973 ≤ 417693741)
    (by decide : 417693741 ≤ 417726509) block2 block3

theorem join_1_0 : (twinPrimeSegment 417595437 417726509).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 417595437 ≤ 417660973)
    (by decide : 417660973 ≤ 417726509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417595437 417726509).card = 422 := join_1_0

end S199C02
end Sude.GeneratedTwinScan
