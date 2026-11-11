import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16989)) 288620589 288653357 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288620589 288653357).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16989 288620589 288653357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16990)) 288653357 288686125 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288653357 288686125).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16990 288653357 288686125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16991)) 288686125 288718893 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288686125 288718893).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16991 288686125 288718893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16992)) 288718893 288751661 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288718893 288751661).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16992 288718893 288751661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288620589 288686125).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 288620589 ≤ 288653357)
    (by decide : 288653357 ≤ 288686125) block0 block1

theorem join_0_1 : (twinPrimeSegment 288686125 288751661).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 288686125 ≤ 288718893)
    (by decide : 288718893 ≤ 288751661) block2 block3

theorem join_1_0 : (twinPrimeSegment 288620589 288751661).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 288620589 ≤ 288686125)
    (by decide : 288686125 ≤ 288751661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288620589 288751661).card = 485 := join_1_0

end S137C10
end Sude.GeneratedTwinScan
