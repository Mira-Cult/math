import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13947)) 194510893 194543661 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194510893 194543661).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13947 194510893 194543661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13949)) 194543661 194576429 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194543661 194576429).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13949 194543661 194576429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13950)) 194576429 194609197 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194576429 194609197).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13950 194576429 194609197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13951)) 194609197 194641965 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194609197 194641965).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13951 194609197 194641965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194510893 194576429).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 194510893 ≤ 194543661)
    (by decide : 194543661 ≤ 194576429) block0 block1

theorem join_0_1 : (twinPrimeSegment 194576429 194641965).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 194576429 ≤ 194609197)
    (by decide : 194609197 ≤ 194641965) block2 block3

theorem join_1_0 : (twinPrimeSegment 194510893 194641965).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 194510893 ≤ 194576429)
    (by decide : 194576429 ≤ 194641965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194510893 194641965).card = 449 := join_1_0

end S092C12
end Sude.GeneratedTwinScan
