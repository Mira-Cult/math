import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14778)) 218365997 218398765 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218365997 218398765).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14778 218365997 218398765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14779)) 218398765 218431533 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218398765 218431533).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14779 218398765 218431533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14780)) 218431533 218464301 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218431533 218464301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14780 218431533 218464301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14781)) 218464301 218497069 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218464301 218497069).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14781 218464301 218497069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218365997 218431533).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 218365997 ≤ 218398765)
    (by decide : 218398765 ≤ 218431533) block0 block1

theorem join_0_1 : (twinPrimeSegment 218431533 218497069).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 218431533 ≤ 218464301)
    (by decide : 218464301 ≤ 218497069) block2 block3

theorem join_1_0 : (twinPrimeSegment 218365997 218497069).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 218365997 ≤ 218431533)
    (by decide : 218431533 ≤ 218497069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218365997 218497069).card = 475 := join_1_0

end S104C02
end Sude.GeneratedTwinScan
