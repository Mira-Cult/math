import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14773)) 218234925 218267693 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218234925 218267693).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14773 218234925 218267693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14774)) 218267693 218300461 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218267693 218300461).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14774 218267693 218300461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14776)) 218300461 218333229 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218300461 218333229).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14776 218300461 218333229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14777)) 218333229 218365997 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218333229 218365997).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14777 218333229 218365997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218234925 218300461).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 218234925 ≤ 218267693)
    (by decide : 218267693 ≤ 218300461) block0 block1

theorem join_0_1 : (twinPrimeSegment 218300461 218365997).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 218300461 ≤ 218333229)
    (by decide : 218333229 ≤ 218365997) block2 block3

theorem join_1_0 : (twinPrimeSegment 218234925 218365997).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 218234925 ≤ 218300461)
    (by decide : 218300461 ≤ 218365997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218234925 218365997).card = 470 := join_1_0

end S104C01
end Sude.GeneratedTwinScan
