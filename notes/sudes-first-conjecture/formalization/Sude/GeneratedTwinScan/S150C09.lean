import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17770)) 315752493 315785261 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 315752493 315785261).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17770 315752493 315785261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17771)) 315785261 315818029 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 315785261 315818029).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17771 315785261 315818029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17772)) 315818029 315850797 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 315818029 315850797).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17772 315818029 315850797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17773)) 315850797 315883565 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 315850797 315883565).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17773 315850797 315883565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 315752493 315818029).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 315752493 ≤ 315785261)
    (by decide : 315785261 ≤ 315818029) block0 block1

theorem join_0_1 : (twinPrimeSegment 315818029 315883565).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 315818029 ≤ 315850797)
    (by decide : 315850797 ≤ 315883565) block2 block3

theorem join_1_0 : (twinPrimeSegment 315752493 315883565).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 315752493 ≤ 315818029)
    (by decide : 315818029 ≤ 315883565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 315752493 315883565).card = 404 := join_1_0

end S150C09
end Sude.GeneratedTwinScan
