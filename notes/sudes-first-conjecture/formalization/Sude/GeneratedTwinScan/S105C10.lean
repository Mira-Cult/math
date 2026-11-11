import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14884)) 221511725 221544493 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221511725 221544493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14884 221511725 221544493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14885)) 221544493 221577261 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221544493 221577261).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14885 221544493 221577261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14886)) 221577261 221610029 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221577261 221610029).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14886 221577261 221610029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14887)) 221610029 221642797 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221610029 221642797).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14887 221610029 221642797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221511725 221577261).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 221511725 ≤ 221544493)
    (by decide : 221544493 ≤ 221577261) block0 block1

theorem join_0_1 : (twinPrimeSegment 221577261 221642797).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 221577261 ≤ 221610029)
    (by decide : 221610029 ≤ 221642797) block2 block3

theorem join_1_0 : (twinPrimeSegment 221511725 221642797).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 221511725 ≤ 221577261)
    (by decide : 221577261 ≤ 221642797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221511725 221642797).card = 445 := join_1_0

end S105C10
end Sude.GeneratedTwinScan
