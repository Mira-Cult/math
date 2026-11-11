import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18944)) 358875181 358907949 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 358875181 358907949).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18944 358875181 358907949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18945)) 358907949 358940717 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 358907949 358940717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18945 358907949 358940717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18946)) 358940717 358973485 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358940717 358973485).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18946 358940717 358973485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18947)) 358973485 359006253 = 89 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358973485 359006253).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18947 358973485 359006253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 358875181 358940717).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 358875181 ≤ 358907949)
    (by decide : 358907949 ≤ 358940717) block0 block1

theorem join_0_1 : (twinPrimeSegment 358940717 359006253).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 358940717 ≤ 358973485)
    (by decide : 358973485 ≤ 359006253) block2 block3

theorem join_1_0 : (twinPrimeSegment 358875181 359006253).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 358875181 ≤ 358940717)
    (by decide : 358940717 ≤ 359006253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 358875181 359006253).card = 451 := join_1_0

end S171C02
end Sude.GeneratedTwinScan
