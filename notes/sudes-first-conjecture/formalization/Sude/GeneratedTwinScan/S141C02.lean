import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17204)) 295960621 295993389 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295960621 295993389).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17204 295960621 295993389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17205)) 295993389 296026157 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295993389 296026157).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17205 295993389 296026157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17206)) 296026157 296058925 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296026157 296058925).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17206 296026157 296058925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17207)) 296058925 296091693 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296058925 296091693).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17207 296058925 296091693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295960621 296026157).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 295960621 ≤ 295993389)
    (by decide : 295993389 ≤ 296026157) block0 block1

theorem join_0_1 : (twinPrimeSegment 296026157 296091693).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 296026157 ≤ 296058925)
    (by decide : 296058925 ≤ 296091693) block2 block3

theorem join_1_0 : (twinPrimeSegment 295960621 296091693).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 295960621 ≤ 296026157)
    (by decide : 296026157 ≤ 296091693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295960621 296091693).card = 451 := join_1_0

end S141C02
end Sude.GeneratedTwinScan
