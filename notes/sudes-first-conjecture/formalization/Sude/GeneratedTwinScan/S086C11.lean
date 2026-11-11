import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13484)) 181796909 181829677 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181796909 181829677).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13484 181796909 181829677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13485)) 181829677 181862445 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181829677 181862445).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13485 181829677 181862445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13486)) 181862445 181895213 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181862445 181895213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13486 181862445 181895213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13488)) 181895213 181927981 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181895213 181927981).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13488 181895213 181927981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181796909 181862445).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 181796909 ≤ 181829677)
    (by decide : 181829677 ≤ 181862445) block0 block1

theorem join_0_1 : (twinPrimeSegment 181862445 181927981).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 181862445 ≤ 181895213)
    (by decide : 181895213 ≤ 181927981) block2 block3

theorem join_1_0 : (twinPrimeSegment 181796909 181927981).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 181796909 ≤ 181862445)
    (by decide : 181862445 ≤ 181927981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181796909 181927981).card = 461 := join_1_0

end S086C11
end Sude.GeneratedTwinScan
