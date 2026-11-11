import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14227)) 202375213 202407981 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202375213 202407981).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14227 202375213 202407981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14228)) 202407981 202440749 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202407981 202440749).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14228 202407981 202440749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14229)) 202440749 202473517 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202440749 202473517).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14229 202440749 202473517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14230)) 202473517 202506285 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202473517 202506285).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14230 202473517 202506285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202375213 202440749).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 202375213 ≤ 202407981)
    (by decide : 202407981 ≤ 202440749) block0 block1

theorem join_0_1 : (twinPrimeSegment 202440749 202506285).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 202440749 ≤ 202473517)
    (by decide : 202473517 ≤ 202506285) block2 block3

theorem join_1_0 : (twinPrimeSegment 202375213 202506285).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 202375213 ≤ 202440749)
    (by decide : 202440749 ≤ 202506285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202375213 202506285).card = 451 := join_1_0

end S096C08
end Sude.GeneratedTwinScan
