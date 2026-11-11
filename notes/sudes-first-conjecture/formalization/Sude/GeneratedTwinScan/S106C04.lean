import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14928)) 222822445 222855213 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222822445 222855213).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14928 222822445 222855213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14929)) 222855213 222887981 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222855213 222887981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14929 222855213 222887981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14930)) 222887981 222920749 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222887981 222920749).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14930 222887981 222920749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14931)) 222920749 222953517 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222920749 222953517).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14931 222920749 222953517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222822445 222887981).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 222822445 ≤ 222855213)
    (by decide : 222855213 ≤ 222887981) block0 block1

theorem join_0_1 : (twinPrimeSegment 222887981 222953517).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 222887981 ≤ 222920749)
    (by decide : 222920749 ≤ 222953517) block2 block3

theorem join_1_0 : (twinPrimeSegment 222822445 222953517).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 222822445 ≤ 222887981)
    (by decide : 222887981 ≤ 222953517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222822445 222953517).card = 477 := join_1_0

end S106C04
end Sude.GeneratedTwinScan
