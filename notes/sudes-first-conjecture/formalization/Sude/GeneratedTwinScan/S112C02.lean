import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15335)) 235143213 235175981 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235143213 235175981).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15335 235143213 235175981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15336)) 235175981 235208749 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235175981 235208749).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15336 235175981 235208749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15337)) 235208749 235241517 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235208749 235241517).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15337 235208749 235241517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15338)) 235241517 235274285 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235241517 235274285).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15338 235241517 235274285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235143213 235208749).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 235143213 ≤ 235175981)
    (by decide : 235175981 ≤ 235208749) block0 block1

theorem join_0_1 : (twinPrimeSegment 235208749 235274285).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 235208749 ≤ 235241517)
    (by decide : 235241517 ≤ 235274285) block2 block3

theorem join_1_0 : (twinPrimeSegment 235143213 235274285).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 235143213 ≤ 235208749)
    (by decide : 235208749 ≤ 235274285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235143213 235274285).card = 477 := join_1_0

end S112C02
end Sude.GeneratedTwinScan
