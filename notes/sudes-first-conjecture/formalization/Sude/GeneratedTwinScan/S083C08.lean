import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13234)) 175112237 175145005 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 175112237 175145005).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13234 175112237 175145005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13235)) 175145005 175177773 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175145005 175177773).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13235 175145005 175177773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13236)) 175177773 175210541 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175177773 175210541).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13236 175177773 175210541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13237)) 175210541 175243309 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175210541 175243309).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13237 175210541 175243309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 175112237 175177773).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 175112237 ≤ 175145005)
    (by decide : 175145005 ≤ 175177773) block0 block1

theorem join_0_1 : (twinPrimeSegment 175177773 175243309).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 175177773 ≤ 175210541)
    (by decide : 175210541 ≤ 175243309) block2 block3

theorem join_1_0 : (twinPrimeSegment 175112237 175243309).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 175112237 ≤ 175177773)
    (by decide : 175177773 ≤ 175243309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 175112237 175243309).card = 501 := join_1_0

end S083C08
end Sude.GeneratedTwinScan
