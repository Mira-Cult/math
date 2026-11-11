import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20316)) 412745773 412778541 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412745773 412778541).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20316 412745773 412778541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20317)) 412778541 412811309 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412778541 412811309).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20317 412778541 412811309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20318)) 412811309 412844077 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412811309 412844077).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20318 412811309 412844077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20319)) 412844077 412876845 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412844077 412876845).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20319 412844077 412876845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412745773 412811309).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 412745773 ≤ 412778541)
    (by decide : 412778541 ≤ 412811309) block0 block1

theorem join_0_1 : (twinPrimeSegment 412811309 412876845).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 412811309 ≤ 412844077)
    (by decide : 412844077 ≤ 412876845) block2 block3

theorem join_1_0 : (twinPrimeSegment 412745773 412876845).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 412745773 ≤ 412811309)
    (by decide : 412811309 ≤ 412876845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412745773 412876845).card = 450 := join_1_0

end S196C13
end Sude.GeneratedTwinScan
