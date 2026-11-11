import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17618)) 310378541 310411309 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310378541 310411309).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17618 310378541 310411309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17619)) 310411309 310444077 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310411309 310444077).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17619 310411309 310444077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17620)) 310444077 310476845 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310444077 310476845).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17620 310444077 310476845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17621)) 310476845 310509613 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310476845 310509613).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17621 310476845 310509613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310378541 310444077).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 310411309)
    (by decide : 310411309 ≤ 310444077) block0 block1

theorem join_0_1 : (twinPrimeSegment 310444077 310509613).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 310444077 ≤ 310476845)
    (by decide : 310476845 ≤ 310509613) block2 block3

theorem join_1_0 : (twinPrimeSegment 310378541 310509613).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 310444077)
    (by decide : 310444077 ≤ 310509613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310378541 310509613).card = 447 := join_1_0

end S148C00
end Sude.GeneratedTwinScan
