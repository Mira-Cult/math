import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19099)) 364773421 364806189 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364773421 364806189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19099 364773421 364806189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19100)) 364806189 364838957 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364806189 364838957).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19100 364806189 364838957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19101)) 364838957 364871725 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364838957 364871725).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19101 364838957 364871725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19102)) 364871725 364904493 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364871725 364904493).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19102 364871725 364904493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364773421 364838957).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 364773421 ≤ 364806189)
    (by decide : 364806189 ≤ 364838957) block0 block1

theorem join_0_1 : (twinPrimeSegment 364838957 364904493).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 364838957 ≤ 364871725)
    (by decide : 364871725 ≤ 364904493) block2 block3

theorem join_1_0 : (twinPrimeSegment 364773421 364904493).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 364773421 ≤ 364838957)
    (by decide : 364838957 ≤ 364904493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364773421 364904493).card = 480 := join_1_0

end S173C15
end Sude.GeneratedTwinScan
