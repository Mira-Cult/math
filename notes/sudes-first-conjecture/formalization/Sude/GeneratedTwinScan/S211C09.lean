import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21064)) 443678765 443711533 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443678765 443711533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21064 443678765 443711533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21065)) 443711533 443744301 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443711533 443744301).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21065 443711533 443744301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21066)) 443744301 443777069 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443744301 443777069).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21066 443744301 443777069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21066)) 443777069 443809837 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443777069 443809837).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21066 443777069 443809837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443678765 443744301).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 443678765 ≤ 443711533)
    (by decide : 443711533 ≤ 443744301) block0 block1

theorem join_0_1 : (twinPrimeSegment 443744301 443809837).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 443744301 ≤ 443777069)
    (by decide : 443777069 ≤ 443809837) block2 block3

theorem join_1_0 : (twinPrimeSegment 443678765 443809837).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 443678765 ≤ 443744301)
    (by decide : 443744301 ≤ 443809837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443678765 443809837).card = 438 := join_1_0

end S211C09
end Sude.GeneratedTwinScan
