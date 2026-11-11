import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13971)) 195166253 195199021 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195166253 195199021).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13971 195166253 195199021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13972)) 195199021 195231789 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195199021 195231789).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13972 195199021 195231789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13973)) 195231789 195264557 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195231789 195264557).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13973 195231789 195264557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13974)) 195264557 195297325 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195264557 195297325).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13974 195264557 195297325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195166253 195231789).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 195166253 ≤ 195199021)
    (by decide : 195199021 ≤ 195231789) block0 block1

theorem join_0_1 : (twinPrimeSegment 195231789 195297325).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 195231789 ≤ 195264557)
    (by decide : 195264557 ≤ 195297325) block2 block3

theorem join_1_0 : (twinPrimeSegment 195166253 195297325).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 195166253 ≤ 195231789)
    (by decide : 195231789 ≤ 195297325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195166253 195297325).card = 494 := join_1_0

end S093C01
end Sude.GeneratedTwinScan
