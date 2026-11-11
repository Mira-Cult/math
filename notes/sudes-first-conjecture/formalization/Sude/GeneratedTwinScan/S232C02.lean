import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22064)) 486801453 486834221 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486801453 486834221).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22064 486801453 486834221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22065)) 486834221 486866989 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486834221 486866989).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22065 486834221 486866989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22065)) 486866989 486899757 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486866989 486899757).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22065 486866989 486899757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22066)) 486899757 486932525 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486899757 486932525).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22066 486899757 486932525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486801453 486866989).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 486801453 ≤ 486834221)
    (by decide : 486834221 ≤ 486866989) block0 block1

theorem join_0_1 : (twinPrimeSegment 486866989 486932525).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 486866989 ≤ 486899757)
    (by decide : 486899757 ≤ 486932525) block2 block3

theorem join_1_0 : (twinPrimeSegment 486801453 486932525).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 486801453 ≤ 486866989)
    (by decide : 486866989 ≤ 486932525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486801453 486932525).card = 425 := join_1_0

end S232C02
end Sude.GeneratedTwinScan
