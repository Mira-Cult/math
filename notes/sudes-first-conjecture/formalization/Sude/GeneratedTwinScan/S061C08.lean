import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128974893 129007661 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128974893 129007661).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128974893 129007661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129007661 129040429 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129007661 129040429).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129007661 129040429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129040429 129073197 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129040429 129073197).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129040429 129073197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129073197 129105965 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129073197 129105965).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129073197 129105965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128974893 129040429).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 128974893 ≤ 129007661)
    (by decide : 129007661 ≤ 129040429) block0 block1

theorem join_0_1 : (twinPrimeSegment 129040429 129105965).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 129040429 ≤ 129073197)
    (by decide : 129073197 ≤ 129105965) block2 block3

theorem join_1_0 : (twinPrimeSegment 128974893 129105965).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 128974893 ≤ 129040429)
    (by decide : 129040429 ≤ 129105965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128974893 129105965).card = 466 := join_1_0

end S061C08
end Sude.GeneratedTwinScan
