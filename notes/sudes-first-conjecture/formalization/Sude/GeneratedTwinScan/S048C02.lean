import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100925485 100958253 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 100925485 100958253).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100925485 100958253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100958253 100991021 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 100958253 100991021).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100958253 100991021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 100991021 101023789 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 100991021 101023789).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 100991021 101023789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101023789 101056557 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101023789 101056557).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101023789 101056557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 100925485 100991021).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 100925485 ≤ 100958253)
    (by decide : 100958253 ≤ 100991021) block0 block1

theorem join_0_1 : (twinPrimeSegment 100991021 101056557).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 100991021 ≤ 101023789)
    (by decide : 101023789 ≤ 101056557) block2 block3

theorem join_1_0 : (twinPrimeSegment 100925485 101056557).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 100925485 ≤ 100991021)
    (by decide : 100991021 ≤ 101056557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 100925485 101056557).card = 510 := join_1_0

end S048C02
end Sude.GeneratedTwinScan
