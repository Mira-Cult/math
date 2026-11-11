import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14036)) 197001261 197034029 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197001261 197034029).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14036 197001261 197034029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14038)) 197034029 197066797 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197034029 197066797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14038 197034029 197066797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14039)) 197066797 197099565 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197066797 197099565).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14039 197066797 197099565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14040)) 197099565 197132333 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197099565 197132333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14040 197099565 197132333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197001261 197066797).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 197001261 ≤ 197034029)
    (by decide : 197034029 ≤ 197066797) block0 block1

theorem join_0_1 : (twinPrimeSegment 197066797 197132333).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 197066797 ≤ 197099565)
    (by decide : 197099565 ≤ 197132333) block2 block3

theorem join_1_0 : (twinPrimeSegment 197001261 197132333).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 197001261 ≤ 197066797)
    (by decide : 197066797 ≤ 197132333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197001261 197132333).card = 462 := join_1_0

end S093C15
end Sude.GeneratedTwinScan
