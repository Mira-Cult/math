import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15539)) 241434669 241467437 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241434669 241467437).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15539 241434669 241467437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15540)) 241467437 241500205 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241467437 241500205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15540 241467437 241500205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15541)) 241500205 241532973 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241500205 241532973).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15541 241500205 241532973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15542)) 241532973 241565741 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241532973 241565741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15542 241532973 241565741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241434669 241500205).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 241434669 ≤ 241467437)
    (by decide : 241467437 ≤ 241500205) block0 block1

theorem join_0_1 : (twinPrimeSegment 241500205 241565741).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 241500205 ≤ 241532973)
    (by decide : 241532973 ≤ 241565741) block2 block3

theorem join_1_0 : (twinPrimeSegment 241434669 241565741).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 241434669 ≤ 241500205)
    (by decide : 241500205 ≤ 241565741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241434669 241565741).card = 478 := join_1_0

end S115C02
end Sude.GeneratedTwinScan
