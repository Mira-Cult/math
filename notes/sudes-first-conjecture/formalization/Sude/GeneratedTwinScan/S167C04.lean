import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S167C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18729)) 350748717 350781485 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 350748717 350781485).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18729 350748717 350781485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18730)) 350781485 350814253 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 350781485 350814253).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18730 350781485 350814253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18730)) 350814253 350847021 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350814253 350847021).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18730 350814253 350847021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18731)) 350847021 350879789 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350847021 350879789).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18731 350847021 350879789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 350748717 350814253).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 350748717 ≤ 350781485)
    (by decide : 350781485 ≤ 350814253) block0 block1

theorem join_0_1 : (twinPrimeSegment 350814253 350879789).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 350814253 ≤ 350847021)
    (by decide : 350847021 ≤ 350879789) block2 block3

theorem join_1_0 : (twinPrimeSegment 350748717 350879789).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 350748717 ≤ 350814253)
    (by decide : 350814253 ≤ 350879789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 350748717 350879789).card = 450 := join_1_0

end S167C04
end Sude.GeneratedTwinScan
