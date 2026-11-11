import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18308)) 335151149 335183917 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335151149 335183917).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18308 335151149 335183917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18308)) 335183917 335216685 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335183917 335216685).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18308 335183917 335216685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18309)) 335216685 335249453 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335216685 335249453).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18309 335216685 335249453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18310)) 335249453 335282221 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335249453 335282221).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18310 335249453 335282221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335151149 335216685).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 335151149 ≤ 335183917)
    (by decide : 335183917 ≤ 335216685) block0 block1

theorem join_0_1 : (twinPrimeSegment 335216685 335282221).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 335216685 ≤ 335249453)
    (by decide : 335249453 ≤ 335282221) block2 block3

theorem join_1_0 : (twinPrimeSegment 335151149 335282221).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 335151149 ≤ 335216685)
    (by decide : 335216685 ≤ 335282221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335151149 335282221).card = 439 := join_1_0

end S159C13
end Sude.GeneratedTwinScan
