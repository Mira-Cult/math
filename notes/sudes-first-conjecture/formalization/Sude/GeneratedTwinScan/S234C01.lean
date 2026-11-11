import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22156)) 490864685 490897453 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 490864685 490897453).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22156 490864685 490897453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22156)) 490897453 490930221 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 490897453 490930221).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22156 490897453 490930221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22157)) 490930221 490962989 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 490930221 490962989).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22157 490930221 490962989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22158)) 490962989 490995757 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 490962989 490995757).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22158 490962989 490995757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 490864685 490930221).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 490864685 ≤ 490897453)
    (by decide : 490897453 ≤ 490930221) block0 block1

theorem join_0_1 : (twinPrimeSegment 490930221 490995757).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 490930221 ≤ 490962989)
    (by decide : 490962989 ≤ 490995757) block2 block3

theorem join_1_0 : (twinPrimeSegment 490864685 490995757).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 490864685 ≤ 490930221)
    (by decide : 490930221 ≤ 490995757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 490864685 490995757).card = 427 := join_1_0

end S234C01
end Sude.GeneratedTwinScan
