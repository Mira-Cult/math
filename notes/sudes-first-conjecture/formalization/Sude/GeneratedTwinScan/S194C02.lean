import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20177)) 407109677 407142445 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 407109677 407142445).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20177 407109677 407142445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20178)) 407142445 407175213 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 407142445 407175213).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20178 407142445 407175213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20179)) 407175213 407207981 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 407175213 407207981).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20179 407175213 407207981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20180)) 407207981 407240749 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 407207981 407240749).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20180 407207981 407240749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 407109677 407175213).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 407109677 ≤ 407142445)
    (by decide : 407142445 ≤ 407175213) block0 block1

theorem join_0_1 : (twinPrimeSegment 407175213 407240749).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 407175213 ≤ 407207981)
    (by decide : 407207981 ≤ 407240749) block2 block3

theorem join_1_0 : (twinPrimeSegment 407109677 407240749).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 407109677 ≤ 407175213)
    (by decide : 407175213 ≤ 407240749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 407109677 407240749).card = 450 := join_1_0

end S194C02
end Sude.GeneratedTwinScan
