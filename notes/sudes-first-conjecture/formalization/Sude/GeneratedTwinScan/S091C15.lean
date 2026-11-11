import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13886)) 192806957 192839725 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192806957 192839725).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13886 192806957 192839725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13887)) 192839725 192872493 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192839725 192872493).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13887 192839725 192872493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13889)) 192872493 192905261 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192872493 192905261).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13889 192872493 192905261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13890)) 192905261 192938029 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192905261 192938029).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13890 192905261 192938029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192806957 192872493).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 192806957 ≤ 192839725)
    (by decide : 192839725 ≤ 192872493) block0 block1

theorem join_0_1 : (twinPrimeSegment 192872493 192938029).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 192872493 ≤ 192905261)
    (by decide : 192905261 ≤ 192938029) block2 block3

theorem join_1_0 : (twinPrimeSegment 192806957 192938029).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 192806957 ≤ 192872493)
    (by decide : 192872493 ≤ 192938029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192806957 192938029).card = 454 := join_1_0

end S091C15
end Sude.GeneratedTwinScan
