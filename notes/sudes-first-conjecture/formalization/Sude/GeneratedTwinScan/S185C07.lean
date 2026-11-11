import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19721)) 388890669 388923437 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 388890669 388923437).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19721 388890669 388923437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19721)) 388923437 388956205 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388923437 388956205).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19721 388923437 388956205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19722)) 388956205 388988973 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388956205 388988973).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19722 388956205 388988973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19723)) 388988973 389021741 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388988973 389021741).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19723 388988973 389021741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 388890669 388956205).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 388890669 ≤ 388923437)
    (by decide : 388923437 ≤ 388956205) block0 block1

theorem join_0_1 : (twinPrimeSegment 388956205 389021741).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 388956205 ≤ 388988973)
    (by decide : 388988973 ≤ 389021741) block2 block3

theorem join_1_0 : (twinPrimeSegment 388890669 389021741).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 388890669 ≤ 388956205)
    (by decide : 388956205 ≤ 389021741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 388890669 389021741).card = 467 := join_1_0

end S185C07
end Sude.GeneratedTwinScan
