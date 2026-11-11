import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17832)) 317980717 318013485 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317980717 318013485).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17832 317980717 318013485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17833)) 318013485 318046253 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318013485 318046253).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17833 318013485 318046253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17834)) 318046253 318079021 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318046253 318079021).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17834 318046253 318079021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17835)) 318079021 318111789 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318079021 318111789).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17835 318079021 318111789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317980717 318046253).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 317980717 ≤ 318013485)
    (by decide : 318013485 ≤ 318046253) block0 block1

theorem join_0_1 : (twinPrimeSegment 318046253 318111789).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 318046253 ≤ 318079021)
    (by decide : 318079021 ≤ 318111789) block2 block3

theorem join_1_0 : (twinPrimeSegment 317980717 318111789).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 317980717 ≤ 318046253)
    (by decide : 318046253 ≤ 318111789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317980717 318111789).card = 468 := join_1_0

end S151C10
end Sude.GeneratedTwinScan
