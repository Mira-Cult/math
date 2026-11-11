import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15889)) 252444717 252477485 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252444717 252477485).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15889 252444717 252477485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15890)) 252477485 252510253 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 252477485 252510253).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15890 252477485 252510253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15891)) 252510253 252543021 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 252510253 252543021).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15891 252510253 252543021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15892)) 252543021 252575789 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252543021 252575789).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15892 252543021 252575789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252444717 252510253).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 252444717 ≤ 252477485)
    (by decide : 252477485 ≤ 252510253) block0 block1

theorem join_0_1 : (twinPrimeSegment 252510253 252575789).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 252510253 ≤ 252543021)
    (by decide : 252543021 ≤ 252575789) block2 block3

theorem join_1_0 : (twinPrimeSegment 252444717 252575789).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 252444717 ≤ 252510253)
    (by decide : 252510253 ≤ 252575789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252444717 252575789).card = 474 := join_1_0

end S120C06
end Sude.GeneratedTwinScan
