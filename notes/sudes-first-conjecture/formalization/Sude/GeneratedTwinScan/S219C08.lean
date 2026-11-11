import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21455)) 460324909 460357677 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460324909 460357677).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21455 460324909 460357677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21456)) 460357677 460390445 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460357677 460390445).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21456 460357677 460390445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21457)) 460390445 460423213 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460390445 460423213).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21457 460390445 460423213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21458)) 460423213 460455981 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460423213 460455981).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21458 460423213 460455981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460324909 460390445).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 460324909 ≤ 460357677)
    (by decide : 460357677 ≤ 460390445) block0 block1

theorem join_0_1 : (twinPrimeSegment 460390445 460455981).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 460390445 ≤ 460423213)
    (by decide : 460423213 ≤ 460455981) block2 block3

theorem join_1_0 : (twinPrimeSegment 460324909 460455981).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 460324909 ≤ 460390445)
    (by decide : 460390445 ≤ 460455981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460324909 460455981).card = 438 := join_1_0

end S219C08
end Sude.GeneratedTwinScan
