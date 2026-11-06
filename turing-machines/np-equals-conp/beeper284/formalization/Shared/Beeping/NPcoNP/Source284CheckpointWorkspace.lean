import Shared.Beeping.NPcoNP.Source284SentinelPositiveTokens
import Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial
import Shared.Beeping.NPcoNP.Source284TwoSidedWorkspace
import Shared.Beeping.NPcoNP.Source284EraseTokenHistory
import Shared.Beeping.NPcoNP.Source284ProductGrowth
import Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup

/-! Generate a polynomial guard-token block, grow a separate larger
workspace, and remove only the newer temporary blocks. The guard block and
the original certificate remain on tape. The later certificate seek and
connection to the dynamic guard are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def base (n : Nat) : Nat := n+2
def guard (k n : Nat) : Nat := innerAfter k (base n) (base n)
def previous (k n : Nat) : Nat := outerAfter k (base n) (base n)
def workspace (k r n : Nat) : Nat := innerAfter (r+2) (previous k n) (guard k n)
def workspaceOuter (k r n : Nat) : Nat := outerAfter (r+2) (previous k n) (guard k n)
def cleanupZeros (k r n : Nat) : Nat := 2*(workspace k r n+1)+2*workspaceOuter k r n

def checkpointHistory (k n certificate : Nat) : Nat :=
  pairTape (List.replicate (guard k n) false)
    (pairTape (List.replicate (previous k n) false)
      (historyAfter k (base n) (base n) (2*certificate+1)))

def extraOuter (k n : Nat) : Nat := previous k n*guard k n
def extraInner (k n : Nat) : Nat := guard k n*extraOuter k n

def retained (k r n suffix : Nat) : Nat :=
  let first := suffixAfter k (base n) (base n) (Source284SentinelPositiveTokens.retained n suffix)
  let second := suffixAfter (r+2) (previous k n) (guard k n) first
  2^(Source284EraseTokenHistory.cells r (extraOuter k n) (extraInner k n))*
    (2^(cleanupZeros k r n+2)*
      (2^(workspace k r n+1)*halves (workspace k r n) (second/2)))

def table (k r : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ProductIteration.table k
    (Source284ProductIteration.table (r+2)
      (Source284TwoSidedWorkspace.table (Source284EraseZeroBlock.table
        (Source284EraseTokenHistory.table r continuation))))

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284SentinelPositiveTokens.description
    (287*k+(287*(r+2)+(73+(30+(30*r+states))))) (table k r continuation)

def totalCost (k r : Nat) (w : List Bool) : Nat :=
  Source284SentinelPositiveTokens.totalCost w+
    cost k (base w.length) (base w.length) (w++[false]).length+
    cost (r+2) (previous k w.length) (guard k w.length) (w++[false]).length+
    Source284TwoSidedWorkspace.workCost (workspace k r w.length) (w++[false]).length+
    Source284EraseZeroBlock.cost (cleanupZeros k r w.length) (w++[false]).length+
    Source284EraseTokenHistory.cost r (extraOuter k w.length) (extraInner k w.length) (w++[false]).length

theorem closed (k r states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (287*k+(287*(r+2)+(73+(30+(30*r+states))))) (table k r continuation) := by
  have hh := Source284EraseTokenHistory.closed r states continuation hn hv
  have hz := Source284EraseZeroBlock.closed (30*r+states)
    (Source284EraseTokenHistory.table r continuation) (by omega) hh
  have hw := Source284TwoSidedWorkspace.closed (30+(30*r+states))
    (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table r continuation)) (by omega) hz
  have he := Source284ProductIteration.closed (r+2) (73+(30+(30*r+states)))
    (Source284TwoSidedWorkspace.table (Source284EraseZeroBlock.table
      (Source284EraseTokenHistory.table r continuation))) (by omega) hw
  exact Source284ProductIteration.closed k _ _ (by omega) he

/-- The later product stages retain the selected earlier guard block just
beneath their removable history, before any table code touches the witness. -/
theorem checkpoint_history (r a b certificate : Nat) :
    historyAfter (r+2) a b certificate =
      historyAfter r (a*b) (b*(a*b))
        (pairTape (List.replicate b false) (pairTape (List.replicate a false) certificate)) := by
  simp [historyAfter]

/-- Mathematical extraction of the protected original certificate from the
two retained token blocks and older history. This is not a runtime decoder. -/
def recoverCertificate (k n tape : Nat) : Nat :=
  (Source284PolynomialRunwayRecovery.unhistory k (base n) (base n)
    (Source284PolynomialRunwayRecovery.unpairBlock (previous k n)
      (Source284PolynomialRunwayRecovery.unpairBlock (guard k n) tape)))/2

theorem recover_checkpoint_certificate (k n certificate : Nat) :
    recoverCertificate k n (checkpointHistory k n certificate) = certificate := by
  simp [recoverCertificate,checkpointHistory,Source284PolynomialRunwayRecovery.unpairBlock_pair,
    Source284PolynomialRunwayRecovery.unhistory_history]
  omega

/-- From raw framed input and an arbitrary certificate, a fixed finite
source table constructs separate workspace and guard blocks, removes only
the newer temporary stack, and follows the supplied continuation. -/
theorem source_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w+fuel) =
    toSource (shiftConfig (1252+287*k+317*r) (run continuation
      ⟨checkpointHistory k w.length certificate,
        2*flipped (w++[false]) (retained k r w.length suffix),some 0⟩ fuel)) := by
  let n := w.length
  let a := previous k n
  let b := guard k n
  let m := workspace k r n
  let outer := workspaceOuter k r n
  let z := cleanupZeros k r n
  let old := historyAfter k (base n) (base n) (2*certificate+1)
  let first := suffixAfter k (base n) (base n) (Source284SentinelPositiveTokens.retained n suffix)
  let second := suffixAfter (r+2) a b first
  let c1 := cost k (base n) (base n) (w++[false]).length
  let c2 := cost (r+2) a b (w++[false]).length
  let cw := Source284TwoSidedWorkspace.workCost m (w++[false]).length
  let cz := Source284EraseZeroBlock.cost z (w++[false]).length
  let ch := Source284EraseTokenHistory.cost r (extraOuter k n) (extraInner k n) (w++[false]).length
  have hc := closed k r states continuation hn hv
  have h := Source284SentinelPositiveTokens.source_then
    (287*k+(287*(r+2)+(73+(30+(30*r+states))))) (table k r continuation)
    w certificate suffix (c1+(c2+(cw+(cz+(ch+fuel))))) (by omega) hc
  have ht : totalCost k r w+fuel = Source284SentinelPositiveTokens.totalCost w+
      (c1+(c2+(cw+(cz+(ch+fuel))))) := by
    simp [totalCost,n,a,b,m,z,c1,c2,cw,cz,ch]; omega
  rw [ht]
  change Source284Relative.run (Source284SentinelPositiveTokens.description _ (table k r continuation)) _ _ = _
  rw [h]
  change toSource (shiftConfig 575 (run (Source284ProductIteration.table k
    (Source284ProductIteration.table (r+2) (Source284TwoSidedWorkspace.table
      (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table r continuation)))))
    ⟨pairTape (List.replicate (base n) false) (pairTape (List.replicate (base n) false) (2*certificate+1)),
      2*flipped (w++[false]) (Source284SentinelPositiveTokens.retained n suffix),some 0⟩ _)) = _
  rw [Source284ProductIteration.iterate_then]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (run
    (Source284ProductIteration.table (r+2) (Source284TwoSidedWorkspace.table
      (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table r continuation))))
    ⟨pairTape (List.replicate b false) (pairTape (List.replicate a false) old),
      2*flipped (w++[false]) first,some 0⟩ _))) = _
  rw [Source284ProductIteration.iterate_then]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig (287*(r+2)) (run
    (Source284TwoSidedWorkspace.table (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table r continuation)))
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate outer false) (historyAfter (r+2) a b old)),
      2*flipped (w++[false]) second,some 0⟩ _)))) = _
  rw [Source284TwoSidedWorkspace.workspace_then,Source284PolynomialRunwayCleanup.top_form]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig (287*(r+2)) (shiftConfig 73
    (run (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table r continuation))
      ⟨2^(z+1)*(2*historyAfter (r+2) a b old+1),_,some 0⟩ _))))) = _
  rw [Source284EraseZeroBlock.erase_then,checkpoint_history]
  have hch : ch = Source284EraseTokenHistory.cost r (a*b) (b*(a*b)) (w++[false]).length := rfl
  rw [hch,Source284EraseTokenHistory.erase_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have he : 575+287*k+287*(r+2)+73+30+30*r=1252+287*k+317*r := by omega
  rw [he]
  rfl

end Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
