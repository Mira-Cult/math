import Shared.Beeping.NPcoNP.Grammar284AdministrativeChain
import Shared.Beeping.NPcoNP.GrammarFullRowsCoverage

/-! Decoding an expanded jump row as one of the four physical routines. -/
namespace Shared.Beeping.NPcoNP.Grammar284AdministrativeTags
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Grammar284AdministrativeChain
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

def acceptableTag (s : String) : Bool :=
  (s == "_continue.1") || (s == "_continue.2") || (s == "_break.1") || (s == "_break.2") ||
    ((s != "jump") && ((operationTag s == some .other) || (operationTag s == some .branch)))

theorem all_tags : traceState557.acc.leaves.toList.all (fun e => acceptableTag e.2) = true := by decide

theorem listed_jump_kind (entry : Path × String) (member : entry ∈ traceState557.acc.leaves.toList)
    (dst : Nat) (hrow : fullRow traceState557.acc.starts entry=some ⟨"jump",[dst]⟩) :
    AdministrativeJump entry dst := by
  have hc := List.all_eq_true.mp all_tags entry member
  simp only [acceptableTag,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at hc
  rcases hc with ((((h1 | h2) | h3) | h4) | ⟨hn,hother | hbranch⟩)
  · left
    refine ⟨h1,?_⟩
    cases hd : restart traceState557.acc.starts entry.1 1 with
    | none => simp [fullRow,h1,operationTag,parseDigits,hd] at hrow
    | some d =>
      simp [fullRow,h1,operationTag,parseDigits,hd] at hrow
      simpa only [hrow] using hd
  · right; left
    refine ⟨h2,?_⟩
    cases hd : restart traceState557.acc.starts entry.1 2 with
    | none => simp [fullRow,h2,operationTag,parseDigits,hd] at hrow
    | some d =>
      simp [fullRow,h2,operationTag,parseDigits,hd] at hrow
      simpa only [hrow] using hd
  · right; right; left
    refine ⟨h3,?_⟩
    cases hd : successor traceState557.acc.starts entry.1 1 with
    | none => simp [fullRow,h3,operationTag,parseDigits,hd] at hrow
    | some d =>
      simp [fullRow,h3,operationTag,parseDigits,hd] at hrow
      simpa only [hrow] using hd
  · right; right; right
    refine ⟨h4,?_⟩
    cases hd : successor traceState557.acc.starts entry.1 2 with
    | none => simp [fullRow,h4,operationTag,parseDigits,hd] at hrow
    | some d =>
      simp [fullRow,h4,operationTag,parseDigits,hd] at hrow
      simpa only [hrow] using hd
  · cases hs : successor traceState557.acc.starts entry.1 0 with
    | none => simp [fullRow,hother,hs] at hrow
    | some d =>
      simp [fullRow,hother,hs] at hrow
      exact False.elim (hn hrow.1)
  · cases hs : successor traceState557.acc.starts entry.1 0 with
    | none => simp [fullRow,hbranch,hs] at hrow
    | some d =>
      cases hs' : successor traceState557.acc.starts entry.1 1 with
      | none => simp [fullRow,hbranch,hs,hs'] at hrow
      | some d' => simp [fullRow,hbranch,hs,hs'] at hrow

#print axioms listed_jump_kind
end Shared.Beeping.NPcoNP.Grammar284AdministrativeTags
