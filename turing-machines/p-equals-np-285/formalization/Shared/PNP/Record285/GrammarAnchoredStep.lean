import Shared.PNP.Record285.GrammarAnchoredContinue
import Shared.PNP.Record285.GrammarReadyInitial

/-! Every anchored valid grammar root takes one positive physical instruction
and returns to the same full invariant, with exact event accounting. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.CleanBank

theorem walk_no_node (code : List Bool) (n i : Nat) : walk n code ≠ some (.node i) := by
  induction code generalizing n with
  | nil => simp [walk]
  | cons b bs ih =>
    cases h : nodeEdge n b with
    | none => simp [walk,h]
    | some found =>
      cases found with
      | node j => simpa only [walk,h] using ih j
      | inc j => cases bs <;> simp [walk,h]
      | dec j => cases bs <;> simp [walk,h]
      | half j => cases bs <;> simp [walk,h]
      | beep => cases bs <;> simp [walk,h]
      | brk j => cases bs <;> simp [walk,h]
      | cont j => cases bs <;> simp [walk,h]

theorem anchored_step (fields : List Nat) (rootHead anchor : Int)
    (physical : Shared.Beeping.Machines.Config 285) (hlen : 15 ≤ fields.length)
    (hroot : AnchoredRoot fields rootHead anchor physical) (hspace : rootHead+328 ≤ anchor) :
    ∃ e newFields steps code head leftTail gap,
      ZeroLeaf fields rootHead anchor e code head leftTail gap physical ∧
      0 < steps ∧ Update e fields newFields ∧
      AnchoredRoot newFields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      Events e physical steps := by
  obtain ⟨e,code,head,leftTail,gap,hleaf⟩ := anchored_zero_leaf fields rootHead anchor physical hroot hspace
  have hwalk := hleaf.1
  cases e with
  | node i =>
    exact False.elim (walk_no_node code rootIndex i hwalk)
  | inc i =>
    have hi := (producer_increment_route code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    obtain ⟨steps,hpos,hnext,hquiet⟩ :=
      increment_anchored before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,_,steps,code,head,leftTail,gap,hleaf,hpos,Update.inc before after target,hnext,by simpa [Events] using hquiet⟩
  | dec i =>
    have hi := (producer_decrement_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    obtain ⟨steps,hpos,hnext,hquiet⟩ :=
      decrement_anchored before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,_,steps,code,head,leftTail,gap,hleaf,hpos,Update.dec before after target,hnext,by simpa [Events] using hquiet⟩
  | half i =>
    have hi := (producer_half_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    obtain ⟨steps,next,hpos,hupdate,hnext,hquiet⟩ :=
      half_anchored before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,next,steps,code,head,leftTail,gap,hleaf,hpos,Update.half before after next target hupdate,hnext,
      by simpa [Events] using hquiet⟩
  | beep =>
    have h := beep_anchored fields rootHead anchor head leftTail gap code physical hleaf
    dsimp only at h
    have hevent : beepEventTime false gap < beepDuration false gap := by
      simp [beepEventTime,beepDuration]; omega
    exact ⟨_,fields,_,code,head,leftTail,gap,hleaf,h.1,Update.beep fields,h.2.1,
      by simpa [Events] using ⟨beepEventTime false gap,hevent,h.2.2⟩⟩
  | brk i =>
    obtain ⟨steps,hpos,hnext,hquiet⟩ :=
      break_anchored fields i rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,fields,steps,code,head,leftTail,gap,hleaf,hpos,Update.brk i fields,hnext,by simpa [Events] using hquiet⟩
  | cont i =>
    obtain ⟨steps,hpos,hnext,hquiet⟩ :=
      continue_anchored fields i rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,fields,steps,code,head,leftTail,gap,hleaf,hpos,Update.cont i fields,hnext,by simpa [Events] using hquiet⟩

end Shared.PNP.Record285.GrammarReady
