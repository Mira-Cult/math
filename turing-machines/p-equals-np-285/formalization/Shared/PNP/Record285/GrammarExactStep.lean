import Shared.PNP.Record285.GrammarExactControl
import Shared.PNP.Record285.GrammarAnchoredStep

/-! Exact one-action refinement step at every anchored valid grammar root. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.GrammarReady

theorem anchored_exact_step (fields : List Nat) (rootHead anchor : Int)
    (physical : Shared.Beeping.Machines.Config 285) (hlen : 15 ≤ fields.length)
    (hroot : AnchoredRoot fields rootHead anchor physical) (hspace : rootHead+328 ≤ anchor) :
    ∃ e newFields steps code head leftTail gap,
      ZeroLeaf fields rootHead anchor e code head leftTail gap physical ∧
      Duration e fields code gap steps ∧ 0 < steps ∧ Update e fields newFields ∧
      AnchoredRoot newFields rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      Events e physical steps := by
  obtain ⟨e,code,head,leftTail,gap,hleaf⟩ := anchored_zero_leaf fields rootHead anchor physical hroot hspace
  have hwalk := hleaf.1
  cases e with
  | node i => exact False.elim (walk_no_node code rootIndex i hwalk)
  | inc i =>
    have hi := (producer_increment_route code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    have hp := increment_exact before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,_,_,code,head,leftTail,gap,hleaf,Duration.inc before after target code gap,hp.1,
      Update.inc before after target,hp.2.1,by simpa [Events] using hp.2.2⟩
  | dec i =>
    have hi := (producer_decrement_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    obtain ⟨steps,hduration,hpos,hnext,hquiet⟩ :=
      decrement_exact before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,_,steps,code,head,leftTail,gap,hleaf,hduration,hpos,Update.dec before after target,hnext,
      by simpa [Events] using hquiet⟩
  | half i =>
    have hi := (producer_half_safe code i hwalk).1
    obtain ⟨before,target,after,hfields,hbefore⟩ := fields_split fields i (by omega)
    subst fields
    subst i
    obtain ⟨steps,next,hduration,hpos,hupdate,hnext,hquiet⟩ :=
      half_exact before after target rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,next,steps,code,head,leftTail,gap,hleaf,hduration,hpos,Update.half before after next target hupdate,hnext,
      by simpa [Events] using hquiet⟩
  | beep =>
    have hp := beep_anchored fields rootHead anchor head leftTail gap code physical hleaf
    dsimp only at hp
    have hevent : beepEventTime false gap < beepDuration false gap := by
      simp [beepEventTime,beepDuration]; omega
    exact ⟨_,fields,_,code,head,leftTail,gap,hleaf,Duration.beep fields code gap,hp.1,Update.beep fields,hp.2.1,
      by simpa [Events] using ⟨beepEventTime false gap,hevent,hp.2.2⟩⟩
  | brk i =>
    obtain ⟨steps,hduration,hpos,hnext,hquiet⟩ :=
      break_exact fields i rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,fields,steps,code,head,leftTail,gap,hleaf,hduration,hpos,Update.brk i fields,hnext,
      by simpa [Events] using hquiet⟩
  | cont i =>
    obtain ⟨steps,hduration,hpos,hnext,hquiet⟩ :=
      continue_exact fields i rootHead anchor head leftTail gap code physical hleaf
    exact ⟨_,fields,steps,code,head,leftTail,gap,hleaf,hduration,hpos,Update.cont i fields,hnext,
      by simpa [Events] using hquiet⟩

end Shared.PNP.Record285.GrammarExact
