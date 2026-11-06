import Shared.Beeping.NPcoNP.Grammar284ReservedCoverage

/-! Every graph row other than beep and root is physically simulated from a
supplied reserved window, preserving that window and emitting no event. -/
namespace Shared.Beeping.NPcoNP.Grammar284ReservedNonspecial
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Grammar284ReservedCoverage
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem step (state : Fin 185) (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow state graph origin separator t) (hzero : state≠0) (hroot : state≠184) :
    let result := target.system.step ⟨state,graph⟩
    ∃ steps out, 0<steps ∧ result.2=[] ∧
      ReservedWindow result.1.state result.1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  obtain ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩ := window
  have window' : ReservedWindow state graph origin separator t :=
    ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩
  have hc := covered state hzero hroot path name hleaf
  have hroot' : state.val≠184 := by
    intro hh
    apply hroot
    apply Fin.ext
    simpa using hh
  rcases hc with ⟨n,inc,hop⟩ | ⟨k,hk,hentry⟩
  · apply Grammar284ReservedOrdinary.ordinary_step state graph origin separator t window' hroot'
    intro path' name' hh
    have he : (path',name')=(path,name) := Option.some.inj (hh.symm.trans hleaf)
    cases Prod.mk.inj he with
    | intro hp hn => subst path'; subst name'; exact ⟨n,inc,hop⟩
  · apply Grammar284HalfReserved.half_step_all state graph origin separator t window'
    intro path' name' hh
    have he : (path',name')=(path,name) := Option.some.inj (hh.symm.trans hleaf)
    cases Prod.mk.inj he with
    | intro hp hn => subst path'; subst name'; exact ⟨k,hk,hentry⟩

#print axioms step
end Shared.Beeping.NPcoNP.Grammar284ReservedNonspecial
