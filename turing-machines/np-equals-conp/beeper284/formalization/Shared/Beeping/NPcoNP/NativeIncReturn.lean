import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeReturnSelectorProgress

/-! Connect the exact increment tape stage to literal blank-start return
progress. The encoded layout is supplied; reachability of that layout and
its identification with a graph configuration remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeIncReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfReachableMarker
open Shared.Beeping.NPcoNP.NativeReturnSelectorProgress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Every nonempty encoded bank has a one immediately before its final
zero delimiter. -/
theorem encoded_last_one (v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (bank : Holds t h (encode (v::rest))) :
    t (h+((encode (v::rest)).length : Int)-2)=true := by
  induction rest generalizing v h with
  | nil =>
    have hc := (first_block_cells t h v [] bank).1 v (by omega)
    have he : h+((encode [v]).length : Int)-2=h+(v : Int) := by
      simp [encode,block_length]
      omega
    rwa [he]
  | cons w ws ih =>
    have htail := first_block_tail t h v (w::ws) bank
    have hlast := ih w (h+((v+2 : Nat):Int)) htail
    have he : h+((encode (v::w::ws)).length : Int)-2 =
        (h+((v+2 : Nat):Int))+((encode (w::ws)).length : Int)-2 := by
      simp only [encode,List.length_append,block_length,Nat.cast_add]
      push_cast
      omega
    rw [he]
    exact hlast

/-- A supplied encoded state-14 boundary that occurs on the blank-start run
passes through the proved increment tape stage, then reaches state 93 in
finite silent time. The intermediate bank update and frame are retained. -/
theorem reachable_increment_then_93 (time : Nat) (v : Nat) (rest : List Nat)
    (h : Int) (t : Int → Bool)
    (hc : machine.system.run time=cfg 14 h t)
    (bank : Holds t h (encode (v::rest) ++ [false])) :
    ∃ (mid out : Config 284) (extra : Nat), mid.state=23 ∧
      mid.head=h+(((v+1)+(encode rest).length : Nat):Int) ∧
      Holds mid.tape h (encode ((v+1)::rest)) ∧
      (∀ p, p<h ∨ h+(((v+1)+(encode rest).length : Nat):Int)<p → mid.tape p=t p) ∧
      0<extra ∧ out.state=93 ∧
      silentSegment machine (machine.system.run time) mid (v+3+(encode rest).length) ∧
      silentSegment machine mid out extra := by
  obtain ⟨mid,hmid,hhead,hout,hframe,hseg⟩ := encoded_increment v rest h t bank
  have hmark : mid.tape mid.head=true := by
    have hh := encoded_last_one (v+1) rest h mid.tape hout
    have he : h+((encode ((v+1)::rest)).length : Int)-2 = mid.head := by
      rw [hhead]
      simp only [encode,List.length_append,block_length,Nat.cast_add]
      push_cast
      omega
    rw [he] at hh
    exact hh
  let duration := v+3+(encode rest).length
  have hseg' : silentSegment machine (machine.system.run time) mid duration := by
    rw [hc]
    exact hseg
  have hrun : machine.system.run (time+duration)=mid := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg'.1
  have h23 : (machine.system.run (time+duration)).state=23 := by rw [hrun]; exact hmid
  have hmarker : (machine.system.run (time+duration)).tape
      (machine.system.run (time+duration)).head=true := by rw [hrun]; exact hmark
  obtain ⟨n,c,hn,h28,hreturn⟩ := reachable_marker_to_28 (time+duration) h23
    (machine.system.run (time+duration)).head (by rfl) hmarker
  have hrun28 : machine.system.run (time+duration+n)=c := by
    rw [EventSystem.run_add]
    change machine.system.advance (machine.system.run (time+duration)) n=c
    rw [← ScalarWordRefinement.advance_ofBeep]
    exact hreturn.1
  have h28' : (machine.system.run (time+duration+n)).state=28 := by rw [hrun28]; exact h28
  obtain ⟨m,out,hm,h93,hmore⟩ := reachable_28_to_93 (time+duration+n) h28'
  refine ⟨mid,out,n+m,hmid,hhead,hout,hframe,by omega,h93,hseg',?_⟩
  have hreturn' : silentSegment machine mid c n := by rw [← hrun]; exact hreturn
  have hmore' : silentSegment machine c out m := by rw [← hrun28]; exact hmore
  exact segAdd machine _ _ _ n m hreturn' hmore'

#print axioms encoded_last_one
#print axioms reachable_increment_then_93
end Shared.Beeping.NPcoNP.NativeIncReturn
