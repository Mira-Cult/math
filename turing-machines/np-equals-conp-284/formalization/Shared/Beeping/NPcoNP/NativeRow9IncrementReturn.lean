import Shared.Beeping.NPcoNP.NativeRow9Increment
import Shared.Beeping.NPcoNP.NativeBankReturn23Generic

/-! Complete the state-23 return after the second-block increment. This is a
finite supplied-layout result, not a recurrent graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.NativeRow9IncrementReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeRow9Increment
open Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The restored bank increment returns silently from state 23 to state 1,
preserving the complete incremented word. -/
theorem increment_then_return_full (h separator : Int) (t : Int → Bool)
    (a b : Nat) (rest : List Nat)
    (hlong : h+12≤separator) (h8 : t (h+8)=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (a::b::rest) ++ [false])) :
    let pos := separator+1+((a+2 : Nat):Int)
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      Holds e.tape (separator+1) (encode (a::(b+1)::rest)) ∧
      e.tape (h+10)=true ∧
      (∀ q, q≠h+10 →
        (q<pos+1 ∨ pos+1+((b+(encode rest).length : Nat):Int)<q) → e.tape q=t q) ∧
      silentSegment machine (cfg 262 (pos-2) (clearAt pos t)) (cfg 1 (h+7) e.tape) n := by
  dsimp only
  let pos := separator+1+((a+2 : Nat):Int)
  let ys := unaryBankPrefix (separator-(h+12)).toNat [a]
  let cost := (2*ys.length+7)+(b+2+(encode rest).length)
  obtain ⟨e,he,hhead,hmark,hbank,hframe,hinc⟩ :=
    restore_then_increment_full h separator t a b rest hlong h8 h9 h10 control hsep bank
  have hinc' : silentSegment machine (cfg 262 (pos-2) (clearAt pos t)) e cost := by
    simpa only [pos,ys,cost] using hinc
  have hpre : ∀ q, q<pos+1 → q≠h+10 → e.tape q=t q := by
    intro q hq hne
    exact hframe q hne (Or.inl hq)
  have hp1 : e.tape ((h+7)+1)=false := by
    have hh : h+7+1=h+8 := by omega
    rw [hh,hpre _ (by dsimp [pos]; omega) (by omega)]
    exact h8
  have hp2 : e.tape ((h+7)+2)=false := by
    have hh : h+7+2=h+9 := by omega
    rw [hh,hpre _ (by dsimp [pos]; omega) (by omega)]
    exact h9
  have hm : e.tape ((h+7)+3)=true := by
    simpa only [show h+7+3=h+10 by omega] using hmark
  have hc : ∀ q, h+7+4≤q → q<separator → e.tape q=true := by
    intro q hq hq'
    rw [hpre q (by dsimp [pos]; omega) (by omega)]
    exact control q (by omega) hq'
  have hz : e.tape separator=false := by
    rw [hpre separator (by dsimp [pos]; omega) (by omega)]
    exact hsep
  have hb : Holds e.tape (separator+1) (encode (a::(b+1)::rest) ++ []) := by simpa using hbank
  have hreturn := return23_generic_weak (h+7) separator e.tape (a::(b+1)::rest) []
    (by omega) hp1 hp2 hm hc hz hb
  have hpos : e.head=separator+((encode (a::(b+1)::rest)).length : Int)-1 := by
    rw [hhead]
    simp [encode,block_length,pos]
    push_cast
    omega
  have heq : e=cfg 23 e.head e.tape := by
    have hh : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [he] using hh
  let r := (separator-((h+7)+5)).toNat
  let ys' := unaryBankPrefix r (a::(b+1)::rest)
  have hreturn' : silentSegment machine e (cfg 1 (h+7) e.tape) (ys'.length+3) := by
    have hh : cfg 23 (separator+((encode (a::(b+1)::rest)).length : Int)-1) e.tape=e := by
      rw [←hpos,←heq]
    simpa only [hh,r,ys',show h+7+5=h+12 by omega] using hreturn
  refine ⟨cost+(ys'.length+3),e,by dsimp [cost]; omega,he,hbank,hmark,hframe,?_⟩
  exact segAdd machine _ _ _ cost (ys'.length+3) hinc' hreturn'

/-- Earlier interface without the control marker and complete frame. -/
theorem increment_then_return (h separator : Int) (t : Int → Bool)
    (a b : Nat) (rest : List Nat)
    (hlong : h+12≤separator) (h8 : t (h+8)=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (a::b::rest) ++ [false])) :
    let pos := separator+1+((a+2 : Nat):Int)
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      Holds e.tape (separator+1) (encode (a::(b+1)::rest)) ∧
      silentSegment machine (cfg 262 (pos-2) (clearAt pos t)) (cfg 1 (h+7) e.tape) n := by
  obtain ⟨n,e,hn,he,hbank,_,_,hseg⟩ :=
    increment_then_return_full h separator t a b rest hlong h8 h9 h10 control hsep bank
  exact ⟨n,e,hn,he,hbank,hseg⟩

#print axioms increment_then_return_full
#print axioms increment_then_return
end Shared.Beeping.NPcoNP.NativeRow9IncrementReturn
