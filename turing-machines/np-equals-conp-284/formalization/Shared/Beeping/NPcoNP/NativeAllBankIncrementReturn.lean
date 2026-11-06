import Shared.Beeping.NPcoNP.NativeAllBankIncrement
import Shared.Beeping.NPcoNP.NativeBankReturn23Generic

/-! Uniform literal increment through its unchanged state-23 bank return.
The following control carry and reachability remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankIncrement
open Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- At any physical bank position, a compatible increment window reaches
state 1 silently with the selected value increased and the stated tape frame.
It does not identify or execute the following control carry. -/
theorem increment_to1 (n : Fin 12) (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (rest : List Nat)
    (marker : t h=true) (hlen : values.length=n.val) (hk : 0<k)
    (h0 : t (h+1)=false) (h1 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int)) (encode (values++value::rest) ++ [false])) :
    let separator := h+3+(k : Int)
    let pos := separator+1+((encode values).length : Int)
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out (separator+1) (encode (values++(value+1)::rest)) ∧
      out h=false ∧ out (h+1)=false ∧ out (h+2)=true ∧
      (∀ q, h+3≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q≠h+2 → (q<pos+1 ∨ pos+1+((value+(encode rest).length : Nat) : Int)<q) →
        out q=clearAt h t q) ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 1 (h-1) out) steps := by
  dsimp only
  let separator := h+3+(k : Int)
  let pos := separator+1+((encode values).length : Int)
  let updated := values++(value+1)::rest
  obtain ⟨a,e,ha,hstate,hhead,hmark,hbank,hframe,hseg⟩ :=
    increment_to23 n h t k values value rest marker hlen hk h0 h1 control delimiter bank
  have hpos : h+4+(k : Int)+((encode values).length : Int)=pos := by dsimp [pos,separator]; omega
  have hpref : ∀ q, q<pos+1 → q≠h+2 → e.tape q=clearAt h t q := by
    intro q hq hne
    apply hframe q hne
    left
    simpa only [hpos] using hq
  have he0 : e.tape h=false := by
    rw [hpref h (by dsimp [pos,separator]; omega) (by omega)]
    simp [clearAt]
  have he1 : e.tape (h+1)=false := by
    rw [hpref (h+1) (by dsimp [pos,separator]; omega) (by omega)]
    simpa [clearAt,show h+1≠h by omega] using h0
  have hecontrol : ∀ q, h+3≤q → q<separator → e.tape q=true := by
    intro q hq hq'
    rw [hpref q (by dsimp [pos]; omega) (by omega)]
    rw [show clearAt h t q=t q by simp [clearAt,show q≠h by omega]]
    let i := (q-(h+3)).toNat
    have hi : (i : Int)=q-(h+3) := Int.toNat_of_nonneg (by omega)
    have hil : i<k := by dsimp [separator] at hq'; omega
    have he : h+3+(i : Int)=q := by omega
    simpa only [he] using control i hil
  have hesep : e.tape separator=false := by
    rw [hpref separator (by dsimp [pos]; omega) (by dsimp [separator]; omega)]
    simpa [clearAt,show separator≠h by dsimp [separator]; omega,separator] using delimiter
  have hebank : Holds e.tape (separator+1) (encode updated ++ []) := by
    have he : separator+1=h+4+(k : Int) := by dsimp [separator]; omega
    simpa only [he,List.append_nil,updated] using hbank
  have hr1 : h-1+1=h := by omega
  have hr2 : h-1+2=h+1 := by omega
  have hr3 : h-1+3=h+2 := by omega
  have hr4 : h-1+4=h+3 := by omega
  have hreturn := return23_generic_weak (h-1) separator e.tape updated []
    (by dsimp [separator]; omega) (by simpa only [hr1] using he0) (by simpa only [hr2] using he1)
    (by simpa only [hr3] using hmark) (by simpa only [hr4] using hecontrol) hesep hebank
  have hend : e.head=separator+((encode updated).length : Int)-1 := by
    rw [hhead]
    dsimp [pos,updated]
    simp only [encode_append,List.length_append,encode,block_length,Nat.cast_add]
    push_cast
    omega
  have he : e=cfg 23 e.head e.tape := by
    have eq : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hstate] using eq
  rw [←hend,←he] at hreturn
  refine ⟨a+((unaryBankPrefix (separator-(h-1+5)).toNat updated).length+3),e.tape,by omega,?_,he0,he1,hmark,hecontrol,hesep,?_,?_⟩
  · have hh : h+3+(k : Int)+1=h+4+(k : Int) := by omega
    simpa only [hh] using hbank
  · simpa only [hpos] using hframe
  · exact segAdd machine _ _ _ a _ hseg hreturn

#print axioms increment_to1
end Shared.Beeping.NPcoNP.NativeAllBankIncrementReturn
