import Shared.Beeping.NPcoNP.NativeRow9Restore
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Restore the temporary bank clear and complete the literal increment of
the second unary block. The input is a supplied finite physical layout. -/
namespace Shared.Beeping.NPcoNP.NativeRow9Increment
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeRow9Restore
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The state-262 return and state-14 insertion increment the second bank
value for every natural input, including zero. The bank sentinel is explicit. -/
theorem restore_then_increment_full (h separator : Int) (t : Int → Bool)
    (a b : Nat) (rest : List Nat)
    (hlong : h+12≤separator) (h8 : t (h+8)=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (a::b::rest) ++ [false])) :
    let pos := separator+1+((a+2 : Nat):Int)
    let ys := unaryBankPrefix (separator-(h+12)).toNat [a]
    ∃ e : Config 284, e.state=23 ∧ e.head=pos+1+((b+(encode rest).length : Nat):Int) ∧
      e.tape (h+10)=true ∧ Holds e.tape (separator+1) (encode (a::(b+1)::rest)) ∧
      (∀ q, q≠h+10 →
        (q<pos+1 ∨ pos+1+((b+(encode rest).length : Nat):Int)<q) → e.tape q=t q) ∧
      silentSegment machine (cfg 262 (pos-2) (clearAt pos t)) e
        ((2*ys.length+7)+(b+2+(encode rest).length)) := by
  dsimp only
  let pos := separator+1+((a+2 : Nat):Int)
  let ys := unaryBankPrefix (separator-(h+12)).toNat [a]
  let u := setAt (h+10) t
  have hbank : Holds t (separator+1) (block a ++ (block b ++ (encode rest ++ [false]))) := by
    simpa [encode,List.append_assoc] using bank
  have hrestore := restore_to14 h separator t a b (encode rest ++ [false]) hlong h8 h9 h10 control hsep hbank
  have hrestore' : silentSegment machine (cfg 262 (pos-2) (clearAt pos t))
      (cfg 14 (pos+1) u) (2*ys.length+7) := by simpa only [pos,ys,u] using hrestore
  have hsecond := holds_append_tail t (separator+1) (block a) (block b ++ (encode rest ++ [false])) hbank
  have hpos : separator+1+((block a).length : Int)=pos := by simp [block_length,pos]
  rw [hpos] at hsecond
  have hsecond' : Holds t pos (true :: inputWord b rest) := by
    simpa [inputWord,block,List.replicate_succ,List.append_assoc] using hsecond
  have hinput : Holds u (pos+1) (inputWord b rest) := by
    apply holds_transport t u _ _ hsecond'.2
    intro q hq _
    simp [u,setAt,show q≠h+10 by dsimp [pos] at *; omega]
  obtain ⟨e,he,hhead,hword,hframe,hinc⟩ := shift_bank rest b (pos+1) u hinput
  have hpre : Holds t (separator+1) (block a ++ [true]) := by
    have hh := holds_prefix_word t (separator+1) (block a ++ [true])
      (List.replicate b true ++ [false] ++ (encode rest ++ [false]))
    apply hh
    simpa [block,List.replicate_succ,List.append_assoc] using hbank
  have hpreU : Holds u (separator+1) (block a ++ [true]) := by
    apply holds_transport t u _ _ hpre
    intro q hq _
    simp [u,setAt,show q≠h+10 by omega]
  have hpreE : Holds e.tape (separator+1) (block a ++ [true]) := by
    apply holds_transport u e.tape _ _ hpreU
    intro q hq hq'
    symm
    apply hframe q
    left
    have hl : (block a ++ [true]).length=a+3 := by simp [block_length]
    rw [hl] at hq'
    dsimp [pos]
    push_cast at hq'
    omega
  have hcombined := holds_append_intro e.tape (separator+1) (block a ++ [true])
    (outputWord b rest) hpreE (by
      have heq : separator+1+(((block a ++ [true]).length : Nat):Int)=pos+1 := by
        simp [block_length,pos]
        omega
      simpa only [heq] using hword)
  have hout : Holds e.tape (separator+1) (encode (a::(b+1)::rest)) := by
    simpa [encode,block,outputWord,List.replicate_succ,List.append_assoc] using hcombined
  have hframe' : ∀ q, q≠h+10 →
      (q<pos+1 ∨ pos+1+((b+(encode rest).length : Nat):Int)<q) → e.tape q=t q := by
    intro q hneq hside
    rw [hframe q hside]
    simp [u,setAt,hneq]
  have hmark : e.tape (h+10)=true := by
    rw [hframe (h+10) (Or.inl (by dsimp [pos]; omega))]
    simp [u,setAt]
  refine ⟨e,he,hhead,hmark,hout,hframe',?_⟩
  exact segAdd machine _ _ _ (2*ys.length+7) (b+2+(encode rest).length) hrestore' hinc

/-- Earlier interface, projecting away the return head and control marker. -/
theorem restore_then_increment (h separator : Int) (t : Int → Bool)
    (a b : Nat) (rest : List Nat)
    (hlong : h+12≤separator) (h8 : t (h+8)=false)
    (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (control : ∀ q, h+11≤q → q<separator → t q=true) (hsep : t separator=false)
    (bank : Holds t (separator+1) (encode (a::b::rest) ++ [false])) :
    let pos := separator+1+((a+2 : Nat):Int)
    let ys := unaryBankPrefix (separator-(h+12)).toNat [a]
    ∃ e : Config 284, e.state=23 ∧
      Holds e.tape (separator+1) (encode (a::(b+1)::rest)) ∧
      (∀ q, q≠h+10 →
        (q<pos+1 ∨ pos+1+((b+(encode rest).length : Nat):Int)<q) → e.tape q=t q) ∧
      silentSegment machine (cfg 262 (pos-2) (clearAt pos t)) e
        ((2*ys.length+7)+(b+2+(encode rest).length)) := by
  obtain ⟨e,he,_,_,hbank,hframe,hseg⟩ :=
    restore_then_increment_full h separator t a b rest hlong h8 h9 h10 control hsep bank
  exact ⟨e,he,hbank,hframe,hseg⟩

#print axioms restore_then_increment_full
#print axioms restore_then_increment
end Shared.Beeping.NPcoNP.NativeRow9Increment
