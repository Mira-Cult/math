import Shared.Beeping.NPcoNP.Grammar284GraphOperation
import Shared.Beeping.NPcoNP.NativeAllBankIncrementNext
import Shared.Beeping.NPcoNP.NativeAllBankDecrementNext

/-! Bank-level agreement between graph actions and the uniform literal
increment/decrement segments. Physical control-successor agreement is separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeAllBankIncrementNext
open Shared.Beeping.NPcoNP.NativeAllBankDecrementNext
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Writing the graph register selected by an array position changes exactly
the corresponding unary-bank list cell. -/
theorem write_selected_array (bank : Bank 12) (n : Fin 12) (values rest : List Nat)
    (value replacement : Nat) (hlen : values.length=n.val)
    (layout : arrayBank bank=values++value::rest) :
    arrayBank (write bank (arrayToSuffix n) replacement)=values++replacement::rest := by
  rw [arrayBank_write,array_suffix_inverse,layout,←hlen]
  simp

/-- For any named increment graph row and compatible supplied tape, the
literal segment reaches state 93 silently with a bank encoding of the graph
step's updated bank. The returned control word is not yet identified. -/
theorem increment_bank_matches (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (h z : Int) (t : Int → Bool) (k : Nat) (marker : t h=true) (hk : 0<k)
    (h0 : t (h+1)=false) (h1 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      (encode (values++value::(graphTail++more)) ++ [false]))
    (hz : z<h) (left : ∀ q, q≤z → t q=false) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧ result.2=[] ∧
      result.1.state=target.code[state].yes ∧ mark≤h-1 ∧ out mark=true ∧
      Holds out (h+4+(k : Int)) (encode (arrayBank result.1.bank ++ more)) ∧
      out (finalHead-1)=true ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 93 finalHead out) steps := by
  dsimp only
  have gstep := graph_increment_step state path name leaf n operation graph values graphTail value hlen layout
  have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++(value+1)::graphTail := by
    rw [gstep]
    exact write_selected_array graph n values graphTail value (value+1) hlen layout
  obtain ⟨steps,out,mark,finalHead,hsteps,hmarkle,hmark,_hleft,hhead,hbank,_hfar,hseg⟩ :=
    increment_to_next93 n h z t k values value (graphTail++more) marker hlen hk h0 h1 control delimiter bank hz left
  refine ⟨steps,out,mark,finalHead,hsteps,?_,?_,hmarkle,hmark,?_,hhead,hseg⟩
  · simp only [gstep]
  · simp only [gstep]
  · rw [gbank]
    have hp : h+3+(k : Int)+1=h+4+(k : Int) := by omega
    simpa only [hp,List.append_assoc,List.cons_append] using hbank

/-- On a zero target, the physical zero branch returns to state 93 with the
same bank as the graph's no branch, under the stated window hypotheses. -/
theorem decrement_zero_bank_matches (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (h z separator : Int) (t : Int → Bool) (hlong : h+4≤separator)
    (marker : t h=true) (prev : t (h-1)=false) (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad))
    (hz : z<h-2) (left : ∀ q, q≤z → t q=false) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧ result.2=[] ∧
      result.1.state=target.code[state].no ∧ mark≤h-2 ∧ out mark=true ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      out (finalHead-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 finalHead out) steps := by
  dsimp only
  have gstep := graph_decrement_zero_step state path name leaf n operation graph values graphTail hlen layout
  have hphysical : Holds t (separator+1)
      (encode values ++ (block 0 ++ (encode (graphTail++more) ++ pad))) := by
    rw [layout] at bank
    simpa [encode_append,encode,List.append_assoc] using bank
  obtain ⟨steps,out,mark,finalHead,hsteps,hmarkle,hmark,_hleft,hhead,hframe,hseg⟩ :=
    zero_to_next93 n h z separator t values (encode (graphTail++more) ++ pad)
      hlen hlong marker prev z1 z2 ones sep hphysical hz left
  have hbank : Holds out (separator+1) (encode (arrayBank graph++more) ++ pad) := by
    apply NativeHalfScannerFrames.holds_transport t out (separator+1) _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  refine ⟨steps,out,mark,finalHead,hsteps,?_,?_,hmarkle,hmark,?_,hhead,hseg⟩
  · simp only [gstep]
  · simp only [gstep]
  · simpa only [gstep] using hbank

/-- On a positive target, the physical decrement returns to state 93 with the
same updated graph bank plus an explicitly encoded zero reserve. -/
theorem decrement_positive_bank_matches (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (h z separator : Int) (t : Int → Bool) (hlong : h+4≤separator)
    (marker : t h=true) (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (ones : ∀ q, h+3≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])))
    (hz : z<h) (left : ∀ q, q≤z → t q=false) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧ result.2=[] ∧
      result.1.state=target.code[state].yes ∧ mark≤h-1 ∧ out mark=true ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      out (finalHead-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 finalHead out) steps := by
  dsimp only
  have gstep := graph_decrement_positive_step state path name leaf n operation graph values graphTail value hlen layout
  have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++value::graphTail := by
    rw [gstep]
    exact write_selected_array graph n values graphTail (value+1) value hlen layout
  obtain ⟨steps,out,mark,finalHead,hsteps,hmarkle,hmark,_hleft,hhead,hbank,_hfar,hseg⟩ :=
    positive_to_next93 n h z separator t values value (graphTail++more) hlen hlong marker z1 z2 ones sep bank hz left
  refine ⟨steps,out,mark,finalHead,hsteps,?_,?_,hmarkle,hmark,?_,hhead,hseg⟩
  · simp only [gstep]
  · simp only [gstep]
  · rw [gbank]
    simpa [encode_append,encode,block,List.append_assoc] using hbank

#print axioms write_selected_array
#print axioms increment_bank_matches
#print axioms decrement_zero_bank_matches
#print axioms decrement_positive_bank_matches
end Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
