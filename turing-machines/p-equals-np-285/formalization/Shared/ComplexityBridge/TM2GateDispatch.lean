import Shared.ComplexityBridge.TM2GateEncoding
import Shared.ComplexityBridge.TM2ListMask
import Shared.ComplexityBridge.TM2UnaryValidation
import Shared.ComplexityBridge.TM2Complement

/-! Runtime dispatch over the explicit gate tuple. Every branch is computed
and masked by its finite Boolean tag test, so all input paths terminate with
polynomial cost. -/
namespace Shared.ComplexityBridge.TM2GateDispatch
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2GateEncoding


theorem all_isPolyTime : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.all id) := by
  simpa only [Shared.Codes.UnaryRequestValidation.unaryCheck_correct] using TM2UnaryValidation.unaryCheck_isPolyTime

theorem not_isPolyTime : ComplexityTheory.IsPolyTime (fun b : Bool => !b) := by
  let one : Bool → List Bool := fun b => [b]
  have hi : ComplexityTheory.IsPolyTime (id : Bool → Bool) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ho : ComplexityTheory.IsPolyTime one := TM2GateCNFPieces.singleton_isPolyTime id hi
  have hn : ComplexityTheory.IsPolyTime (fun xs : List Bool => !(xs.all id)) := TM2Complement.p_complement (fun xs => xs.all id) all_isPolyTime
  have h := TM2Compose.isPolyTime_comp one (fun xs => !(xs.all id)) ho hn
  change ComplexityTheory.IsPolyTime (fun b : Bool => !b)
  simpa [one] using h

theorem and_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Bool × Bool => p.1 && p.2) := by
  let f : Bool × Bool → Bool := fun p => p.1
  let g : Bool × Bool → Bool := fun p => p.2
  let both : Bool × Bool → List Bool := fun p => [f p,g p]
  have hf : ComplexityTheory.IsPolyTime f := TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime g := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime both := TM2GateCNFPieces.pairList_isPolyTime f g hf hg
  have h := TM2Compose.isPolyTime_comp both (fun xs : List Bool => xs.all id) hb all_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Bool × Bool => p.1 && p.2)
  simpa [both,f,g] using h

def matchBit (expected : Bool) (b : Bool) : Bool := if expected then b else !b

theorem matchBit_isPolyTime (expected : Bool) : ComplexityTheory.IsPolyTime (matchBit expected) := by
  cases expected with
  | false => exact not_isPolyTime
  | true => exact ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩

def tagMatch (tag : Bool × Bool) (expected : Bool × Bool) : Bool :=
  matchBit expected.1 tag.1 && matchBit expected.2 tag.2

theorem tagMatch_isPolyTime (expected : Bool × Bool) : ComplexityTheory.IsPolyTime
    (fun tag : Bool × Bool => tagMatch tag expected) := by
  let a : Bool × Bool → Bool := fun p => matchBit expected.1 p.1
  let b : Bool × Bool → Bool := fun p => matchBit expected.2 p.2
  have ha := TM2Compose.isPolyTime_comp (fun p : Bool × Bool => p.1) (matchBit expected.1)
    TM2PairFirst.first_isPolyTime (matchBit_isPolyTime expected.1)
  have hb := TM2Compose.isPolyTime_comp (fun p : Bool × Bool => p.2) (matchBit expected.2)
    TM2GuardAllStep.second_isPolyTime (matchBit_isPolyTime expected.2)
  have hp := TM2GuardAllStep.pair_isPolyTime a b ha hb
  have h := TM2Compose.isPolyTime_comp (fun p => (a p,b p)) (fun p : Bool × Bool => p.1 && p.2) hp and_isPolyTime
  exact h

abbrev Input := Nat × Code

def tag (p : Input) : Bool × Bool := p.2.1
def value (p : Input) : Bool := p.2.2.1
def indices (p : Input) : Nat × Nat := p.2.2.2
def out (p : Input) : Nat := p.1

theorem out_isPolyTime : ComplexityTheory.IsPolyTime out := TM2PairFirst.first_isPolyTime

theorem code_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Input => p.2) := TM2GuardAllStep.second_isPolyTime

theorem tag_isPolyTime : ComplexityTheory.IsPolyTime tag :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun c : Code => c.1) code_isPolyTime TM2PairFirst.first_isPolyTime

theorem payload_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Input => p.2.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun c : Code => c.2) code_isPolyTime TM2GuardAllStep.second_isPolyTime

theorem value_isPolyTime : ComplexityTheory.IsPolyTime value :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2.2) (fun q : Bool × (Nat × Nat) => q.1) payload_isPolyTime TM2PairFirst.first_isPolyTime

theorem indices_isPolyTime : ComplexityTheory.IsPolyTime indices :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2.2) (fun q : Bool × (Nat × Nat) => q.2) payload_isPolyTime TM2GuardAllStep.second_isPolyTime

theorem flag_isPolyTime (expected : Bool × Bool) : ComplexityTheory.IsPolyTime
    (fun p : Input => tagMatch (tag p) expected) :=
  TM2Compose.isPolyTime_comp tag (fun t => tagMatch t expected) tag_isPolyTime (tagMatch_isPolyTime expected)

def constantPart (p : Input) : Formula := gateCNF (out p) (.constant (value p))
def negPart (p : Input) : Formula := gateCNF (out p) (.neg (indices p).1)
def conjPart (p : Input) : Formula := gateCNF (out p) (.conj (indices p).1 (indices p).2)
def disjPart (p : Input) : Formula := gateCNF (out p) (.disj (indices p).1 (indices p).2)

theorem constantPart_isPolyTime : ComplexityTheory.IsPolyTime constantPart := by
  have ha := TM2GuardAllStep.pair_isPolyTime out value out_isPolyTime value_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => (out p,value p))
    (fun q : Nat × Bool => gateCNF q.1 (.constant q.2)) ha TM2GateCNFPieces.constant_isPolyTime

theorem negPart_isPolyTime : ComplexityTheory.IsPolyTime negPart := by
  let x : Input → Nat := fun p => (indices p).1
  have hx : ComplexityTheory.IsPolyTime x := TM2Compose.isPolyTime_comp indices (fun p : Nat × Nat => p.1) indices_isPolyTime TM2PairFirst.first_isPolyTime
  have ha := TM2GuardAllStep.pair_isPolyTime out x out_isPolyTime hx
  exact TM2Compose.isPolyTime_comp (fun p => (out p,x p))
    (fun q : Nat × Nat => gateCNF q.1 (.neg q.2)) ha TM2GateCNFPieces.neg_isPolyTime

theorem binaryPart_isPolyTime (conjunct : Bool) : ComplexityTheory.IsPolyTime
    (if conjunct then conjPart else disjPart) := by
  have ha := TM2GuardAllStep.pair_isPolyTime out indices out_isPolyTime indices_isPolyTime
  cases conjunct with
  | false =>
    exact TM2Compose.isPolyTime_comp (fun p : Input => (out p,indices p))
      (fun q : Nat × (Nat × Nat) => gateCNF q.1 (.disj q.2.1 q.2.2)) ha TM2GateCNFPieces.disj_isPolyTime
  | true =>
    exact TM2Compose.isPolyTime_comp (fun p : Input => (out p,indices p))
      (fun q : Nat × (Nat × Nat) => gateCNF q.1 (.conj q.2.1 q.2.2)) ha TM2GateCNFPieces.conj_isPolyTime

def masked (expected : Bool × Bool) (F : Input → Formula) (p : Input) : Formula :=
  TM2ListMask.mask (tagMatch (tag p) expected,F p)

theorem masked_isPolyTime (expected : Bool × Bool) (F : Input → Formula) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (masked expected F) := by
  have h := TM2GuardAllStep.pair_isPolyTime (fun p => tagMatch (tag p) expected) F (flag_isPolyTime expected) hF
  exact TM2Compose.isPolyTime_comp (fun p => (tagMatch (tag p) expected,F p))
    (TM2ListMask.mask (α := Clause)) h TM2ListMask.mask_isPolyTime

def dispatch (p : Input) : Formula :=
  masked (false,false) constantPart p ++ masked (false,true) negPart p ++
  masked (true,false) conjPart p ++ masked (true,true) disjPart p

theorem append_isPolyTime {α : Type} [BitstringEncoding α] (F G : α → Formula)
    (hF : ComplexityTheory.IsPolyTime F) (hG : ComplexityTheory.IsPolyTime G) :
    ComplexityTheory.IsPolyTime (fun x => F x ++ G x) := by
  have h := TM2GuardAllStep.pair_isPolyTime F G hF hG
  exact TM2Compose.isPolyTime_comp (fun x => (F x,G x)) (TM2ListAppend.append (α := Clause)) h TM2ListAppend.append_isPolyTime

theorem dispatch_isPolyTime : ComplexityTheory.IsPolyTime dispatch := by
  have h0 := masked_isPolyTime (false,false) constantPart constantPart_isPolyTime
  have h1 := masked_isPolyTime (false,true) negPart negPart_isPolyTime
  have h2 := masked_isPolyTime (true,false) conjPart (binaryPart_isPolyTime true)
  have h3 := masked_isPolyTime (true,true) disjPart (binaryPart_isPolyTime false)
  have h := append_isPolyTime _ _ h0 (append_isPolyTime _ _ h1 (append_isPolyTime _ _ h2 h3))
  have he : (fun p : Input => masked (false,false) constantPart p ++
      (masked (false,true) negPart p ++ (masked (true,false) conjPart p ++ masked (true,true) disjPart p))) = dispatch := by
    funext p
    simp [dispatch,List.append_assoc]
  rw [he] at h
  exact h

theorem dispatch_correct (output : Nat) (g : Gate) : dispatch (output,encode g) = gateCNF output g := by
  cases g <;> simp [dispatch,masked,tagMatch,matchBit,tag,value,indices,TM2ListMask.mask,
    constantPart,negPart,conjPart,disjPart,out,encode,gateCNF]

/-- The gate input and the tuple code have definitionally identical serialized
bits, including the outer output-index pair. -/
def repack (p : Nat × Gate) : Input := (p.1,encode p.2)

theorem repack_encoding (p : Nat × Gate) :
    BitstringEncoding.bitEncode (repack p) = BitstringEncoding.bitEncode p := rfl

noncomputable def repackTimeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Nat × Gate → List Bool)
    (BitstringEncoding.bitEncode : Input → List Bool) repack where
  toTM2ComputableAux := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : Nat × Gate → List Bool)).toTM2ComputableAux
  time := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : Nat × Gate → List Bool)).time
  outputsFun p := by
    have h := (Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : Nat × Gate → List Bool)).outputsFun p
    simpa only [repack_encoding,id_eq] using h

theorem gateCNF_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Gate => gateCNF p.1 p.2) := by
  have h := TM2Compose.isPolyTime_comp repack dispatch ⟨repackTimeMachine⟩ dispatch_isPolyTime
  have he : (fun p => dispatch (repack p)) = (fun p : Nat × Gate => gateCNF p.1 p.2) := by
    funext p
    exact dispatch_correct p.1 p.2
  rw [he] at h
  exact h

namespace Fixtures
example : dispatch (4,encode (.constant false)) = [[(4,false)]] := rfl
example : dispatch (4,encode (.neg 2)) = [[(4,false),(2,false)],[(4,true),(2,true)]] := rfl
example : dispatch (4,encode (.conj 1 2)) = gateCNF 4 (.conj 1 2) := rfl
example : dispatch (4,encode (.disj 1 2)) = gateCNF 4 (.disj 1 2) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2GateDispatch
