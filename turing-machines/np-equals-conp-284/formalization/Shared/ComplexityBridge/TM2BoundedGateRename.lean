import Shared.ComplexityBridge.TM2BoundedRemap
import Shared.ComplexityBridge.TM2GateConstruct

set_option backward.isDefEq.respectTransparency false

/-! Rename one dynamically supplied gate with the bounded wire worker. -/
namespace Shared.ComplexityBridge.TM2BoundedGateRename
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2GateEncoding

abbrev Context := List Bool × ((Nat × Nat) × List Nat)
abbrev Input := Context × Gate

def rename (p : Input) : Gate :=
  CircuitRelocate.renameGate
    (fun i => TM2BoundedRemap.remap (p.1.1,(p.1.2.1,(p.1.2.2,i)))) p.2

def code (p : Input) : Code :=
  let c := encode p.2
  let ctx := p.1
  let index := fun i => TM2BoundedRemap.remap (ctx.1,(ctx.2.1,(ctx.2.2,i)))
  let first := if c.1.1 || c.1.2 then index c.2.2.1 else 0
  let second := if c.1.1 then index c.2.2.2 else 0
  (c.1,(c.2.1,(first,second)))

theorem code_correct (p : Input) : encode (rename p) = code p := by
  rcases p with ⟨ctx,g⟩
  cases g <;> rfl

/-- Identity on serialized gate bits, interpreted as the corresponding
canonical gate tuple. -/
theorem encode_isPolyTime : ComplexityTheory.IsPolyTime encode := by
  let m := Turing.idComputableInPolyTime (BitstringEncoding.bitEncode : Gate → List Bool)
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro g
  have h := m.outputsFun g
  change Turing.TM2OutputsInTime m.tm
    ((BitstringEncoding.bitEncode g).map m.inputAlphabet.symm)
    (some ((BitstringEncoding.bitEncode (encode g)).map m.outputAlphabet.symm))
    (m.time.eval (BitstringEncoding.bitEncode g).length)
  rw [←encode_bits]
  exact h

theorem code_isPolyTime : ComplexityTheory.IsPolyTime code := by
  let ctx : Input → Context := fun p => p.1
  let gate : Input → Gate := fun p => p.2
  let c : Input → Code := fun p => encode (gate p)
  let tag : Input → Bool × Bool := fun p => (c p).1
  let payload : Input → Bool × (Nat × Nat) := fun p => (c p).2
  let value : Input → Bool := fun p => (payload p).1
  let coords : Input → Nat × Nat := fun p => (payload p).2
  let x : Input → Nat := fun p => (coords p).1
  let y : Input → Nat := fun p => (coords p).2
  let a : Input → Bool := fun p => (tag p).1
  let b : Input → Bool := fun p => (tag p).2
  let truth : Input → Bool := fun _ => true
  let firstFlag : Input → Bool := fun p => if a p then truth p else b p
  let budget : Input → List Bool := fun p => (ctx p).1
  let tail : Input → (Nat × Nat) × List Nat := fun p => (ctx p).2
  let dims : Input → Nat × Nat := fun p => (tail p).1
  let refs : Input → List Nat := fun p => (tail p).2
  let rx : Input → TM2BoundedRemap.Input := fun p => (budget p,(dims p,(refs p,x p)))
  let ry : Input → TM2BoundedRemap.Input := fun p => (budget p,(dims p,(refs p,y p)))
  let mx : Input → Nat := fun p => TM2BoundedRemap.remap (rx p)
  let my : Input → Nat := fun p => TM2BoundedRemap.remap (ry p)
  let zero : Input → Nat := fun _ => 0
  let first : Input → Nat := fun p => if firstFlag p then mx p else zero p
  let second : Input → Nat := fun p => if a p then my p else zero p
  let outs : Input → Nat × Nat := fun p => (first p,second p)
  let body : Input → Bool × (Nat × Nat) := fun p => (value p,outs p)
  have hctx : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gate := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime c := TM2Compose.isPolyTime_comp gate encode hg encode_isPolyTime
  have htag : ComplexityTheory.IsPolyTime tag := TM2Compose.isPolyTime_comp c (fun c : Code => c.1) hc TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime payload := TM2Compose.isPolyTime_comp c (fun c : Code => c.2) hc TM2GuardAllStep.second_isPolyTime
  have hv : ComplexityTheory.IsPolyTime value := TM2Compose.isPolyTime_comp payload (fun p : Bool × (Nat × Nat) => p.1) hp TM2PairFirst.first_isPolyTime
  have hcoords : ComplexityTheory.IsPolyTime coords := TM2Compose.isPolyTime_comp payload (fun p : Bool × (Nat × Nat) => p.2) hp TM2GuardAllStep.second_isPolyTime
  have hx : ComplexityTheory.IsPolyTime x := TM2Compose.isPolyTime_comp coords (fun p : Nat × Nat => p.1) hcoords TM2PairFirst.first_isPolyTime
  have hy : ComplexityTheory.IsPolyTime y := TM2Compose.isPolyTime_comp coords (fun p : Nat × Nat => p.2) hcoords TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime a := TM2Compose.isPolyTime_comp tag (fun p : Bool × Bool => p.1) htag TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime b := TM2Compose.isPolyTime_comp tag (fun p : Bool × Bool => p.2) htag TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime truth := TM2Constant.isPolyTime true
  have hff : ComplexityTheory.IsPolyTime firstFlag := TM2If.if_isPolyTime a truth b ha ht hb
  have hbudget : ComplexityTheory.IsPolyTime budget := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.1) hctx TM2PairFirst.first_isPolyTime
  have htail : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.2) hctx TM2GuardAllStep.second_isPolyTime
  have hd : ComplexityTheory.IsPolyTime dims := TM2Compose.isPolyTime_comp tail (fun p : (Nat × Nat) × List Nat => p.1) htail TM2PairFirst.first_isPolyTime
  have hrefs : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp tail (fun p : (Nat × Nat) × List Nat => p.2) htail TM2GuardAllStep.second_isPolyTime
  have hrx : ComplexityTheory.IsPolyTime rx := TM2GuardAllStep.pair_isPolyTime budget (fun p => (dims p,(refs p,x p))) hbudget
    (TM2GuardAllStep.pair_isPolyTime dims (fun p => (refs p,x p)) hd (TM2GuardAllStep.pair_isPolyTime refs x hrefs hx))
  have hry : ComplexityTheory.IsPolyTime ry := TM2GuardAllStep.pair_isPolyTime budget (fun p => (dims p,(refs p,y p))) hbudget
    (TM2GuardAllStep.pair_isPolyTime dims (fun p => (refs p,y p)) hd (TM2GuardAllStep.pair_isPolyTime refs y hrefs hy))
  have hmx : ComplexityTheory.IsPolyTime mx := TM2Compose.isPolyTime_comp rx TM2BoundedRemap.remap hrx TM2BoundedRemap.remap_isPolyTime
  have hmy : ComplexityTheory.IsPolyTime my := TM2Compose.isPolyTime_comp ry TM2BoundedRemap.remap hry TM2BoundedRemap.remap_isPolyTime
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hfirst : ComplexityTheory.IsPolyTime first := TM2If.if_isPolyTime firstFlag mx zero hff hmx hz
  have hsecond : ComplexityTheory.IsPolyTime second := TM2If.if_isPolyTime a my zero ha hmy hz
  have ho : ComplexityTheory.IsPolyTime outs := TM2GuardAllStep.pair_isPolyTime first second hfirst hsecond
  have hbody : ComplexityTheory.IsPolyTime body := TM2GuardAllStep.pair_isPolyTime value outs hv ho
  have h := TM2GuardAllStep.pair_isPolyTime tag body htag hbody
  have he : (fun p => (tag p,body p)) = code := by
    funext p
    cases ht' : (encode p.2).1.1 <;> cases hb' : (encode p.2).1.2 <;>
      simp [tag,body,value,outs,first,second,firstFlag,truth,a,b,mx,my,rx,ry,budget,dims,refs,tail,ctx,c,gate,payload,coords,x,y,zero,code,ht',hb']
  rw [he] at h
  exact h

theorem rename_isPolyTime : ComplexityTheory.IsPolyTime rename :=
  TM2GateConstruct.gate_of_code rename code code_isPolyTime code_correct

def refers (g : Gate) (i : Nat) : Prop :=
  match g with
  | .constant _ => False
  | .neg x => i = x
  | .conj x y | .disj x y => i = x ∨ i = y

theorem rename_correct (budget : List Bool) (width base : Nat) (refs : List Nat) (g : Gate)
    (hw : width ≤ budget.length)
    (hg : ∀ i, refers g i → i ≤ budget.length) :
    rename ((budget,((width,base),refs)),g) =
      CircuitRelocate.renameGate (CircuitRelocate.remap width base refs) g := by
  cases g with
  | constant b => rfl
  | neg x => simp [rename,CircuitRelocate.renameGate,TM2BoundedRemap.remap_correct budget width base refs x hw (hg x rfl)]
  | conj x y => simp [rename,CircuitRelocate.renameGate,TM2BoundedRemap.remap_correct budget width base refs x hw (hg x (Or.inl rfl)),
      TM2BoundedRemap.remap_correct budget width base refs y hw (hg y (Or.inr rfl))]
  | disj x y => simp [rename,CircuitRelocate.renameGate,TM2BoundedRemap.remap_correct budget width base refs x hw (hg x (Or.inl rfl)),
      TM2BoundedRemap.remap_correct budget width base refs y hw (hg y (Or.inr rfl))]

/-- Relocate an entire runtime gate list using a shared bounded context. -/
def relocate (p : Context × List Gate) : List Gate :=
  TM2ContextMapGeneric.contextMap rename p

theorem relocate_isPolyTime : ComplexityTheory.IsPolyTime relocate :=
  TM2ContextMapGeneric.contextMap_isPolyTime rename rename_isPolyTime

/-- Exact agreement requires the explicit unary budget to cover the width and
every wire referenced by the supplied gate list. -/
theorem relocate_correct (budget : List Bool) (width base : Nat) (refs : List Nat) (gs : List Gate)
    (hw : width ≤ budget.length)
    (hg : ∀ g ∈ gs, ∀ i, refers g i → i ≤ budget.length) :
    relocate ((budget,((width,base),refs)),gs) = CircuitRelocate.relocate width base refs gs := by
  unfold relocate TM2ContextMapGeneric.contextMap CircuitRelocate.relocate
  apply List.map_congr_left
  intro g hmem
  exact rename_correct budget width base refs g hw (hg g hmem)

/-- A well-formed gate references only wires earlier than its output. -/
theorem validGate_ref (base : Nat) (g : Gate) (hv : validGate base g) (i : Nat)
    (hi : refers g i) : i < base := by
  cases g <;> simp_all [refers,validGate]
  all_goals rcases hi with rfl | rfl <;> simp_all

theorem validGates_refs (base : Nat) (gs : List Gate) (hv : validGates base gs) :
    ∀ g ∈ gs, ∀ i, refers g i →
      i < base+gs.length := by
  induction gs generalizing base with
  | nil => simp
  | cons g gs ih =>
    simp only [validGates] at hv
    intro x hx i hi
    rcases List.mem_cons.mp hx with he | ht
    · subst x
      have h := validGate_ref base g hv.1 i hi
      simp only [List.length_cons]
      omega
    · have h := ih (base+1) hv.2 x ht i hi
      simp only [List.length_cons]
      omega

/-- For a valid circuit, one budget covering its input width and gate count
is enough for exact relocation of the entire list. -/
theorem relocate_correct_valid (budget : List Bool) (width base : Nat) (refs : List Nat) (gs : List Gate)
    (hv : validGates width gs) (hb : width+gs.length ≤ budget.length) :
    relocate ((budget,((width,base),refs)),gs) = CircuitRelocate.relocate width base refs gs := by
  apply relocate_correct budget width base refs gs (by omega)
  intro g hm i hi
  have h := validGates_refs width gs hv g hm i hi
  omega

namespace Fixtures
example : relocate (([true,true,true],((2,9),[7,8])),[.neg 1,.conj 0 3]) =
    [.neg 8,.conj 7 10] := rfl
end Fixtures

end Shared.ComplexityBridge.TM2BoundedGateRename
