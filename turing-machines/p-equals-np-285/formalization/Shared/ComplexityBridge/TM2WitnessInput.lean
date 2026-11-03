import Shared.ComplexityBridge.TM2WitnessOutput
import Shared.ComplexityBridge.TM2NumeralPairLoader

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessInput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2NumeralPairLoader.machine
abbrev SKey := Shared.ComplexityBridge.TM2NumeralPairLoader.Stack
abbrev SLabel := Shared.ComplexityBridge.TM2NumeralPairLoader.Label
abbrev Key := Shared.ComplexityBridge.TM2WitnessLookup.Key
abbrev Label := (Bool × SLabel) ⊕ Unit

def keyMap (stage : Bool) : SKey → Key :=
  if stage then
    fun k => match k with | .input => .right | .xScratch => .scratch | .yScratch => .left | .left => .witness | .right => .vars
  else
    fun k => match k with | .input => .vars | .xScratch => .scratch | .yScratch => .left | .left => .query | .right => .right

def stackMap (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) : Key → List Bool :=
  if stage then
    fun k => match k with | .right => S .input | .scratch => S .xScratch | .left => S .yScratch | .witness => S .left | .vars => S .right | .query => other .query
  else
    fun k => match k with | .vars => S .input | .scratch => S .xScratch | .left => S .yScratch | .query => S .left | .right => S .right | .witness => other .witness

@[simp] theorem stackMap_apply (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) (j : SKey) :
    stackMap stage S other (keyMap stage j) = S j := by cases stage <;> cases j <;> rfl

theorem stackMap_update (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) (j : SKey) (xs : List Bool) :
    stackMap stage (Function.update S j xs) other = Function.update (stackMap stage S other) (keyMap stage j) xs := by
  funext k; cases stage <;> cases j <;> cases k <;> simp [stackMap,keyMap,Function.update]

def embed (stage : Bool) (other : Key → List Bool) (q : Source.Cfg) : Cfg (fun _ : Key => Bool) Label (Option Bool) :=
  ⟨q.l.map (fun l => .inl (stage,l)),q.var,stackMap stage q.stk other⟩

def lift (stage : Bool) : Stmt (fun _ : SKey => Bool) SLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .push j f q => .push (keyMap stage j) f (lift stage q)
  | .peek j f q => .peek (keyMap stage j) f (lift stage q)
  | .pop j f q => .pop (keyMap stage j) f (lift stage q)
  | .load f q => .load f (lift stage q)
  | .branch f q r => .branch f (lift stage q) (lift stage r)
  | .goto f => .goto (fun v => .inl (stage,f v))
  | .halt => .halt

theorem lift_aux (stage : Bool) (q : Source.Stmt) (v : Option Bool) (S : SKey → List Bool) (other : Key → List Bool) :
    stepAux (lift stage q) v (stackMap stage S other) = embed stage other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [lift,stepAux,stackMap_apply]
    rw [← stackMap_update stage S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [lift,stepAux,stackMap_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [lift,stepAux,stackMap_apply]
    rw [← stackMap_update stage S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label (Option Bool)
  | .inl (false,.done) => .load (fun _ => none) (.goto (fun _ => .inl (true,.x0)))
  | .inl (true,.done) => .load (fun _ => none) (.goto (fun _ => .inr ()))
  | .inl (stage,l) => lift stage (Shared.ComplexityBridge.TM2NumeralPairLoader.program l)
  | .inr _ => .goto (fun _ => .inr ())

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .vars
  k₁ := .query
  Γ := fun _ => Bool
  Λ := Label
  main := .inl (false,.x0)
  σ := Option Bool
  initialState := none
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2NumeralPairLoader.Label.done at h
    subst l; rfl

theorem source_step (stage : Bool) (other : Key → List Bool) (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed stage other q) = (Source.step q).map (embed stage other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h rfl)
      | x0 | x1 | x2 | x3 | x4 | x5 | y0 | y1 | y2 | restoreX | restoreY =>
        cases stage <;>
          change some (stepAux (lift _ (Shared.ComplexityBridge.TM2NumeralPairLoader.program _)) v (stackMap _ S other)) = _ <;>
          rw [lift_aux] <;> rfl

theorem initial_eq (bits : List Bool) :
    Turing.initList machine bits = embed false (fun _ => []) (Turing.initList Source bits) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,embed,stackMap,Turing.initList,Source,Shared.ComplexityBridge.TM2NumeralPairLoader.machine] <;> rfl

def finalCfg (first witness query : List Bool) : machine.Cfg :=
  ⟨some (.inr ()),none,Shared.ComplexityBridge.TM2WitnessLookup.stackVals query witness first [] [] []⟩

theorem first_dispatch (first inner : List Bool) :
    machine.step (embed false (fun _ => []) (Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] first inner)) =
      some (embed true (Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] [] first [] [] []) (Turing.initList Source inner)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [embed,stackMap,Shared.ComplexityBridge.TM2NumeralPairLoader.cfg,
    Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Turing.initList,Source,Shared.ComplexityBridge.TM2NumeralPairLoader.machine] <;> rfl

theorem second_dispatch (first witness query : List Bool) :
    machine.step (embed true (Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] [] first [] [] [])
      (Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] witness query)) =
      some (finalCfg first witness query) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

/-- Two canonical pair encodings carry the explicit framed names, witness, and
query; no data are preloaded in auxiliary stacks. -/
def inputBits (first witness query : List Bool) : List Bool :=
  BitstringEncoding.bitEncode (first, BitstringEncoding.bitEncode (witness,query))

/-- The serialized data uniquely determine all three raw inputs. -/
theorem inputBits_injective {first witness query first' witness' query' : List Bool}
    (h : inputBits first witness query = inputBits first' witness' query') :
    first = first' ∧ witness = witness' ∧ query = query' := by
  have hp : (first,BitstringEncoding.bitEncode (witness,query)) =
      (first',BitstringEncoding.bitEncode (witness',query')) :=
    BitstringEncoding.bitEncode_injective h
  have hi : (witness,query) = (witness',query') :=
    BitstringEncoding.bitEncode_injective (congrArg Prod.snd hp)
  exact ⟨congrArg Prod.fst hp,congrArg Prod.fst hi,congrArg Prod.snd hi⟩

/-- Both finite parsing passes, including their dispatches, finish in linear
time in the actual external bitstring length. -/
theorem load_input (first witness query : List Bool) :
    ∃ t ≤ 4*(inputBits first witness query).length+6,
      runSteps machine.step t (Turing.initList machine (inputBits first witness query)) =
        some (finalCfg first witness query) := by
  let inner := BitstringEncoding.bitEncode (witness,query)
  let outer := inputBits first witness query
  let other := Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] [] first [] [] []
  let finish1 := Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] first inner
  let finish2 := Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] witness query
  have h1 := Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair first inner
  change runSteps Source.step (7*first.length+4*inner.length+4) (Turing.initList Source outer) = some finish1 at h1
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step (embed false (fun _ => [])) terminal stable (source_step false (fun _ => []))
    _ (Turing.initList Source outer) finish1 rfl h1
  have h2 := Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair witness query
  change runSteps Source.step (7*witness.length+4*query.length+4) (Turing.initList Source inner) = some finish2 at h2
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step (embed true other) terminal stable (source_step true other)
    _ (Turing.initList Source inner) finish2 rfl h2
  have ha' : a ≤ 2*outer.length+2 := le_trans ha (Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair_cost first inner)
  have hb' : b ≤ 2*inner.length+2 := le_trans hb (Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair_cost witness query)
  have hsize : outer.length = 6*first.length+1+3*inner.length := Shared.ComplexityBridge.bitstring_pair_encoded_length first inner
  have hi : inner.length ≤ outer.length := by omega
  refine ⟨a+1+b+1,?_,?_⟩
  · change a+1+b+1 ≤ 4*outer.length+6
    omega
  · change runSteps machine.step (a+1+b+1) (Turing.initList machine outer) = _
    rw [initial_eq,show a+1+b+1 = a+(1+(b+1)) by omega,runSteps_add,har]
    change runSteps machine.step (1+(b+1)) (embed false (fun _ => []) finish1) = _
    rw [runSteps_add]
    change (machine.step (embed false (fun _ => []) finish1)).bind (runSteps machine.step (b+1)) = _
    rw [first_dispatch]
    change runSteps machine.step (b+1) (embed true other (Turing.initList Source inner)) = _
    rw [runSteps_add,hbr]
    exact second_dispatch first witness query

namespace Fixtures
example : (runSteps machine.step 14 (Turing.initList machine (inputBits [] [] []))).map
    (fun q => ((match q.l with | some (.inr _) => true | _ => false),q.stk .vars,q.stk .witness,q.stk .query)) = some (true,[],[],[]) := by
  change (Option.map (fun q => ((match q.l with | some (.inr _) => true | _ => false),q.stk .vars,q.stk .witness,q.stk .query))
    (runSteps machine.step 14 (Turing.initList machine (inputBits [] [] []))) : Option (Bool × List Bool × List Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2WitnessInput
