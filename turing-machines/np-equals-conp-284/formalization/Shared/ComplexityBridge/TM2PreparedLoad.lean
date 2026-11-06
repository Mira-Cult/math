import Shared.ComplexityBridge.TM2WitnessOutput
import Shared.ComplexityBridge.TM2NumeralPairLoader

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2PreparedLoad
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2NumeralPairLoader.machine
abbrev SKey := Shared.ComplexityBridge.TM2NumeralPairLoader.Stack
abbrev SLabel := Shared.ComplexityBridge.TM2NumeralPairLoader.Label
abbrev Key := Shared.ComplexityBridge.TM2WitnessLookup.Key
inductive Control where | tag | clear | ready deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.tag,.clear,.ready] (by intro l; cases l <;> simp)
abbrev Label := (Bool × SLabel) ⊕ Control

def keyMap (stage : Bool) : SKey → Key :=
  if stage then
    fun k => match k with | .input => .right | .xScratch => .scratch | .yScratch => .left | .left => .vars | .right => .query
  else
    fun k => match k with | .input => .vars | .xScratch => .scratch | .yScratch => .left | .left => .right | .right => .witness

def stackMap (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) : Key → List Bool :=
  if stage then
    fun k => match k with | .right => S .input | .scratch => S .xScratch | .left => S .yScratch | .vars => S .left | .query => S .right | .witness => other .witness
  else
    fun k => match k with | .vars => S .input | .scratch => S .xScratch | .left => S .yScratch | .right => S .left | .witness => S .right | .query => other .query

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
  | .inl (true,.done) => .load (fun _ => none) (.goto (fun _ => .inr .tag))
  | .inl (stage,l) => lift stage (Shared.ComplexityBridge.TM2NumeralPairLoader.program l)
  | .inr .tag => .pop .vars (fun _ h => h)
      (.branch (fun h => h == some true) (.goto (fun _ => .inr .ready)) (.goto (fun _ => .inr .clear)))
  | .inr .clear => .pop .vars (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .inr .clear)) (.load (fun _ => none) (.goto (fun _ => .inr .ready))))
  | .inr .ready => .goto (fun _ => .inr .ready)

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


def cfg (l : Control) (v : Option Bool) (frame witness input : List Bool) : machine.Cfg :=
  ⟨some (.inr l),v,Shared.ComplexityBridge.TM2WitnessLookup.stackVals frame witness input [] [] []⟩

def normalized (tag : List Bool) : List Bool := match tag with | true::tail => tail | _ => []

theorem first_dispatch (packed witness : List Bool) :
    machine.step (embed false (fun _ => []) (Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] packed witness)) =
      some (embed true (Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] witness [] [] [] []) (Turing.initList Source packed)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [embed,stackMap,Shared.ComplexityBridge.TM2NumeralPairLoader.cfg,
    Shared.ComplexityBridge.TM2NumeralPairLoader.stackVals,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Turing.initList,Source,Shared.ComplexityBridge.TM2NumeralPairLoader.machine] <;> rfl

theorem second_dispatch (tag witness input : List Bool) :
    machine.step (embed true (Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] witness [] [] [] [])
      (Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] tag input)) =
      some (cfg .tag none tag witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem tag_true (v : Option Bool) (frame witness input : List Bool) :
    machine.step (cfg .tag v (true::frame) witness input) = some (cfg .ready (some true) frame witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update]
theorem tag_false (v : Option Bool) (frame witness input : List Bool) :
    machine.step (cfg .tag v (false::frame) witness input) = some (cfg .clear (some false) frame witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update]
theorem tag_nil (v : Option Bool) (witness input : List Bool) :
    machine.step (cfg .tag v [] witness input) = some (cfg .clear none [] witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update]
theorem clear_cons (v : Option Bool) (b : Bool) (frame witness input : List Bool) :
    machine.step (cfg .clear v (b::frame) witness input) = some (cfg .clear (some b) frame witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update]
theorem clear_nil (v : Option Bool) (witness input : List Bool) :
    machine.step (cfg .clear v [] witness input) = some (cfg .ready none [] witness input) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update]

theorem clear_run (frame witness input : List Bool) (v : Option Bool) :
    runSteps machine.step (frame.length+1) (cfg .clear v frame witness input) = some (cfg .ready none [] witness input) := by
  induction frame generalizing v with
  | nil => exact clear_nil v witness input
  | cons b frame ih =>
    rw [List.length_cons,show frame.length+1+1 = (frame.length+1)+1 by omega,runSteps_front,clear_cons]
    exact ih (some b)

theorem tag_run (tag witness input : List Bool) :
    ∃ t ≤ tag.length+2, ∃ v,
      runSteps machine.step t (cfg .tag none tag witness input) = some (cfg .ready v (normalized tag) witness input) := by
  cases tag with
  | nil =>
    refine ⟨2,by simp,none,?_⟩
    rw [show 2=1+1 by decide,runSteps_front,tag_nil]
    exact clear_nil none witness input
  | cons b tail => cases b with
    | true => exact ⟨1,by simp,some true,tag_true none tail witness input⟩
    | false =>
      refine ⟨tail.length+2,by simp,none,?_⟩
      rw [show tail.length+2 = 1+(tail.length+1) by omega,runSteps_add]
      change (machine.step (cfg .tag none (false::tail) witness input)).bind _ = _
      rw [tag_false]
      exact clear_run tail witness input (some false)

def inputBits (tag witness input : List Bool) : List Bool :=
  BitstringEncoding.bitEncode (BitstringEncoding.bitEncode (tag,input),witness)

/-- Both pair decoders and the tag normalization complete in linear time in
the full prepared encoding. True tags preserve the payload; all other tags
produce an empty occurrence frame. -/
theorem load_input (tag witness input : List Bool) :
    let bits := inputBits tag witness input
    ∃ t ≤ 5*bits.length+8, ∃ v,
      runSteps machine.step t (Turing.initList machine bits) = some (cfg .ready v (normalized tag) witness input) := by
  let packed := BitstringEncoding.bitEncode (tag,input)
  let bits := inputBits tag witness input
  let other := Shared.ComplexityBridge.TM2WitnessLookup.stackVals [] witness [] [] [] []
  let finish1 := Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] packed witness
  let finish2 := Shared.ComplexityBridge.TM2NumeralPairLoader.cfg .done none [] [] [] tag input
  have h1 := Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair packed witness
  change runSteps Source.step (7*packed.length+4*witness.length+4) (Turing.initList Source bits) = some finish1 at h1
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step (embed false (fun _ => [])) terminal stable (source_step false (fun _ => []))
    _ (Turing.initList Source bits) finish1 rfl h1
  have h2 := Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair tag input
  change runSteps Source.step (7*tag.length+4*input.length+4) (Turing.initList Source packed) = some finish2 at h2
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step (embed true other) terminal stable (source_step true other)
    _ (Turing.initList Source packed) finish2 rfl h2
  obtain ⟨c,hc,v,hcr⟩ := tag_run tag witness input
  have ha' : a ≤ 2*bits.length+2 := le_trans ha (Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair_cost packed witness)
  have hb' : b ≤ 2*packed.length+2 := le_trans hb (Shared.ComplexityBridge.TM2NumeralPairLoader.load_pair_cost tag input)
  have hsize : bits.length = 6*packed.length+1+3*witness.length := Shared.ComplexityBridge.bitstring_pair_encoded_length packed witness
  have hpacked : packed.length = 6*tag.length+1+3*input.length := Shared.ComplexityBridge.bitstring_pair_encoded_length tag input
  refine ⟨a+1+b+1+c,?_,v,?_⟩
  · change a+1+b+1+c ≤ 5*bits.length+8
    omega
  · change runSteps machine.step (a+1+b+1+c) (Turing.initList machine bits) = _
    rw [initial_eq,show a+1+b+1+c = a+(1+(b+(1+c))) by omega,runSteps_add,har]
    change runSteps machine.step (1+(b+(1+c))) (embed false (fun _ => []) finish1) = _
    rw [runSteps_add]
    change (machine.step (embed false (fun _ => []) finish1)).bind _ = _
    rw [first_dispatch]
    change runSteps machine.step (b+(1+c)) (embed true other (Turing.initList Source packed)) = _
    rw [runSteps_add,hbr]
    change runSteps machine.step (1+c) (embed true other finish2) = _
    rw [runSteps_add]
    change (machine.step (embed true other finish2)).bind _ = _
    rw [second_dispatch]
    exact hcr

end Shared.ComplexityBridge.TM2PreparedLoad
