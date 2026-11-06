import Mathlib.Logic.Equiv.Bool
import Shared.ComplexityBridge.TM2GenericStackBound
import Shared.ComplexityBridge.TM2IgnoreWitness
import Shared.ComplexityBridge.CanonicalClasses

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2Compose
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

abbrev Key (f g : Turing.FinTM2) := Unit ⊕ (f.K ⊕ g.K)
def Alphabet (f g : Turing.FinTM2) : Key f g → Type
  | .inl _ => Bool
  | .inr (.inl k) => f.Γ k
  | .inr (.inr k) => g.Γ k
inductive TransferLabel where | load | restore
  deriving DecidableEq
instance : Fintype TransferLabel := Fintype.ofList [.load,.restore] (by intro l; cases l <;> simp)
abbrev Label (f g : Turing.FinTM2) := f.Λ ⊕ (TransferLabel ⊕ g.Λ)
abbrev State (f g : Turing.FinTM2) := f.σ ⊕ (Option Bool ⊕ g.σ)

def firstState (f g : Turing.FinTM2) : State f g → f.σ
  | .inl v => v | _ => f.initialState
def transferState (f g : Turing.FinTM2) : State f g → Option Bool
  | .inr (.inl v) => v | _ => none
def secondState (f g : Turing.FinTM2) : State f g → g.σ
  | .inr (.inr v) => v | _ => g.initialState

def stackVals (f g : Turing.FinTM2) (scratch : List Bool)
    (F : (k : f.K) → List (f.Γ k)) (G : (k : g.K) → List (g.Γ k)) :
    (k : Key f g) → List (Alphabet f g k)
  | .inl _ => scratch
  | .inr (.inl k) => F k
  | .inr (.inr k) => G k

set_option backward.isDefEq.respectTransparency false in
theorem update_first (f g : Turing.FinTM2) (scratch : List Bool)
    (F : (k : f.K) → List (f.Γ k)) (G : (k : g.K) → List (g.Γ k))
    (j : f.K) (xs : List (f.Γ j)) :
    Function.update (stackVals f g scratch F G) (.inr (.inl j)) xs = stackVals f g scratch (Function.update F j xs) G := by
  funext k
  cases k with
  | inl u => cases u; simp [stackVals,Function.update]
  | inr k => cases k with
    | inl k =>
      by_cases h : k = j
      · subst k; simp [stackVals]
      · have hh : (Sum.inr (Sum.inl k) : Key f g) ≠ .inr (.inl j) := by simpa using h
        simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]
    | inr k => simp [stackVals,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem update_second (f g : Turing.FinTM2) (scratch : List Bool)
    (F : (k : f.K) → List (f.Γ k)) (G : (k : g.K) → List (g.Γ k))
    (j : g.K) (xs : List (g.Γ j)) :
    Function.update (stackVals f g scratch F G) (.inr (.inr j)) xs = stackVals f g scratch F (Function.update G j xs) := by
  funext k
  cases k with
  | inl u => cases u; simp [stackVals,Function.update]
  | inr k => cases k with
    | inl k => simp [stackVals,Function.update]
    | inr k =>
      by_cases h : k = j
      · subst k; simp [stackVals]
      · have hh : (Sum.inr (Sum.inr k) : Key f g) ≠ .inr (.inr j) := by simpa using h
        simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

set_option backward.isDefEq.respectTransparency false in
theorem update_scratch (f g : Turing.FinTM2) (scratch : List Bool)
    (F : (k : f.K) → List (f.Γ k)) (G : (k : g.K) → List (g.Γ k)) (xs : List Bool) :
    Function.update (stackVals f g scratch F G) (.inl ()) xs = stackVals f g xs F G := by
  funext k
  cases k with
  | inl u => cases u; simp [stackVals,Function.update]
  | inr k => cases k <;> simp [stackVals,Function.update]

def firstEmbed (f g : Turing.FinTM2) (q : f.Cfg)
    (G : (k : g.K) → List (g.Γ k)) : Cfg (Alphabet f g) (Label f g) (State f g) :=
  match q.l with
  | some l => ⟨some (.inl l),.inl q.var,stackVals f g [] q.stk G⟩
  | none => ⟨some (.inr (.inl .load)),.inr (.inl none),stackVals f g [] q.stk G⟩

def secondEmbed (f g : Turing.FinTM2) (q : g.Cfg) : Cfg (Alphabet f g) (Label f g) (State f g) :=
  ⟨q.l.map (fun l => .inr (.inr l)),match q.l with | none => .inl f.initialState | some _ => .inr (.inr q.var),
    stackVals f g [] (fun _ => []) q.stk⟩

def liftFirst (f g : Turing.FinTM2) : f.Stmt → Stmt (Alphabet f g) (Label f g) (State f g)
  | .push j h q => .push (.inr (.inl j)) (fun v => h (firstState f g v)) (liftFirst f g q)
  | .peek j h q => .peek (.inr (.inl j)) (fun v x => .inl (h (firstState f g v) x)) (liftFirst f g q)
  | .pop j h q => .pop (.inr (.inl j)) (fun v x => .inl (h (firstState f g v) x)) (liftFirst f g q)
  | .load h q => .load (fun v => .inl (h (firstState f g v))) (liftFirst f g q)
  | .branch h q r => .branch (fun v => h (firstState f g v)) (liftFirst f g q) (liftFirst f g r)
  | .goto h => .goto (fun v => .inl (h (firstState f g v)))
  | .halt => .load (fun _ => .inr (.inl none)) (.goto (fun _ => .inr (.inl .load)))

def liftSecond (f g : Turing.FinTM2) : g.Stmt → Stmt (Alphabet f g) (Label f g) (State f g)
  | .push j h q => .push (.inr (.inr j)) (fun v => h (secondState f g v)) (liftSecond f g q)
  | .peek j h q => .peek (.inr (.inr j)) (fun v x => .inr (.inr (h (secondState f g v) x))) (liftSecond f g q)
  | .pop j h q => .pop (.inr (.inr j)) (fun v x => .inr (.inr (h (secondState f g v) x))) (liftSecond f g q)
  | .load h q => .load (fun v => .inr (.inr (h (secondState f g v)))) (liftSecond f g q)
  | .branch h q r => .branch (fun v => h (secondState f g v)) (liftSecond f g q) (liftSecond f g r)
  | .goto h => .goto (fun v => .inr (.inr (h (secondState f g v))))
  | .halt => .load (fun _ => .inl f.initialState) .halt

set_option backward.isDefEq.respectTransparency false in
theorem liftFirst_aux (f g : Turing.FinTM2) (q : f.Stmt) (v : f.σ)
    (F : (k : f.K) → List (f.Γ k)) (G : (k : g.K) → List (g.Γ k)) :
    stepAux (liftFirst f g q) (.inl v) (stackVals f g [] F G) = firstEmbed f g (stepAux q v F) G := by
  induction q generalizing v F with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | push j h q ih =>
    simp only [liftFirst,stepAux,firstState,stackVals]
    rw [update_first]
    exact ih _ _
  | peek j h q ih => exact ih _ _
  | pop j h q ih =>
    simp only [liftFirst,stepAux,firstState,stackVals]
    rw [update_first]
    exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [liftFirst,stepAux,firstState,hh,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftSecond_aux (f g : Turing.FinTM2) (q : g.Stmt) (v : g.σ)
    (G : (k : g.K) → List (g.Γ k)) :
    stepAux (liftSecond f g q) (.inr (.inr v)) (stackVals f g [] (fun _ => []) G) = secondEmbed f g (stepAux q v G) := by
  induction q generalizing v G with
  | halt => rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | push j h q ih =>
    simp only [liftSecond,stepAux,secondState,stackVals]
    rw [update_second]
    exact ih _ _
  | peek j h q ih => exact ih _ _
  | pop j h q ih =>
    simp only [liftSecond,stepAux,secondState,stackVals]
    rw [update_second]
    exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [liftSecond,stepAux,secondState,hh,ihq,ihr]

/-- The intermediate encoding is moved via a Boolean scratch stack, charging
one block per popped symbol in both directions. -/
def program (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool) :
    Label f g → Stmt (Alphabet f g) (Label f g) (State f g)
  | .inl l => liftFirst f g (f.m l)
  | .inr (.inl .load) => .pop (.inr (.inl f.k₁)) (fun _ h => .inr (.inl (h.map out)))
      (.branch (fun s => (transferState f g s).isSome)
        (.push (.inl ()) (fun s => (transferState f g s).getD false) (.goto (fun _ => .inr (.inl .load))))
        (.goto (fun _ => .inr (.inl .restore))))
  | .inr (.inl .restore) => .pop (.inl ()) (fun _ h => .inr (.inl h))
      (.branch (fun s => (transferState f g s).isSome)
        (.push (.inr (.inr g.k₀)) (fun s => inp.symm ((transferState f g s).getD false))
          (.goto (fun _ => .inr (.inl .restore))))
        (.load (fun _ => .inr (.inr g.initialState)) (.goto (fun _ => .inr (.inr g.main)))))
  | .inr (.inr l) => liftSecond f g (g.m l)

def machine (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool) : Turing.FinTM2 := by
  letI := f.kFin; letI := g.kFin
  letI := f.ΛFin; letI := g.ΛFin
  letI := f.σFin; letI := g.σFin
  exact {
    K := Key f g
    k₀ := .inr (.inl f.k₀)
    k₁ := .inr (.inr g.k₁)
    Γ := Alphabet f g
    Λ := Label f g
    main := .inl f.main
    σ := State f g
    initialState := .inl f.initialState
    Γk₀Fin := f.Γk₀Fin
    m := program f g out inp }

set_option backward.isDefEq.respectTransparency false in
theorem first_step (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (G : (k : g.K) → List (g.Γ k)) (q : f.Cfg) (hactive : q.l ≠ none) :
    (machine f g out inp).step (firstEmbed f g q G) = (f.step q).map (fun c => firstEmbed f g c G) := by
  cases q with
  | mk l v F => cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftFirst f g (f.m l)) (.inl v) (stackVals f g [] F G)) = _
      rw [liftFirst_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem first_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (G : (k : g.K) → List (g.Γ k)) (n : Nat) (q r : f.Cfg)
    (h : runSteps f.step n q = some r) :
    runSteps (machine f g out inp).step n (firstEmbed f g q G) = some (firstEmbed f g r G) := by
  induction n generalizing q with
  | zero => change some q = some r at h; cases h; rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change (f.step q).bind (runSteps f.step n) = some r at h
    cases hs : f.step q with
    | none => rw [hs] at h; contradiction
    | some q' =>
      have hactive : q.l ≠ none := by
        intro hl
        have hn : f.step q = none := by cases q with | mk l v S => cases l with | none => rfl | some l => simp at hl
        rw [hn] at hs; contradiction
      rw [hs] at h
      rw [runSteps_front,first_step f g out inp G q hactive,hs]
      exact ih q' h

set_option backward.isDefEq.respectTransparency false in
theorem second_step (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool) (q : g.Cfg) :
    (machine f g out inp).step (secondEmbed f g q) = (g.step q).map (secondEmbed f g) := by
  cases q with
  | mk l v G => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftSecond f g (g.m l)) (.inr (.inr v)) (stackVals f g [] (fun _ => []) G)) = _
      rw [liftSecond_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem second_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool) (q : g.Cfg) (n : Nat) :
    runSteps (machine f g out inp).step n (secondEmbed f g q) = (runSteps g.step n q).map (secondEmbed f g) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,second_step]
    cases h : g.step q with
    | none => rfl
    | some q' => exact ih q'

def transferCfg (f g : Turing.FinTM2) (l : TransferLabel) (v : Option Bool)
    (scratch : List Bool) (xs : List (f.Γ f.k₁)) (ys : List (g.Γ g.k₀)) :
    Cfg (Alphabet f g) (Label f g) (State f g) :=
  ⟨some (.inr (.inl l)),.inr (.inl v),stackVals f g scratch (Turing.haltList f xs).stk (Turing.initList g ys).stk⟩

theorem haltStacks_update (tm : Turing.FinTM2) (old xs : List (tm.Γ tm.k₁)) :
    Function.update (Turing.haltList tm old).stk tm.k₁ xs = (Turing.haltList tm xs).stk := by
  funext k
  by_cases h : k = tm.k₁
  · subst k; simp [Turing.haltList]
  · simp [Turing.haltList,h,Function.update_of_ne h]

theorem initStacks_update (tm : Turing.FinTM2) (old xs : List (tm.Γ tm.k₀)) :
    Function.update (Turing.initList tm old).stk tm.k₀ xs = (Turing.initList tm xs).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [Turing.initList]
  · simp [Turing.initList,h,Function.update_of_ne h]

theorem haltStacks_empty (tm : Turing.FinTM2) : (Turing.haltList tm []).stk = fun _ => [] := by
  funext k
  by_cases h : k = tm.k₁
  · subst k; simp [Turing.haltList]
  · simp [Turing.haltList,h]

theorem initStacks_empty (tm : Turing.FinTM2) : (Turing.initList tm []).stk = fun _ => [] := by
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [Turing.initList]
  · simp [Turing.initList,h]

set_option backward.isDefEq.respectTransparency false in
theorem load_cons (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (v : Option Bool) (scratch : List Bool) (a : f.Γ f.k₁) (xs : List (f.Γ f.k₁)) (ys : List (g.Γ g.k₀)) :
    (machine f g out inp).step (transferCfg f g .load v scratch (a::xs) ys) =
      some (transferCfg f g .load (some (out a)) (out a::scratch) xs ys) := by
  have hout : (Turing.haltList f (a::xs)).stk f.k₁ = a::xs := by simp [Turing.haltList]
  change some (stepAux (program f g out inp (.inr (.inl .load))) (.inr (.inl v))
    (stackVals f g scratch (Turing.haltList f (a::xs)).stk (Turing.initList g ys).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_cons,Option.map_some,transferState,
    Option.isSome_some,Bool.cond_true,List.tail_cons,Option.getD_some]
  congr 1
  congr 1
  rw [update_first,haltStacks_update,update_scratch]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem load_nil (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (v : Option Bool) (scratch : List Bool) (ys : List (g.Γ g.k₀)) :
    (machine f g out inp).step (transferCfg f g .load v scratch [] ys) =
      some (transferCfg f g .restore none scratch [] ys) := by
  have hout : (Turing.haltList f []).stk f.k₁ = [] := by simp [Turing.haltList]
  change some (stepAux (program f g out inp (.inr (.inl .load))) (.inr (.inl v))
    (stackVals f g scratch (Turing.haltList f []).stk (Turing.initList g ys).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_nil,Option.map_none,transferState,Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 1
  congr 1
  rw [update_first,haltStacks_update]

set_option backward.isDefEq.respectTransparency false in
theorem restore_cons (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (v : Option Bool) (b : Bool) (scratch : List Bool) (ys : List (g.Γ g.k₀)) :
    (machine f g out inp).step (transferCfg f g .restore v (b::scratch) [] ys) =
      some (transferCfg f g .restore (some b) scratch [] (inp.symm b::ys)) := by
  have hin : (Turing.initList g ys).stk g.k₀ = ys := by simp [Turing.initList]
  change some (Cfg.mk (some (Sum.inr (Sum.inl TransferLabel.restore)) : Option (Label f g)) _
    (Function.update (Function.update (stackVals f g (b::scratch) (Turing.haltList f []).stk (Turing.initList g ys).stk)
      (.inl ()) scratch) (.inr (.inr g.k₀)) (inp.symm b :: (Turing.initList g ys).stk g.k₀))) = _
  rw [hin]
  congr 1
  congr 1
  rw [update_scratch,update_second,initStacks_update]

set_option backward.isDefEq.respectTransparency false in
theorem restore_nil (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (v : Option Bool) (ys : List (g.Γ g.k₀)) :
    (machine f g out inp).step (transferCfg f g .restore v [] [] ys) =
      some (secondEmbed f g (Turing.initList g ys)) := by
  change some (Cfg.mk (some (Sum.inr (Sum.inr g.main)) : Option (Label f g)) (Sum.inr (Sum.inr g.initialState) : State f g)
    (Function.update (stackVals f g [] (Turing.haltList f []).stk (Turing.initList g ys).stk) (.inl ()) [])) = _
  rw [update_scratch,haltStacks_empty]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem load_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (xs : List (f.Γ f.k₁)) (scratch : List Bool) (ys : List (g.Γ g.k₀)) (v : Option Bool) :
    ∃ v', runSteps (machine f g out inp).step xs.length (transferCfg f g .load v scratch xs ys) =
      some (transferCfg f g .load v' (xs.reverse.map out ++ scratch) [] ys) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by rfl⟩
  | cons a xs ih =>
    obtain ⟨v',h⟩ := ih (out a::scratch) (some (out a))
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,load_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using h

set_option backward.isDefEq.respectTransparency false in
theorem restore_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (scratch : List Bool) (ys : List (g.Γ g.k₀)) (v : Option Bool) :
    runSteps (machine f g out inp).step (scratch.length+1) (transferCfg f g .restore v scratch [] ys) =
      some (secondEmbed f g (Turing.initList g (scratch.reverse.map inp.symm ++ ys))) := by
  induction scratch generalizing ys v with
  | nil =>
    change (machine f g out inp).step (transferCfg f g .restore v [] [] ys) = _
    exact restore_nil f g out inp v ys
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using ih (inp.symm b::ys) (some b)

set_option backward.isDefEq.respectTransparency false in
/-- The full intermediate bitstring is moved in order, even with distinct
input and output alphabet equivalences. Both source and scratch stacks are
empty before the second machine starts. -/
theorem transfer_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool) (bits : List Bool) :
    runSteps (machine f g out inp).step (2*bits.length+2)
      (firstEmbed f g (Turing.haltList f (bits.map out.symm)) (Turing.initList g []).stk) =
      some (secondEmbed f g (Turing.initList g (bits.map inp.symm))) := by
  obtain ⟨v,hl⟩ := load_run f g out inp (bits.map out.symm) [] [] none
  have hbits : (bits.map out.symm).reverse.map out = bits.reverse := by
    simp [List.map_reverse,List.map_map]
  simp only [List.length_map,List.append_nil,hbits] at hl
  have hr := restore_run f g out inp bits.reverse [] none
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hn : 2*bits.length+2 = bits.length+((bits.length+1)+1) := by omega
  rw [hn]
  change runSteps (machine f g out inp).step (bits.length+((bits.length+1)+1))
    (transferCfg f g .load none [] (bits.map out.symm) []) = _
  rw [runSteps_add,hl]
  change runSteps (machine f g out inp).step ((bits.length+1)+1)
    (transferCfg f g .load v bits.reverse [] []) = _
  rw [runSteps_front,load_nil]
  exact hr

set_option backward.isDefEq.respectTransparency false in
theorem initial_eq (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (bits : List (f.Γ f.k₀)) :
    Turing.initList (machine f g out inp) bits = firstEmbed f g (Turing.initList f bits) (Turing.initList g []).stk := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl u => cases u; simp [machine,firstEmbed,stackVals,Turing.initList]
  | inr k => cases k with
    | inl k =>
      by_cases h : k = f.k₀
      · subst k; simp [machine,firstEmbed,stackVals,Turing.initList]
      · simp [machine,firstEmbed,stackVals,Turing.initList,h]
    | inr k =>
      by_cases h : k = g.k₀
      · subst k; simp [machine,firstEmbed,stackVals,Turing.initList]
      · simp [machine,firstEmbed,stackVals,Turing.initList,h]

set_option backward.isDefEq.respectTransparency false in
theorem final_eq (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (bits : List (g.Γ g.k₁)) :
    secondEmbed f g (Turing.haltList g bits) = Turing.haltList (machine f g out inp) bits := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl u => cases u; simp [machine,secondEmbed,stackVals,Turing.haltList]
  | inr k => cases k with
    | inl k => simp [machine,secondEmbed,stackVals,Turing.haltList]
    | inr k =>
      by_cases h : k = g.k₁
      · subst k; simp [machine,secondEmbed,stackVals,Turing.haltList]
      · simp [machine,secondEmbed,stackVals,Turing.haltList,h]

set_option backward.isDefEq.respectTransparency false in
/-- The first run, intermediate transfer, and second run are all charged. -/
theorem compose_run (f g : Turing.FinTM2) (out : f.Γ f.k₁ ≃ Bool) (inp : g.Γ g.k₀ ≃ Bool)
    (input : List (f.Γ f.k₀)) (middle : List Bool) (output : List (g.Γ g.k₁)) (n m : Nat)
    (hf : runSteps f.step n (Turing.initList f input) = some (Turing.haltList f (middle.map out.symm)))
    (hg : runSteps g.step m (Turing.initList g (middle.map inp.symm)) = some (Turing.haltList g output)) :
    runSteps (machine f g out inp).step (n+(2*middle.length+2)+m)
      (Turing.initList (machine f g out inp) input) = some (Turing.haltList (machine f g out inp) output) := by
  have hfirst := first_run f g out inp (Turing.initList g []).stk n (Turing.initList f input)
    (Turing.haltList f (middle.map out.symm)) hf
  rw [initial_eq,show n+(2*middle.length+2)+m = n+((2*middle.length+2)+m) by omega,runSteps_add,hfirst]
  change runSteps (machine f g out inp).step ((2*middle.length+2)+m)
    (firstEmbed f g (Turing.haltList f (middle.map out.symm)) (Turing.initList g []).stk) = _
  rw [runSteps_add,transfer_run]
  change runSteps (machine f g out inp).step m (secondEmbed f g (Turing.initList g (middle.map inp.symm))) = _
  rw [second_run,hg]
  change some (secondEmbed f g (Turing.haltList g output)) = _
  rw [final_eq]

/-- Every natural-coefficient polynomial is monotone on natural inputs. -/
theorem polynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  obtain ⟨terms,ht⟩ := Shared.Codes.NumericPolynomial.polynomial_represented p
  rw [← ht a, ← ht b]
  clear ht p
  induction terms with
  | nil => simp [Shared.Codes.NumericPolynomial.eval]
  | cons term terms ih =>
    rcases term with ⟨c,e⟩
    simp only [Shared.Codes.NumericPolynomial.eval,List.foldr_cons] at *
    gcongr

def composeAux (f g : Turing.TM2ComputableAux Bool Bool) : Turing.TM2ComputableAux Bool Bool where
  tm := machine f.tm g.tm f.outputAlphabet g.inputAlphabet
  inputAlphabet := f.inputAlphabet
  outputAlphabet := g.outputAlphabet

noncomputable def middleBound (p : Polynomial Nat) (d : Nat) : Polynomial Nat :=
  Polynomial.X + p * Polynomial.C d
noncomputable def timePolynomial (p q : Polynomial Nat) (d : Nat) : Polynomial Nat :=
  p + Polynomial.C 2 * middleBound p d + Polynomial.C 2 + q.comp (middleBound p d)

theorem middleBound_eval (p : Polynomial Nat) (d n : Nat) : (middleBound p d).eval n = n + p.eval n*d := by
  simp [middleBound]
theorem timePolynomial_eval (p q : Polynomial Nat) (d n : Nat) :
    (timePolynomial p q d).eval n = p.eval n + 2*(n+p.eval n*d)+2 + q.eval (n+p.eval n*d) := by
  simp [timePolynomial,middleBound_eval,Polynomial.eval_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial-time composition for the pinned canonical bitstring encodings.
The intermediate result is output by the first machine, transferred at a
linear charged cost, and its size is bounded by finite statement syntax. -/
theorem isPolyTime_comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]
    (F : α → β) (G : β → γ) (hF : ComplexityTheory.IsPolyTime F) (hG : ComplexityTheory.IsPolyTime G) :
    ComplexityTheory.IsPolyTime (fun x => G (F x)) := by
  rcases hF with ⟨hF⟩
  rcases hG with ⟨hG⟩
  let f := hF.toTM2ComputableAux
  let g := hG.toTM2ComputableAux
  let c := composeAux f g
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound f.tm
  refine ⟨{ toTM2ComputableAux := c, time := timePolynomial hF.time hG.time D, outputsFun := ?_ }⟩
  intro a
  let rF := hF.outputsFun a
  let rG := hG.outputsFun (F a)
  let n := rF.steps
  let m := rG.steps
  let input := BitstringEncoding.bitEncode a
  let middle := BitstringEncoding.bitEncode (F a)
  let output := BitstringEncoding.bitEncode (G (F a))
  have hf : runSteps f.tm.step n (Turing.initList f.tm (input.map f.inputAlphabet.symm)) =
      some (Turing.haltList f.tm (middle.map f.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact rF.evals_in_steps
  have hg : runSteps g.tm.step m (Turing.initList g.tm (middle.map g.inputAlphabet.symm)) =
      some (Turing.haltList g.tm (output.map g.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact rG.evals_in_steps
  have hfirst : n ≤ hF.time.eval input.length := rF.steps_le_m
  have hsecond : m ≤ hG.time.eval middle.length := rG.steps_le_m
  have hlength := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length f.tm
    (input.map f.inputAlphabet.symm) n (Turing.haltList f.tm (middle.map f.outputAlphabet.symm)) hf f.tm.k₁
  have hmid : middle.length ≤ input.length + n*D := by
    simpa [Turing.haltList,D] using hlength
  have hmul : n*D ≤ hF.time.eval input.length*D := Nat.mul_le_mul_right D hfirst
  have hmid' : middle.length ≤ input.length + hF.time.eval input.length*D := by omega
  have hsecond' := polynomial_eval_mono hG.time hmid'
  let t := n+(2*middle.length+2)+m
  have hrun := compose_run f.tm g.tm f.outputAlphabet g.inputAlphabet
    (input.map f.inputAlphabet.symm) middle (output.map g.outputAlphabet.symm) n m hf hg
  refine ⟨⟨t,?_⟩,?_⟩
  · rw [runSteps_iterate] at hrun
    exact hrun
  · change t ≤ (timePolynomial hF.time hG.time D).eval input.length
    rw [timePolynomial_eval]
    dsimp [t]
    omega

/-- Polynomial many-one reductions preserve membership in the actual class P. -/
theorem p_pullback_closed : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.P := by
  intro A B hB hred
  obtain ⟨F,hF,hAB⟩ := hred
  have hc := isPolyTime_comp F B hF hB
  have heq : A = fun x => B (F x) := funext hAB
  rw [heq]
  exact hc

/-- PNP candidate characterization still requires the concrete SAT-completeness
interface, but no longer assumes P inclusion or P pullback closure. -/
theorem pnp_candidates_conditional
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat) :
    (∃ e, ∀ n, Shared.PNP.TM2Candidate.compareSAT e n = true) ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  have h := Shared.ComplexityBridge.TM2Whole.pnp_controller_conditional complete
    Shared.ComplexityBridge.TM2IgnoreWitness.P_subset_NP p_pullback_closed
  exact (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good
    Shared.PNP.TM2Candidate.compareSAT).symm.trans h

theorem pnp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.TM2IgnoreWitness.pnp_certified_conditional cert complete p_pullback_closed

namespace Fixtures
set_option maxRecDepth 10000 in
/-- Exact eight-block transfer of a two-bit string between identity machines. -/
example : (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
    (Equiv.refl Bool) (Equiv.refl Bool)).step 8
    (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
      (Equiv.refl Bool) (Equiv.refl Bool)) [true,false])).map
    (fun q => (q.l.isNone,q.stk (.inr (.inr ())))) = some (true,[true,false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr (.inr ()))))
    (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 8
      (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
        (Equiv.refl Bool) (Equiv.refl Bool)) [true,false])) : Option (Bool × List Bool)) = _
  decide

set_option maxRecDepth 10000 in
/-- Both alphabet equivalences are honored during the same order-preserving transfer. -/
example : (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
    Equiv.boolNot Equiv.boolNot).step 8
    (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
      Equiv.boolNot Equiv.boolNot) [true,false])).map
    (fun q => (q.l.isNone,q.stk (.inr (.inr ())))) = some (true,[true,false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr (.inr ()))))
    (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool) Equiv.boolNot Equiv.boolNot).step 8
      (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
        Equiv.boolNot Equiv.boolNot) [true,false])) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 10000 in
/-- The empty intermediate uses two empty checks and still reaches a halt. -/
example : (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
    (Equiv.refl Bool) (Equiv.refl Bool)).step 4
    (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
      (Equiv.refl Bool) (Equiv.refl Bool)) [])).map
    (fun q => (q.l.isNone,q.stk (.inr (.inr ())))) = some (true,([] : List Bool)) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr (.inr ()))))
    (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 4
      (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
        (Equiv.refl Bool) (Equiv.refl Bool)) [])) : Option (Bool × List Bool)) = _
  decide

set_option maxRecDepth 10000 in
/-- A nonidentity source output alphabet is transcoded into the target input. -/
example : (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
    Equiv.boolNot (Equiv.refl Bool)).step 8
    (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
      Equiv.boolNot (Equiv.refl Bool)) [true,false])).map
    (fun q => (q.l.isNone,q.stk (.inr (.inr ())))) = some (true,[false,true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr (.inr ()))))
    (runSteps (machine (Turing.idComputer Bool) (Turing.idComputer Bool) Equiv.boolNot (Equiv.refl Bool)).step 8
      (Turing.initList (machine (Turing.idComputer Bool) (Turing.idComputer Bool)
        Equiv.boolNot (Equiv.refl Bool)) [true,false])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2Compose
