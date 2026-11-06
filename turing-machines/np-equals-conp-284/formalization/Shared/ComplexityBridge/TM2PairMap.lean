import Shared.ComplexityBridge.TM2Compose
import Shared.ComplexityBridge.TM2CutoffCompose

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2PairMap
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Key (f : Turing.FinTM2) := Bool ⊕ f.K
def Alphabet (f : Turing.FinTM2) : Key f → Type
  | .inl _ => Bool
  | .inr k => f.Γ k
inductive Control where | header | data | restore | move | prefix
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.header,.data,.restore,.move,.prefix] (by intro l; cases l <;> simp)
abbrev Label (f : Turing.FinTM2) := Control ⊕ f.Λ
abbrev State (f : Turing.FinTM2) := Option Bool ⊕ f.σ

def decodeState (f : Turing.FinTM2) : State f → Option Bool | .inl v => v | .inr _ => none
def coreState (f : Turing.FinTM2) : State f → f.σ | .inl _ => f.initialState | .inr v => v

def stackVals (f : Turing.FinTM2) (pair scratch : List Bool) (S : (k : f.K) → List (f.Γ k)) :
    (k : Key f) → List (Alphabet f k)
  | .inl false => pair
  | .inl true => scratch
  | .inr k => S k

set_option backward.isDefEq.respectTransparency false in
theorem update_pair (f : Turing.FinTM2) (pair scratch : List Bool) (S : (k : f.K) → List (f.Γ k)) (xs : List Bool) :
    Function.update (stackVals f pair scratch S) (.inl false) xs = stackVals f xs scratch S := by
  funext k
  cases k with
  | inl b => cases b <;> simp [stackVals,Function.update]
  | inr k => simp [stackVals,Function.update]
set_option backward.isDefEq.respectTransparency false in
theorem update_scratch (f : Turing.FinTM2) (pair scratch : List Bool) (S : (k : f.K) → List (f.Γ k)) (xs : List Bool) :
    Function.update (stackVals f pair scratch S) (.inl true) xs = stackVals f pair xs S := by
  funext k
  cases k with
  | inl b => cases b <;> simp [stackVals,Function.update]
  | inr k => simp [stackVals,Function.update]
set_option backward.isDefEq.respectTransparency false in
theorem update_core (f : Turing.FinTM2) (pair scratch : List Bool) (S : (k : f.K) → List (f.Γ k))
    (j : f.K) (xs : List (f.Γ j)) :
    Function.update (stackVals f pair scratch S) (.inr j) xs = stackVals f pair scratch (Function.update S j xs) := by
  funext k
  cases k with
  | inl b => cases b <;> simp [stackVals,Function.update]
  | inr k =>
    by_cases h : k = j
    · subst k; simp [stackVals]
    · have hh : (Sum.inr k : Key f) ≠ .inr j := by simpa using h
      simp [stackVals,Function.update_of_ne h,Function.update_of_ne hh]

def coreEmbed (f : Turing.FinTM2) (tail : List Bool) (q : f.Cfg) : Cfg (Alphabet f) (Label f) (State f) :=
  match q.l with
  | some l => ⟨some (.inr l),.inr q.var,stackVals f tail [] q.stk⟩
  | none => ⟨some (.inl .move),.inl none,stackVals f (false::tail) [] q.stk⟩

def liftCore (f : Turing.FinTM2) : f.Stmt → Stmt (Alphabet f) (Label f) (State f)
  | .push j h q => .push (.inr j) (fun v => h (coreState f v)) (liftCore f q)
  | .peek j h q => .peek (.inr j) (fun v x => .inr (h (coreState f v) x)) (liftCore f q)
  | .pop j h q => .pop (.inr j) (fun v x => .inr (h (coreState f v) x)) (liftCore f q)
  | .load h q => .load (fun v => .inr (h (coreState f v))) (liftCore f q)
  | .branch h q r => .branch (fun v => h (coreState f v)) (liftCore f q) (liftCore f r)
  | .goto h => .goto (fun v => .inr (h (coreState f v)))
  | .halt => .push (.inl false) (fun _ => false)
      (.load (fun _ => .inl none) (.goto (fun _ => .inl .move)))

set_option backward.isDefEq.respectTransparency false in
theorem liftCore_aux (f : Turing.FinTM2) (q : f.Stmt) (v : f.σ)
    (S : (k : f.K) → List (f.Γ k)) (tail : List Bool) :
    stepAux (liftCore f q) (.inr v) (stackVals f tail [] S) = coreEmbed f tail (stepAux q v S) := by
  induction q generalizing v S with
  | halt =>
    change Cfg.mk _ _ (Function.update (stackVals f tail [] S) (.inl false) (false::tail)) = _
    rw [update_pair]; rfl
  | goto h => rfl
  | load h q ih => exact ih _ _
  | push j h q ih =>
    simp only [liftCore,stepAux,coreState,stackVals]
    rw [update_core]
    exact ih _ _
  | peek j h q ih => exact ih _ _
  | pop j h q ih =>
    simp only [liftCore,stepAux,coreState,stackVals]
    rw [update_core]
    exact ih _ _
  | branch h q r ihq ihr => by_cases hh : h v <;> simp [liftCore,stepAux,coreState,hh,ihq,ihr]

def program (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) :
    Label f → Stmt (Alphabet f) (Label f) (State f)
  | .inl .header => .pop (.inl false) (fun _ h => .inl h)
      (.branch (fun s => decodeState f s == some true) (.goto (fun _ => .inl .data)) (.goto (fun _ => .inl .restore)))
  | .inl .data => .pop (.inl false) (fun _ h => .inl h)
      (.branch (fun s => (decodeState f s).isSome)
        (.push (.inl true) (fun s => (decodeState f s).getD false) (.goto (fun _ => .inl .header)))
        (.goto (fun _ => .inl .restore)))
  | .inl .restore => .pop (.inl true) (fun _ h => .inl h)
      (.branch (fun s => (decodeState f s).isSome)
        (.push (.inr f.k₀) (fun s => inp.symm ((decodeState f s).getD false)) (.goto (fun _ => .inl .restore)))
        (.load (fun _ => .inr f.initialState) (.goto (fun _ => .inr f.main))))
  | .inl .move => .pop (.inr f.k₁) (fun _ h => .inl (h.map out))
      (.branch (fun s => (decodeState f s).isSome)
        (.push (.inl true) (fun s => (decodeState f s).getD false) (.goto (fun _ => .inl .move)))
        (.goto (fun _ => .inl .prefix)))
  | .inl .prefix => .pop (.inl true) (fun _ h => .inl h)
      (.branch (fun s => (decodeState f s).isSome)
        (.push (.inl false) (fun s => (decodeState f s).getD false)
          (.push (.inl false) (fun _ => true) (.goto (fun _ => .inl .prefix))))
        (.load (fun _ => .inl none) .halt))
  | .inr l => liftCore f (f.m l)

def machine (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) : Turing.FinTM2 := by
  letI := f.kFin; letI := f.ΛFin; letI := f.σFin
  exact {
    K := Key f
    k₀ := .inl false
    k₁ := .inl false
    Γ := Alphabet f
    Λ := Label f
    main := .inl .header
    σ := State f
    initialState := .inl none
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program f inp out }

set_option backward.isDefEq.respectTransparency false in
theorem core_step (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (tail : List Bool) (q : f.Cfg) (h : q.l ≠ none) :
    (machine f inp out).step (coreEmbed f tail q) = (f.step q).map (coreEmbed f tail) := by
  cases q with
  | mk l v S => cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftCore f (f.m l)) (.inr v) (stackVals f tail [] S)) = _
      rw [liftCore_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem core_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (tail : List Bool) (n : Nat) (q r : f.Cfg) (h : runSteps f.step n q = some r) :
    runSteps (machine f inp out).step n (coreEmbed f tail q) = some (coreEmbed f tail r) := by
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
      rw [runSteps_front,core_step f inp out tail q hactive,hs]
      exact ih q' h

def splitCfg (f : Turing.FinTM2) (l : Control) (v : Option Bool) (pair scratch : List Bool)
    (ys : List (f.Γ f.k₀)) : Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inl l),.inl v,stackVals f pair scratch (Turing.initList f ys).stk⟩

set_option backward.isDefEq.respectTransparency false in
theorem header_true (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair scratch : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (splitCfg f .header v (true::pair) scratch ys) =
      some (splitCfg f .data (some true) pair scratch ys) := by
  change some (Cfg.mk (some (Sum.inl Control.data) : Option (Label f)) _
    (Function.update (stackVals f (true::pair) scratch (Turing.initList f ys).stk) (.inl false) pair)) = _
  congr 1; congr 1
  rw [update_pair]

set_option backward.isDefEq.respectTransparency false in
theorem header_false (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair scratch : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (splitCfg f .header v (false::pair) scratch ys) =
      some (splitCfg f .restore (some false) pair scratch ys) := by
  change some (Cfg.mk (some (Sum.inl Control.restore) : Option (Label f)) _
    (Function.update (stackVals f (false::pair) scratch (Turing.initList f ys).stk) (.inl false) pair)) = _
  congr 1; congr 1
  rw [update_pair]

set_option backward.isDefEq.respectTransparency false in
theorem data_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (pair scratch : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (splitCfg f .data v (b::pair) scratch ys) =
      some (splitCfg f .header (some b) pair (b::scratch) ys) := by
  change some (Cfg.mk (some (Sum.inl Control.header) : Option (Label f)) _
    (Function.update (Function.update (stackVals f (b::pair) scratch (Turing.initList f ys).stk) (.inl false) pair)
      (.inl true) (b::scratch))) = _
  congr 1; congr 1
  rw [update_pair,update_scratch]

set_option backward.isDefEq.respectTransparency false in
theorem restore_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (pair scratch : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (splitCfg f .restore v pair (b::scratch) ys) =
      some (splitCfg f .restore (some b) pair scratch (inp.symm b::ys)) := by
  have hin : (Turing.initList f ys).stk f.k₀ = ys := by simp [Turing.initList]
  change some (Cfg.mk (some (Sum.inl Control.restore) : Option (Label f)) _
    (Function.update (Function.update (stackVals f pair (b::scratch) (Turing.initList f ys).stk) (.inl true) scratch)
      (.inr f.k₀) (inp.symm b :: (Turing.initList f ys).stk f.k₀))) = _
  rw [hin]
  congr 1; congr 1
  rw [update_scratch,update_core,Shared.ComplexityBridge.TM2Compose.initStacks_update]

set_option backward.isDefEq.respectTransparency false in
theorem restore_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair : List Bool) (ys : List (f.Γ f.k₀)) :
    (machine f inp out).step (splitCfg f .restore v pair [] ys) =
      some (coreEmbed f pair (Turing.initList f ys)) := by
  change some (Cfg.mk (some (Sum.inr f.main) : Option (Label f)) (Sum.inr f.initialState : State f)
    (Function.update (stackVals f pair [] (Turing.initList f ys).stk) (.inl true) [])) = _
  rw [update_scratch]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem header_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (payload tail scratch : List Bool) (ys : List (f.Γ f.k₀)) (v : Option Bool) :
    ∃ v', runSteps (machine f inp out).step (2*payload.length)
      (splitCfg f .header v (BitstringEncoding.delimit payload ++ tail) scratch ys) =
      some (splitCfg f .header v' (false::tail) (payload.reverse++scratch) ys) := by
  induction payload generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons b xs ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(xs.length+1) = (2*xs.length+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps (machine f inp out).step (2*xs.length+1)
      (splitCfg f .data (some true) (b::(BitstringEncoding.delimit xs ++ tail)) scratch ys) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

set_option backward.isDefEq.respectTransparency false in
theorem restore_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch pair : List Bool) (ys : List (f.Γ f.k₀)) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1) (splitCfg f .restore v pair scratch ys) =
      some (coreEmbed f pair (Turing.initList f (scratch.reverse.map inp.symm ++ ys))) := by
  induction scratch generalizing ys v with
  | nil =>
    change (machine f inp out).step (splitCfg f .restore v pair [] ys) = _
    exact restore_nil f inp out v pair ys
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using ih (inp.symm b::ys) (some b)

set_option backward.isDefEq.respectTransparency false in
theorem initial_eq (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool) (bits : List Bool) :
    Turing.initList (machine f inp out) bits = splitCfg f .header none bits [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [machine,splitCfg,stackVals,Turing.initList] <;> rfl
  | inr k =>
    by_cases h : k = f.k₀
    · subst k; simp [machine,splitCfg,stackVals,Turing.initList]
    · simp [machine,splitCfg,stackVals,Turing.initList,h]

set_option backward.isDefEq.respectTransparency false in
/-- Split the canonical pair prefix while preserving the complete encoded
witness. The first machine starts with the un-delimited payload in its input. -/
theorem split_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (payload tail : List Bool) :
    runSteps (machine f inp out).step (3*payload.length+2)
      (Turing.initList (machine f inp out) (BitstringEncoding.delimit payload ++ tail)) =
      some (coreEmbed f tail (Turing.initList f (payload.map inp.symm))) := by
  obtain ⟨v,hh⟩ := header_run f inp out payload tail [] [] none
  simp only [List.append_nil] at hh
  have hr := restore_run f inp out payload.reverse tail [] (some false)
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hr
  have hn : 3*payload.length+2 = 2*payload.length+((payload.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hh]
  change runSteps (machine f inp out).step ((payload.length+1)+1)
    (splitCfg f .header v (false::tail) payload.reverse []) = _
  rw [runSteps_front,header_false]
  exact hr

def postCfg (f : Turing.FinTM2) (l : Control) (v : Option Bool) (pair scratch : List Bool)
    (xs : List (f.Γ f.k₁)) : Cfg (Alphabet f) (Label f) (State f) :=
  ⟨some (.inl l),.inl v,stackVals f pair scratch (Turing.haltList f xs).stk⟩

set_option backward.isDefEq.respectTransparency false in
theorem move_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair scratch : List Bool) (a : f.Γ f.k₁) (xs : List (f.Γ f.k₁)) :
    (machine f inp out).step (postCfg f .move v pair scratch (a::xs)) =
      some (postCfg f .move (some (out a)) pair (out a::scratch) xs) := by
  have hout : (Turing.haltList f (a::xs)).stk f.k₁ = a::xs := by simp [Turing.haltList]
  change some (stepAux (program f inp out (.inl .move)) (.inl v)
    (stackVals f pair scratch (Turing.haltList f (a::xs)).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_cons,Option.map_some,decodeState,
    Option.isSome_some,Bool.cond_true,List.tail_cons,Option.getD_some]
  congr 1; congr 1
  rw [update_core,Shared.ComplexityBridge.TM2Compose.haltStacks_update,update_scratch]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem move_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair scratch : List Bool) :
    (machine f inp out).step (postCfg f .move v pair scratch []) = some (postCfg f .prefix none pair scratch []) := by
  have hout : (Turing.haltList f []).stk f.k₁ = [] := by simp [Turing.haltList]
  change some (stepAux (program f inp out (.inl .move)) (.inl v)
    (stackVals f pair scratch (Turing.haltList f []).stk)) = _
  simp only [program,stepAux,stackVals,hout,List.head?_nil,Option.map_none,decodeState,
    Option.isSome_none,Bool.cond_false,List.tail_nil]
  congr 1; congr 1
  rw [update_core,Shared.ComplexityBridge.TM2Compose.haltStacks_update]

set_option backward.isDefEq.respectTransparency false in
theorem prefix_cons (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (b : Bool) (pair scratch : List Bool) :
    (machine f inp out).step (postCfg f .prefix v pair (b::scratch) []) =
      some (postCfg f .prefix (some b) (true::b::pair) scratch []) := by
  change some (Cfg.mk (some (Sum.inl Control.prefix) : Option (Label f)) _
    (Function.update (Function.update (Function.update
      (stackVals f pair (b::scratch) (Turing.haltList f []).stk) (.inl true) scratch)
      (.inl false) (b::pair)) (.inl false) (true::b::pair))) = _
  congr 1; congr 1
  rw [update_scratch,update_pair,update_pair]

set_option backward.isDefEq.respectTransparency false in
theorem prefix_nil (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (v : Option Bool) (pair : List Bool) :
    (machine f inp out).step (postCfg f .prefix v pair [] []) = some (Turing.haltList (machine f inp out) pair) := by
  change some (Cfg.mk (none : Option (Label f)) (Sum.inl none : State f)
    (Function.update (stackVals f pair [] (Turing.haltList f []).stk) (.inl true) [])) = _
  rw [update_scratch,Shared.ComplexityBridge.TM2Compose.haltStacks_empty]
  congr 1; congr 1
  funext k
  cases k with
  | inl b => cases b <;> simp [stackVals,Turing.haltList,machine]
  | inr k => simp [stackVals,Turing.haltList,machine]

set_option backward.isDefEq.respectTransparency false in
theorem move_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (xs : List (f.Γ f.k₁)) (pair scratch : List Bool) (v : Option Bool) :
    ∃ v', runSteps (machine f inp out).step xs.length (postCfg f .move v pair scratch xs) =
      some (postCfg f .move v' pair (xs.reverse.map out ++ scratch) []) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by rfl⟩
  | cons a xs ih =>
    obtain ⟨v',h⟩ := ih (out a::scratch) (some (out a))
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,move_cons]
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using h

def blocks (bits : List Bool) : List Bool := bits.flatMap (fun b => [true,b])

theorem delimit_eq_blocks (bits : List Bool) : BitstringEncoding.delimit bits = blocks bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [BitstringEncoding.delimit,blocks,ih]

set_option backward.isDefEq.respectTransparency false in
theorem prefix_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (scratch pair : List Bool) (v : Option Bool) :
    runSteps (machine f inp out).step (scratch.length+1) (postCfg f .prefix v pair scratch []) =
      some (Turing.haltList (machine f inp out) (blocks scratch.reverse ++ pair)) := by
  induction scratch generalizing pair v with
  | nil =>
    change (machine f inp out).step (postCfg f .prefix v pair [] []) = _
    exact prefix_nil f inp out v pair
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,prefix_cons]
    simpa [List.reverse_cons,blocks,List.flatMap_append,List.append_assoc] using ih (true::b::pair) (some b)

set_option backward.isDefEq.respectTransparency false in
/-- Rebuild the exact delimited first encoding in front of the untouched
witness encoding, clearing the first machine's output and scratch stacks. -/
theorem post_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (bits tail : List Bool) :
    runSteps (machine f inp out).step (2*bits.length+2)
      (coreEmbed f tail (Turing.haltList f (bits.map out.symm))) =
      some (Turing.haltList (machine f inp out) (BitstringEncoding.delimit bits ++ tail)) := by
  obtain ⟨v,hm⟩ := move_run f inp out (bits.map out.symm) (false::tail) [] none
  have hbits : (bits.map out.symm).reverse.map out = bits.reverse := by simp [List.map_reverse,List.map_map]
  simp only [List.length_map,List.append_nil,hbits] at hm
  have hp := prefix_run f inp out bits.reverse (false::tail) none
  simp only [List.reverse_reverse,List.length_reverse] at hp
  have hn : 2*bits.length+2 = bits.length+((bits.length+1)+1) := by omega
  rw [hn]
  change runSteps (machine f inp out).step (bits.length+((bits.length+1)+1))
    (postCfg f .move none (false::tail) [] (bits.map out.symm)) = _
  rw [runSteps_add,hm]
  change runSteps (machine f inp out).step ((bits.length+1)+1)
    (postCfg f .move v (false::tail) bits.reverse []) = _
  rw [runSteps_front,move_nil]
  simpa [delimit_eq_blocks,List.append_assoc] using hp

set_option backward.isDefEq.respectTransparency false in
/-- Full pair-map execution: split, run the first-component machine, and
re-encode its output in front of the unchanged witness. -/
theorem pair_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (x w y : List Bool) (n : Nat)
    (hf : runSteps f.step n (Turing.initList f ((BitstringEncoding.bitEncode x).map inp.symm)) =
      some (Turing.haltList f ((BitstringEncoding.bitEncode y).map out.symm))) :
    runSteps (machine f inp out).step
      ((3*(BitstringEncoding.bitEncode x).length+2)+n+(2*(BitstringEncoding.bitEncode y).length+2))
      (Turing.initList (machine f inp out) (BitstringEncoding.bitEncode (x,w))) =
      some (Turing.haltList (machine f inp out) (BitstringEncoding.bitEncode (y,w))) := by
  let payload := BitstringEncoding.bitEncode x
  let tail := BitstringEncoding.bitEncode w
  let output := BitstringEncoding.bitEncode y
  have hsplit := split_run f inp out payload tail
  have hcore := core_run f inp out tail n (Turing.initList f (payload.map inp.symm))
    (Turing.haltList f (output.map out.symm)) hf
  have hpost := post_run f inp out output tail
  change runSteps (machine f inp out).step ((3*payload.length+2)+n+(2*output.length+2))
    (Turing.initList (machine f inp out) (BitstringEncoding.delimit payload ++ tail)) =
    some (Turing.haltList (machine f inp out) (BitstringEncoding.delimit output ++ tail))
  rw [show (3*payload.length+2)+n+(2*output.length+2) =
    (3*payload.length+2)+(n+(2*output.length+2)) by omega,runSteps_add,hsplit]
  change runSteps (machine f inp out).step (n+(2*output.length+2))
    (coreEmbed f tail (Turing.initList f (payload.map inp.symm))) = _
  rw [runSteps_add,hcore]
  exact hpost

def pairMap (F : List Bool → List Bool) : (List Bool × List Bool) → (List Bool × List Bool) :=
  fun a => (F a.1,a.2)

def pairAux (f : Turing.TM2ComputableAux Bool Bool) : Turing.TM2ComputableAux Bool Bool where
  tm := machine f.tm f.inputAlphabet f.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

noncomputable def timePolynomial (p : Polynomial Nat) (d : Nat) : Polynomial Nat :=
  Polynomial.C 5 * Polynomial.X + Polynomial.C (2*d+1) * p + Polynomial.C 4

theorem timePolynomial_eval (p : Polynomial Nat) (d n : Nat) :
    (timePolynomial p d).eval n = 5*n + (2*d+1)*p.eval n + 4 := by simp [timePolynomial]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical pair map applies a polynomial-time function to the first
component while preserving the witness, with a polynomial in the full pair
encoding length. -/
theorem pairMap_isPolyTime (F : List Bool → List Bool) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (pairMap F) := by
  rcases hF with ⟨hF⟩
  let f := hF.toTM2ComputableAux
  let c := pairAux f
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound f.tm
  refine ⟨{ toTM2ComputableAux := c, time := timePolynomial hF.time D, outputsFun := ?_ }⟩
  intro a
  rcases a with ⟨x,w⟩
  let r := hF.outputsFun x
  let n := r.steps
  let payload := BitstringEncoding.bitEncode x
  let result := BitstringEncoding.bitEncode (F x)
  let bits := BitstringEncoding.bitEncode (x,w)
  have hf : runSteps f.tm.step n (Turing.initList f.tm (payload.map f.inputAlphabet.symm)) =
      some (Turing.haltList f.tm (result.map f.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact r.evals_in_steps
  have hn : n ≤ hF.time.eval payload.length := r.steps_le_m
  have hlen : payload.length ≤ bits.length := by
    dsimp [payload,bits]
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length,Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  have htime := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono hF.time hlen
  have hn' : n ≤ hF.time.eval bits.length := le_trans hn htime
  have hstack := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length f.tm
    (payload.map f.inputAlphabet.symm) n (Turing.haltList f.tm (result.map f.outputAlphabet.symm)) hf f.tm.k₁
  have hresult : result.length ≤ payload.length+n*D := by simpa [Turing.haltList,D] using hstack
  have hmul : n*D ≤ hF.time.eval bits.length*D := Nat.mul_le_mul_right D hn'
  let t := (3*payload.length+2)+n+(2*result.length+2)
  have hrun := pair_run f.tm f.inputAlphabet f.outputAlphabet x w (F x) n hf
  refine ⟨⟨t,?_⟩,?_⟩
  · rw [runSteps_iterate] at hrun
    change (fun o => o.bind c.tm.step)^[t]
      (some (Turing.initList c.tm (bits.map id))) =
      some (Turing.haltList c.tm ((BitstringEncoding.bitEncode (pairMap F (x,w))).map id))
    simp only [List.map_id]
    exact hrun
  · change t ≤ (timePolynomial hF.time D).eval bits.length
    rw [timePolynomial_eval]
    dsimp [t]
    have hfactor : (2*D+1)*hF.time.eval bits.length = 2*(hF.time.eval bits.length*D) + hF.time.eval bits.length := by ring
    rw [hfactor]
    omega

/-- A polynomial-time list function has a polynomial raw output-length bound,
derived from its actual encoded machine run and finite push bound. -/
theorem output_length_poly (F : List Bool → List Bool) (hF : ComplexityTheory.IsPolyTime F) :
    ∃ p : Polynomial Nat, ∀ x, (F x).length ≤ p.eval x.length := by
  rcases hF with ⟨hF⟩
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound hF.tm
  let p : Polynomial Nat := Polynomial.C 3 * Polynomial.X +
    hF.time.comp (Polynomial.C 3 * Polynomial.X) * Polynomial.C D
  refine ⟨p,?_⟩
  intro x
  let r := hF.outputsFun x
  let n := r.steps
  have hr : runSteps hF.tm.step n (Turing.initList hF.tm ((BitstringEncoding.bitEncode x).map hF.inputAlphabet.symm)) =
      some (Turing.haltList hF.tm ((BitstringEncoding.bitEncode (F x)).map hF.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact r.evals_in_steps
  have hn : n ≤ hF.time.eval (BitstringEncoding.bitEncode x).length := r.steps_le_m
  have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length hF.tm
    ((BitstringEncoding.bitEncode x).map hF.inputAlphabet.symm) n
    (Turing.haltList hF.tm ((BitstringEncoding.bitEncode (F x)).map hF.outputAlphabet.symm)) hr hF.tm.k₁
  have hsize : (BitstringEncoding.bitEncode (F x)).length ≤ (BitstringEncoding.bitEncode x).length + n*D := by
    simpa [Turing.haltList,D] using hs
  simp only [Shared.ComplexityBridge.bitstring_list_encoded_length] at hn hsize
  have hm : n*D ≤ hF.time.eval (3*x.length)*D := Nat.mul_le_mul_right D hn
  change (F x).length ≤ p.eval x.length
  simp only [p,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_comp]
  omega

/-- Pulling a polynomial verifier back along a polynomial reduction preserves
its original cutoff before the outer witness bound is enlarged. -/
theorem np_pullback_closed : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.NP := by
  intro A B hB hred
  obtain ⟨F,hF,hAB⟩ := hred
  obtain ⟨q,R,hR,hB⟩ := hB
  obtain ⟨p,hp⟩ := output_length_poly F hF
  obtain ⟨terms,hterms⟩ := Shared.Codes.NumericPolynomial.polynomial_represented q
  let masked := Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask terms R
  have hmasked : ComplexityTheory.IsPolyTime masked :=
    Shared.ComplexityBridge.TM2CutoffCompose.cutoffMask_isPolyTime terms R hR
  have hpair : ComplexityTheory.IsPolyTime (pairMap F) := pairMap_isPolyTime F hF
  have hrelation : ComplexityTheory.IsPolyTime (fun a : List Bool × List Bool => masked (pairMap F a)) :=
    Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (pairMap F) masked hpair hmasked
  refine ⟨q.comp p, (fun a : List Bool × List Bool => masked (pairMap F a)), hrelation, ?_⟩
  intro x
  rw [hAB x]
  have hBx := hB (F x)
  change B (F x) = true ↔ ∃ w : List Bool, w.length ≤ q.eval (F x).length ∧ R (F x,w) = true at hBx
  change B (F x) = true ↔ ∃ w : List Bool, w.length ≤ (q.comp p).eval x.length ∧ masked (pairMap F (x,w)) = true
  rw [hBx]
  constructor
  · rintro ⟨w,hw,hr⟩
    refine ⟨w,?_,?_⟩
    · rw [Polynomial.eval_comp]
      exact le_trans hw (Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono q (hp x))
    · change Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask terms R (F x,w) = true
      simp only [Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask]
      rw [hterms (F x).length]
      simp [hw,hr]
  · rintro ⟨w,_,hr⟩
    have hmask : Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask terms R (F x,w) = true := hr
    simp only [Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask] at hmask
    rw [hterms (F x).length] at hmask
    by_cases hw : w.length ≤ q.eval (F x).length
    · exact ⟨w,hw,by simpa [hw] using hmask⟩
    · simp [hw] at hmask

/-- With concrete SAT completeness, good verifier candidates characterize
NP = coNP without a separate NP reduction-closure assumption. -/
theorem npconp_candidates_conditional
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat) :
    (∃ e, ∀ n, Shared.NPCONP.TM2Verifier.compare e n = true) ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
  calc
    (∃ e, ∀ n, Shared.NPCONP.TM2Verifier.compare e n = true) ↔
        (Shared.Beeping.Controller.system Shared.NPCONP.TM2Verifier.compare 0).EventuallySilent :=
      (Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good Shared.NPCONP.TM2Verifier.compare).symm
    _ ↔ ∃ v : Shared.NPCONP.TM2Verifier.Verifier, ∀ x, Shared.NPCONP.TM2Verifier.test v x = true :=
      Shared.NPCONP.TM2Verifier.controller_silent_iff
    _ ↔ Shared.ComplexityBridge.CNF.complementSat ∈ ComplexityTheory.NP :=
      Shared.ComplexityBridge.TM2CutoffCompose.good_verifier_iff_complement_in_NP
    _ ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
      rw [Shared.ComplexityBridge.CanonicalClasses.totalComplement_eq]
      exact (Shared.ComplexityBridge.CanonicalClasses.np_eq_conp_iff_complement_complete_in_np complete np_pullback_closed).symm

/-- A future finite machine still has to supply the comparison certificate;
SAT completeness remains the only class-theory hypothesis. -/
theorem npconp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2CutoffCompose.npconp_certified_conditional cert complete np_pullback_closed

namespace Fixtures
set_option maxRecDepth 10000 in
/-- Identity reduction on a nonempty input leaves a nonempty witness in place. -/
example : (runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 20
    (Turing.initList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool))
      (BitstringEncoding.bitEncode ([true],[false])))).map
    (fun q => (q.l.isNone,q.stk (.inl false))) = some (true,BitstringEncoding.bitEncode ([true],[false])) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inl false)))
    (runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 20
      (Turing.initList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool))
        (BitstringEncoding.bitEncode ([true],[false])))) : Option (Bool × List Bool)) = _
  decide

set_option maxRecDepth 10000 in
/-- Empty first component and nonempty witness cover the delimiter boundary. -/
example : (runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 5
    (Turing.initList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool))
      (BitstringEncoding.bitEncode (([] : List Bool),[true,false])))).map
    (fun q => (q.l.isNone,q.stk (.inl false))) = some (true,BitstringEncoding.bitEncode (([] : List Bool),[true,false])) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inl false)))
    (runSteps (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool)).step 5
      (Turing.initList (machine (Turing.idComputer Bool) (Equiv.refl Bool) (Equiv.refl Bool))
        (BitstringEncoding.bitEncode (([] : List Bool),[true,false])))) : Option (Bool × List Bool)) = _
  decide

set_option maxRecDepth 10000 in
/-- Nonidentity alphabet equivalences preserve the canonical pair encoding. -/
example : (runSteps (machine (Turing.idComputer Bool) Equiv.boolNot Equiv.boolNot).step 20
    (Turing.initList (machine (Turing.idComputer Bool) Equiv.boolNot Equiv.boolNot)
      (BitstringEncoding.bitEncode ([true],[false])))).map
    (fun q => (q.l.isNone,q.stk (.inl false))) = some (true,BitstringEncoding.bitEncode ([true],[false])) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inl false)))
    (runSteps (machine (Turing.idComputer Bool) Equiv.boolNot Equiv.boolNot).step 20
      (Turing.initList (machine (Turing.idComputer Bool) Equiv.boolNot Equiv.boolNot)
        (BitstringEncoding.bitEncode ([true],[false])))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2PairMap
