import Shared.ComplexityBridge.TM2Complement

namespace Shared.ComplexityBridge.TM2PairStrip
open Turing.TM2 Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

inductive Label where
  | header | data | discard | restore | done
  deriving DecidableEq

instance : Fintype Label := Fintype.ofList [.header,.data,.discard,.restore,.done] (by intro x; cases x <;> simp)

def program (ks symbols : Nat) : Label → Stmt (Alphabet ks symbols) Label (Option Bool)
  | .header => .pop (.inl false) (fun _ h => h)
      (.branch (fun v => v == some true) (.goto (fun _ => .data)) (.goto (fun _ => .discard)))
  | .data => .pop (.inl false) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inl true) (fun v => v.getD false) (.goto (fun _ => .header)))
        (.goto (fun _ => .discard)))
  | .discard => .pop (.inl false) (fun _ h => h)
      (.branch Option.isSome (.goto (fun _ => .discard)) (.goto (fun _ => .restore)))
  | .restore => .pop (.inl true) (fun _ h => h)
      (.branch Option.isSome
        (.push (.inl false) (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def stripper (ks symbols : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label
  main := .header
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks symbols

def cfg (ks symbols : Nat) (l : Label) (v : Option Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) : (stripper ks symbols).Cfg :=
  ⟨some l,v,embedStacks ks symbols a b S⟩

theorem header_true (ks symbols : Nat) (v : Option Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .header v (true::a) b S) =
      some (cfg ks symbols .data (some true) a b S) := by
  change some (Cfg.mk (some Label.data) (some true)
      (Function.update (embedStacks ks symbols (true::a) b S) (.inl false) a)) =
    some (Cfg.mk (some Label.data) (some true) (embedStacks ks symbols a b S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem header_false (ks symbols : Nat) (v : Option Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .header v (false::a) b S) =
      some (cfg ks symbols .discard (some false) a b S) := by
  change some (Cfg.mk (some Label.discard) (some false)
      (Function.update (embedStacks ks symbols (false::a) b S) (.inl false) a)) =
    some (Cfg.mk (some Label.discard) (some false) (embedStacks ks symbols a b S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem data_cons (ks symbols : Nat) (v : Option Bool) (x : Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .data v (x::a) b S) =
      some (cfg ks symbols .header (some x) a (x::b) S) := by
  change some (Cfg.mk (some Label.header) (some x)
      (Function.update (Function.update (embedStacks ks symbols (x::a) b S) (.inl false) a) (.inl true) (x::b))) =
    some (Cfg.mk (some Label.header) (some x) (embedStacks ks symbols a (x::b) S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem discard_cons (ks symbols : Nat) (v : Option Bool) (x : Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .discard v (x::a) b S) =
      some (cfg ks symbols .discard (some x) a b S) := by
  change some (Cfg.mk (some Label.discard) (some x)
      (Function.update (embedStacks ks symbols (x::a) b S) (.inl false) a)) =
    some (Cfg.mk (some Label.discard) (some x) (embedStacks ks symbols a b S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem discard_nil (ks symbols : Nat) (v : Option Bool) (b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .discard v [] b S) =
      some (cfg ks symbols .restore none [] b S) := by
  change some (Cfg.mk (some Label.restore) none
      (Function.update (embedStacks ks symbols [] b S) (.inl false) [])) =
    some (Cfg.mk (some Label.restore) none (embedStacks ks symbols [] b S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem restore_cons (ks symbols : Nat) (v : Option Bool) (x : Bool) (a b : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .restore v a (x::b) S) =
      some (cfg ks symbols .restore (some x) (x::a) b S) := by
  change some (Cfg.mk (some Label.restore) (some x)
      (Function.update (Function.update (embedStacks ks symbols a (x::b) S) (.inl true) b) (.inl false) (x::a))) =
    some (Cfg.mk (some Label.restore) (some x) (embedStacks ks symbols (x::a) b S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem restore_nil (ks symbols : Nat) (v : Option Bool) (a : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (stripper ks symbols).step (cfg ks symbols .restore v a [] S) =
      some (cfg ks symbols .done none a [] S) := by
  change some (Cfg.mk (some Label.done) none
      (Function.update (embedStacks ks symbols a [] S) (.inl true) [])) =
    some (Cfg.mk (some Label.done) none (embedStacks ks symbols a [] S))
  congr 1
  congr 1
  funext k
  cases k with
  | inl j => cases j <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

/-- Read each delimiter marker and payload bit in two blocks, collecting the
payload in reverse order while leaving the trailing data untouched. -/
theorem header_run (ks symbols : Nat) (payload tail scratch : List Bool) (v : Option Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (stripper ks symbols).step (2*payload.length)
      (cfg ks symbols .header v (BitstringEncoding.delimit payload ++ tail) scratch S) =
        some (cfg ks symbols .header v' (false::tail) (payload.reverse ++ scratch) S) := by
  induction payload generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (x::scratch) (some x)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(xs.length+1) = (2*xs.length+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps (stripper ks symbols).step (2*xs.length+1)
      (cfg ks symbols .data (some true) (x::(BitstringEncoding.delimit xs ++ tail)) scratch S) = _
    rw [runSteps_front,data_cons]
    simpa [List.reverse_cons,List.append_assoc] using hv

/-- Discard the complete second component, one bit per block. -/
theorem discard_run (ks symbols : Nat) (tail scratch : List Bool) (v : Option Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (stripper ks symbols).step tail.length
      (cfg ks symbols .discard v tail scratch S) =
        some (cfg ks symbols .discard v' [] scratch S) := by
  induction tail generalizing v with
  | nil => exact ⟨v,rfl⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,discard_cons]
    exact hv

/-- Reverse the saved payload back to the input stack. -/
theorem restore_run (ks symbols : Nat) (scratch input : List Bool) (v : Option Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (stripper ks symbols).step scratch.length
      (cfg ks symbols .restore v input scratch S) =
        some (cfg ks symbols .restore v' (scratch.reverse ++ input) [] S) := by
  induction scratch generalizing input v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (x::input) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using hv

theorem initial_eq (ks symbols : Nat) (bits : List Bool) :
    Turing.initList (stripper ks symbols) bits = cfg ks symbols .header none bits [] (fun _ => []) := by
  change Cfg.mk (some Label.header) none _ = Cfg.mk (some Label.header) none (embedStacks ks symbols bits [] (fun _ => []))
  congr 1
  funext k
  cases k with
  | inl b =>
    cases b <;> simp [stripper,embedStacks]
    rfl
  | inr j => simp [stripper,embedStacks]

/-- Exact whole-block cost, including delimiter, trailing-input removal, and
restoring the payload. The extra finite core stacks remain untouched. -/
theorem strip_correct (ks symbols : Nat) (payload tail : List Bool) :
    runSteps (stripper ks symbols).step (3*payload.length+tail.length+3)
      (Turing.initList (stripper ks symbols) (BitstringEncoding.delimit payload ++ tail)) =
        some (cfg ks symbols .done none payload [] (fun _ => [])) := by
  obtain ⟨v,hheader⟩ := header_run ks symbols payload tail [] none (fun _ => [])
  simp only [List.append_nil] at hheader
  have hh : runSteps (stripper ks symbols).step (2*payload.length+1)
      (cfg ks symbols .header none (BitstringEncoding.delimit payload ++ tail) [] (fun _ => [])) =
        some (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => [])) := by
    rw [runSteps_add,hheader]
    change (stripper ks symbols).step (cfg ks symbols .header v (false::tail) payload.reverse (fun _ => [])) = _
    exact header_false ks symbols v tail payload.reverse (fun _ => [])
  obtain ⟨v',hdiscard⟩ := discard_run ks symbols tail payload.reverse (some false) (fun _ => [])
  have hd : runSteps (stripper ks symbols).step (tail.length+1)
      (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => [])) =
        some (cfg ks symbols .restore none [] payload.reverse (fun _ => [])) := by
    rw [runSteps_add,hdiscard]
    change (stripper ks symbols).step (cfg ks symbols .discard v' [] payload.reverse (fun _ => [])) = _
    exact discard_nil ks symbols v' payload.reverse (fun _ => [])
  obtain ⟨v'',hrestore⟩ := restore_run ks symbols payload.reverse [] none (fun _ => [])
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  have hr : runSteps (stripper ks symbols).step (payload.length+1)
      (cfg ks symbols .restore none [] payload.reverse (fun _ => [])) =
        some (cfg ks symbols .done none payload [] (fun _ => [])) := by
    rw [runSteps_add,hrestore]
    change (stripper ks symbols).step (cfg ks symbols .restore v'' payload [] (fun _ => [])) = _
    exact restore_nil ks symbols v'' payload (fun _ => [])
  rw [initial_eq]
  have hn : 3*payload.length+tail.length+3 = ((2*payload.length+1)+(tail.length+1))+(payload.length+1) := by omega
  rw [hn,runSteps_add,runSteps_add,hh]
  change (runSteps (stripper ks symbols).step (tail.length+1)
    (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => []))).bind _ = _
  rw [hd]
  exact hr

/-- On actual library pair encodings the prelude costs exactly
`9|x| + 3|w| + 3` blocks and preserves the whole encoded first component. -/
theorem strip_pair (ks symbols : Nat) (x w : List Bool) :
    runSteps (stripper ks symbols).step (9*x.length+3*w.length+3)
      (Turing.initList (stripper ks symbols) (BitstringEncoding.bitEncode (x,w))) =
        some (cfg ks symbols .done none (BitstringEncoding.bitEncode x) [] (fun _ => [])) := by
  have h := strip_correct ks symbols (BitstringEncoding.bitEncode x) (BitstringEncoding.bitEncode w)
  have he : BitstringEncoding.bitEncode (x,w) =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w := rfl
  rw [← he,Shared.ComplexityBridge.bitstring_list_encoded_length,
    Shared.ComplexityBridge.bitstring_list_encoded_length] at h
  have ht : 3*(3*x.length)+3*w.length+3 = 9*x.length+3*w.length+3 := by omega
  rw [ht] at h
  exact h

example : (runSteps (stripper 1 2).step 3
    (Turing.initList (stripper 1 2) (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))).map
      (fun c => c.stk (.inl false)) = some [] := by
  change (Option.map (fun c => c.stk (.inl false)) (runSteps (stripper 1 2).step 3
    (Turing.initList (stripper 1 2) (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))) : Option (List Bool)) = some []
  decide

example : (runSteps (stripper 1 2).step 24
    (Turing.initList (stripper 1 2) (BitstringEncoding.bitEncode ([true,false],[true])))).map
      (fun c => c.stk (.inl false)) = some (BitstringEncoding.bitEncode [true,false]) := by
  change (Option.map (fun c => c.stk (.inl false)) (runSteps (stripper 1 2).step 24
    (Turing.initList (stripper 1 2) (BitstringEncoding.bitEncode ([true,false],[true])))) : Option (List Bool)) =
      some (BitstringEncoding.bitEncode [true,false])
  decide

end Shared.ComplexityBridge.TM2PairStrip
