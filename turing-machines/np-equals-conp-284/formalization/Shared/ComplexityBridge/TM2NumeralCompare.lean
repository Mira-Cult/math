import Shared.ComplexityBridge.NumeralCompare

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2NumeralCompare
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.NumeralNormalization Shared.ComplexityBridge.NumeralCompare
inductive Stack where | left | right
  deriving DecidableEq
inductive Label where | scan | checkLeft | checkRight | accept | reject
  deriving DecidableEq
inductive Action where | next | checkLeft | checkRight | accept | reject
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.left,.right] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.scan,.checkLeft,.checkRight,.accept,.reject] (by intro l; cases l <;> simp)
abbrev State := Option Bool × Option Bool × Option Bool

def action (s : State) : Action :=
  match s.2.1,s.2.2 with
  | some a,some b => if a == b then .next else .reject
  | none,none => .accept
  | none,some b => if s.1 == some false && b then .checkRight else .reject
  | some a,none => if s.1 == some false && a then .checkLeft else .reject

def program : Label → Stmt (fun _ : Stack => Bool) Label State
  | .scan => .pop .left (fun s h => (s.1,h,s.2.2))
      (.pop .right (fun s h => (s.1,s.2.1,h))
        (.branch (fun s => action s == .next)
          (.load (fun s => (s.2.1,none,none)) (.goto (fun _ => .scan)))
          (.branch (fun s => action s == .accept) (.goto (fun _ => .accept))
            (.branch (fun s => action s == .checkLeft) (.goto (fun _ => .checkLeft))
              (.branch (fun s => action s == .checkRight) (.goto (fun _ => .checkRight))
                (.goto (fun _ => .reject)))))))
  | .checkLeft => .pop .left (fun s h => (s.1,h,s.2.2))
      (.branch (fun s => s.2.1.isSome) (.goto (fun _ => .reject)) (.goto (fun _ => .accept)))
  | .checkRight => .pop .right (fun s h => (s.1,s.2.1,h))
      (.branch (fun s => s.2.2.isSome) (.goto (fun _ => .reject)) (.goto (fun _ => .accept)))
  | .accept => .goto (fun _ => .accept)
  | .reject => .goto (fun _ => .reject)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .right
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := State
  initialState := (none,none,none)
  m := program

def stackVals (left right : List Bool) : Stack → List Bool
  | .left => left | .right => right

def cfg (l : Label) (v : State) (left right : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals left right⟩

theorem scan_equal (last : Option Bool) (b : Bool) (xs ys : List Bool) :
    machine.step (cfg .scan (last,none,none) (b::xs) (b::ys)) =
      some (cfg .scan (some b,none,none) xs ys) := by
  cases b <;>
    change some (Cfg.mk (some Label.scan) _ (Function.update (Function.update (stackVals (_::xs) (_::ys)) .left xs) .right ys)) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem scan_different (last : Option Bool) (a b : Bool) (xs ys : List Bool) (h : a ≠ b) :
    machine.step (cfg .scan (last,none,none) (a::xs) (b::ys)) =
      some (cfg .reject (last,some a,some b) xs ys) := by
  cases a <;> cases b
  all_goals first
    | contradiction
    | change some (Cfg.mk (some Label.reject) _ (Function.update (Function.update (stackVals (_::xs) (_::ys)) .left xs) .right ys)) = _
      congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_empty (last : Option Bool) :
    machine.step (cfg .scan (last,none,none) [] []) = some (cfg .accept (last,none,none) [] []) := by
  change some (Cfg.mk (some Label.accept) (last,none,none)
    (Function.update (Function.update (stackVals [] []) .left []) .right [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_left_end (last : Option Bool) (b : Bool) (ys : List Bool) :
    machine.step (cfg .scan (last,none,none) [] (b::ys)) =
      some (cfg (if last = some false ∧ b = true then .checkRight else .reject) (last,none,some b) [] ys) := by
  cases last with
  | none => cases b <;>
      change some (Cfg.mk _ _ (Function.update (Function.update (stackVals [] (_::ys)) .left []) .right ys)) = _ <;>
      congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]
  | some a => cases a <;> cases b <;>
      change some (Cfg.mk _ _ (Function.update (Function.update (stackVals [] (_::ys)) .left []) .right ys)) = _ <;>
      congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem scan_right_end (last : Option Bool) (a : Bool) (xs : List Bool) :
    machine.step (cfg .scan (last,none,none) (a::xs) []) =
      some (cfg (if last = some false ∧ a = true then .checkLeft else .reject) (last,some a,none) xs []) := by
  cases last with
  | none => cases a <;>
      change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (_::xs) []) .left xs) .right [])) = _ <;>
      congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]
  | some b => cases b <;> cases a <;>
      change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (_::xs) []) .left xs) .right [])) = _ <;>
      congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

theorem check_right_nil (last : Option Bool) :
    machine.step (cfg .checkRight (last,none,some true) [] []) = some (cfg .accept (last,none,none) [] []) := by
  change some (Cfg.mk (some Label.accept) (last,none,none) (Function.update (stackVals [] []) .right [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem check_right_cons (last : Option Bool) (b : Bool) (ys : List Bool) :
    machine.step (cfg .checkRight (last,none,some true) [] (b::ys)) = some (cfg .reject (last,none,some b) [] ys) := by
  change some (Cfg.mk (some Label.reject) (last,none,some b) (Function.update (stackVals [] (b::ys)) .right ys)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem check_left_nil (last : Option Bool) :
    machine.step (cfg .checkLeft (last,some true,none) [] []) = some (cfg .accept (last,none,none) [] []) := by
  change some (Cfg.mk (some Label.accept) (last,none,none) (Function.update (stackVals [] []) .left [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem check_left_cons (last : Option Bool) (b : Bool) (xs : List Bool) :
    machine.step (cfg .checkLeft (last,some true,none) (b::xs) []) = some (cfg .reject (last,some b,none) xs []) := by
  change some (Cfg.mk (some Label.reject) (last,some b,none) (Function.update (stackVals (b::xs) []) .left xs)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

set_option backward.isDefEq.respectTransparency false in
/-- The comparator always reaches accept or reject, and its answer is exactly
whether the two normalized suffixes agree. `last` summarizes a common prefix. -/
theorem scan_correct (xs ys : List Bool) (last : Option Bool) :
    ∃ t ≤ max xs.length ys.length+2, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .scan (last,none,none) xs ys) = some q ∧
      q.l = some (if suffix last xs = suffix last ys then .accept else .reject) := by
  induction xs generalizing ys last with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨1,by simp,cfg .accept (last,none,none) [] [],scan_empty last,?_⟩
      simp [cfg]
    | cons b ys =>
      by_cases h : last = some false ∧ b = true
      · rcases h with ⟨rfl,rfl⟩
        cases ys with
        | nil =>
          refine ⟨2,by simp,cfg .accept (some false,none,none) [] [],?_,?_⟩
          · rw [show 2 = 1+1 by decide,runSteps_front,scan_left_end]
            exact check_right_nil (some false)
          · simp [cfg,suffix_nil_cons_iff]
        | cons c ys =>
          refine ⟨2,by simp,cfg .reject (some false,none,some c) [] ys,?_,?_⟩
          · rw [show 2 = 1+1 by decide,runSteps_front,scan_left_end]
            exact check_right_cons (some false) c ys
          · simp [cfg,suffix_nil_cons_iff]
      · refine ⟨1,by simp,cfg .reject (last,none,some b) [] ys,?_,?_⟩
        · change machine.step (cfg .scan (last,none,none) [] (b::ys)) = _
          simpa [h] using scan_left_end last b ys
        · have hn : suffix last [] ≠ suffix last (b::ys) := by
            intro he
            have hh := (suffix_nil_cons_iff last b ys).1 he
            exact h ⟨hh.1,hh.2.1⟩
          simp [cfg,hn]
  | cons a xs ih =>
    cases ys with
    | nil =>
      by_cases h : last = some false ∧ a = true
      · rcases h with ⟨rfl,rfl⟩
        cases xs with
        | nil =>
          refine ⟨2,by simp,cfg .accept (some false,none,none) [] [],?_,?_⟩
          · rw [show 2 = 1+1 by decide,runSteps_front,scan_right_end]
            exact check_left_nil (some false)
          · have hh := (suffix_nil_cons_iff (some false) true []).2 ⟨rfl,rfl,rfl⟩
            simp [cfg,hh.symm]
        | cons c xs =>
          refine ⟨2,by simp,cfg .reject (some false,some c,none) xs [],?_,?_⟩
          · rw [show 2 = 1+1 by decide,runSteps_front,scan_right_end]
            exact check_left_cons (some false) c xs
          · have hn : suffix (some false) (true::c::xs) ≠ suffix (some false) [] := by
              intro he
              have hh := (suffix_nil_cons_iff (some false) true (c::xs)).1 he.symm
              simp at hh
            simp [cfg,hn]
      · refine ⟨1,by simp,cfg .reject (last,some a,none) xs [],?_,?_⟩
        · change machine.step (cfg .scan (last,none,none) (a::xs) []) = _
          simpa [h] using scan_right_end last a xs
        · have hn : suffix last (a::xs) ≠ suffix last [] := by
            intro he
            have hh := (suffix_nil_cons_iff last a xs).1 he.symm
            exact h ⟨hh.1,hh.2.1⟩
          simp [cfg,hn]
    | cons b ys =>
      by_cases he : a = b
      · subst b
        obtain ⟨t,ht,q,hr,hq⟩ := ih ys (some a)
        refine ⟨t+1,?_,q,?_,?_⟩
        · simp only [List.length_cons] at *
          omega
        · rw [runSteps_front,scan_equal]
          exact hr
        · simpa [suffix_cons] using hq
      · refine ⟨1,by simp,cfg .reject (last,some a,some b) xs ys,scan_different last a b xs ys he,?_⟩
        have hn : suffix last (a::xs) ≠ suffix last (b::ys) := by simp [suffix_cons,he]
        simp [cfg,hn]

set_option backward.isDefEq.respectTransparency false in
/-- The starting configuration stores the two raw encodings on separate
stacks; every comparison terminates in linear time and agrees with mathlib's
actual natural-number decoder, including noncanonical encodings. -/
theorem compare_progress (xs ys : List Bool) :
    ∃ t ≤ max xs.length ys.length+2, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .scan (none,none,none) xs ys) = some q ∧
      q.l = some (if Computability.decodeNat xs = Computability.decodeNat ys then .accept else .reject) := by
  obtain ⟨t,ht,q,hr,hq⟩ := scan_correct xs ys none
  refine ⟨t,ht,q,hr,?_⟩
  by_cases h : Computability.decodeNat xs = Computability.decodeNat ys
  · have hn : normalize xs = normalize ys := (decode_eq_iff_normalize_eq xs ys).1 h
    simp only [h,if_true]
    simp only [suffix_initial,hn,if_true] at hq
    exact hq
  · have hn : normalize xs ≠ normalize ys := by
      intro he
      exact h ((decode_eq_iff_normalize_eq xs ys).2 he)
    simp only [h,if_false]
    simp only [suffix_initial,hn,if_false] at hq
    exact hq

namespace Fixtures
/-- The implicit trailing one makes these distinct bitstrings equal. -/
example : (runSteps machine.step 3 (cfg .scan (none,none,none) [false] [false,true])).map
    (fun q => match q.l with | some .accept => true | _ => false) = some true := by decide
example : (runSteps machine.step 1 (cfg .scan (none,none,none) [false] [true])).map
    (fun q => match q.l with | some .reject => true | _ => false) = some true := by decide
example : (runSteps machine.step 1 (cfg .scan (none,none,none) [] [true])).map
    (fun q => match q.l with | some .reject => true | _ => false) = some true := by decide
example : (runSteps machine.step 1 (cfg .scan (none,none,none) [] [])).map
    (fun q => match q.l with | some .accept => true | _ => false) = some true := by decide
end Fixtures

end Shared.ComplexityBridge.TM2NumeralCompare
