import Shared.Beeping.NPcoNP.GrammarGraph284
/-! A finite, explicit-stack expansion machine and its correspondence with
`Grammar284.expand`. Each successful step processes exactly one pending
frame. No producer-specific trace or graph identity is asserted here. -/
namespace Shared.Beeping.NPcoNP.Grammar284.ExpandSteps
structure Frame where
  fuel : Nat
  leaf : Leaf
  path : Path
  ancestors : List Nat

structure State where
  pending : List Frame
  acc : Expansion

def denoteFrames (nodes : Array (Leaf × Leaf)) : List Frame → Expansion → Option Expansion
  | [], e => some e
  | f::fs, e => do
    let e' ← expand nodes f.fuel f.leaf f.path f.ancestors e
    denoteFrames nodes fs e'

def denote (nodes : Array (Leaf × Leaf)) (s : State) : Option Expansion :=
  denoteFrames nodes s.pending s.acc

def step (nodes : Array (Leaf × Leaf)) (s : State) : Option State := do
  let f :: fs := s.pending | none
  let fuel + 1 := f.fuel | none
  let e := {s.acc with starts := s.acc.starts.push (f.path,s.acc.leaves.size)}
  match f.leaf with
  | .op name => some ⟨fs, { e with leaves := e.leaves.push (f.path,name) }⟩
  | .node i => do
      if f.ancestors.contains i then none else
        let (a,b) ← nodes[i]?
        pure ⟨⟨fuel,a,f.path ++ [false],i::f.ancestors⟩ :: ⟨fuel,b,f.path ++ [true],i::f.ancestors⟩ :: fs,e⟩

lemma denote_step (nodes : Array (Leaf × Leaf)) (s t : State)
    (h : step nodes s = some t) : denote nodes s = denote nodes t := by
  rcases s with ⟨pending, acc⟩
  cases pending with
  | nil => simp [step] at h
  | cons f fs =>
    rcases f with ⟨fuel, leaf, path, ancestors⟩
    cases fuel with
    | zero => simp [step] at h
    | succ fuel =>
      cases leaf with
      | op name =>
        simp only [step, Option.some.injEq] at h
        subst t
        rfl
      | node i =>
        by_cases hc : i ∈ ancestors
        · simp [step, hc] at h
        · cases hv : nodes[i]? with
          | none => simp [step, hc, hv] at h
          | some pair =>
            rcases pair with ⟨a,b⟩
            simp [step, hc, hv] at h
            rcases h with ⟨_, rfl⟩
            simp [denote, denoteFrames, expand, hc, hv, Option.bind_assoc]

def steps (nodes : Array (Leaf × Leaf)) : Nat → State → Option State
  | 0,s => some s
  | n+1,s => do
      let t ← step nodes s
      steps nodes n t

lemma denote_steps (nodes : Array (Leaf × Leaf)) (n : Nat) (s t : State)
    (h : steps nodes n s = some t) : denote nodes s = denote nodes t := by
  induction n generalizing s with
  | zero => simp [steps] at h; subst t; rfl
  | succ n ih =>
    simp only [steps, Option.bind_eq_bind] at h
    cases hs : step nodes s with
    | none => simp [hs] at h
    | some u =>
      have he := denote_step nodes s u hs
      have hr := ih u (by simpa [hs] using h)
      exact he.trans hr

lemma certify (nodes : Array (Leaf × Leaf)) (f : Frame) (n : Nat) (e : Expansion)
    (h : steps nodes n ⟨[f], {}⟩ = some ⟨[],e⟩) :
    expand nodes f.fuel f.leaf f.path f.ancestors {} = some e := by
  have he := denote_steps nodes n _ _ h
  simpa [denote, denoteFrames] using he
end Shared.Beeping.NPcoNP.Grammar284.ExpandSteps
