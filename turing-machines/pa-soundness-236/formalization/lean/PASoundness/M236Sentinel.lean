import PASoundness.M236PathSuccessor
/-! The outer sentinel resets to an empty residual path. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control

/-- A successful pop has exactly the finite run and separator it reports. -/
theorem pop_sound (xs : List Bool) (n : Nat) (rest : List Bool)
    (h : pop xs = some (n, rest)) : xs = List.replicate n true ++ false :: rest := by
  induction xs generalizing n rest with
  | nil => simp [pop] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp [pop] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hp : pop xs with
      | none => simp [pop, hp] at h
      | some p =>
        rcases p with ⟨m, tail⟩
        simp [pop, hp] at h
        rcases h with ⟨rfl, rfl⟩
        rw [ih m tail hp]
        simp [List.replicate_succ]

/-- A successor reaching the outer sentinel has no residual path. -/
theorem sentinel_factor (pcHead word suffix pcTail : List Bool)
    (hin : [true, true, false] ++ word = pcHead ++ false :: suffix)
    (hout : pcHead ++ [true] = [true, true, true] ++ pcTail) : pcTail = [] := by
  cases pcHead with
  | nil => simp at hout
  | cons a xs =>
    cases a with
    | false => simp at hout
    | true =>
      cases xs with
      | nil => simp at hout
      | cons b ys =>
        cases b with
        | false => simp at hout
        | true =>
          cases ys with
          | nil => simpa using hout.symm
          | cons c zs =>
            cases c with
            | false => simp at hout
            | true => simp at hin

/-- A normal return reaching the outer sentinel has no residual path. -/
theorem decodeOne_sentinel (word pcTail : List Bool)
    (h : decodeOne word = some (true, pcTail)) : pcTail = [] := by
  have hsuccess := successor_of_decodeOne word true pcTail h
  have hsuccess' : successorPath ([true, true, false] ++ word) =
      some ([true, true, true] ++ pcTail) := hsuccess
  unfold successorPath at hsuccess'
  change (do let (_, rest) ← pop ([true, true, false] ++ word).reverse
             pure (rest.reverse ++ [true])) = _ at hsuccess'
  cases hp : pop ([true, true, false] ++ word).reverse with
  | none => rw [hp] at hsuccess'; contradiction
  | some p =>
    rcases p with ⟨scratch, rest⟩
    rw [hp] at hsuccess'
    simp at hsuccess'
    have hs := pop_sound ([true, true, false] ++ word).reverse scratch rest hp
    have hin := congrArg List.reverse hs
    simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append] at hin
    exact sentinel_factor rest.reverse word (List.replicate scratch true) pcTail hin hsuccess' 

/-- A zero-branch return reaching the outer sentinel restarts with no tail. -/
theorem decodeZero_sentinel (word pcTail : List Bool)
    (h : decodeZero word = some (true, pcTail)) : pcTail = [] := by
  have hsuccess := successor_of_decodeZero word true pcTail h
  have hsuccess' : skipSuccessorPath ([true, true, false] ++ word) =
      some ([true, true, true] ++ pcTail) := hsuccess
  unfold skipSuccessorPath at hsuccess'
  cases hp1 : pop ([true, true, false] ++ word).reverse with
  | none => rw [hp1] at hsuccess'; contradiction
  | some p =>
    rcases p with ⟨scratch1, rest1⟩
    rw [hp1] at hsuccess'
    cases hp2 : pop rest1 with
    | none => simp [hp2] at hsuccess'
    | some q =>
      rcases q with ⟨scratch2, rest2⟩
      simp [hp2] at hsuccess'
      have hs1 := pop_sound ([true, true, false] ++ word).reverse scratch1 rest1 hp1
      have hs2 := pop_sound rest1 scratch2 rest2 hp2
      rw [hs2] at hs1
      have hin := congrArg List.reverse hs1
      simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append] at hin
      exact sentinel_factor rest2.reverse word
        (List.replicate scratch2 true ++ false :: List.replicate scratch1 true) pcTail hin hsuccess'

/-- The physical normal-return successor can select the outer sentinel only
with an empty residual path, exactly the root restart form. -/
theorem successor_sentinel (word pcTail : List Bool)
    (h : successorPath ([true, true, false] ++ word) = some ([true, true, true] ++ pcTail)) :
    pcTail = [] := by
  have hdec : decodeOne word = some (true, pcTail) := by
    rw [decodeOne_successor, h]
    rfl
  exact decodeOne_sentinel word pcTail hdec

/-- The same root-restart property holds when the zero branch skips one zero. -/
theorem skipSuccessor_sentinel (word pcTail : List Bool)
    (h : skipSuccessorPath ([true, true, false] ++ word) = some ([true, true, true] ++ pcTail)) :
    pcTail = [] := by
  have hdec : decodeZero word = some (true, pcTail) := by
    rw [decodeZero_successor, h]
    rfl
  exact decodeZero_sentinel word pcTail hdec
end PASoundness.M236.Control
