import Shared.Codes.FinitePrograms
import Mathlib.Computability.TuringMachine.Tape

/-! A regression for the finite-program tape boundary. The raw lists `[]`
and `[false]` initialize the same tape, while the canonical CNF language
assigns them different answers. A correct SAT candidate must therefore use
an input encoding that preserves the distinction. -/
namespace Shared.Codes.RawInputCollision
open Shared.Codes.FinitePrograms Turing

/-- A deterministic finite program cannot return two different results from
the same initial configuration, even with different clocks. -/
theorem bounded_same_initial (p : Program) (x y : List Bool) (a b : Nat) (u v : Bool)
    (hinit : initial x = initial y)
    (hx : bounded p x a = some u) (hy : bounded p y b = some v) : u = v := by
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result p x a u).1 hx
  obtain ⟨s,hs,hq⟩ := (bounded_iff_result p y b v).1 hy
  have hr' := run_result_stable p (initial x) (Nat.le_max_left t s) hr
  have hq' := run_result_stable p (initial y) (Nat.le_max_right t s) hq
  rw [hinit] at hr'
  have heq := hr'.symm.trans hq'
  exact Sum.inl.inj (Option.some.inj heq)

theorem empty_false_same_initial : initial [] = initial [false] := rfl

theorem sat_empty : Shared.ComplexityBridge.CNF.sat [] = true := by decide
theorem sat_false : Shared.ComplexityBridge.CNF.sat [false] = false := by decide

/-- The old raw-input SAT candidate specification has no inhabitant, even
if the two inputs are tested with different clock values. -/
theorem no_raw_sat_candidate : ¬ ∃ c : Candidate,
    ∀ input, evaluate c input = some (Shared.ComplexityBridge.CNF.sat input) := by
  rintro ⟨c,h⟩
  have hx := h []
  have hy := h [false]
  rw [sat_empty] at hx
  rw [sat_false] at hy
  have hbad := bounded_same_initial c.2 [] [false] (clock [] c.1) (clock [false] c.1)
    true false empty_false_same_initial hx hy
  contradiction

/-- The canonical list encoding distinguishes the counterexample at the
first tape cell. This does not by itself prove the full simulation bridge. -/
theorem canonical_input_distinguishes :
    initial (BitstringEncoding.bitEncode ([] : List Bool)) ≠
      initial (BitstringEncoding.bitEncode ([false] : List Bool)) := by decide

/-- A canonical Boolean-list encoding cannot acquire a valid new encoding
by appending only blank cells. -/
theorem no_extension (x y : List Bool) (n : Nat)
    (h : BitstringEncoding.bitEncode y = BitstringEncoding.bitEncode x ++ List.replicate n false) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b ys =>
      change [true,b,false] ++ BitstringEncoding.bitEncode ys = ([] : List Bool) ++ List.replicate n false at h
      cases n <;> simp [List.replicate_succ] at h
  | cons a xs ih =>
    cases y with
    | nil =>
      change ([] : List Bool) = ([true,a,false] ++ BitstringEncoding.bitEncode xs) ++ List.replicate n false at h
      simp at h
    | cons b ys =>
      change [true,b,false] ++ BitstringEncoding.bitEncode ys =
        ([true,a,false] ++ BitstringEncoding.bitEncode xs) ++ List.replicate n false at h
      simp only [List.cons_append,List.nil_append,List.cons.injEq,true_and] at h
      obtain ⟨hab,htail⟩ := h
      cases hab
      have hxy := ih ys htail
      cases hxy
      rfl

/-- Canonical encoded lists stay injective after quotienting trailing blanks. -/
theorem quotient_inj (x y : List Bool)
    (h : ListBlank.mk (BitstringEncoding.bitEncode x) = ListBlank.mk (BitstringEncoding.bitEncode y)) : x = y := by
  have hh : BlankRel (BitstringEncoding.bitEncode x) (BitstringEncoding.bitEncode y) := Quotient.exact h
  rcases hh with ⟨n,hn⟩ | ⟨n,hn⟩
  · exact no_extension x y n hn
  · exact (no_extension y x n hn).symm

/-- The canonical encoding remains injective on mathlib's actual initialized
blank-extended two-way tape. -/
theorem encoded_tape_injective (x y : List Bool)
    (h : Tape.mk₁ (BitstringEncoding.bitEncode x) = Tape.mk₁ (BitstringEncoding.bitEncode y)) : x = y := by
  have hh := congrArg Tape.right₀ h
  apply quotient_inj
  simpa [Tape.mk₁,Tape.mk₂] using hh

/-- The canonical pair encoding is also immune to extension by blank bits.
This is the verifier input convention used by `NumericPairCompiler`. -/
theorem pair_no_extension (x w x' w' : List Bool) (n : Nat)
    (h : BitstringEncoding.bitEncode (x',w') =
      BitstringEncoding.bitEncode (x,w) ++ List.replicate n false) : x = x' ∧ w = w' := by
  have hr : BitstringEncoding.delimit (BitstringEncoding.bitEncode x') ++ BitstringEncoding.bitEncode w' =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
        (BitstringEncoding.bitEncode w ++ List.replicate n false) := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x') ++ BitstringEncoding.bitEncode w' =
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w) ++
        List.replicate n false at h
    simpa [List.append_assoc] using h
  have hp := congrArg BitstringEncoding.undelimit hr
  simp only [BitstringEncoding.undelimit_delimit,Option.some.injEq,Prod.mk.injEq] at hp
  exact ⟨BitstringEncoding.bitEncode_injective hp.1.symm, no_extension w w' n hp.2⟩

/-- The verifier's encoded pairs remain injective on blank-extended tapes. -/
theorem pair_quotient_inj (x w x' w' : List Bool)
    (h : ListBlank.mk (BitstringEncoding.bitEncode (x,w)) =
      ListBlank.mk (BitstringEncoding.bitEncode (x',w'))) : x = x' ∧ w = w' := by
  have hh : BlankRel (BitstringEncoding.bitEncode (x,w)) (BitstringEncoding.bitEncode (x',w')) :=
    Quotient.exact h
  rcases hh with ⟨n,hn⟩ | ⟨n,hn⟩
  · exact pair_no_extension x w x' w' n hn
  · obtain ⟨hx,hw⟩ := pair_no_extension x' w' x w n hn
    exact ⟨hx.symm,hw.symm⟩

theorem encoded_pair_tape_injective (x w x' w' : List Bool)
    (h : Tape.mk₁ (BitstringEncoding.bitEncode (x,w)) =
      Tape.mk₁ (BitstringEncoding.bitEncode (x',w'))) : x = x' ∧ w = w' := by
  have hh := congrArg Tape.right₀ h
  apply pair_quotient_inj
  simpa [Tape.mk₁,Tape.mk₂] using hh

end Shared.Codes.RawInputCollision
