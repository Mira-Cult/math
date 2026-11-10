import PASoundness.CompactProof
import PASoundness.CompactMatrix
import PASoundness.Source
import Mathlib.Tactic.NormNum

/-!
The fixed sixteen-command contradiction marker is verified against the exact
compact postfix calculus.  This is a theorem about `KProves 1`, not yet about
genuine PA inconsistency; the PA238 contradiction transport remains separate.
-/

namespace PASoundness.CompactMarker

open PASoundness.Cantor PASoundness.CompactProof

attribute [local irreducible] PASoundness.Cantor.pair PASoundness.Cantor.triangle
set_option maxRecDepth 20000

/-- The explicit fifteen-command AX7/MP weakening derivation recovered from
the observer lane. `T` is arbitrary; the fixed marker specializes it to zero. -/
def weakening (F H T : Nat) : KDerivation (imp F (imp H F)) := by
  let a := imp H F
  let b := imp a F
  let c := imp b a
  let d := imp F a
  let A := imp c d
  let e := imp a T
  let R := axiomCode 7 T T T T
  let d1 : KDerivation R := .axiom ⟨7, by decide⟩ T T T T
  let d2 : KDerivation R := .axiom ⟨7, by decide⟩ T T T T
  let d3 : KDerivation (imp (imp e b) A) := by
    change KDerivation (axiomCode 7 b F a T)
    exact .axiom ⟨7, by decide⟩ b F a T
  let d4 : KDerivation (imp (imp b b) A) := by
    change KDerivation (axiomCode 7 b F a F)
    exact .axiom ⟨7, by decide⟩ b F a F
  let d5 : KDerivation (imp (imp (imp b b) A) (imp (imp A b) (imp e b))) := by
    change KDerivation (axiomCode 7 A e b b)
    exact .axiom ⟨7, by decide⟩ A e b b
  let d6 : KDerivation (imp (imp A b) (imp e b)) := .mp d4 d5
  let d7 : KDerivation
      (imp (imp (imp A b) (imp e b)) (imp (imp (imp e b) A) (imp R A))) := by
    change KDerivation (axiomCode 7 (imp e b) R A b)
    exact .axiom ⟨7, by decide⟩ (imp e b) R A b
  let d8 : KDerivation (imp (imp (imp e b) A) (imp R A)) := .mp d6 d7
  let d9 : KDerivation (imp R A) := .mp d3 d8
  let d10 : KDerivation A := .mp d2 d9
  let d11 : KDerivation (imp (imp d a) c) := by
    change KDerivation (axiomCode 7 a H F a)
    exact .axiom ⟨7, by decide⟩ a H F a
  let d12 : KDerivation (imp (imp (imp d a) c) (imp A (imp R d))) := by
    change KDerivation (axiomCode 7 c R d a)
    exact .axiom ⟨7, by decide⟩ c R d a
  let d13 : KDerivation (imp A (imp R d)) := .mp d11 d12
  let d14 : KDerivation (imp R d) := .mp d10 d13
  exact .mp d1 d14

def weakeningWords (F H T : Nat) : List Nat :=
  let a := imp H F
  let b := imp a F
  let c := imp b a
  let d := imp F a
  let A := imp c d
  let e := imp a T
  let R := axiomCode 7 T T T T
  [axCommand ⟨7, by decide⟩ T T T T,
   axCommand ⟨7, by decide⟩ T T T T,
   axCommand ⟨7, by decide⟩ b F a T,
   axCommand ⟨7, by decide⟩ b F a F,
   axCommand ⟨7, by decide⟩ A e b b,
   2,
   axCommand ⟨7, by decide⟩ (imp e b) R A b,
   2, 2, 2,
   axCommand ⟨7, by decide⟩ a H F a,
   axCommand ⟨7, by decide⟩ c R d a,
   2, 2, 2]

theorem weakening_program (F H T : Nat) :
    program (weakening F H T) = weakeningWords F H T := rfl

def fastImp (a b : Nat) : Nat := 4 * fastPair a b

def fastAx (selector : Fin 9) (a b c u : Nat) : Nat :=
  4 * (9 * fastPair a (fastPair b (fastPair c u)) + selector)

def fastWeakeningWords (F H T : Nat) : List Nat :=
  let a := fastImp H F
  let b := fastImp a F
  let c := fastImp b a
  let d := fastImp F a
  let A := fastImp c d
  let e := fastImp a T
  let R := fastImp (fastImp (fastImp T T) T) (fastImp (fastImp T T) (fastImp T T))
  [fastAx ⟨7, by decide⟩ T T T T,
   fastAx ⟨7, by decide⟩ T T T T,
   fastAx ⟨7, by decide⟩ b F a T,
   fastAx ⟨7, by decide⟩ b F a F,
   fastAx ⟨7, by decide⟩ A e b b,
   2,
   fastAx ⟨7, by decide⟩ (fastImp e b) R A b,
   2, 2, 2,
   fastAx ⟨7, by decide⟩ a H F a,
   fastAx ⟨7, by decide⟩ c R d a,
   2, 2, 2]


theorem weakeningWords_fast (F H T : Nat) :
    weakeningWords F H T = fastWeakeningWords F H T := by
  simp only [weakeningWords, fastWeakeningWords, axCommand, fastAx, imp,
    fastImp, axiomCode, pair_eq_source, fastPair]

def symbolicSuffix : List Nat := weakeningWords 1 610 0 ++ [2]

theorem symbolicSuffix_length : symbolicSuffix.length = 16 := rfl

/-- The symbolic proof program has exactly the published sixteen numeric words.
Large integers are checked through the proved closed Cantor expression. -/
theorem symbolicSuffix_eq : symbolicSuffix = Marker.bottomSuffix := by
  unfold symbolicSuffix
  rw [weakeningWords_fast]
  decide

theorem step_mp_test (F target prior stack : Nat) :
    step 2 (imp F target, pair prior stack) =
      (if F = prior then target else 0, stack) := by
  by_cases h : F = prior <;> simp [step, imp, h]

/-- The selected suffix tests only equality of the producer's accumulated
theorem with literal compact bottom; all saved stack contents are preserved. -/
theorem suffix_run (prior stack : Nat) :
    run Marker.bottomSuffix (prior, stack) =
      (if prior = 1 then imp 610 1 else 0, stack) := by
  rw [← symbolicSuffix_eq]
  unfold symbolicSuffix
  rw [← weakening_program, run_append, program_correct]
  simp only [run, step_mp_test]
  by_cases h : prior = 1
  · simp [h]
  · simp [h, Ne.symm h]

theorem decodeImp (a b : Nat) (h : imp a b ≠ 0) :
    CompactMatrix.decode (imp a b) =
      .imp (CompactMatrix.decode a) (CompactMatrix.decode b) := by
  rw [CompactMatrix.decode]
  simp only [if_neg h]
  simp [imp]

theorem decodeAll (a b : Nat) :
    CompactMatrix.decode (allCode a b) = .all a (CompactMatrix.decode b) := by
  rw [CompactMatrix.decode]
  simp [allCode, Nat.add_mod, Nat.mul_add_div]

theorem decode_one : CompactMatrix.decode 1 = CompactMatrix.falsity := by
  rw [CompactMatrix.decode]
  simp [CompactMatrix.falsity, unpair, unpairAux]

theorem imp_one_one : imp 1 1 = 16 := by norm_num [imp, pair_eq_source]
theorem all_zero_sixteen : allCode 0 16 = 610 := by norm_num [allCode, pair_eq_source]
theorem false_exists_code : imp 610 1 = 747868 := by norm_num [imp, pair_eq_source]

theorem decode_false_exists :
    CompactMatrix.decode 747868 = CompactMatrix.existsAt 0 CompactMatrix.falsity := by
  rw [← false_exists_code, decodeImp 610 1 (by rw [false_exists_code]; decide),
    ← all_zero_sixteen, decodeAll, ← imp_one_one,
    decodeImp 1 1 (by rw [imp_one_one]; decide), decode_one]
  rfl

theorem false_exists_false (ρ : CompactMatrix.Environment) :
    ¬ (CompactMatrix.decode 747868).Realize ρ := by
  rw [decode_false_exists, CompactMatrix.existsAt_realize]
  rintro ⟨x, hx⟩
  exact CompactMatrix.falsity_false _ hx

theorem record_decoded (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat)
    (f : CompactMatrix.Formula) (h : CompactMatrix.decode (conclusion p) = f) :
    CompactMatrix.record conclusion n p xs =
      if xs.length ≠ n then false else
        match CompactMatrix.normalize .ex n f with
        | none => false
        | some r =>
          match CompactMatrix.evalQF (CompactMatrix.bind r.binders xs (fun _ => 0)) r.matrix with
          | none => false
          | some b => !b := by
  unfold CompactMatrix.record
  rw [h]
  rfl

theorem record_false_exists_at (x : Nat) :
    CompactMatrix.record (fun _ => 747868) 1 0 [x] = true := by
  rw [record_decoded _ _ _ _ _ decode_false_exists]
  change (! CompactMatrix.bit x x) = true
  rw [CompactMatrix.bit_self_false]
  rfl

theorem record_false_exists : CompactMatrix.record (fun _ => 747868) 1 0 [0] = true :=
  record_false_exists_at 0

theorem record_truth_at (x : Nat) : CompactMatrix.record (fun _ => 0) 1 0 [x] = false := by
  have h : CompactMatrix.decode 0 = .truth := by rw [CompactMatrix.decode]; rfl
  rw [record_decoded _ _ _ _ _ h]
  rfl

theorem record_truth : CompactMatrix.record (fun _ => 0) 1 0 [0] = false := record_truth_at 0

/-- Every accepted structural marker has a genuine finite prefix decomposition. -/
theorem marker_decomposition (code : Nat) (h : Marker.bottomTail code = true) :
    ∃ words, code = Marker.encode (words ++ Marker.bottomSuffix) := by
  have hd := (Marker.hasBottomSuffix_iff (Marker.decode code)).mp h
  refine ⟨(Marker.decode code).take ((Marker.decode code).length - 16), ?_⟩
  rw [← hd.2, List.take_append_drop, Marker.encode_decode]

/-- Producer execution, not the observer, performs the equality test. -/
theorem marked_conclusion (words : List Nat) :
    theoremCode (Marker.encode (words ++ Marker.bottomSuffix)) =
      if theoremCode (Marker.encode words) = 1 then 747868 else 0 := by
  simp only [theoremCode, sourceLoop_encode, run_append]
  cases h : run words (0, 0) with
  | mk prior stack => simp only [suffix_run, false_exists_code]

theorem record_conclusion_congr (conclusion : Nat → Nat) (n p : Nat) (xs : List Nat)
    (f : Nat) (h : conclusion p = f) :
    CompactMatrix.record conclusion n p xs = CompactMatrix.record (fun _ => f) n 0 xs := by
  simp only [CompactMatrix.record, h]

/-- The selected marker has the same value at every singleton coordinate. -/
theorem marked_record_iff_at (words : List Nat) (x : Nat) :
    CompactMatrix.record theoremCode 1 (Marker.encode (words ++ Marker.bottomSuffix)) [x] = true ↔
      theoremCode (Marker.encode words) = 1 := by
  by_cases h : theoremCode (Marker.encode words) = 1
  · have ht : theoremCode (Marker.encode (words ++ Marker.bottomSuffix)) = 747868 := by
      rw [marked_conclusion, if_pos h]
    rw [record_conclusion_congr theoremCode 1 _ [x] 747868 ht, record_false_exists_at]
    exact iff_of_true rfl h
  · have ht : theoremCode (Marker.encode (words ++ Marker.bottomSuffix)) = 0 := by
      rw [marked_conclusion, if_neg h]
    rw [record_conclusion_congr theoremCode 1 _ [x] 0 ht, record_truth_at]
    exact iff_of_false Bool.false_ne_true h

/-- Exact marker behavior on the finite record that the legacy zero view reads. -/
theorem marked_record_iff (words : List Nat) :
    CompactMatrix.record theoremCode 1 (Marker.encode (words ++ Marker.bottomSuffix)) [0] = true ↔
      theoremCode (Marker.encode words) = 1 := marked_record_iff_at words 0

def PositiveMarker (code : Nat) : Prop :=
  Marker.bottomTail code = true ∧ CompactMatrix.record theoremCode 1 code [0] = true

/-- A positive selected record yields an actual derivation of compact bottom. -/
theorem marker_origin (code : Nat) (h : PositiveMarker code) : KProves 1 := by
  obtain ⟨words, hcode⟩ := marker_decomposition code h.1
  have hout := h.2
  rw [hcode] at hout
  have hp := (marked_record_iff words).mp hout
  rw [← hp]
  exact theorem_origin (Marker.encode words)

/-- Every compact-bottom derivation has an accepted marker in the unchanged wire. -/
theorem marker_coverage (h : KProves 1) : ∃ code, PositiveMarker code := by
  obtain ⟨code, hc⟩ := theorem_coverage h
  refine ⟨Marker.encode (Marker.decode code ++ Marker.bottomSuffix),
    Marker.encoded_suffix_recognized (Marker.decode code), ?_⟩
  apply (marked_record_iff (Marker.decode code)).mpr
  simpa only [Marker.encode_decode] using hc

theorem marker_exact : (∃ code, PositiveMarker code) ↔ KProves 1 :=
  ⟨fun ⟨code, h⟩ => marker_origin code h, marker_coverage⟩

def value (a : Observer.Address) : Bool :=
  CompactMatrix.record theoremCode a.rank a.certificate a.coordinates

/-- A closed zero-level theorem for the exact compact syntactic calculus.
Identification with genuine PA inconsistency is deliberately not asserted. -/
theorem levelZero_iff_KBottom :
    Observer.Q_0 .compactSuffix (Source.events value) ↔ KProves 1 := by
  unfold Observer.Q_0
  rw [and_iff_right (Source.complete value)]
  change (∃ p, Marker.bottomTail p = true ∧
    Observer.Emitted (Source.events value) true ⟨1, p, [0]⟩) ↔ _
  simp only [Source.emitted_exact]
  simpa [Observer.Admissible, value, PositiveMarker] using marker_exact

/-- Concrete zero-to-first-rank nesting uses the suffix's false existential
target, not an assumed arithmetic-hierarchy calibration. -/
theorem levelZero_implies_rankOne
    (h : Observer.Q_0 .compactSuffix (Source.events value)) :
    Observer.Q_n (Source.events value) 1 := by
  obtain ⟨code, hc⟩ := marker_coverage (levelZero_iff_KBottom.mp h)
  obtain ⟨words, hw⟩ := marker_decomposition code hc.1
  have hp : theoremCode (Marker.encode words) = 1 := by
    apply (marked_record_iff words).mp
    simpa only [← hw] using hc.2
  refine ⟨by decide, Source.complete value, code, ?_⟩
  change ∀ x : Nat, Observer.Emitted (Source.events value) true ⟨1, code, [x]⟩
  intro x
  apply (Source.emitted_exact value true ⟨1, code, [x]⟩).mpr
  refine ⟨by simp [Observer.Admissible], ?_⟩
  change CompactMatrix.record theoremCode 1 code [x] = true
  rw [hw]
  exact (marked_record_iff_at words x).mpr hp

end PASoundness.CompactMarker
