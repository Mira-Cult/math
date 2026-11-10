import PASoundness.Marker

/-!
# Exact compact PA926 postfix proof producer

The numeric constructors, nine axiom selectors, stack instructions, and total
postfix interpreter in this file transcribe the pinned compact/source.py.
`KDerivation` is an explicit syntactic calculus. No theorem identifying this
calculus with PA, or proving its standard-HF soundness, is assumed or proved
here. The origin and coverage results concern only this displayed calculus.
-/

namespace PASoundness.CompactProof

open PASoundness.Cantor

def imp (a b : Nat) : Nat := 4 * pair a b
def member (a b : Nat) : Nat := 4 * pair a b + 1
def allCode (a b : Nat) : Nat := 4 * pair a b + 2
def equal (a b : Nat) : Nat := 4 * pair a b + 3
def neg (a : Nat) : Nat := imp a 1
def existsCode (a b : Nat) : Nat := neg (allCode a (neg b))
def both (a b : Nat) : Nat := neg (imp a (neg b))

/-- The source's exact nine selector branches; selector eight includes its
literal fresh-name guard. No semantic formula is evaluated here. -/
def axiomCode (selector a b c u : Nat) : Nat :=
  match selector with
  | 0 => existsCode a (equal a b)
  | 1 => imp (allCode a (imp b c)) (imp (allCode a b) (allCode a c))
  | 2 => imp (member a b) (imp (equal b c) (member a c))
  | 3 => imp (allCode a (allCode b c)) (allCode b (allCode a c))
  | 4 => imp (equal a b) (imp (member a c) (member b c))
  | 5 => imp (existsCode a (allCode a b)) b
  | 6 => imp (equal a b) (imp (equal a c) (equal b c))
  | 7 => imp (imp (imp c u) a) (imp (imp a c) (imp b c))
  | _ => if c = a ∨ c = b then 0 else
      both
        (existsCode c (both
          (allCode b (both
            (imp (member a b) (imp c (member c b)))
            (imp (member c b) c)))
          (imp c (member c b))))
        (both
          (imp (equal a b) (allCode c (equal a b)))
          (imp (member a b) (allCode c (member a b))))

/-- Finite derivation data for the exact compact syntactic rules. -/
inductive KDerivation : Nat → Type
  | truth : KDerivation 0
  | axiom (selector : Fin 9) (a b c u : Nat) :
      KDerivation (axiomCode selector a b c u)
  | generalize {f : Nat} (x : Nat) : KDerivation f → KDerivation (allCode x f)
  | mp {a b : Nat} : KDerivation a → KDerivation (imp a b) → KDerivation b

def KProves (f : Nat) : Prop := Nonempty (KDerivation f)

theorem truth_proves : KProves 0 := ⟨.truth⟩

def axResult (data : Nat) : Nat :=
  let a := unpair (data / 9)
  let b := unpair a.2
  let c := unpair b.2
  axiomCode (data % 9) a.1 b.1 c.1 c.2

abbrev State := Nat × Nat

/-- Exact source instruction: accumulator and pair-encoded stack. Missing
entries are zero because unpair zero = (zero,zero). -/
def step (command : Nat) (st : State) : State :=
  let t := st.1
  let stack := st.2
  let op := command % 4
  let data := command / 4
  if op = 0 then (axResult data, pair t stack)
  else if op = 1 then (allCode data t, stack)
  else if op = 2 then
    let a := unpair stack
    if t % 4 = 0 then
      let lr := unpair (t / 4)
      if lr.1 = a.1 then (lr.2, a.2) else (0, a.2)
    else (0, a.2)
  else unpair stack

def run : List Nat → State → State
  | [], st => st
  | c :: cs, st => run cs (step c st)

theorem run_append (xs ys : List Nat) (st : State) :
    run (xs ++ ys) st = run ys (run xs st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => exact ih (step x st)

/-- The source while loop. Its residual certificate strictly decreases. -/
def sourceLoop (code : Nat) (st : State) : State :=
  if code = 0 then st else
    let p := unpair (code - 1)
    sourceLoop p.2 (step p.1 st)
termination_by code
decreasing_by
  have h := unpair_snd_le (code-1)
  omega

def theoremCode (code : Nat) : Nat := (sourceLoop code (0,0)).1

theorem sourceLoop_encode (words : List Nat) (st : State) :
    sourceLoop (Marker.encode words) st = run words st := by
  induction words generalizing st with
  | nil => simp [Marker.encode, sourceLoop, run]
  | cons c cs ih =>
      rw [Marker.encode, sourceLoop]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel_right, unpair_pair]
      exact ih (step c st)

/-- Exact equivalence between the raw natural loop and finite command parsing. -/
theorem sourceLoop_decode (code : Nat) (st : State) :
    sourceLoop code st = run (Marker.decode code) st := by
  conv_lhs => rw [← Marker.encode_decode code]
  exact sourceLoop_encode _ st

def tailIter : Nat → Nat → Nat
  | 0, s => s
  | n+1, s => tailIter n (unpair s).2

def StackSafe (s : Nat) : Prop := ∀ n, KProves (unpair (tailIter n s)).1

@[simp] theorem unpair_zero : unpair 0 = (0,0) := by simp [unpair, unpairAux]

@[simp] theorem tailIter_zero (n : Nat) : tailIter n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [tailIter] using ih

theorem stack_zero : StackSafe 0 := by
  intro n
  simp only [tailIter_zero, unpair_zero]
  exact truth_proves

theorem stack_head {s : Nat} (h : StackSafe s) : KProves (unpair s).1 := h 0

theorem stack_tail {s : Nat} (h : StackSafe s) : StackSafe (unpair s).2 :=
  fun n => h (n+1)

theorem stack_push {t s : Nat} (ht : KProves t) (hs : StackSafe s) :
    StackSafe (pair t s) := by
  intro n
  cases n with
  | zero => simpa [tailIter] using ht
  | succ n => simpa [tailIter] using hs n

theorem axResult_proves (data : Nat) : KProves (axResult data) :=
  ⟨.axiom ⟨data % 9, Nat.mod_lt _ (by decide)⟩ _ _ _ _⟩

theorem imp_decode {t : Nat} (h : t % 4 = 0) :
    imp (unpair (t/4)).1 (unpair (t/4)).2 = t := by
  rw [imp, pair_unpair]
  omega

theorem step_preserves (command : Nat) (st : State)
    (ht : KProves st.1) (hs : StackSafe st.2) :
    KProves (step command st).1 ∧ StackSafe (step command st).2 := by
  dsimp only [step]
  split
  · exact ⟨axResult_proves _, stack_push ht hs⟩
  · split
    · obtain ⟨d⟩ := ht
      exact ⟨⟨.generalize _ d⟩, hs⟩
    · split
      · split
        next himp =>
          split
          next heq =>
            have ha := stack_head hs
            obtain ⟨da⟩ := ha
            obtain ⟨dt⟩ := ht
            have hi := imp_decode himp
            rw [heq] at hi
            exact ⟨⟨.mp da (hi.symm ▸ dt)⟩, stack_tail hs⟩
          next => exact ⟨truth_proves, stack_tail hs⟩
        next => exact ⟨truth_proves, stack_tail hs⟩
      · exact ⟨stack_head hs, stack_tail hs⟩

theorem run_preserves (words : List Nat) (st : State)
    (ht : KProves st.1) (hs : StackSafe st.2) :
    KProves (run words st).1 ∧ StackSafe (run words st).2 := by
  induction words generalizing st with
  | nil => exact ⟨ht, hs⟩
  | cons c cs ih =>
      obtain ⟨ht', hs'⟩ := step_preserves c st ht hs
      exact ih (step c st) ht' hs'

/-- Every natural certificate returns a theorem of the exact displayed compact
calculus, even when an instruction is unsuitable and falls back to truth. -/
theorem theorem_origin (code : Nat) : KProves (theoremCode code) := by
  rw [theoremCode, sourceLoop_decode]
  exact (run_preserves _ (0,0) truth_proves stack_zero).1

/-- AX payload encoding is the inverse of the literal source decoder. -/
def axCommand (selector : Fin 9) (a b c u : Nat) : Nat :=
  4 * (9 * pair a (pair b (pair c u)) + selector)

def genCommand (x : Nat) : Nat := 4*x+1

theorem step_axCommand (selector : Fin 9) (a b c u t stack : Nat) :
    step (axCommand selector a b c u) (t,stack) =
      (axiomCode selector a b c u, pair t stack) := by
  have hs : (selector : Nat) < 9 := selector.isLt
  simp [step, axCommand, axResult, Nat.add_mod, Nat.div_eq_of_lt hs,
    Nat.mod_eq_of_lt hs, Nat.mul_add_div]

theorem step_genCommand (x t stack : Nat) :
    step (genCommand x) (t,stack) = (allCode x t, stack) := by
  simp [step, genCommand, Nat.add_mod, Nat.mul_add_div]

theorem step_mp (a b stack : Nat) : step 2 (imp a b, pair a stack) = (b,stack) := by
  simp [step, imp]

def program : {f : Nat} → KDerivation f → List Nat
  | _, .truth => [axCommand ⟨8, by decide⟩ 0 0 0 0]
  | _, .axiom s a b c u => [axCommand s a b c u]
  | _, .generalize x d => program d ++ [genCommand x]
  | _, .mp a i => program a ++ program i ++ [2]

/-- Strong compiler invariant: a complete expression saves precisely its
previous accumulator on the unchanged underlying stack. -/
theorem program_correct {f : Nat} (d : KDerivation f) (t stack : Nat) :
    run (program d) (t,stack) = (f, pair t stack) := by
  induction d generalizing t stack with
  | truth =>
      simp only [program, run, step_axCommand]
      rfl
  | «axiom» s a b c u => simp only [program, run, step_axCommand]
  | generalize x d ih =>
      simp only [program, run_append, ih, run, step_genCommand]
  | mp a i iha ihi =>
      simp only [program, run_append, iha, ihi, run, step_mp]

def certificate {f : Nat} (d : KDerivation f) : Nat := Marker.encode (program d)

/-- Every finite derivation is realized by a finite raw natural certificate. -/
theorem certificate_correct {f : Nat} (d : KDerivation f) :
    theoremCode (certificate d) = f := by
  simp only [theoremCode, certificate, sourceLoop_encode, program_correct]

theorem theorem_coverage {f : Nat} (h : KProves f) : ∃ code, theoremCode code = f := by
  obtain ⟨d⟩ := h
  exact ⟨certificate d, certificate_correct d⟩

theorem theorem_exact (f : Nat) : (∃ code, theoremCode code = f) ↔ KProves f := by
  constructor
  · rintro ⟨code, rfl⟩
    exact theorem_origin code
  · exact theorem_coverage

end PASoundness.CompactProof
