import Shared.Beeping.ComparisonResultReader

/-! Attach the concrete two-step result reader to a post-Turing evaluator.
The first reader move replaces the evaluator's terminal operation, so the
combined program continues in one fixed table without a free reset. -/
namespace Shared.Beeping.ComparisonJoined
open Turing Turing.PartrecToTM2
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.ComparisonTM2
open Shared.Beeping.ComparisonResultReader
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

variable {Λ : Type} [Inhabited Λ]

def table (M : TM0.Machine Alphabet Λ) : TM0.Machine Alphabet (Λ ⊕ State)
  | .inl q, a => match M q a with
      | none => some (.inr .scan, .move .right)
      | some (q', cmd) => some (.inl q', cmd)
  | .inr q, a => match program q a with
      | none => none
      | some (q', cmd) => some (.inr q', cmd)

def embed (c : TM0.Cfg Alphabet Λ) : TM0.Cfg Alphabet (Λ ⊕ State) := ⟨.inl c.q, c.Tape⟩

/-- The combined support consists of the evaluator's supported states and
four reader states. -/
def support [DecidableEq Λ] (S : Finset Λ) : Finset (Λ ⊕ State) :=
  S.image Sum.inl ∪ Finset.univ.image Sum.inr

theorem support_bound [DecidableEq Λ] (S : Finset Λ) :
    (support S).card ≤ S.card + 4 := by
  have h := Finset.card_union_le (S.image (Sum.inl : Λ → Λ ⊕ State))
    (Finset.univ.image (Sum.inr : State → Λ ⊕ State))
  have h₁ := Finset.card_image_le (s := S) (f := (Sum.inl : Λ → Λ ⊕ State))
  have h₂ := Finset.card_image_le (s := Finset.univ) (f := (Sum.inr : State → Λ ⊕ State))
  have hc : Fintype.card State = 4 := by decide
  simp only [support] 
  simpa [hc] using Nat.le_trans h (Nat.add_le_add h₁ h₂)

theorem table_support [DecidableEq Λ] (M : TM0.Machine Alphabet Λ) (S : Finset Λ)
    (h : TM0.Supports M (S : Set Λ)) :
    TM0.Supports (table M) (support S : Set (Λ ⊕ State)) := by
  classical
  constructor
  · change Sum.inr (default : State) ∈ support S
    simp [support]
  · intro q a q' cmd hs hq
    cases q with
    | inl q =>
      have hq' : q ∈ S := by simpa [support] using hq
      cases hm : M q a with
      | none =>
        simp [table,hm] at hs
        obtain ⟨rfl,rfl⟩ := hs
        simp [support]
      | some p =>
        cases p with
        | mk next action =>
          simp [table,hm] at hs
          obtain ⟨rfl,rfl⟩ := hs
          have hn : next ∈ S := h.2 (by rw [hm]; rfl) hq'
          simp [support,hn]
    | inr q =>
      cases hp : program q a with
      | none => simp [table,hp] at hs
      | some p =>
        cases p with
        | mk next action =>
          simp [table,hp] at hs
          obtain ⟨rfl,rfl⟩ := hs
          simp [support]

theorem live_step (M : TM0.Machine Alphabet Λ) (c d : TM0.Cfg Alphabet Λ)
    (h : TM0.step M c = some d) : TM0.step (table M) (embed c) = some (embed d) := by
  cases c with
  | mk q T =>
    cases hm : M q T.head with
    | none => simp [TM0.step,hm] at h
    | some p =>
      cases p with
      | mk q' cmd =>
        simp only [TM0.step,hm,Option.map_some,Option.some.injEq] at h
        subst d
        cases cmd <;> simp [TM0.step,table,embed,hm]

theorem terminal_step (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet Λ)
    (h : TM0.step M c = none) :
    TM0.step (table M) (embed c) = some ⟨.inr .scan,c.Tape.move Dir.right⟩ := by
  cases c with
  | mk q T =>
    cases hm : M q T.head with
    | none => simp [TM0.step,table,embed,hm]
    | some p => simp [TM0.step,hm] at h

theorem scan_step (M : TM0.Machine Alphabet Λ) (T : Tape Alphabet) :
    TM0.step (table M) ⟨.inr .scan,T.move Dir.right⟩ =
      some ⟨.inr (resultState (readSymbol (T.move Dir.right).head)), T⟩ := by
  simp [TM0.step,table,program,resultState,Tape.move_right_left]

theorem live_run (M : TM0.Machine Alphabet Λ) (initial final : TM0.Cfg Alphabet Λ) (n : Nat)
    (h : runSteps (TM0.step M) n initial = some final) :
    runSteps (TM0.step (table M)) n (embed initial) = some (embed final) := by
  induction n generalizing final with
  | zero =>
    change some initial = some final at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    change (runSteps (TM0.step M) n initial).bind (TM0.step M) = some final at h
    cases hr : runSteps (TM0.step M) n initial with
    | none => simp [hr] at h
    | some mid =>
      have hm : TM0.step M mid = some final := by simpa [hr] using h
      change (runSteps (TM0.step (table M)) n (embed initial)).bind _ = _
      rw [ih mid hr]
      exact live_step M mid final hm

/-- Result states remain executable forever and retain the full tape. -/
theorem result_step (M : TM0.Machine Alphabet Λ) (b : Bool) (T : Tape Alphabet) :
    TM0.step (table M) ⟨.inr (resultState b), T⟩ =
      some ⟨.inr (resultState b), T⟩ := by
  cases b <;> simp [TM0.step,table,program,resultState,Tape.write_self]

theorem result_run (M : TM0.Machine Alphabet Λ) (b : Bool) (T : Tape Alphabet) (k : Nat) :
    runSteps (TM0.step (table M)) k ⟨.inr (resultState b), T⟩ =
      some ⟨.inr (resultState b), T⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (runSteps (TM0.step (table M)) k _).bind _ = _
    rw [ih]
    exact result_step M b T

/-- The table has no terminal rows, including on malformed configurations. -/
theorem table_total (M : TM0.Machine Alphabet Λ) (c : TM0.Cfg Alphabet (Λ ⊕ State)) :
    ∃ d, TM0.step (table M) c = some d := by
  cases c with
  | mk q T =>
    cases q with
    | inl q =>
      cases hm : M q T.head with
      | none => exact ⟨⟨.inr .scan,T.move Dir.right⟩,by simp [TM0.step,table,hm]⟩
      | some p => cases p with
        | mk q' cmd =>
          cases cmd with
          | move dir => exact ⟨⟨.inl q',T.move dir⟩,by simp [TM0.step,table,hm]⟩
          | write a => exact ⟨⟨.inl q',T.write a⟩,by simp [TM0.step,table,hm]⟩
    | inr q =>
      cases q <;> simp [TM0.step,table,program,resultState] <;> first | exact ⟨_, rfl⟩ | split <;> exact ⟨_, rfl⟩

/-- A finite evaluator prefix followed by the two reader transitions is a
single exact run, with the result in its state and the original tape restored. -/
theorem run (M : TM0.Machine Alphabet Λ) (initial final : TM0.Cfg Alphabet Λ) (n : Nat)
    (h : runSteps (TM0.step M) n initial = some final)
    (ht : TM0.step M final = none) (b : Bool)
    (final1 : TM1.Cfg Alphabet Labels1 Store)
    (he : final.Tape = final1.Tape)
    (hr : TM2to1.TrCfg (halt [if b then 1 else 0]) final1) :
    runSteps (TM0.step (table M)) (n + 2) (embed initial) =
      some ⟨.inr (resultState b), final.Tape⟩ := by
  have hs := read_right b final1 hr
  rw [← he] at hs
  rw [runSteps_add,live_run M initial final n h]
  change runSteps (TM0.step (table M)) 2 (embed final) = _
  change (TM0.step (table M) (embed final)).bind (TM0.step (table M)) = _
  rw [terminal_step M final ht]
  simpa [hs] using scan_step M final.Tape

/-- One finite-support table evaluates each comparison and transfers its
answer to a reader state after two additional transitions. The translated
numerical input is still supplied on the initial tape. -/
def Implements (R : Nat → Nat → Bool) : Prop :=
  ∃ c : ToPartrec.Code,
    letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
    ∃ S : Finset (TM1to0.Λ' program1 ⊕ State),
      TM0.Supports (table (program0 c)) (S : Set _) ∧
      ∀ e n, ∃ (d : Nat) (final1 : TM1.Cfg Alphabet Labels1 Store),
        runSteps (TM0.step (table (program0 c))) (d + 2) (embed (initial0 c [e,n])) =
          some ⟨.inr (resultState (R e n)), final1.Tape⟩

theorem implements_of_singleTape (R : Nat → Nat → Bool)
    (h : Shared.Beeping.ComparisonSingleTape.Implements R) : Implements R := by
  classical
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  refine ⟨support (support0 c), table_support (program0 c) (support0 c) hc.1, ?_⟩
  intro e n
  obtain ⟨final1,hrel,hreach,hhalt⟩ := hc.2 e n
  obtain ⟨d,hd⟩ := reaches_runSteps hreach
  refine ⟨d,final1, ?_⟩
  apply run (program0 c) (initial0 c [e,n]) (TM1to0.trCfg program1 final1) d hd hhalt
    (R e n) final1 rfl
  simpa [result] using hrel

theorem pnp : Implements Shared.PNP.TM2Candidate.compareSAT :=
  implements_of_singleTape _ pnp_has_singleTape

theorem npconp : Implements Shared.NPCONP.TM2Verifier.compare :=
  implements_of_singleTape _ npconp_has_singleTape

end Shared.Beeping.ComparisonJoined
