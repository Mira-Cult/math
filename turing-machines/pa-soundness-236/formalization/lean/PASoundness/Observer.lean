import PASoundness.Producer
import PASoundness.Marker

/-!
A finite, explicitly sorted first-order syntax for the restricted observer.
The four sorts are all natural times, all natural tags, all finite natural
sequences, and all addresses, including never-emitted values.  No constructor
is a proof checker, matrix evaluator, computation predicate, or truth oracle.

This deliberately small many-sorted syntax has eight ordinary first-order
quantifiers (the two polarities in four sorts).  Mathlib's single-sorted syntax
is used for arithmetic elsewhere; a translation between these syntaxes is not
claimed here.  The syntax and generator below are executable inductive data.
-/

namespace PASoundness.Observer

structure Address where
  rank : Nat
  certificate : Nat
  coordinates : List Nat
  deriving DecidableEq, Repr

inductive Profile where
  | blocks
  | legacy
  deriving DecidableEq, Repr

def Admissible (profile : Profile) (a : Address) : Prop :=
  a.coordinates.length = a.rank ∧ (profile = .legacy → 0 < a.rank)

structure EventStructure where
  profile : Profile
  out : Bool → Nat → Address → Prop
  error : Nat → Prop

def Emitted (E : EventStructure) (b : Bool) (a : Address) : Prop :=
  ∃ t, E.out b t a

/-- Complete, conflict-free addressed output; missing values are not zero. -/
def BasicComplete (E : EventStructure) : Prop :=
  (¬ ∃ t, E.error t) ∧
  (∀ a, Admissible E.profile a → Emitted E false a ∨ Emitted E true a) ∧
  (∀ a, ¬ (Emitted E false a ∧ Emitted E true a))

def WellAddressed (E : EventStructure) : Prop :=
  ∀ b t a, E.out b t a → Admissible E.profile a

/-- The extra address guard is automatic for the verified wire decoder.  On
arbitrary structures it prevents invalid records from certifying acceptance. -/
def Complete (E : EventStructure) : Prop := BasicComplete E ∧ WellAddressed E

inductive NatTerm where
  | var : Nat → NatTerm
  | zero : NatTerm
  | succ : NatTerm → NatTerm
  deriving DecidableEq, Repr

inductive TimeTerm where
  | var : Nat → TimeTerm
  deriving DecidableEq, Repr

inductive SeqTerm where
  | var : Nat → SeqTerm
  | nil : SeqTerm
  | cons : NatTerm → SeqTerm → SeqTerm
  deriving DecidableEq, Repr

inductive AddressTerm where
  | var : Nat → AddressTerm
  | key : NatTerm → NatTerm → SeqTerm → AddressTerm
  deriving DecidableEq, Repr

/-- Variables are de Bruijn indices within their own sort. -/
structure Assignment where
  nat : List Nat := []
  time : List Nat := []
  seq : List (List Nat) := []
  address : List Address := []

def NatTerm.realize (v : Assignment) : NatTerm → Nat
  | .var i => v.nat.getD i 0
  | .zero => 0
  | .succ t => t.realize v + 1

def TimeTerm.realize (v : Assignment) : TimeTerm → Nat
  | .var i => v.time.getD i 0

def SeqTerm.realize (v : Assignment) : SeqTerm → List Nat
  | .var i => v.seq.getD i []
  | .nil => []
  | .cons t s => t.realize v :: s.realize v

def AddressTerm.realize (v : Assignment) : AddressTerm → Address
  | .var i => v.address.getD i ⟨0, 0, []⟩
  | .key n p s => ⟨n.realize v, p.realize v, s.realize v⟩

/-- The complete finite vocabulary, with no arbitrary predicate constructor. -/
inductive Formula where
  | out : Bool → TimeTerm → AddressTerm → Formula
  | error : TimeTerm → Formula
  | admissible : AddressTerm → Formula
  | before : TimeTerm → TimeTerm → Formula
  | natEq : NatTerm → NatTerm → Formula
  | timeEq : TimeTerm → TimeTerm → Formula
  | seqEq : SeqTerm → SeqTerm → Formula
  | addressEq : AddressTerm → AddressTerm → Formula
  | bottomTail : NatTerm → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | allNat : Formula → Formula
  | exNat : Formula → Formula
  | allTime : Formula → Formula
  | exTime : Formula → Formula
  | allSeq : Formula → Formula
  | exSeq : Formula → Formula
  | allAddress : Formula → Formula
  | exAddress : Formula → Formula
  deriving DecidableEq, Repr

/-- External satisfaction of finite syntax in the specified infinite structure.
There is no claim that this function has a computable Boolean truth value. -/
def Formula.Realize (E : EventStructure) (v : Assignment) : Formula → Prop
  | .out b t a => E.out b (t.realize v) (a.realize v)
  | .error t => E.error (t.realize v)
  | .admissible a => Admissible E.profile (a.realize v)
  | .before s t => s.realize v < t.realize v
  | .natEq s t => s.realize v = t.realize v
  | .timeEq s t => s.realize v = t.realize v
  | .seqEq s t => s.realize v = t.realize v
  | .addressEq s t => s.realize v = t.realize v
  | .bottomTail p => Marker.bottomTail (p.realize v) = true
  | .neg p => ¬ p.Realize E v
  | .conj p q => p.Realize E v ∧ q.Realize E v
  | .disj p q => p.Realize E v ∨ q.Realize E v
  | .imp p q => p.Realize E v → q.Realize E v
  | .allNat p => ∀ x : Nat, p.Realize E {v with nat := x :: v.nat}
  | .exNat p => ∃ x : Nat, p.Realize E {v with nat := x :: v.nat}
  | .allTime p => ∀ x : Nat, p.Realize E {v with time := x :: v.time}
  | .exTime p => ∃ x : Nat, p.Realize E {v with time := x :: v.time}
  | .allSeq p => ∀ x : List Nat, p.Realize E {v with seq := x :: v.seq}
  | .exSeq p => ∃ x : List Nat, p.Realize E {v with seq := x :: v.seq}
  | .allAddress p => ∀ x : Address, p.Realize E {v with address := x :: v.address}
  | .exAddress p => ∃ x : Address, p.Realize E {v with address := x :: v.address}

def NatTerm.Scoped (n : Nat) : NatTerm → Prop
  | .var i => i < n
  | .zero => True
  | .succ t => t.Scoped n

def TimeTerm.Scoped (n : Nat) : TimeTerm → Prop
  | .var i => i < n

def SeqTerm.Scoped (n s : Nat) : SeqTerm → Prop
  | .var i => i < s
  | .nil => True
  | .cons t xs => t.Scoped n ∧ xs.Scoped n s

def AddressTerm.Scoped (n s a : Nat) : AddressTerm → Prop
  | .var i => i < a
  | .key r p xs => r.Scoped n ∧ p.Scoped n ∧ xs.Scoped n s

/-- The four arguments count bound variables of each sort. -/
def Formula.Scoped (n t s a : Nat) : Formula → Prop
  | .out _ u p => u.Scoped t ∧ p.Scoped n s a
  | .error u => u.Scoped t
  | .admissible p => p.Scoped n s a
  | .before u v => u.Scoped t ∧ v.Scoped t
  | .natEq u v => u.Scoped n ∧ v.Scoped n
  | .timeEq u v => u.Scoped t ∧ v.Scoped t
  | .seqEq u v => u.Scoped n s ∧ v.Scoped n s
  | .addressEq u v => u.Scoped n s a ∧ v.Scoped n s a
  | .bottomTail p => p.Scoped n
  | .neg p => p.Scoped n t s a
  | .conj p q | .disj p q | .imp p q => p.Scoped n t s a ∧ q.Scoped n t s a
  | .allNat p | .exNat p => p.Scoped (n+1) t s a
  | .allTime p | .exTime p => p.Scoped n (t+1) s a
  | .allSeq p | .exSeq p => p.Scoped n t (s+1) a
  | .allAddress p | .exAddress p => p.Scoped n t s (a+1)

def Formula.quantifierCount : Formula → Nat
  | .out _ _ _ | .error _ | .admissible _ | .before _ _ | .natEq _ _ |
    .timeEq _ _ | .seqEq _ _ | .addressEq _ _ | .bottomTail _ => 0
  | .neg p => p.quantifierCount
  | .conj p q | .disj p q | .imp p q => p.quantifierCount + q.quantifierCount
  | .allNat p | .exNat p | .allTime p | .exTime p | .allSeq p | .exSeq p |
    .allAddress p | .exAddress p => p.quantifierCount + 1

def numeral : Nat → NatTerm
  | 0 => .zero
  | n + 1 => .succ (numeral n)

@[simp] theorem numeral_realize (n : Nat) (v : Assignment) :
    (numeral n).realize v = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [numeral, NatTerm.realize, ih]

theorem numeral_scoped (k n : Nat) : (numeral k).Scoped n := by
  induction k with
  | zero => trivial
  | succ k ih => exact ih

/-- Read the n bound coordinates in their original left-to-right order. -/
def coordinates : Nat → SeqTerm
  | 0 => .nil
  | n + 1 => .cons (.var n) (coordinates n)

theorem coordinates_scoped (k n s : Nat) (h : k ≤ n) :
    (coordinates k).Scoped n s := by
  induction k with
  | zero => trivial
  | succ k ih =>
    exact ⟨by change k < n; omega, ih (by omega)⟩

theorem coordinates_realize (n : Nat) (v : Assignment) (h : n ≤ v.nat.length) :
    (coordinates n).realize v = (v.nat.take n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < v.nat.length := by omega
    have hle : n ≤ v.nat.length := by omega
    simp only [coordinates, SeqTerm.realize, NatTerm.realize, ih hle]
    rw [← List.take_append_getElem hn, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl

theorem coordinates_reverse_append (xs tail : List Nat) (v : Assignment) :
    (coordinates xs.length).realize {v with nat := xs.reverse ++ tail} = xs := by
  rw [coordinates_realize]
  · have h : xs.length ≤ xs.reverse.length := by simp
    rw [List.take_append_of_le_length h]
    simpa only [← List.length_reverse (as := xs), List.take_length,
      List.reverse_reverse]
  · simp only [List.length_append, List.length_reverse]
    omega

def quantify : Polarity → Nat → Formula → Formula
  | _, 0, body => body
  | .ex, n + 1, body => .exNat (quantify .all n body)
  | .all, n + 1, body => .allNat (quantify .ex n body)

theorem quantify_scoped (q : Polarity) (k n t s a : Nat) (body : Formula) :
    (quantify q k body).Scoped n t s a ↔ body.Scoped (n+k) t s a := by
  induction k generalizing q n with
  | zero => rfl
  | succ k ih =>
    cases q <;> simp only [quantify, Formula.Scoped, ih,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem quantify_quantifierCount (q : Polarity) (n : Nat) (body : Formula) :
    (quantify q n body).quantifierCount = n + body.quantifierCount := by
  induction n generalizing q with
  | zero => simp only [quantify, Nat.zero_add]
  | succ n ih =>
    cases q <;> simp only [quantify, Formula.quantifierCount, ih] <;> omega

theorem quantify_realize (E : EventStructure) (q : Polarity) (n : Nat)
    (body : Formula) (v : Assignment) :
    (quantify q n body).Realize E v ↔
      altPrefix q n (fun xs => body.Realize E {v with nat := xs.reverse ++ v.nat}) := by
  induction n generalizing q v with
  | zero => rfl
  | succ n ih =>
    cases q with
    | ex =>
      apply exists_congr
      intro x
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih .all {v with nat := x :: v.nat}
    | all =>
      apply forall_congr'
      intro x
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih .ex {v with nat := x :: v.nat}

/-- Fully expanded finite completeness formula. -/
def basicCompleteFormula : Formula :=
  .conj (.neg (.exTime (.error (.var 0))))
    (.conj
      (.allAddress (.imp (.admissible (.var 0))
        (.exTime (.disj (.out false (.var 0) (.var 0))
          (.out true (.var 0) (.var 0))))))
      (.neg (.exAddress (.exTime (.exTime
        (.conj (.out false (.var 1) (.var 0))
          (.out true (.var 0) (.var 0))))))))

theorem basicCompleteFormula_realize (E : EventStructure) (v : Assignment) :
    basicCompleteFormula.Realize E v ↔ BasicComplete E := by
  simp only [basicCompleteFormula, Formula.Realize, TimeTerm.realize,
    AddressTerm.realize, List.getD_cons_zero, List.getD_cons_succ,
    BasicComplete, Emitted]
  constructor
  · rintro ⟨he, hc, hn⟩
    refine ⟨he, ?_, ?_⟩
    · intro a ha
      obtain ⟨t, ht⟩ := hc a ha
      cases ht with
      | inl h => exact Or.inl ⟨t, h⟩
      | inr h => exact Or.inr ⟨t, h⟩
    · rintro a ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
      exact hn ⟨a, s, t, hs, ht⟩
  · rintro ⟨he, hc, hn⟩
    refine ⟨he, ?_, ?_⟩
    · intro a ha
      cases hc a ha with
      | inl h => obtain ⟨t, ht⟩ := h; exact ⟨t, Or.inl ht⟩
      | inr h => obtain ⟨t, ht⟩ := h; exact ⟨t, Or.inr ht⟩
    · rintro ⟨a, s, t, hs, ht⟩
      exact hn a ⟨⟨s, hs⟩, ⟨t, ht⟩⟩

def wellAddressedFormula : Formula :=
  .allAddress (.allTime (.imp
    (.disj (.out false (.var 0) (.var 0)) (.out true (.var 0) (.var 0)))
    (.admissible (.var 0))))

theorem wellAddressedFormula_realize (E : EventStructure) (v : Assignment) :
    wellAddressedFormula.Realize E v ↔ WellAddressed E := by
  change (∀ a t, E.out false t a ∨ E.out true t a → Admissible E.profile a) ↔ _
  constructor
  · intro h b t a hb
    cases b with
    | false => exact h a t (Or.inl hb)
    | true => exact h a t (Or.inr hb)
  · intro h a t hb
    cases hb with
    | inl hb => exact h false t a hb
    | inr hb => exact h true t a hb

def completeFormula : Formula := .conj basicCompleteFormula wellAddressedFormula

theorem completeFormula_realize (E : EventStructure) (v : Assignment) :
    completeFormula.Realize E v ↔ Complete E :=
  and_congr (basicCompleteFormula_realize E v) (wellAddressedFormula_realize E v)

def rawLevelFormula (n : Nat) : Formula :=
  .exNat (quantify .all n (.exTime
    (.out true (.var 0) (.key (numeral n) (.var n) (coordinates n)))))

def levelFormula (n : Nat) : Formula := .conj completeFormula (rawLevelFormula n)

theorem completeFormula_closed : completeFormula.Scoped 0 0 0 0 := by
  simp [completeFormula, basicCompleteFormula, wellAddressedFormula,
    Formula.Scoped, TimeTerm.Scoped, AddressTerm.Scoped]

theorem rawLevelFormula_closed (n : Nat) : (rawLevelFormula n).Scoped 0 0 0 0 := by
  change (quantify .all n _).Scoped 1 0 0 0
  rw [quantify_scoped]
  exact ⟨by change 0 < 1; decide, numeral_scoped n (1+n), by change n < 1+n; omega,
    coordinates_scoped n (1+n) 0 (by omega)⟩

theorem levelFormula_closed (n : Nat) : (levelFormula n).Scoped 0 0 0 0 :=
  ⟨completeFormula_closed, rawLevelFormula_closed n⟩

theorem rawLevelFormula_quantifierCount (n : Nat) :
    (rawLevelFormula n).quantifierCount = n+2 := by
  simp only [rawLevelFormula, Formula.quantifierCount, quantify_quantifierCount]

theorem levelFormula_quantifierCount (n : Nat) :
    (levelFormula n).quantifierCount = n+10 := by
  change 8 + (rawLevelFormula n).quantifierCount = n+10
  rw [rawLevelFormula_quantifierCount]
  omega

def RawFailure (E : EventStructure) (n : Nat) : Prop :=
  ∃ p, altPrefix .all n (fun xs => Emitted E true ⟨n, p, xs⟩)

theorem rawLevelFormula_realize (E : EventStructure) (n : Nat) (v : Assignment) :
    (rawLevelFormula n).Realize E v ↔ RawFailure E n := by
  change (∃ p, (quantify .all n _).Realize E {v with nat := p :: v.nat}) ↔ _
  unfold RawFailure
  apply exists_congr
  intro p
  rw [quantify_realize]
  apply altPrefix_congr_length
  intro xs hx
  simp only [Formula.Realize, TimeTerm.realize, AddressTerm.realize,
    NatTerm.realize, List.getD_cons_zero, numeral_realize, Emitted]
  have hp : (xs.reverse ++ p :: v.nat).getD n 0 = p := by
    rw [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simpa [List.length_reverse, hx])]
    simp [List.length_reverse, hx]
  simp only [hp]
  apply exists_congr
  intro t
  have hcoord : (coordinates n).realize
      {v with nat := xs.reverse ++ p :: v.nat, time := t :: v.time} = xs := by
    rw [← hx]
    exact coordinates_reverse_append xs (p :: v.nat) {v with time := t :: v.time}
  rw [hcoord]

/-- Two fixed wire views, not an arbitrary decoder-program parameter.
`rankZero` is the proposed block interface; PA926 uses `compactSuffix`. -/
inductive ZeroView where
  | rankZero
  | compactSuffix
  deriving DecidableEq, Repr

def rawZeroFormula : ZeroView → Formula
  | .rankZero => rawLevelFormula 0
  | .compactSuffix => .exNat (.conj (.bottomTail (.var 0))
      (.exTime (.out true (.var 0)
        (.key (numeral 1) (.var 0) (.cons (.zero) (.nil))))))

theorem rawZeroFormula_closed (view : ZeroView) :
    (rawZeroFormula view).Scoped 0 0 0 0 := by
  cases view with
  | rankZero => exact rawLevelFormula_closed 0
  | compactSuffix =>
    simp [rawZeroFormula, Formula.Scoped, NatTerm.Scoped, TimeTerm.Scoped,
      AddressTerm.Scoped, SeqTerm.Scoped, numeral]

def RawZero (view : ZeroView) (E : EventStructure) : Prop :=
  match view with
  | .rankZero => RawFailure E 0
  | .compactSuffix => ∃ p, Marker.bottomTail p = true ∧ Emitted E true ⟨1, p, [0]⟩

theorem rawZeroFormula_realize (view : ZeroView) (E : EventStructure) (v : Assignment) :
    (rawZeroFormula view).Realize E v ↔ RawZero view E := by
  cases view with
  | rankZero => exact rawLevelFormula_realize E 0 v
  | compactSuffix => rfl

/-- Guarded level zero is an inconsistency convention only after a separate
contradiction-certificate bridge.  It never says the producer physically halts. -/
def Q_0 (view : ZeroView) (E : EventStructure) : Prop := Complete E ∧ RawZero view E

/-- Positive observed level; arithmetic Sigma_n calibration is a separate bridge. -/
def Q_n (E : EventStructure) (n : Nat) : Prop :=
  0 < n ∧ Complete E ∧ RawFailure E n

/-- External finite-level existence, not a single generated FO sentence. -/
def Q_omega (view : ZeroView) (E : EventStructure) : Prop := Q_0 view E ∨ ∃ n, Q_n E n

def zeroFormula (view : ZeroView) : Formula :=
  .conj completeFormula (rawZeroFormula view)

/-- One effective family supplies the intended zero convention and every
positive level. The only parameter other than n is the fixed wire view. -/
def finiteLevelFormula (view : ZeroView) : Nat → Formula
  | 0 => zeroFormula view
  | n+1 => levelFormula (n+1)

theorem zeroFormula_closed (view : ZeroView) : (zeroFormula view).Scoped 0 0 0 0 :=
  ⟨completeFormula_closed, rawZeroFormula_closed view⟩

theorem finiteLevelFormula_closed (view : ZeroView) (n : Nat) :
    (finiteLevelFormula view n).Scoped 0 0 0 0 := by
  cases n with
  | zero => exact zeroFormula_closed view
  | succ n => exact levelFormula_closed (n+1)

theorem zeroFormula_realize (view : ZeroView) (E : EventStructure) (v : Assignment) :
    (zeroFormula view).Realize E v ↔ Q_0 view E :=
  and_congr (completeFormula_realize E v) (rawZeroFormula_realize view E v)

def SoundnessAcceptance (view : ZeroView) (E : EventStructure) : Prop :=
  Complete E ∧ ¬ RawZero view E ∧ ∀ n, 0 < n → ¬ RawFailure E n

def Failure (E : EventStructure) : Prop := ¬ Complete E

theorem levelFormula_realize (E : EventStructure) (n : Nat) (v : Assignment) :
    (levelFormula n).Realize E v ↔ Complete E ∧ RawFailure E n := by
  exact and_congr (completeFormula_realize E v) (rawLevelFormula_realize E n v)

theorem positiveFormula_realize (E : EventStructure) (n : Nat)
    (hn : 0 < n) (v : Assignment) : (levelFormula n).Realize E v ↔ Q_n E n :=
  (levelFormula_realize E n v).trans (and_iff_right hn).symm

theorem Q_omega_formula (view : ZeroView) (E : EventStructure) (v : Assignment) :
    Q_omega view E ↔ ∃ n, (finiteLevelFormula view n).Realize E v := by
  constructor
  · rintro (hz | ⟨n, hn, hc, hb⟩)
    · exact ⟨0, (zeroFormula_realize view E v).mpr hz⟩
    · cases n with
      | zero => omega
      | succ n => exact ⟨n+1, (levelFormula_realize E (n+1) v).mpr ⟨hc, hb⟩⟩
  · rintro ⟨n, h⟩
    cases n with
    | zero => exact Or.inl ((zeroFormula_realize view E v).mp h)
    | succ n =>
      exact Or.inr ⟨n+1, (positiveFormula_realize E (n+1) (Nat.zero_lt_succ n) v).mp h⟩

theorem levelZero_reachability (E : EventStructure) :
    RawFailure E 0 ↔ ∃ p t, E.out true t ⟨0, p, []⟩ := Iff.rfl

theorem Q_omega_iff (view : ZeroView) (E : EventStructure) :
    Q_omega view E ↔ Complete E ∧
      (RawZero view E ∨ ∃ n, 0 < n ∧ RawFailure E n) := by
  constructor
  · rintro (h | ⟨n, hn, hc, h⟩)
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨hc, Or.inr ⟨n, hn, h⟩⟩
  · rintro ⟨hc, h | ⟨n, hn, h⟩⟩
    · exact Or.inl ⟨hc, h⟩
    · exact Or.inr ⟨n, hn, hc, h⟩

theorem acceptance_complement_on_complete (view : ZeroView) (E : EventStructure) :
    SoundnessAcceptance view E ↔ Complete E ∧ ¬ Q_omega view E := by
  rw [Q_omega_iff]
  constructor
  · rintro ⟨hc, hz, h⟩
    refine ⟨hc, ?_⟩
    rintro ⟨_, hzero | ⟨n, hn, hb⟩⟩
    · exact hz hzero
    · exact h n hn hb
  · rintro ⟨hc, h⟩
    exact ⟨hc, fun hz => h ⟨hc, Or.inl hz⟩,
      fun n hn hb => h ⟨hc, Or.inr ⟨n, hn, hb⟩⟩⟩

theorem incomplete_neither (view : ZeroView) (E : EventStructure) (h : Failure E) :
    ¬ SoundnessAcceptance view E ∧ ¬ Q_omega view E := by
  refine ⟨fun ha => h ha.1, ?_⟩
  intro hq
  exact h ((Q_omega_iff view E).mp hq).1

/-- Relate receipt semantics to a supplied value table without filling missing data. -/
def RecordsAgree (E : EventStructure) (values : RecordValues) : Prop :=
  ∀ n p xs, 0 < n → xs.length = n →
    (Emitted E true ⟨n, p, xs⟩ ↔ values n p xs = true)

theorem rawFailure_iff_rankFailure (E : EventStructure) (values : RecordValues)
    (h : RecordsAgree E values) (n : Nat) (hn : 0 < n) :
    RawFailure E n ↔ RankFailure values n := by
  apply exists_congr
  intro p
  exact altPrefix_congr_length .all n _ _ (fun xs hx => h n p xs hn hx)

/-- Exact receipt preservation permits silent delays and changed completion times.
No theorem about reordering, inserting, or deleting raw positional bits follows
from this receipt-level relation; the ordered wire refinement is separate. -/
structure SameReceipts (E F : EventStructure) : Prop where
  profile : E.profile = F.profile
  errors : (∃ t, E.error t) ↔ ∃ t, F.error t
  emitted : ∀ b a, Emitted E b a ↔ Emitted F b a

theorem basicComplete_preserved {E F : EventStructure} (h : SameReceipts E F) :
    BasicComplete E ↔ BasicComplete F := by
  unfold BasicComplete
  constructor
  · rintro ⟨he, hc, hn⟩
    refine ⟨fun hf => he (h.errors.mpr hf), ?_, ?_⟩
    · intro a ha
      have ha' : Admissible E.profile a := by simpa only [h.profile] using ha
      exact (or_congr (h.emitted false a) (h.emitted true a)).mp (hc a ha')
    · intro a hf
      exact hn a ⟨(h.emitted false a).mpr hf.1, (h.emitted true a).mpr hf.2⟩
  · rintro ⟨he, hc, hn⟩
    refine ⟨fun hf => he (h.errors.mp hf), ?_, ?_⟩
    · intro a ha
      have ha' : Admissible F.profile a := by simpa only [h.profile] using ha
      exact (or_congr (h.emitted false a) (h.emitted true a)).mpr (hc a ha')
    · intro a hf
      exact hn a ⟨(h.emitted false a).mp hf.1, (h.emitted true a).mp hf.2⟩

theorem wellAddressed_preserved {E F : EventStructure} (h : SameReceipts E F) :
    WellAddressed E ↔ WellAddressed F := by
  constructor
  · intro hw b t a ho
    obtain ⟨s, hs⟩ := (h.emitted b a).mpr ⟨t, ho⟩
    simpa only [← h.profile] using hw b s a hs
  · intro hw b t a ho
    obtain ⟨s, hs⟩ := (h.emitted b a).mp ⟨t, ho⟩
    simpa only [h.profile] using hw b s a hs

theorem complete_preserved {E F : EventStructure} (h : SameReceipts E F) :
    Complete E ↔ Complete F :=
  and_congr (basicComplete_preserved h) (wellAddressed_preserved h)

theorem rawFailure_preserved {E F : EventStructure} (h : SameReceipts E F) (n : Nat) :
    RawFailure E n ↔ RawFailure F n := by
  apply exists_congr
  intro p
  exact altPrefix_congr_length .all n _ _ (fun xs _ => h.emitted true ⟨n, p, xs⟩)

theorem rawZero_preserved {E F : EventStructure} (view : ZeroView)
    (h : SameReceipts E F) : RawZero view E ↔ RawZero view F := by
  cases view with
  | rankZero => exact rawFailure_preserved h 0
  | compactSuffix =>
    apply exists_congr
    intro p
    exact and_congr Iff.rfl (h.emitted true ⟨1, p, [0]⟩)

theorem acceptance_preserved {E F : EventStructure} (view : ZeroView)
    (h : SameReceipts E F) :
    SoundnessAcceptance view E ↔ SoundnessAcceptance view F := by
  apply and_congr (complete_preserved h)
  apply and_congr (not_congr (rawZero_preserved view h))
  apply forall_congr'
  intro n
  exact imp_congr_right (fun _ => not_congr (rawFailure_preserved h n))

end PASoundness.Observer
