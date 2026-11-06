import Shared.ComplexityBridge.ParserComputability
import Shared.Beeping.Controller

/-! Finite binary program tables and a bounded evaluator. This module does
not prove a polynomial simulation or any bit-cost bound. -/
namespace Shared.Codes.FinitePrograms

/-- A row consists of a write bit, a direction bit (`false` means left), a
numeric next state, and a result tag. Tag 0 continues, 1 returns false, 2
returns true, and any other tag is invalid. -/
abbrev Row := Bool × Bool × Nat × Nat
abbrev Program := List (Row × Row)
/-- Left cells are nearest first; the current cell and right cells follow. -/
abbrev Tape := List Bool × Bool × List Bool
abbrev Config := Nat × Tape
/-- `none` is invalid, `.inl` is a Boolean result, `.inr` continues. -/
abbrev Status := Option (Bool ⊕ Config)
abbrev Candidate := Nat × Program

def moveTape (leftward : Bool) (written : Bool) (tape : Tape) : Tape :=
  if leftward then
    (tape.1.tail, tape.1.head?.getD false, written :: tape.2.2)
  else
    (written :: tape.1, tape.2.2.head?.getD false, tape.2.2.tail)

def initial (input : List Bool) : Config :=
  (0, [], input.head?.getD false, input.tail)

def step (program : Program) (config : Config) : Status :=
  match program[config.1]? with
  | none => none
  | some rows =>
    let row := if config.2.2.1 then rows.2 else rows.1
    match row.2.2.2 with
    | 0 => some (.inr (row.2.2.1, moveTape (!row.2.1) row.1 config.2))
    | 1 => some (.inl false)
    | 2 => some (.inl true)
    | _ => none

def advance (program : Program) : Status → Status
  | none => none
  | some (.inl b) => some (.inl b)
  | some (.inr c) => step program c

def run (program : Program) (config : Config) : Nat → Status
  | 0 => some (.inr config)
  | n + 1 => advance program (run program config n)

def bounded (program : Program) (input : List Bool) (fuel : Nat) : Option Bool :=
  match run program (initial input) fuel with
  | some (.inl b) => some b
  | _ => none

def validRow (length : Nat) (row : Row) : Bool :=
  (row.2.2.2 ≤ 2) && (row.2.2.2 != 0 || row.2.2.1 < length)

def valid (program : Program) : Bool :=
  !program.isEmpty && program.all fun rows =>
    validRow program.length rows.1 && validRow program.length rows.2

def decode (n : Nat) : Option Candidate :=
  match (Encodable.decode n : Option Candidate) with
  | none => none
  | some (k, p) => if valid p then some (k, p) else none

def clock (input : List Bool) (k : Nat) : Nat := (input.length + 2) ^ k

def evaluate (candidate : Candidate) (input : List Bool) : Option Bool :=
  bounded candidate.2 input (clock input candidate.1)

/-- Test every raw SAT input, presenting its pinned Google encoding to the
finite candidate. The clock counts the encoded tape length. -/
def compareSAT (e n : Nat) : Bool :=
  match decode e with
  | none => false
  | some candidate =>
    let x := Shared.Codes.Inputs.inputAt n
    match evaluate candidate (BitstringEncoding.bitEncode x) with
    | none => false
    | some b => b == Shared.ComplexityBridge.CNF.sat x

@[simp] theorem run_zero (p : Program) (c : Config) : run p c 0 = some (.inr c) := rfl
@[simp] theorem run_succ (p : Program) (c : Config) (n : Nat) :
    run p c (n + 1) = advance p (run p c n) := rfl

@[simp] theorem advance_result (p : Program) (b : Bool) :
    advance p (some (.inl b)) = some (.inl b) := rfl

@[simp] theorem advance_invalid (p : Program) : advance p none = none := rfl

theorem run_add (p : Program) (c : Config) (m n : Nat) :
    run p c (m + n) = (advance p)^[n] (run p c m) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.add_succ, run_succ, ih, Function.iterate_succ_apply']

theorem run_result_stable (p : Program) (c : Config) {m n : Nat} {b : Bool}
    (hm : m ≤ n) (h : run p c m = some (.inl b)) : run p c n = some (.inl b) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [run_add, h]
  induction d with
  | zero => rfl
  | succ d ih => simp [Function.iterate_succ_apply, ih]

theorem bounded_iff_result (p : Program) (input : List Bool) (fuel : Nat) (b : Bool) :
    bounded p input fuel = some b ↔
      ∃ t ≤ fuel, run p (initial input) t = some (.inl b) := by
  constructor
  · intro h
    refine ⟨fuel, le_rfl, ?_⟩
    unfold bounded at h
    cases hr : run p (initial input) fuel with
    | none => simp [hr] at h
    | some v =>
      cases v with
      | inl out => simp [hr] at h; subst out; rfl
      | inr c => simp [hr] at h
  · rintro ⟨t, ht, hr⟩
    unfold bounded
    rw [run_result_stable p (initial input) ht hr]

@[simp] theorem bounded_zero (p : Program) (input : List Bool) : bounded p input 0 = none := rfl

theorem decode_encode (candidate : Candidate) (h : valid candidate.2 = true) :
    decode (Encodable.encode candidate) = some candidate := by
  rcases candidate with ⟨k, p⟩
  simp [decode, h]

theorem candidate_coverage (candidate : Candidate) (h : valid candidate.2 = true) :
    ∃ e, decode e = some candidate := ⟨Encodable.encode candidate, decode_encode candidate h⟩


/-! The following results establish recursion-theoretic computability of the
bounded interpreter. They do not charge bit operations or prove TM2 coverage. -/
abbrev MoveArg := Bool × Bool × Tape

theorem moveTape_primrec : Primrec (fun p : MoveArg => moveTape p.1 p.2.1 p.2.2) := by
  have hl : Primrec (fun p : MoveArg => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p : MoveArg => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hw : Primrec (fun p : MoveArg => p.2.1) := Primrec.fst.comp Primrec.snd
  have hlbit := Primrec.option_getD.comp (Primrec.list_head?.comp hl) (Primrec.const false)
  have hrbit := Primrec.option_getD.comp (Primrec.list_head?.comp hr) (Primrec.const false)
  have hleft : Primrec (fun p : MoveArg =>
      (p.2.2.1.tail, p.2.2.1.head?.getD false, p.2.1 :: p.2.2.2.2)) :=
    Primrec.pair (Primrec.list_tail.comp hl)
      (Primrec.pair hlbit (Primrec.list_cons.comp hw hr))
  have hright : Primrec (fun p : MoveArg =>
      (p.2.1 :: p.2.2.1, p.2.2.2.2.head?.getD false, p.2.2.2.2.tail)) :=
    Primrec.pair (Primrec.list_cons.comp hw hl)
      (Primrec.pair hrbit (Primrec.list_tail.comp hr))
  have h := Primrec.cond (Primrec.fst : Primrec (fun p : MoveArg => p.1)) hleft hright
  apply h.of_eq
  intro p
  rcases p with ⟨b, w, tape⟩
  cases b <;> rfl

theorem initial_primrec : Primrec initial := by
  have hbit := Primrec.option_getD.comp Primrec.list_head? (Primrec.const false)
  exact Primrec.pair (Primrec.const 0)
    (Primrec.pair (Primrec.const []) (Primrec.pair hbit Primrec.list_tail))


def rowAt (program : Program) (config : Config) : Option Row :=
  (program[config.1]?).map (fun rows => if config.2.2.1 then rows.2 else rows.1)

def executeRow (row : Row) (tape : Tape) : Status :=
  match row.2.2.2 with
  | 0 => some (.inr (row.2.2.1, moveTape (!row.2.1) row.1 tape))
  | 1 => some (.inl false)
  | 2 => some (.inl true)
  | _ => none

theorem rowAt_primrec : Primrec₂ rowAt := by
  have hrows : Primrec (fun p : Program × Config => p.1[p.2.1]?) :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : (Program × Config) × (Row × Row) => p.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hr : Primrec (fun p : (Program × Config) × (Row × Row) =>
      if p.1.2.2.2.1 then p.2.2 else p.2.1) := by
    have ht : Primrec (fun p : (Program × Config) × (Row × Row) => p.2.2) := Primrec.snd.comp Primrec.snd
    have hf : Primrec (fun p : (Program × Config) × (Row × Row) => p.2.1) := Primrec.fst.comp Primrec.snd
    refine (Primrec.cond hb ht hf).of_eq ?_
    intro p
    cases p.1.2.2.2.1 <;> rfl
  exact (Primrec.option_map hrows hr.to₂).to₂

theorem executeRow_primrec : Primrec₂ executeRow := by
  let Arg := Row × Tape
  have hnext : Primrec (fun p : Arg => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hdir : Primrec (fun p : Arg => !p.1.2.1) :=
    Primrec.not.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hwrite : Primrec (fun p : Arg => p.1.1) := Primrec.fst.comp Primrec.fst
  have htape : Primrec (fun p : Arg => moveTape (!p.1.2.1) p.1.1 p.2) :=
    moveTape_primrec.comp (Primrec.pair hdir (Primrec.pair hwrite Primrec.snd))
  have hcontinue : Primrec (fun p : Arg =>
      (some (.inr (p.1.2.2.1, moveTape (!p.1.2.1) p.1.1 p.2)) : Status)) :=
    Primrec.option_some.comp (Primrec.sumInr.comp (Primrec.pair hnext htape))
  have htag : Primrec (fun p : Arg => p.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h := Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) hcontinue
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (Primrec.const (some (.inl false) : Status))
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) (Primrec.const (some (.inl true) : Status))
        (Primrec.const none)))
  apply h.to₂.of_eq
  intro row tape
  rcases row with ⟨w, dir, next, tag⟩
  cases tag with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

theorem step_primrec : Primrec₂ step := by
  have h := Primrec.option_bind rowAt_primrec
    (executeRow_primrec.comp Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  apply h.to₂.of_eq
  intro program config
  unfold rowAt step executeRow
  cases hrows : program[config.1]? with
  | none => rfl
  | some rows => cases config.2.2.1 <;> rfl


theorem advance_primrec : Primrec₂ advance := by
  let Arg := Program × (Bool ⊕ Config)
  have hinl : Primrec₂ (fun (_ : Arg) (b : Bool) => (some (.inl b) : Status)) :=
    (Primrec.option_some.comp (Primrec.sumInl.comp Primrec.snd)).to₂
  have hinr : Primrec₂ (fun p : Arg => fun c : Config => step p.1 c) :=
    (step_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hsum : Primrec (fun p : Arg => match p.2 with
      | .inl b => (some (.inl b) : Status)
      | .inr c => step p.1 c) := by
    refine (Primrec.sumCasesOn Primrec.snd hinl hinr).of_eq ?_
    intro p
    cases p.2 <;> rfl
  have h := Primrec.option_casesOn Primrec.snd (Primrec.const none)
    (hsum.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  apply h.to₂.of_eq
  intro program status
  cases status with
  | none => rfl
  | some v => cases v <;> rfl

theorem run_primrec : Primrec (fun p : (Program × Config) × Nat => run p.1.1 p.1.2 p.2) := by
  have hi : Primrec (fun p : (Program × Config) × Nat => (some (.inr p.1.2) : Status)) :=
    Primrec.option_some.comp (Primrec.sumInr.comp (Primrec.snd.comp Primrec.fst))
  have hs : Primrec₂ (fun p : (Program × Config) × Nat => fun s : Status => advance p.1.1 s) :=
    (advance_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂
  have h := Primrec.nat_iterate Primrec.snd hi hs
  apply h.of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', run_succ, ih]

def statusResult : Status → Option Bool
  | some (.inl b) => some b
  | _ => none

theorem statusResult_primrec : Primrec statusResult := by
  have hsum : Primrec (fun s : Bool ⊕ Config => match s with
      | .inl b => some b
      | .inr _ => (none : Option Bool)) := by
    refine (Primrec.sumCasesOn Primrec.id (Primrec.option_some.comp Primrec.snd).to₂
      (Primrec.const none).to₂).of_eq ?_
    intro s
    cases s <;> rfl
  have h := Primrec.option_casesOn Primrec.id (Primrec.const none) (hsum.comp Primrec.snd).to₂
  apply h.of_eq
  intro s
  cases s with
  | none => rfl
  | some v => cases v <;> rfl

theorem bounded_primrec : Primrec (fun p : (Program × List Bool) × Nat => bounded p.1.1 p.1.2 p.2) := by
  have hrun : Primrec (fun p : (Program × List Bool) × Nat =>
      run p.1.1 (initial p.1.2) p.2) :=
    run_primrec.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (initial_primrec.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)
  have h := statusResult_primrec.comp hrun
  apply h.of_eq
  intro p
  unfold statusResult bounded
  cases run p.1.1 (initial p.1.2) p.2 with
  | none => rfl
  | some v => cases v <;> rfl


theorem validRow_primrec : Primrec₂ validRow := by
  have htag : Primrec (fun p : Nat × Row => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hnext : Primrec (fun p : Nat × Row => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hle := Primrec.nat_le.decide.comp htag (Primrec.const 2)
  have hne := Primrec.not.comp (Primrec.beq.comp htag (Primrec.const 0))
  have hlt := Primrec.nat_lt.decide.comp hnext Primrec.fst
  exact (Primrec.and.comp hle (Primrec.or.comp hne hlt)).to₂

theorem valid_primrec : Primrec valid := by
  have hempty : Primrec (fun p : Program => p.isEmpty) := by
    have hh : Primrec₂ (fun (_ : Program) (_ : (Row × Row) × Program) => false) := Primrec₂.const false
    have h := Primrec.list_casesOn Primrec.id (Primrec.const true) hh
    apply h.of_eq
    intro p
    cases p <;> rfl
  have hrow : Primrec₂ (fun p : Program => fun rows : Row × Row =>
      validRow p.length rows.1 && validRow p.length rows.2) :=
    (Primrec.and.comp
      (validRow_primrec.comp (Primrec.list_length.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (validRow_primrec.comp (Primrec.list_length.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.and.comp (Primrec.not.comp hempty)
    (Shared.ComplexityBridge.CNF.list_all_primrec Primrec.id hrow)

theorem clock_primrec : Primrec₂ clock := by
  have hpow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  exact (hpow.comp (Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 2)) Primrec.snd).to₂

theorem evaluate_primrec : Primrec₂ evaluate := by
  have hc : Primrec (fun p : Candidate × List Bool => clock p.2 p.1.1) :=
    clock_primrec.comp Primrec.snd (Primrec.fst.comp Primrec.fst)
  exact (bounded_primrec.comp (Primrec.pair
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd) hc)).to₂

def checked (candidate : Candidate) : Option Candidate :=
  if valid candidate.2 then some candidate else none

theorem checked_primrec : Primrec checked := by
  have hv := valid_primrec.comp (Primrec.snd : Primrec (fun c : Candidate => c.2))
  have h := Primrec.cond hv Primrec.option_some (Primrec.const none)
  apply h.of_eq
  intro c
  unfold checked
  cases valid c.2 <;> rfl

theorem decode_computable : Computable decode := by
  have h := Computable.option_bind (Computable.decode : Computable (Encodable.decode : Nat → Option Candidate))
    (checked_primrec.to_comp.comp Computable.snd).to₂
  apply h.of_eq
  intro n
  unfold decode checked
  cases (Encodable.decode n : Option Candidate) with
  | none => rfl
  | some c => rcases c with ⟨k, p⟩; cases valid p <;> rfl


namespace InputEncoding

/-- Primitive-recursive Google bit encoding of a pair of raw bitstrings. -/
theorem delimit_primrec : Primrec BitstringEncoding.delimit := by
  have hs : Primrec₂ (fun (_ : List Bool) => fun p : Bool × List Bool =>
      true :: p.1 :: p.2) :=
    (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_foldr (Primrec.id : Primrec (id : List Bool → List Bool))
    (Primrec.const [false]) hs
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [id_eq, List.foldr_cons] at *
    simp [BitstringEncoding.delimit, ih]

theorem boolEncoding_primrec : Primrec (@BitstringEncoding.bitEncode Bool _) := by
  exact Primrec.list_cons.comp Primrec.id (Primrec.const [])

theorem bitListEncoding_primrec : Primrec (@BitstringEncoding.bitEncode (List Bool) _) := by
  have hmap : Primrec (fun xs : List Bool => xs.map (fun b => BitstringEncoding.delimit (BitstringEncoding.bitEncode b))) :=
    Primrec.list_map Primrec.id (delimit_primrec.comp (boolEncoding_primrec.comp Primrec.snd)).to₂
  have h := Primrec.list_flatten.comp hmap
  apply h.of_eq
  intro xs
  change (xs.map (fun b => BitstringEncoding.delimit (BitstringEncoding.bitEncode b))).flatten =
    ((xs.map (fun b => BitstringEncoding.bitEncode b)).map BitstringEncoding.delimit).flatten
  simp only [List.map_map, Function.comp_def]


end InputEncoding

theorem compareSAT_computable : Computable₂ compareSAT := by
  let Arg := Candidate × Nat
  have hx : Computable (fun p : Arg => Shared.Codes.Inputs.inputAt p.2) :=
    Shared.Codes.Inputs.computable.comp Computable.snd
  have hencoded : Computable (fun p : Arg => BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt p.2)) :=
    InputEncoding.bitListEncoding_primrec.to_comp.comp hx
  have he : Computable (fun p : Arg => evaluate p.1 (BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt p.2))) :=
    evaluate_primrec.to_comp.comp Computable.fst hencoded
  have hs : Computable (fun p : Arg => Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) :=
    Shared.ComplexityBridge.ParserComputability.sat_computable.comp hx
  have hb : Computable₂ (fun p : Arg => fun b : Bool =>
      b == Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) :=
    (Primrec.beq.to_comp.comp Computable.snd (hs.comp Computable.fst)).to₂
  have hresult : Computable (fun p : Arg =>
      match evaluate p.1 (BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt p.2)) with
      | none => false
      | some b => b == Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt p.2)) := by
    refine (Computable.option_casesOn he (Computable.const false) hb).of_eq ?_
    intro p
    cases evaluate p.1 (BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt p.2)) <;> rfl
  have h := Computable.option_casesOn (decode_computable.comp Computable.fst) (Computable.const false)
    (hresult.comp (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨e, n⟩
  unfold compareSAT
  cases decode e <;> rfl

theorem compareSAT_iff (e n : Nat) : compareSAT e n = true ↔ ∃ c,
    decode e = some c ∧ evaluate c (BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt n)) =
      some (Shared.ComplexityBridge.CNF.sat (Shared.Codes.Inputs.inputAt n)) := by
  cases hd : decode e with
  | none => simp [compareSAT, hd]
  | some c =>
    cases he : evaluate c (BitstringEncoding.bitEncode (Shared.Codes.Inputs.inputAt n)) with
    | none => simp [compareSAT, hd, he]
    | some b => simp [compareSAT, hd, he]

theorem good_iff (e : Nat) : (∀ n, compareSAT e n = true) ↔ ∃ c,
    decode e = some c ∧ ∀ input, evaluate c (BitstringEncoding.bitEncode input) = some (Shared.ComplexityBridge.CNF.sat input) := by
  constructor
  · intro h
    obtain ⟨c, hc, _⟩ := (compareSAT_iff e 0).1 (h 0)
    refine ⟨c, hc, ?_⟩
    intro input
    obtain ⟨n, hn⟩ := Shared.Codes.Inputs.covers input
    obtain ⟨c', hc', he⟩ := (compareSAT_iff e n).1 (h n)
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    subst c'
    simpa [hn] using he
  · rintro ⟨c, hc, h⟩ n
    exact (compareSAT_iff e n).2 ⟨c, hc, h _⟩


theorem decode_some_valid {e : Nat} {c : Candidate} (h : decode e = some c) : valid c.2 = true := by
  unfold decode at h
  cases hd : (Encodable.decode e : Option Candidate) with
  | none => simp [hd] at h
  | some d =>
    rcases d with ⟨k, p⟩
    cases hv : valid p <;> simp [hd, hv] at h
    subst c
    exact hv

theorem controller_silent_iff :
    (Shared.Beeping.Controller.system compareSAT 0).EventuallySilent ↔
      ∃ c : Candidate, valid c.2 = true ∧
        ∀ input, evaluate c (BitstringEncoding.bitEncode input) = some (Shared.ComplexityBridge.CNF.sat input) := by
  rw [Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨c, hc, hcorrect⟩ := (good_iff e).1 he
    exact ⟨c, decode_some_valid hc, hcorrect⟩
  · rintro ⟨c, hv, hcorrect⟩
    obtain ⟨e, he⟩ := candidate_coverage c hv
    exact ⟨e, (good_iff e).2 ⟨c, he, hcorrect⟩⟩


end Shared.Codes.FinitePrograms
