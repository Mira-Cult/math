import Shared.Codes.UnaryRequestValidation

/-! Table lookup for the bit-list bounded evaluator. The observable state is
a raw binary payload, not an unbounded machine integer. Counters below charge
recursive list calls; instrumentation arithmetic and machine simulation are
not included. -/
namespace Shared.Codes.BitProgramLookup

open Shared.Codes.FinitePrograms
open Shared.Codes.ProgramParseCosts
open Shared.Codes.BitNumeralCompare
open Shared.Codes.BitTableValidation

def lookupFrom (target counter : List Bool) : BitProgram → Option BitPair × Nat
  | [] => (none,1)
  | row::rest =>
      let cmp := compareCost target counter
      if cmp.1 = .eq then (some row,1+cmp.2)
      else
        let next := increment counter
        let result := lookupFrom target next.1 rest
        (result.1,1+cmp.2+next.2+result.2)

theorem lookupFrom_correct (target counter : List Bool) (rows : BitProgram) :
    (lookupFrom target counter rows).1.map interpretPair =
      if value target < value counter then none
      else (interpretProgram rows)[value target-value counter]? := by
  induction rows generalizing counter with
  | nil => simp [lookupFrom,interpretProgram]
  | cons row rest ih =>
    have hc : (compareCost target counter).1 = compare (value target) (value counter) := by
      rw [compareCost_correct,compareBits_correct]
    by_cases he : value target = value counter
    · have heq : (compareCost target counter).1 = .eq := by rw [hc,compare_eq_iff_eq]; exact he
      simp [lookupFrom,heq,he,interpretProgram]
    · have hne : (compareCost target counter).1 ≠ .eq := by
        rw [hc]
        intro h
        exact he (compare_eq_iff_eq.mp h)
      simp only [lookupFrom,hne,↓reduceIte,Prod.fst]
      rw [ih,increment_value]
      by_cases hlt : value target < value counter
      · have hl' : value target < value counter+1 := by omega
        simp [hlt,hl']
      · have hgt : value counter < value target := by omega
        have hn : ¬ value target < value counter+1 := by omega
        have hindex : value target-value counter = (value target-(value counter+1))+1 := by omega
        simp [interpretProgram,hlt,hn,hindex,List.getElem?_cons_succ]

theorem lookupFrom_steps (target counter : List Bool) (rows : BitProgram) :
    (lookupFrom target counter rows).2 ≤
      (rows.length+1)*(target.length+2*counter.length+2*rows.length+6) := by
  induction rows generalizing counter with
  | nil => simp [lookupFrom]
  | cons row rest ih =>
    have hc := compareCost_steps target counter
    by_cases he : (compareCost target counter).1 = .eq
    · simp only [lookupFrom,he,↓reduceIte,List.length_cons]
      have hmul : target.length+2*counter.length+2*(rest.length+1)+6 ≤
          (rest.length+1+1)*(target.length+2*counter.length+2*(rest.length+1)+6) := by
        simpa using Nat.le_mul_of_pos_left (target.length+2*counter.length+2*(rest.length+1)+6) (by omega)
      omega
    · have hi := increment_steps counter
      have hl := increment_length counter
      have ht := ih (increment counter).1
      have hmono :
          (rest.length+1)*(target.length+2*(increment counter).1.length+2*rest.length+6) ≤
          (rest.length+1)*(target.length+2*(counter.length+1)+2*rest.length+6) :=
        Nat.mul_le_mul_left _ (by omega)
      have ht' := ht.trans hmono
      simp only [lookupFrom,he,↓reduceIte,List.length_cons]
      simp only [Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add] at *
      omega

def lookup (state : List Bool) (rows : BitProgram) : Option BitPair × Nat :=
  let normalized := normalizeCost state
  let result := lookupFrom normalized.1 [] rows
  (result.1,1+normalized.2+result.2)

theorem lookup_correct (state : List Bool) (rows : BitProgram) :
    (lookup state rows).1.map interpretPair = (interpretProgram rows)[Computability.decodeNat state]? := by
  simp [lookup,lookupFrom_correct,normalizeCost_correct,value_normalize,value]

theorem lookup_steps (state : List Bool) (rows : BitProgram) :
    (lookup state rows).2 ≤ (rows.length+1)*(state.length+2*rows.length+10)+state.length+3 := by
  have hn := normalizeCost_steps state
  have hl : (normalizeCost state).1.length ≤ state.length+1 := by
    rw [normalizeCost_correct]
    exact Shared.ComplexityBridge.NumeralNormalization.normalize_length state
  have h := lookupFrom_steps (normalizeCost state).1 [] rows
  have hm : (rows.length+1)*((normalizeCost state).1.length+2*rows.length+6) ≤
      (rows.length+1)*(state.length+2*rows.length+10) := Nat.mul_le_mul_left _ (by omega)
  simp only [lookup,List.length_nil,Nat.mul_zero,Nat.add_zero] at *
  omega

theorem lookupFrom_mem (target counter : List Bool) (rows : BitProgram) (row : BitPair)
    (h : (lookupFrom target counter rows).1 = some row) : row ∈ rows := by
  induction rows generalizing counter with
  | nil => simp [lookupFrom] at h
  | cons first rest ih =>
    by_cases he : (compareCost target counter).1 = .eq
    · simp [lookupFrom,he] at h
      subst row
      simp
    · have ht : (lookupFrom target (increment counter).1 rest).1 = some row := by
        simpa [lookupFrom,he] using h
      exact List.mem_cons_of_mem first (ih _ ht)

theorem lookup_mem (state : List Bool) (rows : BitProgram) (row : BitPair)
    (h : (lookup state rows).1 = some row) : row ∈ rows := by
  exact lookupFrom_mem (normalizeCost state).1 [] rows row (by simpa [lookup] using h)

abbrev BitConfig := List Bool × Tape
abbrev BitStatus := Option (Bool ⊕ BitConfig)

def interpretConfig (c : BitConfig) : Config := (Computability.decodeNat c.1,c.2)

def interpretStatus (s : BitStatus) : Status :=
  s.map fun v => v.map id interpretConfig

def executeRow (row : BitRow) (t : Tape) : BitStatus × Nat :=
  let c0 := compareRawCost row.2.2.2 []
  let c1 := compareRawCost row.2.2.2 [true]
  let c2 := compareRawCost row.2.2.2 [false,true]
  (if c0.1 = .eq then some (.inr (row.2.2.1,moveTape (!row.2.1) row.1 t))
   else if c1.1 = .eq then some (.inl false)
   else if c2.1 = .eq then some (.inl true)
   else none,1+c0.2+c1.2+c2.2)

theorem executeRow_correct (row : BitRow) (t : Tape) :
    interpretStatus (executeRow row t).1 = Shared.Codes.FinitePrograms.executeRow (interpretRow row) t := by
  have h0 : Computability.decodeNat [] = 0 := rfl
  have h1 : Computability.decodeNat [true] = 1 := by decide
  have h2 : Computability.decodeNat [false,true] = 2 := by decide
  simp only [executeRow,compareRawCost_correct,h0,h1,h2,compare_eq_iff_eq,
    interpretRow,Shared.Codes.FinitePrograms.executeRow]
  split_ifs <;> simp_all [interpretStatus,interpretConfig]

theorem executeRow_steps (row : BitRow) (t : Tape) :
    (executeRow row t).2 ≤ 6*row.2.2.2.length+31 := by
  have h0 := compareRawCost_steps row.2.2.2 []
  have h1 := compareRawCost_steps row.2.2.2 [true]
  have h2 := compareRawCost_steps row.2.2.2 [false,true]
  simp only [executeRow,List.length_nil,List.length_cons] at *
  omega

def step (rows : BitProgram) (c : BitConfig) : BitStatus × Nat :=
  let found := lookup c.1 rows
  match found.1 with
  | none => (none,1+found.2)
  | some pair =>
      let row := if c.2.2.1 then pair.2 else pair.1
      let result := executeRow row c.2
      (result.1,1+found.2+result.2)

theorem step_correct (rows : BitProgram) (c : BitConfig) :
    interpretStatus (step rows c).1 = Shared.Codes.FinitePrograms.step (interpretProgram rows) (interpretConfig c) := by
  have hl := lookup_correct c.1 rows
  cases hr : (lookup c.1 rows).1 with
  | none =>
    have hn : (interpretProgram rows)[Computability.decodeNat c.1]? = none := by rw [←hl,hr]; rfl
    simp only [step,hr,interpretStatus,Option.map_none,FinitePrograms.step,interpretConfig,hn]
  | some pair =>
    have hs : (interpretProgram rows)[Computability.decodeNat c.1]? = some (interpretPair pair) := by rw [←hl,hr]; rfl
    cases hb : c.2.2.1 <;>
      simpa only [step,hr,hb,Bool.false_eq_true,↓reduceIte,FinitePrograms.step,interpretConfig,hs,
        interpretPair,Prod.fst,Prod.snd,FinitePrograms.executeRow] using executeRow_correct (if c.2.2.1 then pair.2 else pair.1) c.2

theorem pairWeight_le (rows : BitProgram) (pair : BitPair) (h : pair ∈ rows) :
    pairWeight pair ≤ tableWeight rows := by
  induction rows with
  | nil => simp at h
  | cons first rest ih =>
    simp only [List.mem_cons] at h
    simp only [tableWeight,List.map_cons,List.sum_cons]
    rcases h with rfl | h
    · omega
    · have hh := ih h
      simp only [tableWeight] at hh
      omega

theorem step_steps (rows : BitProgram) (c : BitConfig) :
    (step rows c).2 ≤ (rows.length+1)*(c.1.length+2*rows.length+10)+c.1.length+6*tableWeight rows+35 := by
  have hl := lookup_steps c.1 rows
  cases hr : (lookup c.1 rows).1 with
  | none => simp only [step,hr]; omega
  | some pair =>
    have hm := lookup_mem c.1 rows pair hr
    have hw := pairWeight_le rows pair hm
    let row := if c.2.2.1 then pair.2 else pair.1
    have ht : row.2.2.2.length ≤ tableWeight rows := by
      dsimp [row,pairWeight,rowWeight] at *
      split_ifs <;> omega
    have he := executeRow_steps row c.2
    simp only [step,hr]
    change 1+(lookup c.1 rows).2+(executeRow row c.2).2 ≤ _
    omega

def advance (rows : BitProgram) : BitStatus → BitStatus × Nat
  | none => (none,1)
  | some (.inl b) => (some (.inl b),1)
  | some (.inr c) => let r := step rows c; (r.1,1+r.2)

theorem advance_correct (rows : BitProgram) (s : BitStatus) :
    interpretStatus (advance rows s).1 = FinitePrograms.advance (interpretProgram rows) (interpretStatus s) := by
  cases s with
  | none => rfl
  | some v =>
    cases v with
    | inl b => rfl
    | inr c => simpa [advance,interpretStatus,interpretConfig,FinitePrograms.advance] using step_correct rows c

/-- One recursive call per unary fuel cell. The table and machine have no
unbounded integer state. -/
def run (rows : BitProgram) (initial : BitConfig) : List Bool → BitStatus × Nat
  | [] => (some (.inr initial),1)
  | _::fuel =>
      let prior := run rows initial fuel
      let next := advance rows prior.1
      (next.1,1+prior.2+next.2)

theorem run_correct (rows : BitProgram) (initial : BitConfig) (fuel : List Bool) :
    interpretStatus (run rows initial fuel).1 =
      FinitePrograms.run (interpretProgram rows) (interpretConfig initial) fuel.length := by
  induction fuel with
  | nil => rfl
  | cons b fuel ih =>
    simp only [run,List.length_cons,FinitePrograms.run_succ]
    rw [advance_correct,ih]

def initial (input : List Bool) : BitConfig := ([],(FinitePrograms.initial input).2)

def bounded (rows : BitProgram) (input fuel : List Bool) : Option Bool :=
  match (run rows (initial input) fuel).1 with
  | some (.inl b) => some b
  | _ => none

theorem bounded_correct (rows : BitProgram) (input fuel : List Bool) :
    bounded rows input fuel = FinitePrograms.bounded (interpretProgram rows) input fuel.length := by
  have h := run_correct rows (initial input) fuel
  have hi : interpretConfig (initial input) = FinitePrograms.initial input := by
    simp [interpretConfig,initial,FinitePrograms.initial,Computability.decodeNat,Computability.decodeNum]
  rw [hi] at h
  unfold bounded FinitePrograms.bounded
  cases hs : (run rows (initial input) fuel).1 with
  | none => simp [interpretStatus,hs] at h; simp [hs,←h]
  | some v =>
    cases v with
    | inl b => simp [interpretStatus,hs] at h; simp [hs,←h]
    | inr c => simp [interpretStatus,hs] at h; simp [hs,←h]

theorem step_state_length (rows : BitProgram) (c next : BitConfig)
    (h : (step rows c).1 = some (.inr next)) : next.1.length ≤ tableWeight rows := by
  cases hr : (lookup c.1 rows).1 with
  | none => simp [step,hr] at h
  | some pair =>
    have hm := lookup_mem c.1 rows pair hr
    have hw := pairWeight_le rows pair hm
    let row := if c.2.2.1 then pair.2 else pair.1
    have hn : row.2.2.1.length ≤ tableWeight rows := by
      dsimp [row,pairWeight,rowWeight] at *
      split_ifs <;> omega
    simp only [step,hr] at h
    change (executeRow row c.2).1 = some (.inr next) at h
    unfold executeRow at h
    dsimp only at h
    split_ifs at h <;> simp_all
    cases h
    exact hn

theorem run_state_length (rows : BitProgram) (initial : BitConfig) (fuel : List Bool) (c : BitConfig)
    (h : (run rows initial fuel).1 = some (.inr c)) : c.1.length ≤ initial.1.length+tableWeight rows := by
  induction fuel generalizing c with
  | nil => simp [run] at h; subst c; omega
  | cons b fuel ih =>
    cases hp : (run rows initial fuel).1 with
    | none => simp [run,hp,advance] at h
    | some v =>
      cases v with
      | inl x => simp [run,hp,advance] at h
      | inr previous =>
        have hs : (step rows previous).1 = some (.inr c) := by simpa [run,hp,advance] using h
        have ht := step_state_length rows previous c hs
        omega

def stepBudget (rows : BitProgram) (initial : BitConfig) : Nat :=
  let stateBound := initial.1.length+tableWeight rows
  (rows.length+1)*(stateBound+2*rows.length+10)+stateBound+6*tableWeight rows+35

theorem run_steps (rows : BitProgram) (initial : BitConfig) (fuel : List Bool) :
    (run rows initial fuel).2 ≤ 1+fuel.length*(stepBudget rows initial+2) := by
  induction fuel with
  | nil => simp [run]
  | cons b fuel ih =>
    cases hp : (run rows initial fuel).1 with
    | none =>
      simp only [run,hp,advance,List.length_cons,Nat.succ_mul]
      omega
    | some v =>
      cases v with
      | inl x =>
        simp only [run,hp,advance,List.length_cons,Nat.succ_mul]
        omega
      | inr c =>
        have hc := run_state_length rows initial fuel c hp
        have ht := step_steps rows c
        have hm : (rows.length+1)*(c.1.length+2*rows.length+10) ≤
            (rows.length+1)*(initial.1.length+tableWeight rows+2*rows.length+10) :=
          Nat.mul_le_mul_left _ (by omega)
        have hstep : (step rows c).2 ≤ stepBudget rows initial := by
          simp only [stepBudget]
          omega
        simp only [run,hp,advance,List.length_cons,Nat.succ_mul]
        omega

theorem parseAndCheck_success (bits : List Bool) (rows : BitProgram)
    (h : (parseAndCheck bits).1 = some rows) : (programParser bits).1 = some rows := by
  cases hp : (programParser bits).1 with
  | none => simp [parseAndCheck,hp] at h
  | some p =>
    cases hc : (checkProgram p).1 <;> simp [parseAndCheck,hp,hc] at h
    subst p
    rfl

theorem validated_run_steps (description : List Bool) (rows : BitProgram) (input fuel : List Bool)
    (h : (parseAndCheck description).1 = some rows) :
    (run rows (initial input) fuel).2 ≤
      1+fuel.length*((description.length+1)*(3*description.length+10)+7*description.length+37) := by
  have hs := parseAndCheck_success description rows h
  have hn := programParser_count description rows hs
  have hw := programParser_weight description rows hs
  have hr := run_steps rows (initial input) fuel
  have hfactor : rows.length+1 ≤ description.length+1 := by omega
  have hbound : tableWeight rows+2*rows.length+10 ≤ 3*description.length+10 := by omega
  have hmul := Nat.mul_le_mul hfactor hbound
  have hbudget : stepBudget rows (initial input)+2 ≤
      (description.length+1)*(3*description.length+10)+7*description.length+37 := by
    simp only [stepBudget,initial,List.length_nil,Nat.zero_add]
    omega
  exact hr.trans (Nat.add_le_add_left (Nat.mul_le_mul_left fuel.length hbudget) 1)

namespace Fixtures
example : bounded [] [] [] = none := by rw [bounded_correct]; rfl
example : bounded [] [] [true] = none := by rw [bounded_correct]; rfl
def yes : BitProgram := [((false,false,[],[false]),(false,false,[],[false]))]
example : bounded yes [] [] = none := by rw [bounded_correct]; decide
example : bounded yes [] [true] = some true := by rw [bounded_correct]; decide
def bad : BitProgram := [((false,false,[],[true,true]),(false,false,[],[true,true]))]
example : bounded bad [] [true] = none := by rw [bounded_correct]; decide
end Fixtures

end Shared.Codes.BitProgramLookup
