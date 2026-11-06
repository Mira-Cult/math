import Shared.Beeping.NPcoNP.Source284Parser
import Mathlib.Computability.Partrec

/-! Computability of the concrete marker/payload parser.  The executable
iteration below performs at most `scan + 1` total steps and agrees with the
source loop; no polynomial-cost claim or physical-machine implementation is
made here. -/
namespace Shared.Beeping.NPcoNP.Source284Parser

abbrev ParserState := Nat × Nat × Nat

def parseStep (s : ParserState) : ParserState :=
  if s.1 % 2 = 1 then
    (s.1 / 4, s.2.1 + 1, 2 * s.2.2 + (s.1 / 2) % 2)
  else s

theorem parseStep_primrec : Primrec parseStep := by
  have hs : Primrec (fun s : ParserState => s.1) := Primrec.fst
  have hn : Primrec (fun s : ParserState => s.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun s : ParserState => s.2.2) := Primrec.snd.comp Primrec.snd
  have hmod : Primrec (fun s : ParserState => s.1 % 2) :=
    Primrec.nat_mod.comp hs (Primrec.const 2)
  have hq : Primrec (fun s : ParserState => s.1 / 4) :=
    Primrec.nat_div.comp hs (Primrec.const 4)
  have hp : Primrec (fun s : ParserState => (s.1 / 2) % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hs (Primrec.const 2)) (Primrec.const 2)
  have hn' : Primrec (fun s : ParserState => s.2.1 + 1) :=
    Primrec.nat_add.comp hn (Primrec.const 1)
  have he' : Primrec (fun s : ParserState => 2 * s.2.2 + (s.1 / 2) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) he) hp
  exact Primrec.ite (Primrec.eq.comp hmod (Primrec.const 1))
    (Primrec.pair hq (Primrec.pair hn' he')) Primrec.id

/-- Once a zero marker is reached the iterative state is fixed. -/
theorem parseStep_fixed (s : ParserState) (h : s.1 % 2 = 0) : parseStep s = s := by
  simp [parseStep, h]

theorem iterate_fixed (s : ParserState) (h : s.1 % 2 = 0) (k : Nat) :
    (parseStep^[k]) s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', parseStep_fixed s h, ih]

/-- The recursion consumes at least one unit of the scan in every odd step;
the numerical scan itself is therefore a sufficient primitive-recursive
iteration bound, independently of the magnitude of the accumulators. -/
theorem run_eq_iterate (k scan n e : Nat) (hk : scan < k) :
    ((parseStep^[k]) (scan, n, e)).2 = run scan n e := by
  induction k generalizing scan n e with
  | zero => omega
  | succ k ih =>
    by_cases h : scan % 2 = 1
    · have hscan : 0 < scan := by omega
      have hlt : scan / 4 < scan := Nat.div_lt_self hscan (by decide)
      have hbound : scan / 4 < k := by omega
      rw [Function.iterate_succ_apply]
      simp only [parseStep, h, ↓reduceIte]
      rw [ih (scan / 4) (n + 1) (2 * e + (scan / 2) % 2) hbound,
        run_odd scan n e h]
    · have hz : scan % 2 = 0 := by omega
      rw [iterate_fixed (scan,n,e) hz (k+1), run_even scan n e hz]

theorem parse_primrec : Primrec parse := by
  have hinit : Primrec (fun i : Nat => (show ParserState from (i, 0, 1))) :=
    Primrec.pair Primrec.id (Primrec.const (0,1))
  have hiter : Primrec (fun i : Nat => (parseStep^[i+1]) (i, 0, 1)) :=
    Primrec.nat_iterate (Primrec.succ.comp Primrec.id) hinit
      (parseStep_primrec.comp Primrec.snd).to₂
  have hout : Primrec (fun i : Nat => ((parseStep^[i+1]) (i, 0, 1)).2) :=
    Primrec.snd.comp hiter
  apply hout.of_eq
  intro i
  exact run_eq_iterate (i+1) i 0 1 (by omega)

theorem parse_computable : Computable parse := parse_primrec.to_comp
theorem length_primrec : Primrec length := Primrec.fst.comp parse_primrec
theorem description_primrec : Primrec description := Primrec.snd.comp parse_primrec

end Shared.Beeping.NPcoNP.Source284Parser
