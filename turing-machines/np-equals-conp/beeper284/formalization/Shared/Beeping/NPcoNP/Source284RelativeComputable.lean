import Shared.Beeping.NPcoNP.Source284Relative
import Mathlib.Computability.Partrec

/-! Primitive-recursive realization of the exact bounded relative evaluator.
The numerical iteration bounds prove computability; they are not bit-cost
bounds and do not constitute a physical-machine implementation. -/
namespace Shared.Beeping.NPcoNP.Source284Relative

def recordScan (s : Nat × Nat) : Nat × Nat :=
  if s.1 % 2 = 1 then (s.1 / 2, s.2 + 1) else s

theorem recordScan_primrec : Primrec recordScan := by
  have hd : Primrec (fun s : Nat × Nat => s.1) := Primrec.fst
  have hc : Primrec (fun s : Nat × Nat => s.2) := Primrec.snd
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hd (Primrec.const 2)) (Primrec.const 1))
    (Primrec.pair (Primrec.nat_div.comp hd (Primrec.const 2)) (Primrec.succ.comp hc)) Primrec.id

theorem recordScan_fixed (s : Nat × Nat) (h : s.1 % 2 = 0) : recordScan s = s := by
  simp [recordScan, h]

theorem recordScan_iterate_fixed (s : Nat × Nat) (h : s.1 % 2 = 0) (k : Nat) :
    (recordScan^[k]) s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', recordScan_fixed s h, ih]

theorem recordScan_correct (k digit count : Nat) (hk : digit < k) :
    let out := (recordScan^[k]) (digit, count)
    (out.2, out.1 / 2) = ((readRecord digit).1 + count, (readRecord digit).2) := by
  induction k generalizing digit count with
  | zero => omega
  | succ k ih =>
    by_cases h : digit % 2 = 1
    · have hd : 0 < digit := by omega
      have hlt : digit / 2 < digit := Nat.div_lt_self hd (by decide)
      have hbound : digit / 2 < k := by omega
      rw [Function.iterate_succ_apply]
      simp only [recordScan, h, ↓reduceIte]
      have hi := ih (digit / 2) (count + 1) hbound
      rw [readRecord_odd digit h]
      dsimp only at *
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
    · have hz : digit % 2 = 0 := by omega
      rw [recordScan_iterate_fixed (digit,count) hz (k+1), readRecord_even digit hz]
      simp

theorem readRecord_primrec : Primrec readRecord := by
  have hinit : Primrec (fun i : Nat => (i,0)) := Primrec.pair Primrec.id (Primrec.const 0)
  have hiter : Primrec (fun i : Nat => (recordScan^[i+1]) (i,0)) :=
    Primrec.nat_iterate (Primrec.succ.comp Primrec.id) hinit
      (recordScan_primrec.comp Primrec.snd).to₂
  have hr : Primrec (fun i : Nat => (((recordScan^[i+1]) (i,0)).2,
      ((recordScan^[i+1]) (i,0)).1 / 2)) :=
    Primrec.pair (Primrec.snd.comp hiter)
      (Primrec.nat_div.comp (Primrec.fst.comp hiter) (Primrec.const 2))
  apply hr.of_eq
  intro i
  simpa using recordScan_correct (i+1) i 0 (by omega)

def dropStep (digit : Nat) : Nat := (readRecord digit).2

theorem dropStep_primrec : Primrec dropStep := Primrec.snd.comp readRecord_primrec

theorem dropRecords_iterate (digit ordinal : Nat) :
    dropRecords digit ordinal = (dropStep^[ordinal]) digit := by
  induction ordinal generalizing digit with
  | zero => rfl
  | succ ordinal ih =>
    rw [dropRecords, ih, Function.iterate_succ_apply]
    rfl

theorem dropRecords_primrec : Primrec₂ dropRecords := by
  have hi : Primrec (fun p : Nat × Nat => (dropStep^[p.2]) p.1) :=
    Primrec.nat_iterate Primrec.snd Primrec.fst
      (dropStep_primrec.comp Primrec.snd).to₂
  apply hi.to₂.of_eq
  intro digit ordinal
  exact (dropRecords_iterate digit ordinal).symm

theorem record_primrec : Primrec₂ record := by
  exact (Primrec.fst.comp (readRecord_primrec.comp dropRecords_primrec)).to₂



abbrev EncodedConfig := Nat × Nat × Nat
abbrev StepArg := Nat × EncodedConfig

def encodeConfig (c : Config) : EncodedConfig := (c.left, c.right, c.state)
def decodeConfig (c : EncodedConfig) : Config := ⟨c.1, c.2.1, c.2.2⟩

@[simp] theorem decode_encodeConfig (c : Config) : decodeConfig (encodeConfig c) = c := by
  cases c; rfl
@[simp] theorem encode_decodeConfig (c : EncodedConfig) : encodeConfig (decodeConfig c) = c := by
  rcases c with ⟨l,r,s⟩; rfl

def stepEncoded (description : Nat) (c : EncodedConfig) : EncodedConfig :=
  encodeConfig (step description (decodeConfig c))

theorem stepEncoded_primrec (hrecord : Primrec₂ record) : Primrec₂ stepEncoded := by
  let A := StepArg
  have hd : Primrec (fun x : A => x.1) := Primrec.fst
  have hc : Primrec (fun x : A => x.2) := Primrec.snd
  have hl : Primrec (fun x : A => x.2.1) := Primrec.fst.comp hc
  have hr : Primrec (fun x : A => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp hc)
  have hs : Primrec (fun x : A => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp hc)
  have hi : Primrec (fun x : A => x.2.2.2 - 1 + x.2.2.1 % 2) :=
    Primrec.nat_add.comp (Primrec.nat_sub.comp hs (Primrec.const 1))
      (Primrec.nat_mod.comp hr (Primrec.const 2))
  have hv : Primrec (fun x : A => record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2)) :=
    hrecord.comp hd hi
  have hw : Primrec (fun x : A => record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) % 2) :=
    Primrec.nat_mod.comp hv (Primrec.const 2)
  have ht : Primrec (fun x : A => (record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) / 2) % 2) :=
    Primrec.nat_mod.comp (Primrec.nat_div.comp hv (Primrec.const 2)) (Primrec.const 2)
  have hn : Primrec (fun x : A => record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) / 4) :=
    Primrec.nat_div.comp hv (Primrec.const 4)
  have hf : Primrec (fun x : A => x.2.2.1 / 2) := Primrec.nat_div.comp hr (Primrec.const 2)
  have hforward : Primrec (fun x : A => 2 * (x.2.2.1 / 2) +
      record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hf) hw
  have hleft : Primrec (fun x : A => 2 * x.2.1 +
      record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) % 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hl) hw
  have hturn : Primrec (fun x : A => if (record x.1
      (x.2.2.2 - 1 + x.2.2.1 % 2) / 2) % 2 = 1 then
      (2 * (x.2.2.1 / 2) + record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) % 2,
        x.2.1, record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) / 4)
    else (2 * x.2.1 + record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) % 2,
        x.2.2.1 / 2, record x.1 (x.2.2.2 - 1 + x.2.2.1 % 2) / 4)) :=
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 1))
      (Primrec.pair hforward (Primrec.pair hl hn))
      (Primrec.pair hleft (Primrec.pair hf hn))
  have hfinal := Primrec.ite (Primrec.eq.comp hs (Primrec.const 0)) hc hturn
  have hout : Primrec (fun x : A => stepEncoded x.1 x.2) := by
    apply hfinal.of_eq
    intro x
    rcases x with ⟨d,l,r,s⟩
    by_cases hs0 : s = 0
    · simp [stepEncoded, decodeConfig, encodeConfig, step, hs0]
    · by_cases ht0 : (record d (s - 1 + r % 2) / 2) % 2 = 1 <;>
        simp [stepEncoded, decodeConfig, encodeConfig, step, hs0, ht0]
  exact hout.to₂


abbrev RunArg := (Nat × EncodedConfig) × Nat

theorem rawRun_iterate (d : Nat) (r : EncodedConfig) (c : Nat) :
    encodeConfig (run d (decodeConfig r) c) = (stepEncoded d)^[c] r := by
  induction c with
  | zero => simp [run]
  | succ c ih =>
    rw [run_succ, Function.iterate_succ_apply', ← ih]
    simp [stepEncoded]

theorem rawRun_primrec
    (hstep : Primrec (fun p : Nat × EncodedConfig => stepEncoded p.1 p.2)) :
    Primrec (fun p : RunArg => encodeConfig (run p.1.1 (decodeConfig p.1.2) p.2)) := by
  have hstep' : Primrec₂ (fun p : RunArg => fun r : EncodedConfig => stepEncoded p.1.1 r) :=
    (hstep.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂
  have hiter : Primrec (fun p : RunArg => (stepEncoded p.1.1)^[p.2] p.1.2) :=
    Primrec.nat_iterate Primrec.snd (Primrec.snd.comp Primrec.fst) hstep'
  apply hiter.of_eq
  intro p
  exact (rawRun_iterate p.1.1 p.1.2 p.2).symm

theorem any_primrec {α : Type} [Primcodable α]
    (P : α → Nat → Bool) (bound : α → Nat) (hp : Primrec₂ P) (hb : Primrec bound) :
    Primrec (fun a => (List.range (bound a)).any (P a)) := by
  have hlist : Primrec (fun a => List.range (bound a)) := Primrec.list_range.comp hb
  have hfold := Primrec.list_foldr hlist (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply hfold.of_eq
  intro a
  induction List.range (bound a) with
  | nil => rfl
  | cons b bs ih => simp [ih]


abbrev EvalArg := (Nat × Nat) × (Nat × Nat)
abbrev BoundArg := ((Nat × Nat) × Nat) × Nat

def evalArg (p : EvalArg) : Bool := accepts p.1.1 p.1.2 p.2.1 p.2.2

theorem evalArg_primrec
    (hstep : Primrec (fun p : Nat × EncodedConfig => stepEncoded p.1 p.2)) : Primrec evalArg := by
  have hd : Primrec (fun p : EvalArg => p.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun p : EvalArg => p.1.2) := Primrec.snd.comp Primrec.fst
  have hw : Primrec (fun p : EvalArg => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : EvalArg => p.2.2) := Primrec.snd.comp Primrec.snd
  have hstart : Primrec (fun p : EvalArg => (p.2.1,p.1.2,1) : EvalArg → EncodedConfig) :=
    Primrec.pair hw (Primrec.pair hi (Primrec.const 1))
  have hrun : Primrec (fun p : EvalArg =>
      encodeConfig (run p.1.1 (decodeConfig (p.2.1,p.1.2,1)) p.2.2)) :=
    (rawRun_primrec hstep).comp (Primrec.pair (Primrec.pair hd hstart) hc)
  have hstate : Primrec (fun p : EvalArg =>
      (encodeConfig (run p.1.1 (decodeConfig (p.2.1,p.1.2,1)) p.2.2)).2.2) :=
    (Primrec.snd.comp Primrec.snd).comp hrun
  have h := Primrec.beq.comp hstate (Primrec.const 0)
  apply h.of_eq
  intro p
  rfl

theorem bound_primrec
    (hstep : Primrec (fun p : Nat × EncodedConfig => stepEncoded p.1 p.2)) :
    Primrec (fun p : BoundArg => acceptBound p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let P (p : BoundArg) (w : Nat) := accepts p.1.1.1 p.1.1.2 w p.1.2
  have hargs : Primrec (fun z : BoundArg × Nat => ((z.1.1.1.1,z.1.1.1.2),(z.2,z.1.1.2)) : BoundArg × Nat → EvalArg) := by
    have hdi : Primrec (fun z : BoundArg × Nat => z.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have hc : Primrec (fun z : BoundArg × Nat => z.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact Primrec.pair hdi (Primrec.pair Primrec.snd hc)
  have hp : Primrec₂ P := ((evalArg_primrec hstep).comp hargs).to₂
  have h := any_primrec P (fun p : BoundArg => p.2) hp Primrec.snd
  apply h.of_eq
  intro p
  rfl


/-- The concrete, explicitly clocked attempt is primitive recursive. -/
theorem boundedAttempt_primrec : Primrec evalArg :=
  evalArg_primrec (stepEncoded_primrec record_primrec)

theorem boundedAttempt_computable : Computable evalArg :=
  boundedAttempt_primrec.to_comp

/-- The complete bounded existential certificate search is primitive recursive. -/
theorem boundedAcceptance_primrec :
    Primrec (fun p : BoundArg => acceptBound p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  bound_primrec (stepEncoded_primrec record_primrec)

theorem boundedAcceptance_computable :
    Computable (fun p : BoundArg => acceptBound p.1.1.1 p.1.1.2 p.1.2 p.2) :=
  boundedAcceptance_primrec.to_comp

end Shared.Beeping.NPcoNP.Source284Relative
