import Shared.Beeping.NPcoNP.Source284PaddedDecodedPipeline
import Shared.ComplexityBridge.TM2BoundedWitnessGuard
import Shared.ComplexityBridge.TM2GateDispatch

/-! A polynomial-time verifier wrapper that retains the original witness
cutoff when the outer decoder uses a larger prepared limit. The finite source
verifier below requires the canonical joined-input window; this does not
construct that window or the enlarged unary limit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OriginalCutoffVerifier

open ComplexityTheory Shared.ComplexityBridge

abbrev Input := List Bool × List Bool

def cutoffTokens (p : Polynomial Nat) (z : Input) : List Bool :=
  List.replicate (p.eval z.1.length+1) true

def cutoffFlag (p : Polynomial Nat) (z : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (cutoffTokens p z,z.2.length)

def guarded (p : Polynomial Nat) (R : Input → Bool) (z : Input) : Bool :=
  cutoffFlag p z && R z

/-- The guard includes the exact original bound, including zero-length
witnesses and the equality boundary. -/
theorem cutoffFlag_true (p : Polynomial Nat) (x w : List Bool) :
    cutoffFlag p (x,w) = true ↔ w.length ≤ p.eval x.length := by
  rw [cutoffFlag,TM2BoundedWitnessGuard.guard_correct]
  simp [cutoffTokens]

theorem guarded_correct (p : Polynomial Nat) (R : Input → Bool) (x w : List Bool) :
    guarded p R (x,w) = if w.length ≤ p.eval x.length then R (x,w) else false := by
  by_cases h : w.length ≤ p.eval x.length
  · have hf := (cutoffFlag_true p x w).2 h
    simp [guarded,hf,h]
  · have hf : cutoffFlag p (x,w) = false := by
      cases hb : cutoffFlag p (x,w) with
      | false => rfl
      | true => exact False.elim (h ((cutoffFlag_true p x w).1 hb))
    simp [guarded,hf,h]

theorem guarded_true_iff (p : Polynomial Nat) (R : Input → Bool) (x w : List Bool) :
    guarded p R (x,w) = true ↔ w.length ≤ p.eval x.length ∧ R (x,w) = true := by
  simp [guarded,cutoffFlag_true]

theorem cutoffTokens_isPolyTime (p : Polynomial Nat) : IsPolyTime (cutoffTokens p) := by
  have h := TM2Compose.isPolyTime_comp (fun z : Input => z.1)
    (fun x : List Bool => List.replicate (p.eval x.length+1) true)
    TM2PairFirst.first_isPolyTime (TM2UnaryPolynomialIO.witnessCount_isPolyTime p)
  exact h

theorem cutoffFlag_isPolyTime (p : Polynomial Nat) : IsPolyTime (cutoffFlag p) := by
  let witness : Input → List Bool := fun z => z.2
  let length : Input → Nat := fun z => (witness z).length
  have hw : IsPolyTime witness := TM2GuardAllStep.second_isPolyTime
  have hl : IsPolyTime length := TM2Compose.isPolyTime_comp witness List.length
    hw TM2BinaryListLength.length_isPolyTime
  have hpair := TM2GuardAllStep.pair_isPolyTime (cutoffTokens p) length (cutoffTokens_isPolyTime p) hl
  exact TM2Compose.isPolyTime_comp (fun z => (cutoffTokens p z,length z))
    TM2BoundedWitnessGuard.guard hpair TM2BoundedWitnessGuard.guard_isPolyTime

/-- This uses the canonical library's actual polynomial-time machine class. -/
theorem guarded_isPolyTime (p : Polynomial Nat) (R : Input → Bool) (hR : IsPolyTime R) :
    IsPolyTime (guarded p R) := by
  have hp := TM2GuardAllStep.pair_isPolyTime (cutoffFlag p) R (cutoffFlag_isPolyTime p) hR
  exact TM2Compose.isPolyTime_comp (fun z => (cutoffFlag p z,R z))
    (fun b : Bool × Bool => b.1 && b.2) hp TM2GateDispatch.and_isPolyTime

/-- The NP witness relation can use the original canonical length bound
inside the actual polynomial-time guard, after accounting for the parser's
`2*n+1` framed-input length. The complexity assumption is explicit. -/
theorem reference_guarded_witness
    (hNP : Shared.Beeping.NPcoNP.Source284CanonicalConditional.referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (R : Input → Bool), IsPolyTime (guarded p R) ∧
      ∀ i : Nat,
        (!Source284Comparison.reference i) = true ↔
          ∃ w : List Bool, guarded p R (Source284RawParse.payload i.bits,w) = true := by
  obtain ⟨p,R,hR,hcorrect⟩ := Source284PrefixVerifier.witness_of_complement_mem_NP hNP
  let q : Polynomial Nat := p.comp (2*Polynomial.X+1)
  refine ⟨q,R,guarded_isPolyTime q R hR,?_⟩
  intro i
  have hlen : (Source284RawParse.payload i.bits).length = Source284Parser.length i := by
    have h := Source284RawParse.parse_length i.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  have hbudget : q.eval (Source284RawParse.payload i.bits).length =
      p.eval (2*Source284Parser.length i+1) := by
    simp [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,hlen]
  rw [hcorrect i]
  constructor
  · rintro ⟨w,hw,hval⟩
    exact ⟨w,(guarded_true_iff q R _ w).2 ⟨by simpa [hbudget] using hw,hval⟩⟩
  · rintro ⟨w,hw⟩
    obtain ⟨hlen',hval⟩ := (guarded_true_iff q R _ w).1 hw
    exact ⟨w,by simpa [hbudget] using hlen',hval⟩

/-- A real finite source verifier implements the original-cutoff check and R
on the canonical joined-input window. The caller must still construct that
window, and the bound supplied to this theorem is an outer time bound. -/
theorem guarded_source_verifier (p : Polynomial Nat) (R : Input → Bool) (hR : IsPolyTime R) :
    ∃ (program : Shared.Codes.FinitePrograms.Program) (clock : Polynomial Nat),
      Shared.Codes.FinitePrograms.valid program = true ∧
      ∀ (x w : List Bool) (outer : Nat), w.length ≤ outer →
      ∀ (c : Source284Relative.Config) (extra : Nat),
        let packed := BitstringEncoding.bitEncode (Source284JoinedFrames.joinedBits x w,([] : List Bool))
        let t := clock.eval (12*x.length+12*outer+37)
        Source284Relative.Window t c (Source284Relative.initial (Shared.Codes.BitNumeralCompare.value packed) 0) →
        ((Source284Relative.run (Source284CompileRecords.compile program) c (t+extra)).state == 0) =
          (if w.length ≤ p.eval x.length then R (x,w) else false) := by
  obtain ⟨program,clock,hvalid,hsource⟩ := Source284JoinedDecodeTM2.source_verifier
    (guarded p R) (guarded_isPolyTime p R hR)
  refine ⟨program,clock,hvalid,?_⟩
  intro x w outer hw c extra
  dsimp only
  intro hwindow
  have h := hsource x w outer hw c extra hwindow
  simpa only [guarded_correct] using h

/-- Under complement membership in canonical NP, one guarded relation and
one fixed finite source verifier satisfy both witness coverage and the
original-cutoff test on each prepared joined-input window. -/
theorem reference_guarded_finite_source
    (hNP : Shared.Beeping.NPcoNP.Source284CanonicalConditional.referenceLanguageᶜ ∈ NP) :
    ∃ (p : Polynomial Nat) (R : Input → Bool) (program : Shared.Codes.FinitePrograms.Program)
      (clock : Polynomial Nat),
      IsPolyTime (guarded p R) ∧ Shared.Codes.FinitePrograms.valid program = true ∧
      (∀ i : Nat, (!Source284Comparison.reference i) = true ↔
        ∃ w : List Bool, guarded p R (Source284RawParse.payload i.bits,w) = true) ∧
      (∀ (x w : List Bool) (outer : Nat), w.length ≤ outer →
        ∀ (c : Source284Relative.Config) (extra : Nat),
          let packed := BitstringEncoding.bitEncode (Source284JoinedFrames.joinedBits x w,([] : List Bool))
          let t := clock.eval (12*x.length+12*outer+37)
          Source284Relative.Window t c (Source284Relative.initial (Shared.Codes.BitNumeralCompare.value packed) 0) →
          ((Source284Relative.run (Source284CompileRecords.compile program) c (t+extra)).state == 0) =
            (if w.length ≤ p.eval x.length then R (x,w) else false)) := by
  obtain ⟨p,R,hpoly,hwitness⟩ := reference_guarded_witness hNP
  obtain ⟨program,clock,hvalid,hsource⟩ := Source284JoinedDecodeTM2.source_verifier (guarded p R) hpoly
  refine ⟨p,R,program,clock,hpoly,hvalid,hwitness,?_⟩
  intro x w outer hw c extra
  dsimp only
  intro hwindow
  have h := hsource x w outer hw c extra hwindow
  simpa only [guarded_correct] using h

namespace Fixtures
example : cutoffFlag (0 : Polynomial Nat) ([],[]) = true := by
  apply (cutoffFlag_true _ _ _).2
  simp
example : cutoffFlag (0 : Polynomial Nat) ([],[true]) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := (cutoffFlag_true _ _ _).1 h
  simp at hh
example : cutoffFlag (1 : Polynomial Nat) ([],[false]) = true := by
  apply (cutoffFlag_true _ _ _).2
  simp
example : cutoffFlag (1 : Polynomial Nat) ([],[false,true]) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := (cutoffFlag_true _ _ _).1 h
  simp at hh
end Fixtures

end Shared.Beeping.NPcoNP.Source284OriginalCutoffVerifier
