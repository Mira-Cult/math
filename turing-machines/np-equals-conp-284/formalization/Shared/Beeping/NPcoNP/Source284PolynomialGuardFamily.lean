import Shared.Beeping.NPcoNP.Source284FixedGuardTimedTM2
import Shared.Beeping.NPcoNP.Source284EmptyBranchFiniteTM2
import Shared.Beeping.NPcoNP.Source284TaggedTimedCoverage
import Shared.ComplexityBridge.TM2UnaryPolynomialIO

/-! Polynomial-time generation of the paid empty-prefix adapter around a
finite timed guard. Bounds are fixed polynomials evaluated at the input length,
but the resulting finite table changes with the input. This is not a single
finite program implementing input-dependent bounds. -/
set_option maxHeartbeats 1200000

namespace Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := List Bool × EncRows

def stretch (x : List Bool) : List Bool := x ++ x ++ [true]

theorem stretch_isPolyTime : IsPolyTime stretch := by
  have hi : IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime (id : List Bool → List Bool) id hi hi
  have ha := TM2Compose.isPolyTime_comp (fun x : List Bool => (x,x))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  have hb := TM2Compose.isPolyTime_comp (fun x : List Bool => x ++ x)
    (fun xs : List Bool => xs ++ [true]) (by simpa [TM2ListAppend.append] using ha)
    Source284FixedGuardRowTM2.addSingleton_isPolyTime
  change IsPolyTime (fun x : List Bool => x ++ x ++ [true])
  simpa only [TM2ListAppend.append,List.append_assoc] using hb

def parameters (p time : Polynomial Nat) (x : Input) :
    Source284FixedGuardTimedTM2.Input :=
  (TM2UnaryPolynomialIO.unaryPolynomial p (stretch x.1),
    (TM2UnaryPolynomialIO.unaryPolynomial time x.1,x.2))

theorem parameters_isPolyTime (p time : Polynomial Nat) : IsPolyTime (parameters p time) := by
  let input : Input → List Bool := fun x => x.1
  let original : Input → EncRows := fun x => x.2
  let witness : Input → List Bool := fun x => TM2UnaryPolynomialIO.unaryPolynomial p (stretch (input x))
  let fuel : Input → List Bool := fun x => TM2UnaryPolynomialIO.unaryPolynomial time (input x)
  have hi : IsPolyTime input := TM2PairFirst.first_isPolyTime
  have ho : IsPolyTime original := TM2GuardAllStep.second_isPolyTime
  have hs : IsPolyTime (fun x : Input => stretch (input x)) :=
    TM2Compose.isPolyTime_comp input stretch hi stretch_isPolyTime
  have hw : IsPolyTime witness := TM2Compose.isPolyTime_comp _ _ hs
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime p)
  have hf : IsPolyTime fuel := TM2Compose.isPolyTime_comp input _ hi
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime time)
  exact TM2GuardAllStep.pair_isPolyTime witness (fun x => (fuel x,original x)) hw
    (TM2GuardAllStep.pair_isPolyTime fuel original hf ho)

theorem witness_length (p time : Polynomial Nat) (x : Input) :
    ((parameters p time x).1).length = p.eval (2*x.1.length+1) := by
  simp [parameters,TM2UnaryPolynomialIO.unaryPolynomial,stretch,show 2*x.1.length = x.1.length+x.1.length by omega,
    Nat.add_assoc]

theorem fuel_length (p time : Polynomial Nat) (x : Input) :
    ((parameters p time x).2.1).length = time.eval x.1.length := by
  simp [parameters,TM2UnaryPolynomialIO.unaryPolynomial]

def baseRows (p time : Polynomial Nat) (x : Input) : EncRows :=
  Source284FixedGuardTimedTM2.rows (parameters p time x)

def rows (p time : Polynomial Nat) (x : Input) : EncRows :=
  Source284EmptyBranchFinite.adapt (baseRows p time x)

theorem baseRows_isPolyTime (p time : Polynomial Nat) : IsPolyTime (baseRows p time) :=
  TM2Compose.isPolyTime_comp (parameters p time) Source284FixedGuardTimedTM2.rows
    (parameters_isPolyTime p time) Source284FixedGuardTimedTM2.rows_isPolyTime

theorem rows_isPolyTime (p time : Polynomial Nat) : IsPolyTime (rows p time) :=
  TM2Compose.isPolyTime_comp (baseRows p time) Source284EmptyBranchFinite.adapt
    (baseRows_isPolyTime p time) Source284EmptyBranchFiniteTM2.adapt_isPolyTime

theorem baseRows_nonempty (p time : Polynomial Nat) (x : Input) : 0 < (baseRows p time x).length := by
  simp only [baseRows,Source284FixedGuardTimedTM2.rows_length,
    Source284FixedGuardTimed.statesTotal,Source284FixedGuardRewind.state_count]
  omega

theorem baseRows_valid (p time : Polynomial Nat) (x : Input) :
    Source284ListTables.valid (decodeRows (baseRows p time x)) = true :=
  Source284FixedGuardTimedTM2.rows_valid _

theorem rows_valid (p time : Polynomial Nat) (x : Input) :
    Source284ListTables.valid (decodeRows (rows p time x)) = true :=
  Source284EmptyBranchValidity.adapt_valid _ (baseRows_nonempty p time x) (baseRows_valid p time x)

def sourceBits (p time : Polynomial Nat) (x : Input) : List Bool :=
  Source284TableRowsTM2.serializeRows (Source284EncodedRecordList.recordsList (rows p time x))

theorem sourceBits_isPolyTime (p time : Polynomial Nat) : IsPolyTime (sourceBits p time) := by
  have hr := TM2Compose.isPolyTime_comp (rows p time) Source284EncodedRecordList.recordsList
    (rows_isPolyTime p time) Source284EncodedRecordListTM2.recordsList_isPolyTime
  exact TM2Compose.isPolyTime_comp _ Source284TableRowsTM2.serializeRows hr
    Source284TableRowsTM2.serializeRows_isPolyTime

theorem sourceBits_correct (p time : Polynomial Nat) (x : Input) :
    value (sourceBits p time x) = Source284ListTables.source (decodeRows (rows p time x)) := by
  have hc := Source284ListTables.valid_closed (decodeRows (rows p time x)) (rows_valid p time x)
  rw [sourceBits,Source284EncodedRecordList.recordsList_eq,
    Source284TableRowsTM2.closed_table_correct _ _ hc]
  rfl

theorem base_source (p time : Polynomial Nat) (x : Input) :
    Source284ListTables.source (decodeRows (baseRows p time x)) =
      Source284FixedGuardTimedFinite.source (p.eval (2*x.1.length+1)) (time.eval x.1.length) x.2 := by
  have h := Source284FixedGuardTimedTM2.sourceBits_eq_source (parameters p time x)
  have hc := Source284ListTables.valid_closed (decodeRows (baseRows p time x)) (baseRows_valid p time x)
  change value (Source284TableRowsTM2.serializeRows
    (Source284EncodedRecordList.recordsList (baseRows p time x))) = _ at h
  rw [Source284EncodedRecordList.recordsList_eq,
    Source284TableRowsTM2.closed_table_correct _ _ hc] at h
  rw [witness_length, fuel_length] at h
  change Source284ListTables.source (decodeRows (baseRows p time x)) = _ at h
  exact h

/-- Empty source inputs use the actual paid adapter's first transition. -/
theorem empty_attempt (p time : Polynomial Nat) (x : Input) (i c : Nat)
    (hzero : Source284Parser.length i = 0) :
    Source284Relative.accepts (value (sourceBits p time x)) i c 1 = true := by
  rw [sourceBits_correct]
  change Source284Relative.accepts
    (encode (decodeRows (Source284EmptyBranchFinite.adapt (baseRows p time x))).length
      (Source284ListTables.table (decodeRows (Source284EmptyBranchFinite.adapt (baseRows p time x)))) 0) i c 1 = true
  rw [decodeRows_length]
  exact Source284EmptyBranchFinite.adapt_empty_attempt (baseRows p time x) 0 i c hzero

/-- Positive inputs pay two adapter steps before the timed guard runs. -/
theorem positive_attempt (p time : Polynomial Nat) (x : Input) (i c k : Nat)
    (hi : 0 < Source284Parser.length i) :
    Source284Relative.accepts (value (sourceBits p time x)) i c (k+2) =
      Source284Relative.accepts
        (Source284FixedGuardTimedFinite.source (p.eval (2*x.1.length+1)) (time.eval x.1.length) x.2) i c k := by
  rw [sourceBits_correct]
  unfold Source284ListTables.source rows
  rw [decodeRows_length,Source284EmptyBranchFinite.adapt_encode]
  have hc : Closed (baseRows p time x).length (Source284ListTables.table (decodeRows (baseRows p time x))) := by
    simpa using Source284ListTables.valid_closed _ (baseRows_valid p time x)
  rw [Source284EmptyBranchAdapter.encoded_odd_acceptance _ _ 0 i c k
    (baseRows_nonempty p time x) hc
    (Source284TaggedTimedCoverage.positive_odd i hi)]
  have hb := base_source p time x
  simp only [Source284ListTables.source,decodeRows_length] at hb
  exact congrArg (fun code => Source284Relative.accepts code i c k) hb

/-- The two polynomials are fixed for the generator; their values are computed
from the supplied public length for each generated finite table. -/
def limit (p : Polynomial Nat) (x : Input) : Nat := p.eval (2*x.1.length+1)
def fuel (time : Polynomial Nat) (x : Input) : Nat := time.eval x.1.length
def cutoff (p time : Polynomial Nat) (x : Input) : Nat :=
  Source284FixedGuardTimed.time (limit p x) (fuel time x)+2

/-- Pointwise correctness requires the supplied verifier to compute the
predicate for every decoded alias at its stated finite cutoff. -/
theorem positive_check (p time : Polynomial Nat) (x : Input) (i c : Nat)
    (predicate : List Bool → Bool) (hi : 0 < Source284Parser.length i)
    (hn : 0 < x.2.length) (hv : Source284ListTables.valid (decodeRows x.2) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode (limit p x) c = some w →
      (run (Source284ListTables.table (decodeRows x.2)) ⟨c,i,some 0⟩ (fuel time x+1)).state.isNone =
        predicate w) :
    Source284Relative.accepts (value (sourceBits p time x)) i c (cutoff p time x) =
      Source284TaggedWitnessCodec.check (limit p x) predicate c := by
  rw [cutoff,positive_attempt p time x i c _ hi]
  exact Source284TaggedTimedCoverage.timed_check (limit p x) (fuel time x) i c x.2 predicate hn hv hmatch

/-- No later clock can turn a timed-out verifier into an acceptance. -/
theorem positive_stable (p time : Polynomial Nat) (x : Input) (i c extra : Nat)
    (hi : 0 < Source284Parser.length i) (hn : 0 < x.2.length)
    (hv : Source284ListTables.valid (decodeRows x.2) = true) :
    Source284Relative.accepts (value (sourceBits p time x)) i c (cutoff p time x+extra) =
      Source284Relative.accepts (value (sourceBits p time x)) i c (cutoff p time x) := by
  have h1 := positive_attempt p time x i c (Source284FixedGuardTimed.time (limit p x) (fuel time x)+extra) hi
  have h0 := positive_attempt p time x i c (Source284FixedGuardTimed.time (limit p x) (fuel time x)) hi
  have hs := Source284FixedGuardTimedFinite.source_stable (limit p x) (fuel time x) i c extra x.2 hn hv
  simp only [limit,fuel] at h1 h0 hs
  simpa only [cutoff,limit,fuel,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1.trans (hs.trans h0.symm)

/-- At any later coupled clock, this generated program searches exactly the
original polynomially bounded witness set, subject to the concrete verifier
hypothesis. This does not assert that one source program generates or runs
this family internally. -/
theorem positive_bounded_search (p time : Polynomial Nat) (x : Input) (i extra : Nat)
    (predicate : List Bool → Bool) (hi : 0 < Source284Parser.length i)
    (hn : 0 < x.2.length) (hv : Source284ListTables.valid (decodeRows x.2) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode (limit p x) c = some w →
      (run (Source284ListTables.table (decodeRows x.2)) ⟨c,i,some 0⟩ (fuel time x+1)).state.isNone =
        predicate w) :
    Source284Relative.acceptBound (value (sourceBits p time x)) i (cutoff p time x+extra)
      (2^(cutoff p time x+extra)) = true ↔
      ∃ w, w.length ≤ limit p x ∧ predicate w = true := by
  rw [Source284Relative.acceptBound_iff]
  simp_rw [positive_stable p time x i _ extra hi hn hv,
    positive_check p time x i _ predicate hi hn hv hmatch]
  apply Source284TaggedWitnessCodec.clock_search_iff
  have hd := Source284FixedGuardRewind.duration_exact (limit p x)
  simp only [cutoff,Source284FixedGuardTimed.time,Source284WitnessWindow.width]
  omega

end Shared.Beeping.NPcoNP.Source284PolynomialGuardFamily
