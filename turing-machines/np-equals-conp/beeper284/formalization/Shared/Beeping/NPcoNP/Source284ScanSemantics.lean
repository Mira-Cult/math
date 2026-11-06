import Shared.Beeping.NPcoNP.Source284Parser

/-! Finite operational semantics for the source's marker/payload loop.
The only state represented here is the parser's own `(scan,n,e)` triple.
It neither models candidate evaluation nor asserts a compiled-machine
refinement. The source provenance is documented in `Source284Parser`. -/

namespace Shared.Beeping.NPcoNP.Source284Parser

structure ScanState where
  scan : Nat
  n : Nat
  e : Nat
  deriving DecidableEq, Repr

/-- The sequential operations of one successful source loop iteration:
consume the marker, use the payload, then consume it. -/
def sourceBody (s : ScanState) : ScanState :=
  let afterMarker := s.scan / 2
  ⟨afterMarker / 2, s.n + 1, 2 * s.e + afterMarker % 2⟩

/-- After the loop, the source consumes the failed zero marker. Its
remaining scan is ignored by the reference parser; the original input is
preserved separately by the source program. -/
def consumeFailedMarker (s : ScanState) : ScanState :=
  ⟨s.scan / 2, s.n, s.e⟩

@[simp] theorem consumeFailedMarker_accumulators (s : ScanState) :
    ((consumeFailedMarker s).n, (consumeFailedMarker s).e) = (s.n, s.e) := rfl

/-- `done` labels a failed marker; `more` is one successful iteration. -/
inductive SourceExec : ScanState → ScanState → Prop where
  | done (s : ScanState) (h : s.scan % 2 = 0) : SourceExec s s
  | more (s out : ScanState) (h : s.scan % 2 = 1)
      (tail : SourceExec (sourceBody s) out) : SourceExec s out

theorem body_scan (s : ScanState) : (sourceBody s).scan = s.scan / 4 := by
  simp [sourceBody, Nat.div_div_eq_div_mul]

theorem body_scan_lt (s : ScanState) (h : s.scan % 2 = 1) :
    (sourceBody s).scan < s.scan := by
  rw [body_scan]
  have hs : 0 < s.scan := by omega
  exact Nat.div_lt_self hs (by decide)

/-- Every finite initial parser state finishes after finitely many source
iterations. The final scan retains the unconsumed even suffix. -/
theorem source_terminates (s : ScanState) :
    ∃ out, SourceExec s out ∧ out.scan % 2 = 0 ∧
      (out.n, out.e) = run s.scan s.n s.e := by
  induction hscan : s.scan using Nat.strong_induction_on generalizing s with
  | h m ih =>
    by_cases h : s.scan % 2 = 1
    · have hlt : (sourceBody s).scan < m := by simpa [hscan] using body_scan_lt s h
      obtain ⟨out, he, hf, hv⟩ := ih _ hlt (sourceBody s) rfl
      refine ⟨out, .more s out h he, hf, ?_⟩
      rw [← hscan, run_odd _ _ _ h]
      simpa [sourceBody, Nat.div_div_eq_div_mul] using hv
    · have hz : s.scan % 2 = 0 := by omega
      refine ⟨s, .done s hz, hz, ?_⟩
      rw [← hscan, run_even _ _ _ hz]

/-- The operational loop has the same returned pair for any terminating
execution. In particular, no nondeterministic choice of result is possible. -/
theorem source_exec_correct {s out : ScanState} (h : SourceExec s out) :
    out.scan % 2 = 0 ∧ (out.n, out.e) = run s.scan s.n s.e := by
  induction h with
  | done s hz =>
    exact ⟨hz, by simp [run_even _ _ _ hz]⟩
  | more s out ho tail ih =>
    refine ⟨ih.1, ?_⟩
    rw [run_odd _ _ _ ho]
    simpa [sourceBody, Nat.div_div_eq_div_mul] using ih.2

/-- Both the parsed values and the unconsumed scan are uniquely determined. -/
theorem source_exec_unique {s a b : ScanState}
    (ha : SourceExec s a) (hb : SourceExec s b) : a = b := by
  induction ha generalizing b with
  | done s hz =>
    cases hb with
    | done => rfl
    | more _ _ ho _ => omega
  | more s a ho tail ih =>
    cases hb with
    | done _ hz => omega
    | more _ _ _ tail' => exact ih tail'

end Shared.Beeping.NPcoNP.Source284Parser
