import Shared.Beeping.NPcoNP.Source284SATWorkerSelect
namespace Shared.Beeping.NPcoNP.Source284SATWorkerSelect
open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284SATProducerIteration
open Shared.Beeping.NPcoNP.Source284SATWorkerInputs

theorem select_initial_correct (p : Request) (hq : p.2 = 0) :
    select p = rowWorker p := by
  have hb : p.2 < (budget p.1).length := by
    rw [hq,budget_length,Source284SATProducerSize.rows_length]
    omega
  have hz : isZero p = true := (isZero_correct p).2 hq
  simp only [select,inBudget,hb,decide_true,if_true,hz]
  exact initialBranch_correct p hq

theorem select_prefix_correct (p : Request) (hpos : 0 < p.2)
    (hp : p.2-1 < p.1.1.length) (hb : p.2 < (budget p.1).length) :
    select p = rowWorker p := by
  have hn : isZero p = false := by
    cases h : isZero p with
    | false => rfl
    | true => have := (isZero_correct p).1 h; omega
  have hl : prefixEnd p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp only [prefixEnd]
    omega
  have ht : test prefixEnd p = true := by
    rw [test,below_correct p (prefixEnd p) (by omega) hl]
    simp [prefixEnd,hp]
  simp only [select,inBudget,hb,decide_true,hn,Bool.false_eq_true,↓reduceIte,ht]
  exact prefixBranch_correct p hpos hp (by omega)

theorem select_grammar_correct (p : Request) (hpos : 0 < p.2)
    (hlo : p.1.1.length ≤ p.2-1)
    (hhi : p.2-1 < p.1.1.length+5*p.1.2.1.length)
    (hb : p.2 < (budget p.1).length) : select p = rowWorker p := by
  have hn : isZero p = false := by
    cases h : isZero p with
    | false => rfl
    | true => have := (isZero_correct p).1 h; omega
  have hl : prefixEnd p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp only [prefixEnd]
    omega
  have hg : grammarEnd p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length,grammarEnd_correct]
    omega
  have ht : test prefixEnd p = false := by
    rw [test,below_correct p (prefixEnd p) (by omega) hl]
    simp [prefixEnd,Nat.not_lt.mpr hlo]
  have hs : test grammarEnd p = true := by
    rw [test,below_correct p (grammarEnd p) (by omega) hg,grammarEnd_correct]
    simp [hhi]
  simp only [select,inBudget,hb,decide_true,hn,Bool.false_eq_true,↓reduceIte,ht,hs]
  exact Source284SATGrammarWorker.branch_correct p hpos hlo hhi (by omega)

/-- The selector agrees with the table in all five final grammar modes. -/
theorem select_boundary_correct (p : Request) (hpos : 0 < p.2)
    (hlo : p.1.1.length+5*p.1.2.1.length ≤ p.2-1)
    (hhi : p.2-1 < p.1.1.length+5*p.1.2.1.length+5)
    (hb : p.2 < (budget p.1).length) : select p = rowWorker p := by
  have hn : isZero p = false := by
    cases h : isZero p with
    | false => rfl
    | true => have := (isZero_correct p).1 h; omega
  have hl : prefixEnd p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp only [prefixEnd]
    omega
  have hg (n : Nat) (h : n ≤ 5) : shifted grammarEnd n p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp only [shifted,grammarEnd_correct]
    omega
  have hg0 : grammarEnd p ≤ (budget p.1).length := by
    have h := hg 0 (by omega); simpa [shifted] using h
  have ht : test prefixEnd p = false := by
    rw [test,below_correct p (prefixEnd p) (by omega) hl]
    have hnot : ¬ p.2-1 < p.1.1.length := by omega
    simp [prefixEnd,hnot]
  have hs : test grammarEnd p = false := by
    rw [test,below_correct p (grammarEnd p) (by omega) hg0,grammarEnd_correct]
    simp only [decide_eq_false_iff_not]
    omega
  simp only [select,inBudget,hb,decide_true,hn,Bool.false_eq_true,↓reduceIte,ht,hs]
  rw [show test (shifted grammarEnd 1) p = decide (p.2-1 < shifted grammarEnd 1 p) from
      below_correct p _ (by omega) (hg 1 (by omega)),
    show test (shifted grammarEnd 3) p = decide (p.2-1 < shifted grammarEnd 3 p) from
      below_correct p _ (by omega) (hg 3 (by omega)),
    show test (shifted grammarEnd 4) p = decide (p.2-1 < shifted grammarEnd 4 p) from
      below_correct p _ (by omega) (hg 4 (by omega)),
    show test (shifted grammarEnd 5) p = decide (p.2-1 < shifted grammarEnd 5 p) from
      below_correct p _ (by omega) (hg 5 (by omega))]
  simp only [shifted,grammarEnd_correct,decide_eq_true_eq]
  split_ifs
  all_goals first
    | apply boundaryAcceptBranch_correct p (p.2-1-(p.1.1.length+5*p.1.2.1.length))
    | apply boundaryRejectBranch_correct p (p.2-1-(p.1.1.length+5*p.1.2.1.length))
  all_goals try simp only [Source284CertificateValidator.boundary,Source284CertificateGrammarClock.state]
  all_goals omega

set_option maxHeartbeats 1200000 in
/-- All prefix and grammar tests are false once the rewind range starts. -/
theorem select_late_correct (p : Request)
    (hstart : Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length ≤ p.2-1)
    (hb : p.2 < (budget p.1).length) : select p = rowWorker p := by
  have hpos : 0 < p.2 := by
    simp only [Source284CertificateDispatch.rewindStart] at hstart
    omega
  have hn : isZero p = false := by
    cases h : isZero p with
    | false => rfl
    | true => have := (isZero_correct p).1 h; omega
  have htest (f : Request → Nat) (hf : f p ≤ p.2-1) : test f p = false := by
    rw [test,below_correct p (f p) (by omega) (by omega)]
    have hnot : ¬p.2-1 < f p := by omega
    simp [hnot]
  have ht : test prefixEnd p = false := htest prefixEnd (by
    simp only [prefixEnd,Source284CertificateDispatch.rewindStart] at *; omega)
  have hg : test grammarEnd p = false := htest grammarEnd (by
    rw [grammarEnd_correct]; simp only [Source284CertificateDispatch.rewindStart] at *; omega)
  have hg1 : test (shifted grammarEnd 1) p = false := htest _ (by
    simp only [shifted,grammarEnd_correct,Source284CertificateDispatch.rewindStart] at *; omega)
  have hg3 : test (shifted grammarEnd 3) p = false := htest _ (by
    simp only [shifted,grammarEnd_correct,Source284CertificateDispatch.rewindStart] at *; omega)
  have hg4 : test (shifted grammarEnd 4) p = false := htest _ (by
    simp only [shifted,grammarEnd_correct,Source284CertificateDispatch.rewindStart] at *; omega)
  have hg5 : test (shifted grammarEnd 5) p = false := htest _ (by
    simp only [shifted,grammarEnd_correct,Source284CertificateDispatch.rewindStart] at *; omega)
  have hr (n : Nat) (hn : n ≤ 3) : shifted rewindEnd n p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp only [shifted,rewindEnd_correct,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width]
    omega
  have hr0 : rewindEnd p ≤ (budget p.1).length := by
    have h := hr 0 (by omega); simpa [shifted] using h
  simp only [select,inBudget,hb,decide_true,hn,Bool.false_eq_true,↓reduceIte,
    ht,hg,hg1,hg3,hg4,hg5]
  rw [show test rewindEnd p = decide (p.2-1 < rewindEnd p) from
      below_correct p _ (by omega) hr0,
    show test (shifted rewindEnd 1) p = decide (p.2-1 < shifted rewindEnd 1 p) from
      below_correct p _ (by omega) (hr 1 (by omega)),
    show test (shifted rewindEnd 2) p = decide (p.2-1 < shifted rewindEnd 2 p) from
      below_correct p _ (by omega) (hr 2 (by omega)),
    show test (shifted rewindEnd 3) p = decide (p.2-1 < shifted rewindEnd 3 p) from
      below_correct p _ (by omega) (hr 3 (by omega))]
  simp only [shifted,rewindEnd_correct,decide_eq_true_eq]
  clear htest ht hg hg1 hg3 hg4 hg5 hr hr0 hn
  split_ifs
  · exact rewindBranch_correct p hstart (by assumption)
  · apply finalTurnBranch_correct
    omega
  · apply handoffBranch_correct
    simp only [Source284CertificateDispatch.handoff]
    omega
  · apply sinkBranch_correct
    simp only [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff]
    omega
  · apply verifierBranch_correct
    · simp only [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
        Source284CertificateDispatch.handoff]
      omega
    · omega

/-- The charged selector agrees with the bounded source-table worker on
all requests, including out-of-budget indices. -/
theorem select_eq_boundedRowWorker : select = boundedRowWorker := by
  funext p
  by_cases hb : p.2 < (budget p.1).length
  · have hresult : select p = rowWorker p := by
      by_cases hz : p.2 = 0
      · exact select_initial_correct p hz
      · have hpos : 0 < p.2 := by omega
        by_cases hp : p.2-1 < p.1.1.length
        · exact select_prefix_correct p hpos hp hb
        · by_cases hg : p.2-1 < p.1.1.length+5*p.1.2.1.length
          · exact select_grammar_correct p hpos (by omega) hg hb
          · by_cases hf : p.2-1 < p.1.1.length+5*p.1.2.1.length+5
            · exact select_boundary_correct p hpos (by omega) hf hb
            · apply select_late_correct p _ hb
              simp only [Source284CertificateDispatch.rewindStart]
              omega
    simpa [boundedRowWorker,hb] using hresult
  · simp [select,boundedRowWorker,inBudget,hb]

end Shared.Beeping.NPcoNP.Source284SATWorkerSelect
