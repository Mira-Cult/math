import PASoundness.PAtoCompactBinaryTermTruth

/-! Standard-HF truth of the generated term graph. This does not assert a K
proof of term-graph totality or any PA axiom. -/
namespace PASoundness.PAtoCompactTermGraphFullTruth

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphTruth PASoundness.PAtoCompactBinaryTermTruth
open PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem graph_ordinal_truth {α : Type} [DecidableEq α] (varName : α → Nat)
    (t : Peano.language.Term α) :
    ∀ (out base k : Nat) (ρ : Environment) (v : α → Nat),
      out < base →
      (∀ a ∈ t.varFinset, varName a < out) →
      (∀ a ∈ t.varFinset, ρ (varName a) = (ordinal (v a)).code) →
      ρ out = (ordinal k).code →
      ((termGraph varName t out base).Realize ρ ↔ k = t.realize v) := by
  induction t with
  | var a =>
      intro out base k ρ v hout hnames hvalues hresult
      have ha : a ∈ (FirstOrder.Language.Term.var a : Peano.language.Term α).varFinset := by simp [FirstOrder.Language.Term.varFinset]
      have hn := hnames a ha
      have hv := hvalues a ha
      simpa [FirstOrder.Language.Term.realize] using
        variable_graph_truth varName a out base (v a) k ρ hn hout hv hresult
  | @func l f ts ih =>
      cases f with
      | zero =>
          intro out base k ρ v hout hnames hvalues hresult
          have hts : ts = Fin.elim0 := by funext i; exact Fin.elim0 i
          subst ts
          change (termGraph varName (.func .zero Fin.elim0) out base).Realize ρ ↔ k = 0
          exact zero_graph_truth varName out base k ρ hout hresult
      | succ =>
          intro out base k ρ v hout hnames hvalues hresult
          have hn : ∀ a ∈ (ts 0).varFinset, varName a < out := by
            intro a ha
            exact hnames a (child_var .succ ts 0 a ha)
          have hv : ∀ a ∈ (ts 0).varFinset, ρ (varName a) = (ordinal (v a)).code := by
            intro a ha
            exact hvalues a (child_var .succ ts 0 a ha)
          change (termGraph varName (.func .succ ![ts 0]) out base).Realize ρ ↔
            k = (ts 0).realize v + 1
          apply successor_graph_truth varName (ts 0) out base ((ts 0).realize v) k ρ hout hresult
          intro j
          apply ih 0 base (base + 64) j (update ρ base (ordinal j).code) v (by omega)
          · intro a ha
            have h := hn a ha
            omega
          · intro a ha
            have h := hn a ha
            have hne : varName a ≠ base := by omega
            simpa [update, hne] using hv a ha
          · simp [update]
      | add =>
          intro out base k ρ v hout hnames hvalues hresult
          have hn : ∀ i a, a ∈ (ts i).varFinset → varName a < out := by
            intro i a ha
            exact hnames a (child_var .add ts i a ha)
          have hv : ∀ i a, a ∈ (ts i).varFinset → ρ (varName a) = (ordinal (v a)).code := by
            intro i a ha
            exact hvalues a (child_var .add ts i a ha)
          change (termGraph varName (.func .add ![ts 0, ts 1]) out base).Realize ρ ↔
            k = (ts 0).realize v + (ts 1).realize v
          apply addition_graph_truth varName (ts 0) (ts 1) out base
            ((ts 0).realize v) ((ts 1).realize v) k ρ hout hresult
          · intro i j
            apply ih 0 base (base + 64) i
              (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) v (by omega)
            · intro a ha
              have h := hn 0 a ha
              omega
            · intro a ha
              have h := hn 0 a ha
              have h0 : varName a ≠ base := by omega
              have h1 : varName a ≠ base + 1 := by omega
              simpa [update, h0, h1] using hv 0 a ha
            · simp [update]
          · intro i j
            apply ih 1 (base + 1) (base + 64 + termCost (ts 0)) j
              (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) v (by omega)
            · intro a ha
              have h := hn 1 a ha
              omega
            · intro a ha
              have h := hn 1 a ha
              have h0 : varName a ≠ base := by omega
              have h1 : varName a ≠ base + 1 := by omega
              simpa [update, h0, h1] using hv 1 a ha
            · simp [update]
      | mul =>
          intro out base k ρ v hout hnames hvalues hresult
          have hn : ∀ i a, a ∈ (ts i).varFinset → varName a < out := by
            intro i a ha
            exact hnames a (child_var .mul ts i a ha)
          have hv : ∀ i a, a ∈ (ts i).varFinset → ρ (varName a) = (ordinal (v a)).code := by
            intro i a ha
            exact hvalues a (child_var .mul ts i a ha)
          change (termGraph varName (.func .mul ![ts 0, ts 1]) out base).Realize ρ ↔
            k = (ts 0).realize v * (ts 1).realize v
          apply multiplication_graph_truth varName (ts 0) (ts 1) out base
            ((ts 0).realize v) ((ts 1).realize v) k ρ hout hresult
          · intro i j
            apply ih 0 base (base + 64) i
              (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) v (by omega)
            · intro a ha
              have h := hn 0 a ha
              omega
            · intro a ha
              have h := hn 0 a ha
              have h0 : varName a ≠ base := by omega
              have h1 : varName a ≠ base + 1 := by omega
              simpa [update, h0, h1] using hv 0 a ha
            · simp [update]
          · intro i j
            apply ih 1 (base + 1) (base + 64 + termCost (ts 0)) j
              (update (update ρ base (ordinal i).code) (base + 1) (ordinal j).code) v (by omega)
            · intro a ha
              have h := hn 1 a ha
              omega
            · intro a ha
              have h := hn 1 a ha
              have h0 : varName a ≠ base := by omega
              have h1 : varName a ≠ base + 1 := by omega
              simpa [update, h0, h1] using hv 1 a ha
            · simp [update]

/-- In standard HF, the generated graph has exactly the standard value of
the original PA term. Source variable labels lie below the output label;
their denoted numbers are allowed to be equal. -/
theorem graph_truth {α : Type} [DecidableEq α] (varName : α → Nat)
    (t : Peano.language.Term α) (out base : Nat) (ρ : Environment) (v : α → Nat)
    (hout : out < base)
    (hnames : ∀ a ∈ t.varFinset, varName a < out)
    (hvalues : ∀ a ∈ t.varFinset, ρ (varName a) = (ordinal (v a)).code) :
    (termGraph varName t out base).Realize ρ ↔ ρ out = (ordinal (t.realize v)).code := by
  constructor
  · intro h
    have hd := termGraph_has_domain varName t out base ρ h
    obtain ⟨k, hk⟩ := (domainAt_iff base out (by omega) ρ).mp hd
    have he := (graph_ordinal_truth varName t out base k ρ v hout hnames hvalues hk).mp h
    simpa [he] using hk
  · intro h
    exact (graph_ordinal_truth varName t out base (t.realize v) ρ v hout hnames hvalues h).mpr rfl

end PASoundness.PAtoCompactTermGraphFullTruth

#print axioms PASoundness.PAtoCompactTermGraphFullTruth.graph_ordinal_truth
#print axioms PASoundness.PAtoCompactTermGraphFullTruth.graph_truth
