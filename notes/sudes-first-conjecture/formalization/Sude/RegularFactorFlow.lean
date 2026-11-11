import Sude.RegularFactorCut
import Sude.DirectedFlow

/-! Translate physical bipartite cuts and directed unit flows. -/
namespace Sude
noncomputable section

/-- Counting a physical cut by columns equals counting its actual cells. -/
theorem cellCutCount_eq_filter_card {n : ℕ} (E : Finset (Cell n)) (A B : Finset (Fin n)) :
    cellCutCount E A B = (E.filter fun z => z.1 ∈ A ∧ z.2 ∈ B).card := by
  classical
  let F := E.filter fun z => z.1 ∈ A
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter F B (fun z : Cell n => z.2)
  have heach (j : Fin n) : (F.filter fun z => z.2 = j).card =
      (A.bipartiteBelow (fun i j => (i, j) ∈ E) j).card := by
    have hset : (F.filter fun z => z.2 = j) =
        (A.bipartiteBelow (fun i j => (i, j) ∈ E) j).image (fun i => (i, j)) := by
      ext ⟨i, q⟩
      simp [F, Finset.bipartiteBelow, Prod.ext_iff, and_comm, eq_comm]
      aesop
    rw [hset, Finset.card_image_of_injective]
    intro i q h
    exact congrArg Prod.fst h
  have hF : (F.filter fun z => z.2 ∈ B) = E.filter (fun z => z.1 ∈ A ∧ z.2 ∈ B) := by
    ext z
    simp [F, and_assoc]
  rw [hF] at hfiber
  unfold cellCutCount
  simpa only [heach] using hfiber

/-- Each physical edge is oriented from its row vertex to its column vertex. -/
def factorEdgeSource {n : ℕ} {E : Finset (Cell n)} (z : {z // z ∈ E}) : Fin (n + n) :=
  Fin.castAdd n z.val.1

def factorEdgeTarget {n : ℕ} {E : Finset (Cell n)} (z : {z // z ∈ E}) : Fin (n + n) :=
  Fin.natAdd n z.val.2

def factorDemand {n : ℕ} (k : ℕ) : Fin (n + n) → ℤ :=
  Fin.addCases (fun _ => (k : ℤ)) (fun _ => -(k : ℤ))

def factorCutRows {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => Fin.castAdd n i ∈ S

def factorCutOmittedColumns {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun j => Fin.natAdd n j ∉ S

/-- Every outgoing directed edge corresponds bijectively to a physical cell
in the associated row/omitted-column cut. -/
theorem factor_directed_cut_card {n : ℕ} (E : Finset (Cell n)) (S : Finset (Fin (n + n))) :
    (directedCutEdges (@factorEdgeSource n E) (@factorEdgeTarget n E) S).card =
      cellCutCount E (factorCutRows S) (factorCutOmittedColumns S) := by
  classical
  rw [cellCutCount_eq_filter_card]
  apply Finset.card_bij (fun z _ => z.val)
  · intro z hz
    have hh := (Finset.mem_filter.mp hz).2
    simpa [factorCutRows, factorCutOmittedColumns, factorEdgeSource, factorEdgeTarget] using hh
  · intro x hx y hy he
    exact Subtype.ext he
  · intro z hz
    have hh := Finset.mem_filter.mp hz
    refine ⟨⟨z, hh.1⟩, ?_, rfl⟩
    simpa [directedCutEdges, factorEdgeSource, factorEdgeTarget, factorCutRows,
      factorCutOmittedColumns] using hh.2

/-- A directed cut's signed demand is the RF1 row/column cut expression. -/
theorem factor_demand_cut {n : ℕ} (k : ℕ) (S : Finset (Fin (n + n))) :
    (∑ v ∈ S, factorDemand k v) =
      (k : ℤ) * ((factorCutRows S).card + (factorCutOmittedColumns S).card - (n : ℤ)) := by
  classical
  have hsum : (∑ v ∈ S, factorDemand k v) =
      ∑ v : Fin (n + n), if v ∈ S then factorDemand k v else 0 := by
    rw [Finset.sum_ite_mem]
    simp
  rw [hsum, Fin.sum_univ_add]
  simp only [factorDemand, Fin.addCases_left, Fin.addCases_right]
  have hrow : (∑ i : Fin n, if Fin.castAdd n i ∈ S then (k : ℤ) else 0) =
      (factorCutRows S).card * (k : ℤ) := by
    rw [← Finset.sum_filter]
    simp [factorCutRows]
  let C : Finset (Fin n) := Finset.univ.filter fun j => Fin.natAdd n j ∈ S
  have hcol : (∑ j : Fin n, if Fin.natAdd n j ∈ S then -(k : ℤ) else 0) =
      -(C.card : ℤ) * k := by
    rw [← Finset.sum_filter]
    simp [C]
  rw [hrow, hcol]
  have hc : C.card + (factorCutOmittedColumns S).card = n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun j => Fin.natAdd n j ∈ S)
    simpa [C, factorCutOmittedColumns] using h
  have hc' : (C.card : ℤ) + (factorCutOmittedColumns S).card = n := by exact_mod_cast hc
  nlinarith

theorem factor_demand_sum_zero {n : ℕ} (k : ℕ) : ∑ v : Fin (n + n), factorDemand k v = 0 := by
  rw [Fin.sum_univ_add]
  simp only [factorDemand, Fin.addCases_left, Fin.addCases_right]
  simp

/-- The RF1 physical cut inequalities imply every directed flow cut. -/
theorem factor_directed_cuts {n k : ℕ} (E : Finset (Cell n))
    (hcuts : ∀ A B : Finset (Fin n), k * (A.card + B.card - n) ≤ cellCutCount E A B) :
    ∀ S : Finset (Fin (n + n)),
      (∑ v ∈ S, factorDemand k v) ≤
        (directedCutEdges (@factorEdgeSource n E) (@factorEdgeTarget n E) S).card := by
  intro S
  rw [factor_demand_cut, factor_directed_cut_card]
  let A := factorCutRows S
  let B := factorCutOmittedColumns S
  have hn0 : (0 : ℤ) ≤ k := by positivity
  by_cases hsum : n ≤ A.card + B.card
  · have h := hcuts A B
    have hz : ((k * (A.card + B.card - n) : ℕ) : ℤ) ≤ cellCutCount E A B := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hsum] at hz
    push_cast at hz
    simpa [A, B] using hz
  · have hsumnat : A.card + B.card ≤ n := by omega
    have hsumcast : (A.card : ℤ) + B.card ≤ n := by exact_mod_cast hsumnat
    have hsum' : (A.card : ℤ) + B.card - n ≤ 0 := by linarith
    have hp := mul_nonpos_of_nonneg_of_nonpos hn0 hsum'
    have hc : (0 : ℤ) ≤ cellCutCount E A B := by positivity
    exact le_trans hp hc

/-- A feasible physical cut family supplies an actual integral flow on the
physical edges, with the prescribed row and column divergences. -/
theorem factor_flow_of_cuts {n k : ℕ} (E : Finset (Cell n))
    (hcuts : ∀ A B : Finset (Fin n), k * (A.card + B.card - n) ≤ cellCutCount E A B) :
    ∃ flow : {z // z ∈ E} → ℤ,
      (∀ e, 0 ≤ flow e ∧ flow e ≤ 1) ∧
      ∀ v, (∑ e : {z // z ∈ E},
        edgeTransfer factorEdgeSource factorEdgeTarget flow e v) = factorDemand k v :=
  directed_unit_flow_of_cut_inequalities factorEdgeSource factorEdgeTarget (factorDemand k)
    (factor_demand_sum_zero k) (factor_directed_cuts E hcuts)

/-- A zero-or-one sum over a predicate counts the selected actual edges. -/
theorem unit_flow_filter_sum {α : Type*} [Fintype α] [DecidableEq α]
    (flow : α → ℤ) (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1) (P : α → Prop) [DecidablePred P] :
    (∑ e : α, if P e then flow e else 0) =
      (((Finset.univ : Finset α).filter fun e => P e ∧ flow e = 1).card : ℤ) := by
  classical
  have hone : ∀ e, flow e = if flow e = 1 then 1 else 0 := by
    intro e
    have h := hflow e
    split_ifs with he <;> omega
  calc
    _ = ∑ e : α, if P e ∧ flow e = 1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : P e
      · simp only [hp, true_and, ↓reduceIte]
        exact hone e
      · simp only [hp, false_and, ↓reduceIte]
    _ = _ := Finset.sum_boole _ _

/-- Physical cells on which the integral unit flow is one. -/
def factorFlowCells {n : ℕ} (E : Finset (Cell n)) (flow : {z // z ∈ E} → ℤ) : Finset (Cell n) :=
  ((Finset.univ : Finset {z // z ∈ E}).filter fun e => flow e = 1).image Subtype.val

theorem factorFlowCells_subset {n : ℕ} (E : Finset (Cell n)) (flow : {z // z ∈ E} → ℤ) :
    factorFlowCells E flow ⊆ E := by
  intro z hz
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hz
  exact e.property

/-- A selected row edge has a unique column and vice versa. -/
theorem factorFlowCells_row_card {n : ℕ} (E : Finset (Cell n))
    (flow : {z // z ∈ E} → ℤ) (r : Fin n) :
    (LayerPacking.rowUsed (factorFlowCells E flow) r).card =
      ((Finset.univ : Finset {z // z ∈ E}).filter fun e => e.val.1 = r ∧ flow e = 1).card := by
  classical
  have hE : ∀ c ∈ LayerPacking.rowUsed (factorFlowCells E flow) r, (r, c) ∈ E := by
    intro c hc
    have hc' : (r, c) ∈ factorFlowCells E flow := by simpa [LayerPacking.rowUsed] using hc
    exact factorFlowCells_subset E flow hc'
  refine Finset.card_bij (fun c hc => (⟨(r, c), hE c hc⟩ : {z // z ∈ E})) ?_ ?_ ?_
  · intro c hc
    have hc' : (r, c) ∈ factorFlowCells E flow := by simpa [LayerPacking.rowUsed] using hc
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hc'
    have hf : flow e = 1 := (Finset.mem_filter.mp he).2
    have he' : e = ⟨(r, c), factorFlowCells_subset E flow hc'⟩ := Subtype.ext heq
    subst e
    simp [hf]
  · intro c hc d hd he
    exact congrArg Prod.snd (congrArg Subtype.val he)
  · intro e he
    have hp := (Finset.mem_filter.mp he).2
    refine ⟨e.val.2, ?_, ?_⟩
    · simp only [LayerPacking.rowUsed, Finset.mem_filter, Finset.mem_univ, true_and]
      have heq : (r, e.val.2) = e.val := by cases e with | mk z hz => cases z; simp_all
      rw [heq]
      exact Finset.mem_image.mpr ⟨e, by simp [hp.2], rfl⟩
    · apply Subtype.ext
      exact Prod.ext hp.1.symm rfl

theorem factorFlowCells_column_card {n : ℕ} (E : Finset (Cell n))
    (flow : {z // z ∈ E} → ℤ) (c : Fin n) :
    (LayerPacking.colUsed (factorFlowCells E flow) c).card =
      ((Finset.univ : Finset {z // z ∈ E}).filter fun e => e.val.2 = c ∧ flow e = 1).card := by
  classical
  have hE : ∀ r ∈ LayerPacking.colUsed (factorFlowCells E flow) c, (r, c) ∈ E := by
    intro r hr
    have hr' : (r, c) ∈ factorFlowCells E flow := by simpa [LayerPacking.colUsed] using hr
    exact factorFlowCells_subset E flow hr'
  refine Finset.card_bij (fun r hr => (⟨(r, c), hE r hr⟩ : {z // z ∈ E})) ?_ ?_ ?_
  · intro r hr
    have hr' : (r, c) ∈ factorFlowCells E flow := by simpa [LayerPacking.colUsed] using hr
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hr'
    have hf : flow e = 1 := (Finset.mem_filter.mp he).2
    have he' : e = ⟨(r, c), factorFlowCells_subset E flow hr'⟩ := Subtype.ext heq
    subst e
    simp [hf]
  · intro r hr s hs he
    exact congrArg Prod.fst (congrArg Subtype.val he)
  · intro e he
    have hp := (Finset.mem_filter.mp he).2
    refine ⟨e.val.1, ?_, ?_⟩
    · simp only [LayerPacking.colUsed, Finset.mem_filter, Finset.mem_univ, true_and]
      have heq : (e.val.1, c) = e.val := Prod.ext rfl hp.1.symm
      rw [heq]
      exact Finset.mem_image.mpr ⟨e, by simp [hp.2], rfl⟩
    · apply Subtype.ext
      exact Prod.ext rfl hp.1.symm

theorem factor_left_ne_right {n : ℕ} (i j : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

/-- The zero-or-one physical flow selects an actual regular subgraph. -/
theorem factorFlowCells_regular {n k : ℕ} (E : Finset (Cell n))
    (flow : {z // z ∈ E} → ℤ) (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1)
    (hdiv : ∀ v, (∑ e : {z // z ∈ E},
      edgeTransfer factorEdgeSource factorEdgeTarget flow e v) = factorDemand k v) :
    CellFactorRegular (factorFlowCells E flow) k := by
  constructor
  · intro r
    have hsum := hdiv (Fin.castAdd n r)
    have hterms : ∀ e : {z // z ∈ E},
        edgeTransfer factorEdgeSource factorEdgeTarget flow e (Fin.castAdd n r) =
          if e.val.1 = r then flow e else 0 := by
      intro e
      have hsame : Fin.castAdd n e.val.1 = Fin.castAdd n r ↔ e.val.1 = r :=
        (Fin.castAdd_injective n n).eq_iff
      change ((if Fin.castAdd n e.val.1 = Fin.castAdd n r then flow e else 0) -
        (if Fin.natAdd n e.val.2 = Fin.castAdd n r then flow e else 0)) = _
      rw [if_neg (factor_left_ne_right r e.val.2).symm, sub_zero]
      simp only [hsame]
    simp_rw [hterms] at hsum
    rw [unit_flow_filter_sum flow hflow] at hsum
    rw [factorFlowCells_row_card]
    have hk : (((Finset.univ : Finset {z // z ∈ E}).filter
        fun e => e.val.1 = r ∧ flow e = 1).card : ℤ) = k := by
      simpa [factorDemand] using hsum
    exact_mod_cast hk
  · intro c
    have hsum := hdiv (Fin.natAdd n c)
    have hterms : ∀ e : {z // z ∈ E},
        edgeTransfer factorEdgeSource factorEdgeTarget flow e (Fin.natAdd n c) =
          -(if e.val.2 = c then flow e else 0) := by
      intro e
      have hsame : Fin.natAdd n e.val.2 = Fin.natAdd n c ↔ e.val.2 = c :=
        (Fin.natAdd_injective n n).eq_iff
      change ((if Fin.castAdd n e.val.1 = Fin.natAdd n c then flow e else 0) -
        (if Fin.natAdd n e.val.2 = Fin.natAdd n c then flow e else 0)) = _
      rw [if_neg (factor_left_ne_right e.val.1 c), zero_sub]
      simp only [hsame]
    simp_rw [hterms, Finset.sum_neg_distrib] at hsum
    rw [unit_flow_filter_sum flow hflow] at hsum
    rw [factorFlowCells_column_card]
    have hk : (((Finset.univ : Finset {z // z ∈ E}).filter
        fun e => e.val.2 = c ∧ flow e = 1).card : ℤ) = k := by
      simp only [factorDemand, Fin.addCases_right] at hsum
      omega
    exact_mod_cast hk

/-- Every feasible physical cut family has an actual spanning regular factor. -/
theorem regular_factor_of_cut_inequalities {n k : ℕ} (E : Finset (Cell n))
    (hcuts : ∀ A B : Finset (Fin n), k * (A.card + B.card - n) ≤ cellCutCount E A B) :
    ∃ F ⊆ E, CellFactorRegular F k := by
  obtain ⟨flow, hflow, hdiv⟩ := factor_flow_of_cuts E hcuts
  exact ⟨factorFlowCells E flow, factorFlowCells_subset E flow,
    factorFlowCells_regular E flow hflow hdiv⟩

/-- RF1: the actual dense residual support contains a regular factor of the
source's degree. The ceiling non-underflow is explicit. -/
theorem dense_residual_regular_factor {n r Δ : ℕ} (E : Finset (Cell n))
    (hrowlo : ∀ i, r ≤ (LayerPacking.rowUsed E i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed E i).card ≤ r + Δ)
    (hcollo : ∀ j, r ≤ (LayerPacking.colUsed E j).card)
    (hcolhi : ∀ j, (LayerPacking.colUsed E j).card ≤ r + Δ)
    (hdense : 3 * n ≤ 4 * r) (hceil : (Δ + 1) / 2 ≤ r) :
    ∃ F ⊆ E, CellFactorRegular F (r - (Δ + 1) / 2) :=
  regular_factor_of_cut_inequalities E
    (dense_factor_source_cuts E hrowlo hrowhi hcollo hcolhi hdense hceil)

end
end Sude
