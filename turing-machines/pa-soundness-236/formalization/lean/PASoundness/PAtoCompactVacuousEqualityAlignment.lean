import PASoundness.PAtoCompactScopedEqualityReplace
import PASoundness.PAtoCompactZeroTermBaseTransport
import PASoundness.PAtoCompactGuardedVacuousAxiom
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactAllTermTransport

/-! Proof-data assembly for equality-body allocation alignment. The child
graph transports and subsequent witness-name alignment are explicit; this
file does not establish the full equality or vacuous-axiom handler. -/
namespace PASoundness.PAtoCompactVacuousEqualityAlignment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactZeroTermBaseTransport
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedAlphaInvariant
open PASoundness.PAtoCompactGuardedGeneralizationAlignment PASoundness.PeanoBetaCRTAlignment
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuousAxiom
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactAllTermTransport

theorem eq_free (t u : Peano.Term) : (t.equal u).freeVarFinset = t.varFinset ∪ u.varFinset := by
  simp [Term.equal, Term.bdEqual, BoundedFormula.freeVarFinset]

theorem eq_not (t u : Peano.Term) (x : Nat) (hx : x ∉ (t.equal u).freeVarFinset) :
    x ∉ t.varFinset ∧ x ∉ u.varFinset := by
  simpa only [eq_free, Finset.mem_union, not_or] using hx

theorem frame_relabel {α β : Type} (t u : Peano.language.Term α) (r : α → β)
    (v : β → Nat) (b : Nat) :
    equalityFrame v (t.relabel r) (u.relabel r) b = equalityFrame (v ∘ r) t u b := by
  simp only [equalityFrame, termCost_relabel, termGraph_relabel]

theorem original_shape (t u : Peano.Term) :
    formula (t.equal u) = equalityFrame id t u (scopeBase (t.equal u) Fin.elim0) := by
  unfold formula
  change scopedFormula 0 (.equal (t.relabel Sum.inl) (u.relabel Sum.inl)) Fin.elim0 = _
  rw [scoped_equal_frame, frame_relabel]
  rfl

theorem topName_eq (t u : Peano.Term) (x : Nat) (hx : x ∉ (t.equal u).freeVarFinset) :
    topName x (t.equal u) = scopeBase (t.equal u) Fin.elim0 := by
  simp [topName, scopeBase, PASoundness.SyntaxTransport.allAt_freeVars, hx]

theorem fresh_term (t : Peano.Term) (x : Nat) (hx : x ∉ t.varFinset) :
    (t.relabel (Sum.inl : Nat → Nat ⊕ Fin 0)).relabel
      (BoundedFormula.relabelAux (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) 0) =
      t.relabel (Sum.inl : Nat → Nat ⊕ Fin 1) := by
  have hg : (fun y => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) = binder x := by
    funext y
    rfl
  rw [hg]
  exact term_bind_fresh (n := 0) x t hx

/-- Binding a source name absent from an equality atom changes its allocated
equality frame's base by exactly one; the source term-name map remains `id`. -/
theorem top_body_shape (t u : Peano.Term) (x : Nat) (hx : x ∉ (t.equal u).freeVarFinset) :
    topBody x (t.equal u) = equalityFrame id t u (scopeBase (t.equal u) Fin.elim0 + 1) := by
  have htn := (eq_not t u x hx).1
  have hun := (eq_not t u x hx).2
  unfold topBody allAtBody
  simp only [Term.equal, Term.bdEqual, BoundedFormula.relabel, BoundedFormula.mapTermRel]
  rw [fresh_term t x htn, fresh_term u x hun]
  rw [scoped_equal_frame, frame_relabel]
  have hbase : scopeBase (.equal (t.relabel Sum.inl) (u.relabel Sum.inl))
      (Fin.snoc Fin.elim0 (topName x (t.equal u))) = scopeBase (t.equal u) Fin.elim0 + 1 := by
    rw [topName_eq t u x hx]
    simp [scopeBase, Term.equal, Term.bdEqual, BoundedFormula.freeVarFinset, Fin.snoc]
  simp only [Term.equal, Term.bdEqual] at hbase
  rw [hbase]
  rfl

theorem names_lt_original_base (t u : Peano.Term) (z : Nat)
    (hz : z ∈ t.varFinset ∪ u.varFinset) : z < scopeBase (t.equal u) Fin.elim0 := by
  apply free_lt_scopeBase (t.equal u) Fin.elim0 z
  simpa only [eq_free] using hz

/-- A finite K transport between the exact consecutive equality frames
discharges the guarded vacuous-axiom leaf for that equality atom. The frame
transport is an explicit input, not inferred from standard-HF semantics. -/
def vacuous_equality_of_frame_transport (t u : Peano.Term) (x : Nat)
    (hx : x ∉ (t.equal u).freeVarFinset)
    (hframe : KDerivation (imp (equalityFrame id t u (scopeBase (t.equal u) Fin.elim0)).encode
      (equalityFrame id t u (scopeBase (t.equal u) Fin.elim0 + 1)).encode)) :
    KDerivation (guardedCode ((t.equal u).imp (FOL.allAt x (t.equal u)))) := by
  apply vacuous_of_body_alignment (t.equal u) x hx
  simpa only [code, original_shape, top_body_shape t u x hx] using hframe

/-- The equality matrix with the value-witness and private-block names made
explicit. No distinctness of represented values is required. -/
def matrix {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (w z p q r : Nat) : Formula :=
  andF (termGraph v t w p) (andF (termGraph v u z q) (equivAt r w z))

theorem replace_andF (x y : Nat) (a b : Formula) :
    replace x y (andF a b) = andF (replace x y a) (replace x y b) := by
  simp [andF, CompactNamed.Formula.not, replace]

theorem equivAt_replace (base w z x y : Nat) (hx : x < base + 2) :
    replace x y (equivAt base w z) =
      equivAt base (rename x y w) (rename x y z) := by
  have hb : x ∉ (equivAt base w z).binders := by
    intro h
    have hh := equivAt_private base w z x h
    omega
  rw [← map_eq_replace x y _ hb]
  unfold equivAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro i hi
  by_cases h0 : i = 0
  · simp [twoMap, h0]
  · by_cases h1 : i = 1
    · simp [twoMap, h1]
    · have hneq : base + (2 + i) ≠ x := by omega
      simp [twoMap, h0, h1, rename, hneq, Nat.add_assoc]

theorem termGraph_rename_name_map {α : Type} [DecidableEq α]
    (t : Peano.language.Term α) (v : α → Nat) (x y out base : Nat)
    (hx : ∀ a ∈ t.varFinset, v a ≠ x) :
    termGraph (rename x y ∘ v) t out base = termGraph v t out base := by
  apply termGraph_name_agree t (rename x y ∘ v) v
  intro a ha
  simp [rename, hx a ha]

theorem matrix_replace_fresh_source {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (w z p q r x y : Nat)
    (hp : x < p) (hq : x < q) (hr : x < r + 2)
    (ht : ∀ a ∈ t.varFinset, v a ≠ x) (hu : ∀ a ∈ u.varFinset, v a ≠ x) :
    replace x y (matrix v t u w z p q r) =
      matrix v t u (rename x y w) (rename x y z) p q r := by
  unfold matrix
  simp only [replace_andF, replace_termGraph _ _ _ _ _ _ hp,
    replace_termGraph _ _ _ _ _ _ hq, equivAt_replace _ _ _ _ _ hr]
  rw [termGraph_rename_name_map t v x y _ _ ht,
    termGraph_rename_name_map u v x y _ _ hu]

theorem matrix_replace_two_witnesses {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (w z dw dz p q r : Nat)
    (hwp : w < p) (hwq : w < q) (hwr : w < r + 2)
    (hzp : z < p) (hzq : z < q) (hzr : z < r + 2)
    (hwsrc1 : ∀ a ∈ t.varFinset, v a ≠ w) (hwsrc2 : ∀ a ∈ u.varFinset, v a ≠ w)
    (hzsrc1 : ∀ a ∈ t.varFinset, v a ≠ z) (hzsrc2 : ∀ a ∈ u.varFinset, v a ≠ z)
    (hzw : z ≠ w) (hdwz : dw ≠ z) :
    replace z dz (replace w dw (matrix v t u w z p q r)) =
      matrix v t u dw dz p q r := by
  rw [matrix_replace_fresh_source v t u w z p q r w dw hwp hwq hwr hwsrc1 hwsrc2]
  simp only [rename, ↓reduceIte, if_neg hzw]
  rw [matrix_replace_fresh_source v t u dw z p q r z dz hzp hzq hzr hzsrc1 hzsrc2]
  simp [rename, hdwz]

theorem termGraph_fresh_gap {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out base z : Nat)
    (hz : z < base) (hout : z ≠ out)
    (hv : ∀ a ∈ t.varFinset, z ≠ v a) : z ∉ (termGraph v t out base).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with hfree | hbound
  · rcases Finset.mem_union.mp (termGraph_free_subset v t out base hfree) with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      exact hv a ha he.symm
    · exact hout (Finset.mem_singleton.mp h)
  · exact termGraph_below_not_binder v t out base z hz hbound

theorem matrix_fresh_gap {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (w z p q r d : Nat)
    (hp : d < p) (hq : d < q) (hr : d < r + 2)
    (hw : d ≠ w) (hz : d ≠ z)
    (ht : ∀ a ∈ t.varFinset, d ≠ v a)
    (hu : ∀ a ∈ u.varFinset, d ≠ v a) :
    d ∉ (matrix v t u w z p q r).names := by
  have he : d ∉ (equivAt r w z).names := by
    intro hh
    rcases equivAt_name_bound r w z d hh with hew | hez | hi
    · exact hw hew
    · exact hz hez
    · omega
  simpa [matrix, andF, PASoundness.CompactNamed.Formula.not, Formula.names] using
    (show d ∉ (termGraph v t w p).names ∧
      d ∉ (termGraph v u z q).names ∧ d ∉ (equivAt r w z).names from
      ⟨termGraph_fresh_gap v t w p d hp hw ht,
        termGraph_fresh_gap v u z q d hq hz hu, he⟩)

theorem matrix_below_not_binder {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (w z p q r d : Nat)
    (hp : d < p) (hq : d < q) (hr : d < r + 2) :
    d ∉ (matrix v t u w z p q r).binders := by
  simp only [matrix, andF_binders, Finset.mem_union, not_or]
  refine ⟨termGraph_below_not_binder v t w p d hp,
    termGraph_below_not_binder v u z q d hq, ?_⟩
  intro h
  have hh := equivAt_private r w z d h
  omega

/-- Rename the two existential value witnesses after private blocks have
been moved above a fresh pair of names. The bound assumptions concern labels;
source terms and represented values may coincide. -/
def matrix_witness_alpha {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (w d p q r : Nat)
    (hwd : w + 1 < d) (hdp : d + 1 < p) (hdq : d + 1 < q)
    (hdr : d + 1 < r + 2)
    (ht : ∀ a ∈ t.varFinset, v a < w) (hu : ∀ a ∈ u.varFinset, v a < w) :
    ProofEquiv (.ex w (.ex (w + 1) (matrix v t u w (w + 1) p q r)))
      (.ex d (.ex (d + 1) (matrix v t u d (d + 1) p q r))) := by
  have ht' : ∀ a ∈ t.varFinset, v a ≠ w := by
    intro a ha; have := ht a ha; omega
  have hu' : ∀ a ∈ u.varFinset, v a ≠ w := by
    intro a ha; have := hu a ha; omega
  have ht'' : ∀ a ∈ t.varFinset, v a ≠ w + 1 := by
    intro a ha; have := ht a ha; omega
  have hu'' : ∀ a ∈ u.varFinset, v a ≠ w + 1 := by
    intro a ha; have := hu a ha; omega
  have hdf : d ∉ (matrix v t u w (w + 1) p q r).names := by
    apply matrix_fresh_gap v t u w (w + 1) p q r d <;> try omega
    · intro a ha; have := ht a ha; omega
    · intro a ha; have := hu a ha; omega
  have hd1f : d + 1 ∉ (matrix v t u w (w + 1) p q r).names := by
    apply matrix_fresh_gap v t u w (w + 1) p q r (d + 1) <;> try omega
    · intro a ha; have := ht a ha; omega
    · intro a ha; have := hu a ha; omega
  have hwbind := matrix_below_not_binder v t u w (w + 1) p q r w
    (by omega) (by omega) (by omega)
  have hzbind := matrix_below_not_binder v t u w (w + 1) p q r (w + 1)
    (by omega) (by omega) (by omega)
  let m := matrix v t u w (w + 1) p q r
  have hfirst := ProofEquiv.alphaExists w d (.ex (w + 1) m) (by omega)
    (by simpa [Formula.binders, show w ≠ w + 1 by omega] using hwbind)
    (by simpa [Formula.names, show d ≠ w + 1 by omega] using hdf)
  have hnew : d + 1 ∉ (replace w d m).names := by
    intro h
    have hh := replace_names_subset w d m h
    rcases Finset.mem_insert.mp hh with hEq | hOrig
    · omega
    · exact hd1f hOrig
  have hsecond := ProofEquiv.alphaExists (w + 1) (d + 1) (replace w d m) (by omega)
    (by simpa [replace_binders] using hzbind) hnew
  have hrep := matrix_replace_two_witnesses v t u w (w + 1) d (d + 1) p q r
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ht' hu' ht'' hu'' (by omega) (by omega)
  have heq := hfirst.trans (ProofEquiv.existential d hsecond)
  dsimp only [m] at heq
  rw [hrep] at heq
  exact heq

/-- Lift three actual finite K implications through the equality matrix and
both existential value witnesses. The child implications retain their exact
source and target outputs. -/
def frame_private_forward {α : Type} (v : α → Nat) (t u : Peano.language.Term α)
    (w z p q r p' q' r' : Nat)
    (ht : KDerivation (imp (termGraph v t w p).encode (termGraph v t w p').encode))
    (hu : KDerivation (imp (termGraph v u z q).encode (termGraph v u z q').encode))
    (he : KDerivation (imp (equivAt r w z).encode (equivAt r' w z).encode)) :
    KDerivation (imp (Formula.ex w (.ex z (matrix v t u w z p q r))).encode
      (Formula.ex w (.ex z (matrix v t u w z p' q' r'))).encode) := by
  have hm : KDerivation (imp (matrix v t u w z p q r).encode
      (matrix v t u w z p' q' r').encode) := by
    exact andF_transport _ _ _ _ ht (andF_transport _ _ _ _ hu he)
  exact existsCongr w (existsCongr z hm)

/-- The precise equality-frame source can first move just its private
blocks, while keeping its existential witness names unchanged. -/
def equalityFrame_private_forward {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (b p q r : Nat)
    (ht : KDerivation (imp (termGraph v t b (b + 2)).encode
      (termGraph v t b p).encode))
    (hu : KDerivation (imp (termGraph v u (b + 1) (b + 2 + termCost t)).encode
      (termGraph v u (b + 1) q).encode))
    (he : KDerivation (imp (equivAt (b + 2 + termCost t + termCost u) b (b + 1)).encode
      (equivAt r b (b + 1)).encode)) :
    KDerivation (imp (equalityFrame v t u b).encode
      (Formula.ex b (.ex (b + 1) (matrix v t u b (b + 1) p q r))).encode) := by
  exact frame_private_forward v t u b (b + 1) (b + 2)
    (b + 2 + termCost t) (b + 2 + termCost t + termCost u) p q r ht hu he

/-- Transport an equality frame to a strictly higher frame, given finite K
proofs transporting its two child graphs to the corresponding high private
blocks. All source names must lie below the original value-witness pair. -/
def equalityFrame_high_forward {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b d : Nat) (hbd : b + 1 < d)
    (htname : ∀ a ∈ t.varFinset, v a < b)
    (huname : ∀ a ∈ u.varFinset, v a < b)
    (ht : KDerivation (imp (termGraph v t b (b + 2)).encode
      (termGraph v t b (d + 2)).encode))
    (hu : KDerivation (imp (termGraph v u (b + 1) (b + 2 + termCost t)).encode
      (termGraph v u (b + 1) (d + 2 + termCost t)).encode)) :
    KDerivation (imp (equalityFrame v t u b).encode (equalityFrame v t u d).encode) := by
  let p := d + 2
  let q := d + 2 + termCost t
  let r := d + 2 + termCost t + termCost u
  let s := b + 2 + termCost t + termCost u
  have he : KDerivation (imp (equivAt s b (b + 1)).encode (equivAt r b (b + 1)).encode) :=
    (equivAt_base_alpha s r b (b + 1) (by dsimp [s]; omega) (by dsimp [s]; omega)
      (by dsimp [r]; omega) (by dsimp [r]; omega)).forward
  have hprivate := equalityFrame_private_forward v t u b p q r ht hu he
  have halpha := matrix_witness_alpha v t u b d p q r hbd
    (by dsimp [p]; omega) (by dsimp [q]; omega) (by dsimp [r]; omega) htname huname
  exact compose hprivate halpha.forward

/-- The reverse high-frame transport, retaining the two reverse child-graph
proofs as explicit inputs. -/
def equalityFrame_high_backward {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b d : Nat) (hbd : b + 1 < d)
    (htname : ∀ a ∈ t.varFinset, v a < b)
    (huname : ∀ a ∈ u.varFinset, v a < b)
    (ht : KDerivation (imp (termGraph v t b (d + 2)).encode
      (termGraph v t b (b + 2)).encode))
    (hu : KDerivation (imp (termGraph v u (b + 1) (d + 2 + termCost t)).encode
      (termGraph v u (b + 1) (b + 2 + termCost t)).encode)) :
    KDerivation (imp (equalityFrame v t u d).encode (equalityFrame v t u b).encode) := by
  let p := d + 2
  let q := d + 2 + termCost t
  let r := d + 2 + termCost t + termCost u
  let s := b + 2 + termCost t + termCost u
  have he : KDerivation (imp (equivAt r b (b + 1)).encode (equivAt s b (b + 1)).encode) :=
    (equivAt_base_alpha s r b (b + 1) (by dsimp [s]; omega) (by dsimp [s]; omega)
      (by dsimp [r]; omega) (by dsimp [r]; omega)).backward
  have hprivate := frame_private_forward v t u b (b + 1) p q r (b + 2)
    (b + 2 + termCost t) s ht hu he
  have halpha := matrix_witness_alpha v t u b d p q r hbd
    (by dsimp [p]; omega) (by dsimp [q]; omega) (by dsimp [r]; omega) htname huname
  exact compose halpha.backward hprivate

/-- Consecutive equality frames have a finite K implication whenever both
child term graphs can be transported through one shared high block. All four
child proof inputs are explicit and use fixed witness-output labels. -/
def equalityFrame_consecutive_of_child_transport (t u : Peano.Term) (b d : Nat)
    (hbd : b + 2 < d)
    (htname : ∀ a ∈ t.varFinset, a < b)
    (huname : ∀ a ∈ u.varFinset, a < b)
    (htf : KDerivation (imp (termGraph id t b (b + 2)).encode
      (termGraph id t b (d + 2)).encode))
    (huf : KDerivation (imp (termGraph id u (b + 1) (b + 2 + termCost t)).encode
      (termGraph id u (b + 1) (d + 2 + termCost t)).encode))
    (htb : KDerivation (imp (termGraph id t (b + 1) (d + 2)).encode
      (termGraph id t (b + 1) (b + 3)).encode))
    (hub : KDerivation (imp (termGraph id u (b + 2) (d + 2 + termCost t)).encode
      (termGraph id u (b + 2) (b + 3 + termCost t)).encode)) :
    KDerivation (imp (equalityFrame id t u b).encode (equalityFrame id t u (b + 1)).encode) := by
  have hf := equalityFrame_high_forward id t u b d (by omega) htname huname htf huf
  have hb := equalityFrame_high_backward id t u (b + 1) d (by omega)
    (by intro a ha; simp only [id_eq]; have := htname a ha; omega)
    (by intro a ha; simp only [id_eq]; have := huname a ha; omega) htb hub
  exact compose hf hb

/-- The guarded vacuous PA axiom for an arbitrary equality atom. Every
term-graph block transport is actual finite K proof data produced by the
all-term base-transport construction; no soundness premise is used. -/
noncomputable def vacuous_equality (t u : Peano.Term) (x : Nat)
    (hx : x ∉ (t.equal u).freeVarFinset) :
    KDerivation (guardedCode ((t.equal u).imp (FOL.allAt x (t.equal u)))) := by
  let b := scopeBase (t.equal u) Fin.elim0
  let d := b + 10
  have htname : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_left _ ha)
  have huname : ∀ a ∈ u.varFinset, a < b := by
    intro a ha
    exact names_lt_original_base t u a (Finset.mem_union_right _ ha)
  have htf := (termGraph_base_transport id t (b + 2) (d + 2) b
    (by omega) (by dsimp [d]; omega)
    (by intro a ha; simp only [id_eq]; have := htname a ha; omega)
    (by intro a ha; simp only [id_eq]; have := htname a ha; dsimp [d]; omega)).1
  have huf := (termGraph_base_transport id u (b + 2 + termCost t)
    (d + 2 + termCost t) (b + 1) (by omega) (by dsimp [d]; omega)
    (by intro a ha; simp only [id_eq]; have := huname a ha; omega)
    (by intro a ha; simp only [id_eq]; have := huname a ha; dsimp [d]; omega)).1
  have htb := (termGraph_base_transport id t (b + 3) (d + 2) (b + 1)
    (by omega) (by dsimp [d]; omega)
    (by intro a ha; simp only [id_eq]; have := htname a ha; omega)
    (by intro a ha; simp only [id_eq]; have := htname a ha; dsimp [d]; omega)).2
  have hub := (termGraph_base_transport id u (b + 3 + termCost t)
    (d + 2 + termCost t) (b + 2) (by omega) (by dsimp [d]; omega)
    (by intro a ha; simp only [id_eq]; have := huname a ha; omega)
    (by intro a ha; simp only [id_eq]; have := huname a ha; dsimp [d]; omega)).2
  apply vacuous_equality_of_frame_transport t u x hx
  exact equalityFrame_consecutive_of_child_transport t u b d (by dsimp [d]; omega)
    htname huname htf huf htb hub

theorem vacuous_equality_certificate (t u : Peano.Term) (x : Nat)
    (hx : x ∉ (t.equal u).freeVarFinset) :
    theoremCode (certificate (vacuous_equality t u x hx)) =
      guardedCode ((t.equal u).imp (FOL.allAt x (t.equal u))) :=
  certificate_correct _

end PASoundness.PAtoCompactVacuousEqualityAlignment

#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.frame_private_forward
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.equalityFrame_private_forward
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.top_body_shape
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.vacuous_equality_of_frame_transport
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.matrix_witness_alpha
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.equalityFrame_high_forward
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.equalityFrame_high_backward
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.equalityFrame_consecutive_of_child_transport
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.vacuous_equality
#print axioms PASoundness.PAtoCompactVacuousEqualityAlignment.vacuous_equality_certificate
