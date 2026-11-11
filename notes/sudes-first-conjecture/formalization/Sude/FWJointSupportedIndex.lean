import Sude.FWSeedJointIndex
import Sude.FWBridgeJointIndex
import Sude.FWGrowthJointIndex
import Sude.FWWideJointIndex
import Sude.FWJointGridTransport

/-! Injectively map supported family tags and graph edges to actual joint
layer pair indices. No grid transport, physical switching or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The four stage families; bridge labels are restricted to actual support. -/
inductive FWJointSupportedTag (n P : ℕ) where
  | seed (j : Fin 16)
  | growth (j : Fin P)
  | bridge (j : {j : ℕ // j ∈ Finset.range 5})
  | wide (j : Fin (3 * (n / 450)))

/-- The existing seed/growth, bridge, then wide nested grid-label shape. -/
abbrev FWJointGridTag (n P : ℕ) :=
  ((Fin 16 ⊕ Fin P) ⊕ ℕ) ⊕ Fin (3 * (n / 450))

/-- Only the bridge summand needs a support restriction. -/
def fwJointGridTagSupported {n P : ℕ} : FWJointGridTag n P → Prop
  | .inl (.inr j) => j ∈ Finset.range 5
  | _ => True

/-- The pre-wide labels exported by the actual seed/growth and bridge grid. -/
def fwJointPreWideGridLabels (P : ℕ) : Finset ((Fin 16 ⊕ Fin P) ⊕ ℕ) :=
  (Finset.univ : Finset (Fin 16 ⊕ Fin P)).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.range 5).image (Sum.inr : ℕ → (Fin 16 ⊕ Fin P) ⊕ ℕ)

/-- Every label in the actual nested seed/growth/bridge/wide support meets
the bridge restriction used by the joint index map. -/
theorem fwJointGridLabels_supported {n P : ℕ} (t : FWJointGridTag n P)
    (ht : t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))) :
    fwJointGridTagSupported t := by
  rcases t with ((j | j) | j) | j <;>
    simp [fwJointGridLabels, fwJointPreWideGridLabels, fwJointGridTagSupported] at ht ⊢
  exact ht

/-- Convert a supported existing grid label without assigning stages to
out-of-range bridge labels. -/
def fwJointSupportedTagOfGrid {n P : ℕ} :
    {t : FWJointGridTag n P // fwJointGridTagSupported t} → FWJointSupportedTag n P
  | ⟨.inl (.inl (.inl j)), _⟩ => .seed j
  | ⟨.inl (.inl (.inr j)), _⟩ => .growth j
  | ⟨.inl (.inr j), hj⟩ => .bridge ⟨j, hj⟩
  | ⟨.inr j, _⟩ => .wide j

/-- Forget the support proof while retaining the original nested label. -/
def fwJointSupportedTagToGrid {n P : ℕ} : FWJointSupportedTag n P → FWJointGridTag n P
  | .seed j => .inl (.inl (.inl j))
  | .growth j => .inl (.inl (.inr j))
  | .bridge j => .inl (.inr j.1)
  | .wide j => .inr j

@[simp] theorem fwJointSupportedTagToGrid_ofGrid {n P : ℕ}
    (t : {t : FWJointGridTag n P // fwJointGridTagSupported t}) :
    fwJointSupportedTagToGrid (fwJointSupportedTagOfGrid t) = t.1 := by
  rcases t with ⟨t, ht⟩
  rcases t with ((j | j) | j) | j <;> rfl

/-- The support-aware conversion preserves all original grid-label identity. -/
theorem fwJointSupportedTagOfGrid_injective {n P : ℕ} :
    Function.Injective (fwJointSupportedTagOfGrid (n := n) (P := P)) := by
  intro x y h
  apply Subtype.ext
  have hi := congrArg fwJointSupportedTagToGrid h
  simpa using hi

def fwJointSupportedLayerIndex {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (tag : FWJointSupportedTag n P) (k : Fin 3) : Fin (((br ++ sr) ++ wr) ++ gr).length :=
  match tag with
  | .seed j => fwSeedJointLayerIndex br sr wr gr hsr j k
  | .growth j => fwGrowthJointLayerIndex br sr wr gr hgr j k
  | .bridge j => fwBridgeJointLayerIndex br sr wr gr hbr (fwBridgeSupportStage j) k
  | .wide j => fwWideJointLayerIndex br sr wr gr hwr j k

/-- The vertex is retained as part of the actual network pair index. -/
def fwJointSupportedPairIndex {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (x : (FWJointSupportedTag n P × Fin 3) × Fin n) :
    Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
  (fwJointSupportedLayerIndex br sr wr gr hbr hsr hwr hgr x.1.1 x.1.2, x.2)

/-- Each family occupies its own half-open layer band. -/
theorem fwJointSupportedLayerIndex_band {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (tag : FWJointSupportedTag n P) (k : Fin 3) :
    let i := (fwJointSupportedLayerIndex br sr wr gr hbr hsr hwr hgr tag k).val
    match tag with
    | .bridge _ => i < br.length
    | .seed _ => br.length ≤ i ∧ i < br.length + sr.length
    | .wide _ => br.length + sr.length ≤ i ∧ i < br.length + sr.length + wr.length
    | .growth _ => br.length + sr.length + wr.length ≤ i := by
  cases tag with
  | seed j =>
    have hj := (finProdFinEquiv (j,k)).isLt
    simp only [fwJointSupportedLayerIndex, fwSeedJointLayerIndex]
    omega
  | growth j =>
    simp only [fwJointSupportedLayerIndex, fwGrowthJointLayerIndex]
    omega
  | bridge j =>
    have hj := (finProdFinEquiv (fwBridgeSupportStage j,k)).isLt
    simp only [fwJointSupportedLayerIndex, fwBridgeJointLayerIndex]
    omega
  | wide j =>
    have hj := (finProdFinEquiv (j,k)).isLt
    simp only [fwJointSupportedLayerIndex, fwWideJointLayerIndex]
    omega

/-- A joint pair index uniquely identifies its supported family, stage,
graph-layer label, and vertex, even when graph edges share endpoints. -/
theorem fwJointSupportedPairIndex_injective {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3) :
    Function.Injective (fwJointSupportedPairIndex br sr wr gr hbr hsr hwr hgr) := by
  rintro ⟨⟨tag,k⟩,e⟩ ⟨⟨tag',k'⟩,e'⟩ heq
  have he := congrArg Prod.snd heq
  have hi := congrArg (fun x => x.1.val) heq
  have hb := fwJointSupportedLayerIndex_band br sr wr gr hbr hsr hwr hgr tag k
  have hb' := fwJointSupportedLayerIndex_band br sr wr gr hbr hsr hwr hgr tag' k'
  cases tag <;> cases tag' <;>
    simp only [fwJointSupportedPairIndex, fwJointSupportedLayerIndex] at heq hi hb hb'
  all_goals first
    | omega
    | (have h := @fwSeedJointPairIndex_injective n br sr wr gr hsr ((_,k),e) ((_,k'),e') heq; cases h; rfl)
    | (have h := @fwGrowthJointPairIndex_injective n P br sr wr gr hgr ((_,k),e) ((_,k'),e') heq; cases h; rfl)
    | (have h := @fwBridgeJointPairIndex_injective n br sr wr gr hbr ((_,k),e) ((_,k'),e') heq
       have hj := fwBridgeSupportStage_injective (congrArg (fun x => x.1.1) h)
       have hk := congrArg (fun x => x.1.2) h
       cases hj; cases hk; cases he; rfl)
    | (have h := @fwWideJointPairIndex_injective n br sr wr gr hwr ((_,k),e) ((_,k'),e') heq; cases h; rfl)

/-- Direct mapping of an existing supported grid label and graph edge to the
corresponding joint pair index. -/
def fwJointGridPairIndex {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (x : ({t : FWJointGridTag n P // fwJointGridTagSupported t} × Fin 3) × Fin n) :
    Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
  fwJointSupportedPairIndex br sr wr gr hbr hsr hwr hgr ((fwJointSupportedTagOfGrid x.1.1,x.1.2),x.2)

/-- Distinct supported existing grid labels or graph edges name distinct
joint pair indices. -/
theorem fwJointGridPairIndex_injective {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3) :
    Function.Injective (fwJointGridPairIndex br sr wr gr hbr hsr hwr hgr) := by
  rintro ⟨⟨x,k⟩,e⟩ ⟨⟨y,k'⟩,e'⟩ heq
  have hi := fwJointSupportedPairIndex_injective br sr wr gr hbr hsr hwr hgr heq
  have ht : fwJointSupportedTagOfGrid x = fwJointSupportedTagOfGrid y := congrArg (fun t => t.1.1) hi
  have hk := congrArg (fun t => t.1.2) hi
  have he := congrArg Prod.snd hi
  have hxy := fwJointSupportedTagOfGrid_injective ht
  cases hxy
  cases hk
  cases he
  rfl

/-- Map a label from the actual finite nested grid support to its joint
pair index. Its edge vertex is preserved. -/
def fwJointActualGridPairIndex {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (x : ({t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))} × Fin 3) × Fin n) :
    Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
  fwJointGridPairIndex br sr wr gr hbr hsr hwr hgr
    ((⟨x.1.1.1, fwJointGridLabels_supported x.1.1.1 x.1.1.2⟩, x.1.2), x.2)

/-- Distinct actual grid-support labels or graph edges yield distinct joint
pair indices, including across all four family bands. -/
theorem fwJointActualGridPairIndex_injective {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3) :
    Function.Injective (fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr) := by
  rintro ⟨⟨x,k⟩,e⟩ ⟨⟨y,k'⟩,e'⟩ heq
  have hi := fwJointGridPairIndex_injective br sr wr gr hbr hsr hwr hgr heq
  have ht : x.1 = y.1 := congrArg (fun t => t.1.1.1) hi
  have hk := congrArg (fun t => t.1.2) hi
  have he := congrArg Prod.snd hi
  have hxy : x = y := Subtype.ext ht
  cases hxy
  cases hk
  cases he
  rfl

end
end Sude
