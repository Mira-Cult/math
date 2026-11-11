import Sude.LayerPacking

/-! Finite iteration of PB's physical permutation-layer packing. This proves
geometry and budgets, not the supply of prime values or the controllers. -/
namespace Sude.LayerPacking
noncomputable section

abbrev Layer (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)

def layerSupport {n : ℕ} (x : Layer n) : Finset (Cell n) := layerCells x.1 x.2

def layersSupport {n : ℕ} : List (Layer n) → Finset (Cell n)
  | [] => ∅
  | x :: xs => layerSupport x ∪ layersSupport xs

/-- Each layer is physically balanced, avoids the current reservation, and
is added to the reservation before the next layer is constructed. -/
inductive PackedLayers {n : ℕ} : Finset (Cell n) → List (Layer n) → Prop
  | nil (reserved) : PackedLayers reserved []
  | cons {reserved π f rest}
      (hinj : Function.Injective (layerCell π f))
      (hsafe : ∀ z ∈ layerCells π f,
        z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n)
      (hrows : ∀ r, ((layerCells π f).filter (fun z => z.1 = r)).card = 2)
      (hcols : ∀ c, ((layerCells π f).filter (fun z => z.2 = c)).card = 2)
      (htail : PackedLayers (reserved ∪ layerCells π f) rest) :
      PackedLayers reserved ((π, f) :: rest)

/-- Any finite list of derangements can be packed by repeatedly applying PB's
Hall matching. The bound pays the maximum cumulative two-cell increment per
line; prior reservations may already have unequal row and column loads. -/
theorem pack_finite_layers {n L : ℕ} (πs : List (Equiv.Perm (Fin n)))
    (reserved : Finset (Cell n))
    (hderange : ∀ π ∈ πs, ∀ i, π i ≠ i)
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L)
    (hn : 4 * (L + 2 * πs.length) + 8 < n) :
    ∃ layers : List (Layer n), layers.map Prod.fst = πs ∧ PackedLayers reserved layers := by
  induction πs generalizing reserved L with
  | nil => exact ⟨[], rfl, PackedLayers.nil reserved⟩
  | cons π πs ih =>
    have hd : ∀ i, π i ≠ i := hderange π (by simp)
    have hdrest : ∀ q ∈ πs, ∀ i, q i ≠ i := by
      intro q hq
      exact hderange q (by simp [hq])
    have hn0 : 4 * L + 8 < n := by simp only [List.length_cons] at hn; omega
    obtain ⟨f, hinj, hsafe, _, hrows, hcols⟩ :=
      physical_balanced_layer π hd reserved hrow hcol hn0
    obtain ⟨hrow', hcol'⟩ := layer_load_update π f reserved hrow hcol
    have hn' : 4 * ((L + 2) + 2 * πs.length) + 8 < n := by
      simp only [List.length_cons] at hn
      omega
    obtain ⟨layers, hmap, hpacked⟩ := ih (reserved ∪ layerCells π f) hdrest hrow' hcol' hn'
    refine ⟨(π, f) :: layers, ?_, PackedLayers.cons hinj hsafe hrows hcols hpacked⟩
    simp [hmap]

/-- Each listed support is contained in the accumulated physical support. -/
theorem layerSupport_subset {n : ℕ} (x : Layer n) (xs : List (Layer n))
    (hx : x ∈ xs) : layerSupport x ⊆ layersSupport xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Finset.subset_union_left
    · exact (ih hx).trans Finset.subset_union_right

/-- No accumulated layer touches any reservation that existed before the
sequence began. -/
theorem PackedLayers.reserved_disjoint {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    Disjoint reserved (layersSupport layers) := by
  induction h with
  | nil => simp [layersSupport]
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    apply Finset.disjoint_left.mpr
    intro z hz hmem
    simp only [layersSupport, layerSupport, Finset.mem_union] at hmem
    rcases hmem with hc | hc
    · exact (hsafe z hc).1 hz
    · exact Finset.disjoint_left.mp ih (Finset.mem_union_left _ hz) hc

/-- Distinct layers have disjoint physical supports. -/
theorem PackedLayers.pairwise_disjoint {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    layers.Pairwise (fun x y => Disjoint (layerSupport x) (layerSupport y)) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    apply List.Pairwise.cons
    · intro y hy
      apply Finset.disjoint_left.mpr
      intro z hz₁ hz₂
      have hzrest := layerSupport_subset y rest hy hz₂
      exact Finset.disjoint_left.mp htail.reserved_disjoint
        (Finset.mem_union_right reserved hz₁) hzrest
    · exact ih

/-- All layers stay away from the original reservations and both diagonals,
while retaining their individual injectivity and line balance. -/
theorem PackedLayers.each_layer {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    ∀ x ∈ layers,
      Function.Injective (layerCell x.1 x.2) ∧
      (∀ z ∈ layerSupport x, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ r, ((layerSupport x).filter (fun z => z.1 = r)).card = 2) ∧
      (∀ c, ((layerSupport x).filter (fun z => z.2 = c)).card = 2) := by
  induction h with
  | nil => simp
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨hinj, hsafe, hrows, hcols⟩
    · obtain ⟨hi, hs, hr, hc⟩ := ih x hx
      refine ⟨hi, ?_, hr, hc⟩
      intro z hz
      obtain ⟨hnot, hm, ha⟩ := hs z hz
      exact ⟨fun hz' => hnot (Finset.mem_union_left _ hz'), hm, ha⟩

/-- The union of all physical layers contains exactly two cells per row for
each layer, with no overcount from overlapping supports. -/
theorem PackedLayers.row_balance {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    ∀ r, ((layersSupport layers).filter (fun z => z.1 = r)).card = 2 * layers.length := by
  induction h with
  | nil => simp [layersSupport]
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    intro r
    have hd : Disjoint (layerCells π f) (layersSupport rest) := by
      apply Finset.disjoint_left.mpr
      intro z hz₁ hz₂
      exact Finset.disjoint_left.mp htail.reserved_disjoint
        (Finset.mem_union_right reserved hz₁) hz₂
    have hdf : Disjoint ((layerCells π f).filter (fun z => z.1 = r))
        ((layersSupport rest).filter (fun z => z.1 = r)) :=
      hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    simp only [layersSupport, layerSupport, Finset.filter_union, List.length_cons]
    rw [Finset.card_union_of_disjoint hdf, hrows r, ih r]
    omega

/-- The same exact occupancy statement holds for every column. -/
theorem PackedLayers.column_balance {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    ∀ c, ((layersSupport layers).filter (fun z => z.2 = c)).card = 2 * layers.length := by
  induction h with
  | nil => simp [layersSupport]
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    intro c
    have hd : Disjoint (layerCells π f) (layersSupport rest) := by
      apply Finset.disjoint_left.mpr
      intro z hz₁ hz₂
      exact Finset.disjoint_left.mp htail.reserved_disjoint
        (Finset.mem_union_right reserved hz₁) hz₂
    have hdf : Disjoint ((layerCells π f).filter (fun z => z.2 = c))
        ((layersSupport rest).filter (fun z => z.2 = c)) :=
      hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    simp only [layersSupport, layerSupport, Finset.filter_union, List.length_cons]
    rw [Finset.card_union_of_disjoint hdf, hcols c, ih c]
    omega

/-- All cells used by the layer sequence are off both diagonals. -/
theorem PackedLayers.support_off_diagonals {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    ∀ z ∈ layersSupport layers, z ∉ mainCells n ∧ z ∉ antiCells n := by
  induction h with
  | nil => simp [layersSupport]
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    intro z hz
    simp only [layersSupport, layerSupport, Finset.mem_union] at hz
    rcases hz with hz | hz
    · exact ⟨(hsafe z hz).2.1, (hsafe z hz).2.2⟩
    · exact ih z hz

/-- An index selects one of the actual physical cells of a packed sequence. -/
def sequenceCell {n : ℕ} (layers : List (Layer n))
    (x : Fin layers.length × (Fin n × Bool)) : Cell n :=
  layerCell (layers.get x.1).1 (layers.get x.1).2 x.2

theorem sequenceCell_mem {n : ℕ} (layers : List (Layer n))
    (i : Fin layers.length) (x : Fin n × Bool) :
    sequenceCell layers (i, x) ∈ layerSupport (layers.get i) := by
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

/-- Distinct labels across every edge, side and layer denote distinct actual
cells, using both within-layer injection and between-layer disjointness. -/
theorem PackedLayers.sequenceCell_injective {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers) :
    Function.Injective (sequenceCell layers) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ heq
  by_cases hij : i = j
  · subst j
    have hinj := (h.each_layer (layers.get i) (List.get_mem layers i)).1
    have hxy : x = y := hinj heq
    cases hxy
    rfl
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := h.pairwise_disjoint.rel_get_of_lt hlt
      have hx := sequenceCell_mem layers i x
      have hy := sequenceCell_mem layers j y
      rw [← heq] at hy
      exact False.elim (Finset.disjoint_left.mp hd hx hy)
    · have hd := h.pairwise_disjoint.rel_get_of_lt hgt
      have hx := sequenceCell_mem layers i x
      have hy := sequenceCell_mem layers j y
      rw [heq] at hx
      exact False.elim (Finset.disjoint_left.mp hd hy hx)

/-- Every sequence slot avoids the reservation present before the first layer. -/
theorem PackedLayers.sequenceCell_unreserved {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers)
    (x : Fin layers.length × (Fin n × Bool)) : sequenceCell layers x ∉ reserved := by
  have hx := sequenceCell_mem layers x.1 x.2
  have hall := layerSupport_subset (layers.get x.1) layers (List.get_mem layers x.1) hx
  intro hr
  exact Finset.disjoint_left.mp h.reserved_disjoint hr hall

/-- Install a globally distinct family of actual pool values at every slot
of the sequence, preserving every original reserved cell. -/
theorem PackedLayers.install_values {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers)
    (a : Cell n ≃ Fin (n * n))
    (values : (Fin layers.length × (Fin n × Bool)) → pool n)
    (hvalues : Function.Injective values)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x, entry b (sequenceCell layers x) = (values x).val) ∧
      (∀ c ∈ reserved, entry b c = entry a c) := by
  exact place_distinct_pool_entries_preserving a (sequenceCell layers) values reserved
    h.sequenceCell_injective hvalues h.sequenceCell_unreserved havoid

/-- Actual equal-gap pairs for all layers can be installed simultaneously.
The supplied values must be globally distinct pool entries and avoid the
entries already held by the initial reservation. -/
theorem PackedLayers.install_gap_values {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers)
    (a : Cell n ≃ Fin (n * n))
    (values : (Fin layers.length × (Fin n × Bool)) → pool n)
    (hvalues : Function.Injective values)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c)
    (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, (values (i, (e, true))).val =
      (values (i, (e, false))).val + gap i e) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
        entry b (e, (layers.get i).2 e) + gap i e) ∧
      (∀ x, entry b (sequenceCell layers x) = (values x).val) ∧
      (∀ c ∈ reserved, entry b c = entry a c) := by
  obtain ⟨b, hplace, hfixed⟩ := h.install_values a values hvalues havoid
  refine ⟨b, ?_, hplace, hfixed⟩
  intro i e
  have hlow := hplace (i, (e, false))
  have hhigh := hplace (i, (e, true))
  simp only [sequenceCell, layerCell, Bool.false_eq_true, ↓reduceIte] at hlow hhigh
  rw [hhigh, hlow]
  exact hgap i e

/-- Full finite row-layer construction with supplied distinct pool values.
It chooses disjoint balanced physical layers, installs all supplied pairs at
once, retains every specified gap and preserves the initial reservation.
The derangements, pool-value supply, gap equations and load bound are explicit
caller hypotheses. -/
theorem pack_and_install_finite_layers {n L : ℕ}
    (πs : List (Equiv.Perm (Fin n))) (reserved : Finset (Cell n))
    (hderange : ∀ π ∈ πs, ∀ i, π i ≠ i)
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L)
    (hn : 4 * (L + 2 * πs.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n))
    (values : (Fin πs.length × (Fin n × Bool)) → pool n)
    (hvalues : Function.Injective values)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c)
    (gap : Fin πs.length → Fin n → ℕ)
    (hgap : ∀ i e, (values (i, (e, true))).val =
      (values (i, (e, false))).val + gap i e) :
    ∃ (layers : List (Layer n)) (hlen : layers.length = πs.length)
      (b : Cell n ≃ Fin (n * n)),
      layers.map Prod.fst = πs ∧ PackedLayers reserved layers ∧
      (∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
        entry b (e, (layers.get i).2 e) + gap (Fin.cast hlen i) e) ∧
      (∀ x, entry b (sequenceCell layers x) = (values (Fin.cast hlen x.1, x.2)).val) ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      (∀ r, ((layersSupport layers).filter (fun z => z.1 = r)).card = 2 * πs.length) ∧
      (∀ c, ((layersSupport layers).filter (fun z => z.2 = c)).card = 2 * πs.length) := by
  obtain ⟨layers, hmap, hpacked⟩ := pack_finite_layers πs reserved hderange hrow hcol hn
  have hlen : layers.length = πs.length := by
    simpa using congrArg List.length hmap
  let relabel : Fin layers.length × (Fin n × Bool) → Fin πs.length × (Fin n × Bool) :=
    fun x => (Fin.cast hlen x.1, x.2)
  have hrelabel : Function.Injective relabel := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hi : Fin.cast hlen i = Fin.cast hlen j := congrArg Prod.fst heq
    have hx : x = y := congrArg Prod.snd heq
    have hij : i = j := (finCongr hlen).injective hi
    subst j
    subst y
    rfl
  let v := values ∘ relabel
  have hv : Function.Injective v := hvalues.comp hrelabel
  have ha : ∀ x c, c ∈ reserved → (v x).val ≠ entry a c := by
    intro x c hc
    exact havoid (relabel x) c hc
  have hg : ∀ i e, (v (i, (e, true))).val =
      (v (i, (e, false))).val + gap (Fin.cast hlen i) e := by
    intro i e
    exact hgap (Fin.cast hlen i) e
  obtain ⟨b, hphysical, hplaced, hfixed⟩ :=
    hpacked.install_gap_values a v hv ha (fun i e => gap (Fin.cast hlen i) e) hg
  refine ⟨layers, hlen, b, hmap, hpacked, hphysical, ?_, hfixed, ?_, ?_⟩
  · intro x
    exact hplaced x
  · intro r
    simpa [hlen] using hpacked.row_balance r
  · intro c
    simpa [hlen] using hpacked.column_balance c

/-- Membership in the union is witnessed by an actual listed layer. -/
theorem mem_layersSupport_iff {n : ℕ} (layers : List (Layer n)) (z : Cell n) :
    z ∈ layersSupport layers ↔ ∃ x ∈ layers, z ∈ layerSupport x := by
  induction layers with
  | nil => simp [layersSupport]
  | cons x xs ih =>
    simp only [layersSupport, Finset.mem_union, List.mem_cons, ih]
    aesop

/-- Every cell in the accumulated support has a concrete layer/edge/side
label. Together with injectivity this prevents unaccounted physical cells. -/
theorem sequenceCell_covers {n : ℕ} (layers : List (Layer n)) (z : Cell n)
    (hz : z ∈ layersSupport layers) :
    ∃ x, sequenceCell layers x = z := by
  obtain ⟨layer, hlayer, hcell⟩ := (mem_layersSupport_iff layers z).mp hz
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hlayer
  obtain ⟨slot, _, hslot⟩ := Finset.mem_image.mp hcell
  refine ⟨(i, slot), ?_⟩
  change layerCell (layers.get i).1 (layers.get i).2 slot = z
  rw [hi]
  exact hslot

/-- For a fixed physical row, counting occupied columns is the same as
counting occupied cells in that row. -/
theorem rowUsed_card_eq {n : ℕ} (s : Finset (Cell n)) (r : Fin n) :
    (rowUsed s r).card = (s.filter (fun z => z.1 = r)).card := by
  have himage : (s.filter (fun z => z.1 = r)).image Prod.snd = rowUsed s r := by
    ext c
    simp [rowUsed]
  rw [← himage, Finset.card_image_iff.mpr]
  intro x hx y hy heq
  apply Prod.ext
  · exact ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm
  · exact heq

/-- The corresponding physical column count. -/
theorem colUsed_card_eq {n : ℕ} (s : Finset (Cell n)) (c : Fin n) :
    (colUsed s c).card = (s.filter (fun z => z.2 = c)).card := by
  have himage : (s.filter (fun z => z.2 = c)).image Prod.fst = colUsed s c := by
    ext r
    simp [colUsed]
  rw [← himage, Finset.card_image_iff.mpr]
  intro x hx y hy heq
  apply Prod.ext
  · exact heq
  · exact ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm

/-- Adding a whole packed sequence to the initial reservation increases the
row and column loads by at most two per layer. -/
theorem PackedLayers.union_load {n L : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers)
    (hrow : ∀ r, (rowUsed reserved r).card ≤ L)
    (hcol : ∀ c, (colUsed reserved c).card ≤ L) :
    (∀ r, (rowUsed (reserved ∪ layersSupport layers) r).card ≤ L + 2 * layers.length) ∧
    (∀ c, (colUsed (reserved ∪ layersSupport layers) c).card ≤ L + 2 * layers.length) := by
  constructor
  · intro r
    rw [rowUsed_union]
    have hu := Finset.card_union_le (rowUsed reserved r) (rowUsed (layersSupport layers) r)
    have hs : (rowUsed (layersSupport layers) r).card = 2 * layers.length := by
      rw [rowUsed_card_eq]
      exact h.row_balance r
    have hr := hrow r
    omega
  · intro c
    rw [colUsed_union]
    have hu := Finset.card_union_le (colUsed reserved c) (colUsed (layersSupport layers) c)
    have hs : (colUsed (layersSupport layers) c).card = 2 * layers.length := by
      rw [colUsed_card_eq]
      exact h.column_balance c
    have hc := hcol c
    omega

end
end Sude.LayerPacking
