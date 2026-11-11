import Sude.CentralDiagonalPlacement

/-! Exact free-diagonal partition around the unique odd-order center. -/
namespace Sude
noncomputable section

def centralCell (n : ℕ) (hn : 0 < n) : Cell n :=
  (centerIndex n hn, centerIndex n hn)

def centralFreeMain {n : ℕ} (hn : 0 < n) (reserved : Finset (Cell n)) : Finset (Cell n) :=
  (mainCells n \ reserved) \ {centralCell n hn}

def centralFreeAnti {n : ℕ} (hn : 0 < n) (reserved : Finset (Cell n)) : Finset (Cell n) :=
  (antiCells n \ reserved) \ {centralCell n hn}

/-- On an odd square the two full diagonals intersect only at the center. -/
theorem main_anti_intersection {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    mainCells n ∩ antiCells n = {centralCell n hn} := by
  ext z
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, ha⟩
    have hm' := (mem_mainCells z).1 hm
    have ha' := (mem_antiCells z).1 ha
    have hr : z.1.rev = z.1 := ha'.symm.trans hm'.symm
    have hv := congrArg Fin.val hr
    change n - (z.1.val + 1) = z.1.val at hv
    obtain ⟨k, hk⟩ := hodd
    have hz : z.1.val < n := z.1.isLt
    have hcenter : z.1 = centerIndex n hn := by
      apply Fin.ext
      change z.1.val = n / 2
      omega
    apply Prod.ext
    · exact hcenter
    · exact hm'.symm.trans hcenter
  · intro hz
    subst z
    exact centerCell_on_both_diagonals n hn hodd

theorem mainCells_card (n : ℕ) : (mainCells n).card = n := by
  unfold mainCells
  rw [Finset.card_image_of_injective _ (by
    intro i j h
    exact congrArg Prod.fst h)]
  simp

theorem antiCells_card (n : ℕ) : (antiCells n).card = n := by
  unfold antiCells
  rw [Finset.card_image_of_injective _ (by
    intro i j h
    exact congrArg Prod.fst h)]
  simp

/-- The actual free diagonal cells split into one shared center and two
disjoint noncentral groups, each of size at most `n - 1`. -/
theorem central_free_diagonal_geometry {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (reserved : Finset (Cell n)) (hcenter : centralCell n hn ∉ reserved) :
    let X : Finset (Cell n) := {centralCell n hn}
    let Y := centralFreeMain hn reserved
    let Z := centralFreeAnti hn reserved
    X.card = 1 ∧ Y.card ≤ n - 1 ∧ Z.card ≤ n - 1 ∧
      Disjoint X reserved ∧ Disjoint Y reserved ∧ Disjoint Z reserved ∧
      Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
      X ∪ Y = mainCells n \ reserved ∧ X ∪ Z = antiCells n \ reserved := by
  classical
  let X : Finset (Cell n) := {centralCell n hn}
  let Y := centralFreeMain hn reserved
  let Z := centralFreeAnti hn reserved
  have hc := centerCell_on_both_diagonals n hn hodd
  have hcmain : centralCell n hn ∈ mainCells n := hc.1
  have hcanti : centralCell n hn ∈ antiCells n := hc.2
  have hmain : X ∪ Y = mainCells n \ reserved := by
    ext z
    simp only [X, Y, centralFreeMain, Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
    constructor
    · rintro (rfl | ⟨⟨hm, hr⟩, _⟩)
      · exact ⟨hcmain, hcenter⟩
      · exact ⟨hm, hr⟩
    · rintro ⟨hm, hr⟩
      by_cases hz : z = centralCell n hn
      · exact Or.inl hz
      · exact Or.inr ⟨⟨hm, hr⟩, hz⟩
  have hanti : X ∪ Z = antiCells n \ reserved := by
    ext z
    simp only [X, Z, centralFreeAnti, Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff]
    constructor
    · rintro (rfl | ⟨⟨ha, hr⟩, _⟩)
      · exact ⟨hcanti, hcenter⟩
      · exact ⟨ha, hr⟩
    · rintro ⟨ha, hr⟩
      by_cases hz : z = centralCell n hn
      · exact Or.inl hz
      · exact Or.inr ⟨⟨ha, hr⟩, hz⟩
  have hXR : Disjoint X reserved := by simp [X, hcenter]
  have hYR : Disjoint Y reserved := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hr
  have hZR : Disjoint Z reserved := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hr
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro z hz hy
    have heq : z = centralCell n hn := Finset.mem_singleton.mp hz
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_singleton.mpr heq)
  have hXZ : Disjoint X Z := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have heq : z = centralCell n hn := Finset.mem_singleton.mp hz
    exact (Finset.mem_sdiff.mp hz').2 (Finset.mem_singleton.mpr heq)
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro z hy hz
    have hm : z ∈ mainCells n := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hy).1).1
    have ha : z ∈ antiCells n := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).1
    have hzcenter : z = centralCell n hn := by
      have h := Finset.mem_inter.mpr ⟨hm, ha⟩
      rw [main_anti_intersection hn hodd] at h
      exact Finset.mem_singleton.mp h
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_singleton.mpr hzcenter)
  have hYX : Y ⊆ mainCells n \ X := by
    intro z hz
    have hz' := Finset.mem_sdiff.mp hz
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz'.1).1, hz'.2⟩
  have hZX : Z ⊆ antiCells n \ X := by
    intro z hz
    have hz' := Finset.mem_sdiff.mp hz
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz'.1).1, hz'.2⟩
  have hXm : X ⊆ mainCells n := by simpa [X] using hcmain
  have hXa : X ⊆ antiCells n := by simpa [X] using hcanti
  have hcountm := Finset.card_sdiff_add_card_eq_card hXm
  have hcounta := Finset.card_sdiff_add_card_eq_card hXa
  have hYcard := Finset.card_le_card hYX
  have hZcard := Finset.card_le_card hZX
  have hXcard : X.card = 1 := by simp [X]
  rw [mainCells_card, hXcard] at hcountm
  rw [antiCells_card, hXcard] at hcounta
  have hYbound : Y.card ≤ n - 1 := by omega
  have hZbound : Z.card ≤ n - 1 := by omega
  exact ⟨hXcard, hYbound, hZbound, hXR, hYR, hZR, hXY, hXZ, hYZ, hmain, hanti⟩

end
end Sude
