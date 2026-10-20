import CollatzTM.Twelve

namespace CollatzTM.M12.Binary

/-- Removing a low-order digit preserves normality when digits remain. -/
theorem normal_tail (b : Bool) (bs : List Bool) (h : Normal (b::bs))
    (hne : bs≠[]) : Normal bs := by
  refine ⟨hne,?_⟩
  have hh := h.2
  rw [List.getLast?_cons_of_ne_nil hne] at hh
  exact hh

theorem normal_cons (b : Bool) (bs : List Bool) (h : Normal bs) : Normal (b::bs) := by
  refine ⟨by simp,?_⟩
  rw [List.getLast?_cons_of_ne_nil h.1]
  exact h.2

theorem normal_pos (bs : List Bool) (h : Normal bs) : 0<value bs := by
  induction bs with
  | nil => exact False.elim (h.1 rfl)
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb : b=true := by simpa [Normal] using h.2
      subst b
      decide
    | cons c cs =>
      have ht := normal_tail b (c::cs) h (by simp)
      have hv := ih ht
      change 0 < b.toNat+2*value (c::cs)
      omega

/-- The canonical LSB-first representation is unique, including zero as the
    empty word. Normality is essential to rule out high zero padding. -/
theorem value_injective (bs cs : List Bool)
    (hb : bs=[] ∨ Normal bs) (hc : cs=[] ∨ Normal cs)
    (he : value bs=value cs) : bs=cs := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil => rfl
    | cons c cs =>
      have hn : Normal (c::cs) := hc.resolve_left (by simp)
      have hv := normal_pos _ hn
      change 0=value (c::cs) at he
      omega
  | cons b bs ih =>
    have hn : Normal (b::bs) := hb.resolve_left (by simp)
    cases cs with
    | nil =>
      have hv := normal_pos _ hn
      change value (b::bs)=0 at he
      omega
    | cons c cs =>
      have hm : Normal (c::cs) := hc.resolve_left (by simp)
      have hb' : bs=[] ∨ Normal bs := by
        by_cases h : bs=[]
        · exact Or.inl h
        · exact Or.inr (normal_tail b bs hn h)
      have hc' : cs=[] ∨ Normal cs := by
        by_cases h : cs=[]
        · exact Or.inl h
        · exact Or.inr (normal_tail c cs hm h)
      have he' : value bs=value cs := by
        simp only [value] at he
        cases b <;> cases c <;> simp at he <;> omega
      have hbc : b=c := by
        simp only [value] at he
        cases b <;> cases c <;> simp at he ⊢ <;> omega
      rw [hbc,ih cs hb' hc' he']

theorem normal_value_injective (bs cs : List Bool) (hb : Normal bs) (hc : Normal cs)
    (he : value bs=value cs) : bs=cs :=
  value_injective bs cs (Or.inr hb) (Or.inr hc) he

/-- Computational LSB-first binary digits with no high-order zero. -/
def bits (n : Nat) : List Bool :=
  if n=0 then [] else
  if n=1 then [true] else
  decide (n%2=1) :: bits (n/2)
termination_by n
  decreasing_by omega

theorem bits_positive_spec (n : Nat) (hn : 0<n) :
    Normal (bits n) ∧ value (bits n)=n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n=1
    · subst n
      simp [bits,Normal,value]
    have h0 : n≠0 := by omega
    have hn2 : 0<n/2 := by omega
    have hlt : n/2<n := by omega
    obtain ⟨hN,hV⟩ := ih (n/2) hlt hn2
    rw [bits,if_neg h0,if_neg h1]
    refine ⟨normal_cons _ _ hN,?_⟩
    simp only [value,hV]
    by_cases hp : n%2=1
    · simp [hp]; omega
    · simp [hp]; omega

@[simp] theorem value_bits (n : Nat) : value (bits n)=n := by
  by_cases h : n=0
  · subst n; simp [bits,value]
  · exact (bits_positive_spec n (by omega)).2

theorem bits_normal (n : Nat) (hn : 0<n) : Normal (bits n) :=
  (bits_positive_spec n hn).1

theorem normal_eq_bits (bs : List Bool) (h : Normal bs) : bs=bits (value bs) := by
  exact normal_value_injective _ _ h (bits_normal _ (normal_pos _ h)) (by simp)

theorem positive_has_unique_normal (n : Nat) (hn : 0<n) :
    ∃ bs, Normal bs ∧ value bs=n ∧ ∀ cs, Normal cs → value cs=n → cs=bs := by
  refine ⟨bits n,bits_normal n hn,value_bits n,?_⟩
  intro cs hc he
  exact normal_value_injective _ _ hc (bits_normal n hn) (he.trans (value_bits n).symm)

/-- Every finite binary word is strictly below its length's power of two. -/
theorem value_lt_pow_length (bs : List Bool) : value bs<2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    simp only [value,List.length_cons,Nat.pow_succ]
    cases b <;> simp <;> omega

/-- The highest digit of a normal word supplies the matching lower bound. -/
theorem pow_pred_length_le_value (bs : List Bool) (h : Normal bs) :
    2^(bs.length-1)≤value bs := by
  induction bs with
  | nil => exact False.elim (h.1 rfl)
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb : b=true := by simpa [Normal] using h.2
      subst b
      decide
    | cons c cs =>
      have ht := normal_tail b (c::cs) h (by simp)
      have hv := ih ht
      simp only [List.length_cons,Nat.add_sub_cancel] at hv
      change 2^(cs.length+1)≤b.toNat+2*value (c::cs)
      rw [Nat.pow_succ]
      omega

/-- This length specification is the usual positive integer bitlength. -/
def bitlength (n : Nat) : Nat := (bits n).length

theorem bitlength_bounds (n : Nat) (hn : 0<n) :
    2^(bitlength n-1)≤n ∧ n<2^bitlength n := by
  have h := bits_normal n hn
  have hl := pow_pred_length_le_value (bits n) h
  have hu := value_lt_pow_length (bits n)
  simpa only [bitlength,value_bits] using And.intro hl hu

theorem normal_length_bitlength (bs : List Bool) (h : Normal bs) :
    bs.length=bitlength (value bs) := by
  rw [normal_eq_bits bs h]
  simp only [bitlength,value_bits]

theorem bitlength_eq_log2 (n : Nat) (hn : 0<n) : bitlength n=n.log2+1 := by
  have hlen : 0<bitlength n := List.length_pos_iff.mpr (bits_normal n hn).1
  have hb := bitlength_bounds n hn
  have hlo := (Nat.le_log2 (by omega : n≠0)).mpr hb.1
  have hhi := (Nat.log2_lt (by omega : n≠0)).mpr hb.2
  omega

end CollatzTM.M12.Binary

namespace CollatzTM.M12

/-- Exact canonical input on a positive natural number, using computed LSB bits. -/
def canonicalNat (n : Nat) (p : Int) : Config State := canonical (Binary.bits n) p

theorem canonicalNat_value (n : Nat) : value (Binary.bits n)=n := Binary.value_bits n

theorem canonicalNat_normal (n : Nat) (hn : 0<n) : Normal (Binary.bits n) :=
  Binary.bits_normal n hn

end CollatzTM.M12
