import Sude.FastTwinStrideSixScan

/-!
# Native 8,192-Bit Parallel SWAR Popcount (`FastSwarPopcount`)

Computes the exact popcount of an `8,192`-bit `ℕ` word in `13` straight-line GMP
operations (`swarPop8192 m0 m1 m2 m3 x`), proved equal to `fastSetCount 10 (x &&& ((1 <<< 8192) - 1))`.
Eliminates the `2,047`-node divide-and-conquer recursion tree of `fastSetCount 10`
inside `decide +kernel`.
-/

namespace Sude

noncomputable section

set_option autoImplicit false

/-- Repeat a 16-bit constant across `2 ^ d` 16-bit lanes (`16 <<< d` bits total). -/
def rep16 : ℕ → ℕ → ℕ
  | 0, c => c
  | d + 1, c =>
      let v := rep16 d c
      v ||| (v <<< (16 <<< d))

/-- Fold `2 ^ d` non-overflowing 16-bit lanes down to a single 16-bit sum. -/
def fold16 : ℕ → ℕ → ℕ
  | 0, x => x &&& 0xffff
  | d + 1, x =>
      let h := 16 <<< d
      fold16 d ((x &&& ((1 <<< h) - 1)) + (x >>> h))

/-- Parallel 16-bit-lane popcount over `16 <<< d` bits. -/
def swar16LanesWithMasks (d m0 m1 m2 m3 x : ℕ) : ℕ :=
  let xm := x &&& ((1 <<< (16 <<< d)) - 1)
  let x1 := (xm &&& m0) + ((xm >>> 1) &&& m0)
  let x2 := (x1 &&& m1) + ((x1 >>> 2) &&& m1)
  let x3 := (x2 &&& m2) + ((x2 >>> 4) &&& m2)
  (x3 &&& m3) + ((x3 >>> 8) &&& m3)

/-- Canonical `swar16Lanes` using `rep16 d` masks. -/
def swar16Lanes (d x : ℕ) : ℕ :=
  swar16LanesWithMasks d (rep16 d 0x5555) (rep16 d 0x3333) (rep16 d 0x0f0f) (rep16 d 0x00ff) x

/-- Precomputed `8,192`-bit SWAR masks (`d = 9`, `16 <<< 9 = 8,192`). -/
def swarMask0 : ℕ := rep16 9 0x5555
def swarMask1 : ℕ := rep16 9 0x3333
def swarMask2 : ℕ := rep16 9 0x0f0f
def swarMask3 : ℕ := rep16 9 0x00ff

/-- Straight-line `8,192`-bit popcount taking pre-forced masks `m0..m3`. -/
def swarPop8192 (m0 m1 m2 m3 x : ℕ) : ℕ :=
  fold16 9 (swar16LanesWithMasks 9 m0 m1 m2 m3 x)

private def swarByte (x : ℕ) : ℕ :=
  let xm := x &&& 0xff
  let x1 := (xm &&& 0x55) + ((xm >>> 1) &&& 0x55)
  let x2 := (x1 &&& 0x33) + ((x1 >>> 2) &&& 0x33)
  (x2 &&& 0x0f) + ((x2 >>> 4) &&& 0x0f)

private theorem swarByte_fin :
    ∀ y : Fin 256, swarByte y.val = popcount8 y.val ∧ swarByte y.val ≤ 8 := by
  decide +kernel

private theorem and_mask_lt (x w : ℕ) : x &&& ((1 <<< w) - 1) < 2 ^ w := by
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt x (Nat.two_pow_pos w)

private theorem split_at_bit (w x : ℕ) :
    x = (x &&& ((1 <<< w) - 1)) + 2 ^ w * (x >>> w) := by
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_add_div x (2 ^ w)).symm

private theorem add_mul_pow_and_shr {w aLo aHi : ℕ} (ha : aLo < 2 ^ w) :
    (aLo + 2 ^ w * aHi) &&& ((1 <<< w) - 1) = aLo ∧
    (aLo + 2 ^ w * aHi) >>> w = aHi := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  rw [Nat.add_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt ha, Nat.add_zero]
  exact ⟨rfl, rfl⟩

private theorem or_shift_eq_add_mul {w aLo aHi : ℕ} (ha : aLo < 2 ^ w) :
    (aLo ||| (aHi <<< w)) = aLo + 2 ^ w * aHi := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm aHi (2 ^ w), Nat.lor_comm, Nat.add_comm]
  simpa [Nat.mul_comm] using (Nat.two_pow_add_eq_or_of_lt ha aHi).symm

private theorem and_lt_of_right_lt {x m k : ℕ} (hm : m < 2 ^ k) : (x &&& m) < 2 ^ k := by
  by_contra hge
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hge' : 2 ^ k ≤ x &&& m := by omega
  have hne0 : x &&& m ≠ 0 := by omega
  have hlog : k ≤ (x &&& m).log2 := (Nat.le_log2 hne0).mpr hge'
  have htb := Nat.testBit_log2 hne0
  rw [Nat.testBit_and] at htb
  have hm_tb : m.testBit (x &&& m).log2 = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hlog))
  simp [hm_tb] at htb

private theorem rep16_top_clear (d c s : ℕ) (hc : c < 2 ^ (16 - s)) (hs : s ≤ 16) :
    rep16 d c < 2 ^ ((16 <<< d) - s) := by
  induction d with
  | zero => simpa [rep16] using hc
  | succ d ih =>
    set h := 16 <<< d
    have hge : 16 ≤ h := by
      dsimp [h]; rw [Nat.shiftLeft_eq]; have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; nlinarith
    have hsh : 16 <<< (d + 1) = h + h := by dsimp [h]; simp [Nat.shiftLeft_eq, pow_succ]; ring
    have hexp : (h + h) - s = h + (h - s) := by omega
    unfold rep16
    dsimp only
    have hlt_h : rep16 d c < 2 ^ h :=
      lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega))
    rw [or_shift_eq_add_mul hlt_h, hsh, hexp, pow_add]
    nlinarith [Nat.two_pow_pos h]

private theorem rep16_succ_eq (d c : ℕ) (hc : c < 65536) :
    rep16 (d + 1) c = rep16 d c + 2 ^ (16 <<< d) * rep16 d c := by
  have hlt := rep16_top_clear d c 0 (by simpa using hc) (by decide)
  simp only [Nat.sub_zero] at hlt
  conv_lhs => unfold rep16
  exact or_shift_eq_add_mul (aHi := rep16 d c) hlt

private theorem and_split_at_bit (w x y : ℕ) :
    (x &&& y) = ((x &&& ((1 <<< w) - 1)) &&& (y &&& ((1 <<< w) - 1))) +
      2 ^ w * ((x >>> w) &&& (y >>> w)) := by
  have hlt : ((x &&& ((1 <<< w) - 1)) &&& (y &&& ((1 <<< w) - 1))) < 2 ^ w :=
    and_lt_of_right_lt (and_mask_lt y w)
  rw [← or_shift_eq_add_mul hlt]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_lor, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < w
  · have hn : ¬ (w ≤ b) := by omega
    simp [hb, hn]
  · have hge : w ≤ b := by omega
    have hadd : w + (b - w) = b := by omega
    simp [hb, hge, hadd]

private theorem swar_step_split {w s : ℕ} (x m : ℕ)
    (hm : m < 2 ^ (w - s)) (hs1 : 1 ≤ s) (hsw : s ≤ w) :
    ((x &&& (m + 2 ^ w * m)) + ((x >>> s) &&& (m + 2 ^ w * m))) =
      (((x &&& ((1 <<< w) - 1)) &&& m) + (((x &&& ((1 <<< w) - 1)) >>> s) &&& m)) +
        2 ^ w * ((((x >>> w) &&& m) + (((x >>> w) >>> s) &&& m))) ∧
    (((x &&& ((1 <<< w) - 1)) &&& m) + (((x &&& ((1 <<< w) - 1)) >>> s) &&& m)) < 2 ^ w := by
  have hm1 : m < 2 ^ (w - 1) :=
    lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
  have hm_lt : m < 2 ^ w :=
    lt_of_lt_of_le hm1 (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨m_and, m_shr⟩ := add_mul_pow_and_shr hm_lt
  have h1 : x &&& (m + 2 ^ w * m) = ((x &&& ((1 <<< w) - 1)) &&& m) + 2 ^ w * ((x >>> w) &&& m) := by
    rw [and_split_at_bit w x (m + 2 ^ w * m), m_and, m_shr]
  have h2 : (x >>> s) &&& (m + 2 ^ w * m) =
      (((x &&& ((1 <<< w) - 1)) >>> s) &&& m) + 2 ^ w * (((x >>> w) >>> s) &&& m) := by
    rw [and_split_at_bit w (x >>> s) (m + 2 ^ w * m), m_and, m_shr]
    congr 1
    · apply Nat.eq_of_testBit_eq
      intro b
      simp only [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
      by_cases hb : b < w - s
      · have hbs : s + b < w := by omega
        have hbw : b < w := by omega
        simp [hbs, hbw]
      · have hm_b : m.testBit b = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hm_b]
    · congr 1
      rw [← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_comm]
  have hlo1 := and_lt_of_right_lt (x := x &&& ((1 <<< w) - 1)) hm1
  have hlo2 := and_lt_of_right_lt (x := (x &&& ((1 <<< w) - 1)) >>> s) hm1
  have hpow2 : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, pow_succ]
    omega
  refine ⟨by rw [h1, h2]; ring, by omega⟩

private theorem swar16Lanes_zero (x : ℕ) :
    swar16Lanes 0 x = popcount8 (x &&& 0xff) + popcount8 ((x >>> 8) &&& 0xff) ∧
    swar16Lanes 0 x ≤ 16 := by
  have h55 : (0x55 + 2 ^ 8 * 0x55) = 0x5555 := by decide
  have h33 : (0x33 + 2 ^ 8 * 0x33) = 0x3333 := by decide
  have h0f : (0x0f + 2 ^ 8 * 0x0f) = 0x0f0f := by decide
  set xm := x &&& 0xffff
  set bLo := xm &&& 0xff
  set bHi := xm >>> 8
  have hb8 : ((1 <<< 8) - 1) = 0xff := by decide
  obtain ⟨hstep1, hy1Lo_lt⟩ := swar_step_split (w := 8) (s := 1) xm 0x55 (by decide) (by decide) (by decide)
  rw [h55] at hstep1
  rw [hb8] at hstep1 hy1Lo_lt
  set y1Lo := (bLo &&& 0x55) + ((bLo >>> 1) &&& 0x55)
  set y1Hi := (bHi &&& 0x55) + ((bHi >>> 1) &&& 0x55)
  obtain ⟨hy1_and, hy1_shr⟩ := add_mul_pow_and_shr (aHi := y1Hi) hy1Lo_lt
  set x1 := y1Lo + 2 ^ 8 * y1Hi
  obtain ⟨hstep2, hy2Lo_lt⟩ := swar_step_split (w := 8) (s := 2) x1 0x33 (by decide) (by decide) (by decide)
  rw [h33, hy1_and, hy1_shr] at hstep2
  rw [hy1_and] at hy2Lo_lt
  set y2Lo := (y1Lo &&& 0x33) + ((y1Lo >>> 2) &&& 0x33)
  set y2Hi := (y1Hi &&& 0x33) + ((y1Hi >>> 2) &&& 0x33)
  obtain ⟨hy2_and, hy2_shr⟩ := add_mul_pow_and_shr (aHi := y2Hi) hy2Lo_lt
  set x2 := y2Lo + 2 ^ 8 * y2Hi
  obtain ⟨hstep3, _⟩ := swar_step_split (w := 8) (s := 4) x2 0x0f (by decide) (by decide) (by decide)
  rw [h0f] at hstep3
  rw [hy2_and, hy2_shr] at hstep3
  have hbLo_eq : bLo = x &&& 0xff := by
    dsimp [bLo, xm]
    apply Nat.eq_of_testBit_eq; intro b
    simp only [Nat.testBit_and]
    have h8 : (0xff : ℕ).testBit b = decide (b < 8) := by
      change ((1 <<< 8) - 1).testBit b = _; rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    have h16 : (0xffff : ℕ).testBit b = decide (b < 16) := by
      change ((1 <<< 16) - 1).testBit b = _; rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    rw [h8, h16]
    by_cases hb : b < 8
    · simp [hb, show b < 16 by omega]
    · simp [hb]
  have hbHi_eq : bHi = (x >>> 8) &&& 0xff := by
    dsimp [bHi, xm]
    apply Nat.eq_of_testBit_eq; intro b
    simp only [Nat.testBit_shiftRight, Nat.testBit_and]
    have h8 : (0xff : ℕ).testBit b = decide (b < 8) := by
      change ((1 <<< 8) - 1).testBit b = _; rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    have h16 : ∀ k, (0xffff : ℕ).testBit k = decide (k < 16) := fun k => by
      change ((1 <<< 16) - 1).testBit k = _; rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    rw [h8, h16]
    by_cases hb : b < 8
    · have : 8 + b < 16 := by omega
      simp [hb, this]
    · have : ¬ (8 + b < 16) := by omega
      simp [hb, this]
  have hsLo : (y2Lo &&& 0x0f) + ((y2Lo >>> 4) &&& 0x0f) = swarByte (x &&& 0xff) := by
    unfold swarByte
    dsimp only
    have hidem : (x &&& 0xff) &&& 0xff = x &&& 0xff := by rw [Nat.and_assoc, Nat.and_self]
    rw [hidem, ← hbLo_eq]
  have hsHi : (y2Hi &&& 0x0f) + ((y2Hi >>> 4) &&& 0x0f) = swarByte ((x >>> 8) &&& 0xff) := by
    unfold swarByte
    dsimp only
    have hidem : ((x >>> 8) &&& 0xff) &&& 0xff = (x >>> 8) &&& 0xff := by rw [Nat.and_assoc, Nat.and_self]
    rw [hidem, ← hbHi_eq]
  have hfLo := swarByte_fin ⟨x &&& 0xff, by
    change _ &&& (2 ^ 8 - 1) < 256; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)⟩
  have hfHi := swarByte_fin ⟨(x >>> 8) &&& 0xff, by
    change _ &&& (2 ^ 8 - 1) < 256; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by decide)⟩
  dsimp at hfLo hfHi
  have hx3_eq : ((x2 &&& 0x0f0f) + ((x2 >>> 4) &&& 0x0f0f)) =
      swarByte (x &&& 0xff) + 2 ^ 8 * swarByte ((x >>> 8) &&& 0xff) := by
    rw [hstep3, hsLo, hsHi]
  have hsLo_lt : swarByte (x &&& 0xff) < 2 ^ 8 := by omega
  obtain ⟨hx3_and, hx3_shr⟩ := add_mul_pow_and_shr (aHi := swarByte ((x >>> 8) &&& 0xff)) hsLo_lt
  have h16mask : ((1 <<< (16 <<< 0)) - 1) = 0xffff := by decide
  unfold swar16Lanes swar16LanesWithMasks
  simp only [rep16, h16mask]
  rw [show (x &&& 0xffff &&& 0x5555) + ((x &&& 0xffff) >>> 1 &&& 0x5555) = x1 from hstep1,
    show (x1 &&& 0x3333) + (x1 >>> 2 &&& 0x3333) = x2 from hstep2,
    hx3_eq]
  have h0xff : (0xff : ℕ) = (1 <<< 8) - 1 := by decide
  have ha1 : (swarByte (x &&& 0xff) + 2 ^ 8 * swarByte ((x >>> 8) &&& 0xff)) &&& 0xff =
      swarByte (x &&& 0xff) := by rw [h0xff]; exact hx3_and
  have hsHi_lt : swarByte ((x >>> 8) &&& 0xff) < 2 ^ 8 := by omega
  have ha2 : ((swarByte (x &&& 0xff) + 2 ^ 8 * swarByte ((x >>> 8) &&& 0xff)) >>> 8) &&& 0xff =
      swarByte ((x >>> 8) &&& 0xff) := by
    rw [hx3_shr]
    change swarByte ((x >>> 8) &&& 0xff) &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hsHi_lt]
  rw [ha1, ha2, hfLo.1, hfHi.1]
  exact ⟨rfl, by omega⟩

private theorem swar16Lanes_succ (d x : ℕ) :
    let h := 16 <<< d
    swar16Lanes (d + 1) x =
      swar16Lanes d (x &&& ((1 <<< h) - 1)) + 2 ^ h * swar16Lanes d (x >>> h) := by
  set h := 16 <<< d
  have hge : 16 ≤ h := by
    dsimp [h]; rw [Nat.shiftLeft_eq]; have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; nlinarith
  have hm0 := rep16_succ_eq d 0x5555 (by decide)
  have hm1 := rep16_succ_eq d 0x3333 (by decide)
  have hm2 := rep16_succ_eq d 0x0f0f (by decide)
  have hm3 := rep16_succ_eq d 0x00ff (by decide)
  set xm := x &&& ((1 <<< (16 <<< (d + 1))) - 1)
  have hxm_lo : xm &&& ((1 <<< h) - 1) = (x &&& ((1 <<< h) - 1)) &&& ((1 <<< h) - 1) := by
    have hsh : h ≤ 16 <<< (d + 1) := by
      dsimp [h]; simp only [Nat.shiftLeft_eq, pow_succ]; omega
    apply Nat.eq_of_testBit_eq; intro b
    simp only [xm, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hb : b < h
    · simp [hb, lt_of_lt_of_le hb hsh]
    · simp [hb]
  have hxm_hi : xm >>> h = (x >>> h) &&& ((1 <<< h) - 1) := by
    have hsh : 16 <<< (d + 1) = h + h := by dsimp [h]; simp [Nat.shiftLeft_eq, pow_succ]; ring
    apply Nat.eq_of_testBit_eq; intro b
    simp only [xm, hsh, Nat.testBit_shiftRight, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hb : b < h
    · have : h + b < h + h := by omega
      simp [hb, this]
    · have : ¬ (h + b < h + h) := by omega
      simp [hb, this]
  obtain ⟨hs1, hlt1⟩ := swar_step_split (w := h) (s := 1) xm (rep16 d 0x5555)
    (rep16_top_clear d 0x5555 1 (by decide) (by decide)) (by decide) (by omega)
  rw [← hm0, hxm_lo, hxm_hi] at hs1
  rw [hxm_lo] at hlt1
  set s1Lo := (((x &&& ((1 <<< h) - 1)) &&& ((1 <<< h) - 1)) &&& rep16 d 0x5555) +
    ((((x &&& ((1 <<< h) - 1)) &&& ((1 <<< h) - 1)) >>> 1) &&& rep16 d 0x5555)
  set s1Hi := (((x >>> h) &&& ((1 <<< h) - 1)) &&& rep16 d 0x5555) +
    ((((x >>> h) &&& ((1 <<< h) - 1)) >>> 1) &&& rep16 d 0x5555)
  obtain ⟨ha1, hb1⟩ := add_mul_pow_and_shr (aHi := s1Hi) hlt1
  obtain ⟨hs2, hlt2⟩ := swar_step_split (w := h) (s := 2) (s1Lo + 2 ^ h * s1Hi) (rep16 d 0x3333)
    (rep16_top_clear d 0x3333 2 (by decide) (by decide)) (by decide) (by omega)
  rw [← hm1, ha1, hb1] at hs2
  rw [ha1] at hlt2
  set s2Lo := (s1Lo &&& rep16 d 0x3333) + ((s1Lo >>> 2) &&& rep16 d 0x3333)
  set s2Hi := (s1Hi &&& rep16 d 0x3333) + ((s1Hi >>> 2) &&& rep16 d 0x3333)
  obtain ⟨ha2, hb2⟩ := add_mul_pow_and_shr (aHi := s2Hi) hlt2
  obtain ⟨hs3, hlt3⟩ := swar_step_split (w := h) (s := 4) (s2Lo + 2 ^ h * s2Hi) (rep16 d 0x0f0f)
    (rep16_top_clear d 0x0f0f 4 (by decide) (by decide)) (by decide) (by omega)
  rw [← hm2, ha2, hb2] at hs3
  rw [ha2] at hlt3
  set s3Lo := (s2Lo &&& rep16 d 0x0f0f) + ((s2Lo >>> 4) &&& rep16 d 0x0f0f)
  set s3Hi := (s2Hi &&& rep16 d 0x0f0f) + ((s2Hi >>> 4) &&& rep16 d 0x0f0f)
  obtain ⟨ha3, hb3⟩ := add_mul_pow_and_shr (aHi := s3Hi) hlt3
  obtain ⟨hs4, _⟩ := swar_step_split (w := h) (s := 8) (s3Lo + 2 ^ h * s3Hi) (rep16 d 0x00ff)
    (rep16_top_clear d 0x00ff 8 (by decide) (by decide)) (by decide) (by omega)
  rw [← hm3, ha3, hb3] at hs4
  unfold swar16Lanes swar16LanesWithMasks
  dsimp only
  rw [hs1, hs2, hs3, hs4]

private def lanesBounded : ℕ → ℕ → ℕ → Prop
  | 0, b, x => x ≤ b ∧ b < 65536
  | d + 1, b, x =>
      let h := 16 <<< d
      x < 2 ^ (16 <<< (d + 1)) ∧
      lanesBounded d b (x &&& ((1 <<< h) - 1)) ∧
      lanesBounded d b (x >>> h)

private theorem lanesBounded_lt_pow (d b x : ℕ) (h : lanesBounded d b x) :
    x < 2 ^ (16 <<< d) := by
  cases d with
  | zero => dsimp [lanesBounded] at h; change x < 65536; omega
  | succ d => exact h.1

private theorem swar16Lanes_bounded (d x : ℕ) : lanesBounded d 16 (swar16Lanes d x) := by
  induction d generalizing x with
  | zero =>
    exact ⟨(swar16Lanes_zero x).2, by decide⟩
  | succ d ih =>
    set h := 16 <<< d
    have hsplit := swar16Lanes_succ d x
    dsimp only at hsplit
    have hlo := ih (x &&& ((1 <<< h) - 1))
    have hhi := ih (x >>> h)
    have hlo_lt := lanesBounded_lt_pow d 16 _ hlo
    have hhi_lt := lanesBounded_lt_pow d 16 _ hhi
    obtain ⟨hand, hshr⟩ := add_mul_pow_and_shr (aHi := swar16Lanes d (x >>> h)) hlo_lt
    have h2h : 2 ^ (16 <<< (d + 1)) = 2 ^ h * 2 ^ h := by
      have : 16 <<< (d + 1) = h + h := by dsimp [h]; simp [Nat.shiftLeft_eq, pow_succ]; ring
      rw [this, pow_add]
    rw [hsplit]
    exact ⟨by rw [h2h]; nlinarith, by rw [hand]; exact hlo, by rw [hshr]; exact hhi⟩

private theorem fold16_add (d b1 b2 A B : ℕ)
    (hA : lanesBounded d b1 A) (hB : lanesBounded d b2 B)
    (hsum : 2 ^ d * (b1 + b2) < 65536) :
    lanesBounded d (b1 + b2) (A + B) ∧ fold16 d (A + B) = fold16 d A + fold16 d B := by
  induction d generalizing b1 b2 A B with
  | zero =>
    dsimp [lanesBounded, fold16] at hA hB ⊢
    simp only [pow_zero, one_mul] at hsum
    have hAB : A + B < 65536 := by omega
    have hmA : A &&& 0xffff = A := by
      change A &&& (2 ^ 16 - 1) = A
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hmB : B &&& 0xffff = B := by
      change B &&& (2 ^ 16 - 1) = B
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hmAB : (A + B) &&& 0xffff = A + B := by
      change (A + B) &&& (2 ^ 16 - 1) = A + B
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hAB]
    exact ⟨⟨by omega, hsum⟩, by rw [hmA, hmB, hmAB]⟩
  | succ d ih =>
    set h := 16 <<< d
    rcases hA with ⟨_, hAlo, hAhi⟩
    rcases hB with ⟨_, hBlo, hBhi⟩
    have hpow_pos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hpow_le : 2 ^ d * (b1 + b2) < 65536 := by rw [pow_succ] at hsum; nlinarith
    obtain ⟨hL_lo, _⟩ := ih b1 b2 _ _ hAlo hBlo hpow_le
    obtain ⟨hL_hi, _⟩ := ih b1 b2 _ _ hAhi hBhi hpow_le
    have hlo_lt : (A &&& ((1 <<< h) - 1)) + (B &&& ((1 <<< h) - 1)) < 2 ^ h :=
      lanesBounded_lt_pow d (b1 + b2) _ hL_lo
    have hhi_lt : (A >>> h) + (B >>> h) < 2 ^ h :=
      lanesBounded_lt_pow d (b1 + b2) _ hL_hi
    have hAs := split_at_bit h A
    have hBs := split_at_bit h B
    have hAB_eq : A + B = ((A &&& ((1 <<< h) - 1)) + (B &&& ((1 <<< h) - 1))) +
        2 ^ h * ((A >>> h) + (B >>> h)) := by
      conv_lhs => rw [hAs, hBs]
      ring
    obtain ⟨hand, hshr⟩ := add_mul_pow_and_shr hlo_lt
    rw [← hAB_eq] at hand hshr
    have h2h : 2 ^ (16 <<< (d + 1)) = 2 ^ h * 2 ^ h := by
      have : 16 <<< (d + 1) = h + h := by dsimp [h]; simp [Nat.shiftLeft_eq, pow_succ]; ring
      rw [this, pow_add]
    have hAB_lt : A + B < 2 ^ (16 <<< (d + 1)) := by
      rw [hAB_eq, h2h]; nlinarith
    have hb11 : 2 ^ d * (b1 + b1) < 65536 := by rw [pow_succ] at hsum; nlinarith
    have hb22 : 2 ^ d * (b2 + b2) < 65536 := by rw [pow_succ] at hsum; nlinarith
    have hb12 : 2 ^ d * ((b1 + b1) + (b2 + b2)) < 65536 := by rw [pow_succ] at hsum; nlinarith
    obtain ⟨_, hfold_step⟩ := ih (b1 + b1) (b2 + b2)
      ((A &&& ((1 <<< h) - 1)) + (A >>> h))
      ((B &&& ((1 <<< h) - 1)) + (B >>> h))
      (ih b1 b1 _ _ hAlo hAhi hb11).1
      (ih b2 b2 _ _ hBlo hBhi hb22).1
      hb12
    refine ⟨⟨hAB_lt, ?_, ?_⟩, ?_⟩
    · rw [hand]; exact hL_lo
    · rw [hshr]; exact hL_hi
    · unfold fold16
      dsimp only
      change fold16 d (((A + B) &&& ((1 <<< h) - 1)) + ((A + B) >>> h)) = _
      rw [hand, hshr]
      have hrearr : (A &&& ((1 <<< h) - 1)) + (B &&& ((1 <<< h) - 1)) + ((A >>> h) + (B >>> h)) =
          ((A &&& ((1 <<< h) - 1)) + (A >>> h)) + ((B &&& ((1 <<< h) - 1)) + (B >>> h)) := by omega
      rw [hrearr, hfold_step]

private theorem fastSetCount_mask_eq (d x : ℕ) :
    fastSetCount d (x &&& ((1 <<< (8 <<< d)) - 1)) =
      ∑ i ∈ Finset.range (8 <<< d), if x.testBit i = true then 1 else 0 := by
  rw [fastSetCount_spec]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < 8 <<< d := Finset.mem_range.mp hi
  rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp [hi_lt]

private theorem swar16_fold_eq_fastSetCount (d : ℕ) (hd : d ≤ 9) (x : ℕ) :
    fold16 d (swar16Lanes d x) = fastSetCount (d + 1) (x &&& ((1 <<< (16 <<< d)) - 1)) := by
  induction d generalizing x with
  | zero =>
    obtain ⟨h0, hle16⟩ := swar16Lanes_zero x
    unfold fold16
    have hm : swar16Lanes 0 x &&& 0xffff = swar16Lanes 0 x := by
      change _ &&& (2 ^ 16 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hm, h0]
    have hsh : (16 <<< 0) = (8 <<< 1) := by decide
    rw [hsh, fastSetCount_mask_eq 1 x]
    have h16 : (8 <<< 1) = 8 + 8 := by decide
    rw [h16, Finset.sum_range_add, popcount8_spec x, popcount8_spec (x >>> 8)]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Nat.testBit_shiftRight]
  | succ d ih =>
    set h := 16 <<< d
    have hsplit := swar16Lanes_succ d x
    dsimp only at hsplit
    have hlo_b := swar16Lanes_bounded d (x &&& ((1 <<< h) - 1))
    have hhi_b := swar16Lanes_bounded d (x >>> h)
    obtain ⟨hand, hshr⟩ := add_mul_pow_and_shr (aHi := swar16Lanes d (x >>> h))
      (lanesBounded_lt_pow d 16 _ hlo_b)
    unfold fold16
    dsimp only
    change fold16 d ((swar16Lanes (d + 1) x &&& ((1 <<< h) - 1)) + (swar16Lanes (d + 1) x >>> h)) = _
    rw [hsplit, hand, hshr]
    have hbound_sum : 2 ^ d * (16 + 16) < 65536 := by
      have : 2 ^ d ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [(fold16_add d 16 16 _ _ hlo_b hhi_b hbound_sum).2, ih (by omega), ih (by omega)]
    have hidem : (x &&& ((1 <<< h) - 1)) &&& ((1 <<< h) - 1) = x &&& ((1 <<< h) - 1) := by
      rw [Nat.and_assoc, Nat.and_self]
    rw [hidem]
    have h8_d : (8 <<< (d + 1)) = h := by
      dsimp [h]; simp [Nat.shiftLeft_eq, pow_succ]; ring
    have h8_d2 : (8 <<< (d + 2)) = 16 <<< (d + 1) := by
      simp [Nat.shiftLeft_eq, pow_succ]; ring
    rw [← h8_d, fastSetCount_mask_eq (d + 1) x, ← h8_d2, fastSetCount_mask_eq (d + 2) x,
      fastSetCount_mask_eq (d + 1) (x >>> (8 <<< (d + 1)))]
    have h2 : (8 <<< (d + 2)) = (8 <<< (d + 1)) + (8 <<< (d + 1)) := by
      simp [Nat.shiftLeft_eq, pow_succ]; ring
    rw [h2, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem swarPop8192_eq_fastSetCount10 (x : ℕ) :
    swarPop8192 swarMask0 swarMask1 swarMask2 swarMask3 x =
      fastSetCount 10 (x &&& ((1 <<< 8192) - 1)) :=
  swar16_fold_eq_fastSetCount 9 (by decide) x

end
end Sude
