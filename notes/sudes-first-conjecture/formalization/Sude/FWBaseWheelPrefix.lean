import Sude.FWAffineWheelExtension

/-! Exact finite prefix checks for the first FW wheel, with an explicit
kernel-checked carry. No source discrepancy inference is claimed here. -/
namespace Sude

def fwBaseWheelPrefix (n : ℕ) : ℕ :=
  Nat.count (fun x : ℕ => Nat.Coprime 15015 (x + 1)) n

def fwBasePrefixBounds (n c : ℕ) : Prop :=
  5760 * n ≤ 15015 * c + 47505 ∧ 15015 * c ≤ 5760 * n + 53265

instance (n c : ℕ) : Decidable (fwBasePrefixBounds n c) := by
  unfold fwBasePrefixBounds
  infer_instance

def fwBasePrefixCheck (n c : ℕ) : ℕ → ℕ → Prop
  | 0, expected => fwBasePrefixBounds n c ∧ c = expected
  | fuel + 1, expected => fwBasePrefixBounds n c ∧
      fwBasePrefixCheck (n + 1)
        (c + if Nat.Coprime 15015 (n + 1) then 1 else 0) fuel expected

instance (n c fuel expected : ℕ) : Decidable (fwBasePrefixCheck n c fuel expected) := by
  induction fuel generalizing n c with
  | zero => change Decidable (fwBasePrefixBounds n c ∧ c = expected); infer_instance
  | succ fuel ih =>
    change Decidable (fwBasePrefixBounds n c ∧ fwBasePrefixCheck (n + 1)
      (c + if Nat.Coprime 15015 (n + 1) then 1 else 0) fuel expected)
    exact @instDecidableAnd _ _ _ (ih _ _)

theorem fw_base_prefix_check_sound (n c fuel expected : ℕ)
    (hc : fwBaseWheelPrefix n = c) (hcheck : fwBasePrefixCheck n c fuel expected) :
    fwBaseWheelPrefix (n + fuel) = expected ∧
      ∀ t ≤ fuel, fwBasePrefixBounds (n + t) (fwBaseWheelPrefix (n + t)) := by
  induction fuel generalizing n c with
  | zero =>
    constructor
    · simpa [hc, fwBasePrefixCheck] using hcheck.2
    · intro t ht
      have : t = 0 := by omega
      subst t
      simpa [hc, fwBasePrefixCheck] using hcheck.1
  | succ fuel ih =>
    have hnext : fwBaseWheelPrefix (n + 1) =
        c + if Nat.Coprime 15015 (n + 1) then 1 else 0 := by
      unfold fwBaseWheelPrefix at hc ⊢
      rw [Nat.count_succ, hc]
    have h := ih (n + 1) _ hnext hcheck.2
    constructor
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
    · intro t ht
      cases t with
      | zero => simpa [hc, fwBasePrefixCheck] using hcheck.1
      | succ t =>
        have h' := h.2 t (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_00 : fwBasePrefixCheck 0 0 500 192 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_01 : fwBasePrefixCheck 500 192 500 382 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_02 : fwBasePrefixCheck 1000 382 500 575 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_03 : fwBasePrefixCheck 1500 575 500 766 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_04 : fwBasePrefixCheck 2000 766 500 959 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_05 : fwBasePrefixCheck 2500 959 500 1150 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_06 : fwBasePrefixCheck 3000 1150 500 1342 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_07 : fwBasePrefixCheck 3500 1342 500 1532 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_08 : fwBasePrefixCheck 4000 1532 500 1726 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_09 : fwBasePrefixCheck 4500 1726 500 1918 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_10 : fwBasePrefixCheck 5000 1918 500 2109 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_11 : fwBasePrefixCheck 5500 2109 500 2301 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_12 : fwBasePrefixCheck 6000 2301 500 2494 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_13 : fwBasePrefixCheck 6500 2494 500 2686 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_14 : fwBasePrefixCheck 7000 2686 500 2879 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_15 : fwBasePrefixCheck 7500 2879 500 3067 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_16 : fwBasePrefixCheck 8000 3067 500 3260 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_17 : fwBasePrefixCheck 8500 3260 500 3452 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_18 : fwBasePrefixCheck 9000 3452 500 3645 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_19 : fwBasePrefixCheck 9500 3645 500 3835 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_20 : fwBasePrefixCheck 10000 3835 500 4029 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_21 : fwBasePrefixCheck 10500 4029 500 4221 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_22 : fwBasePrefixCheck 11000 4221 500 4412 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_23 : fwBasePrefixCheck 11500 4412 500 4603 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_24 : fwBasePrefixCheck 12000 4603 500 4796 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_25 : fwBasePrefixCheck 12500 4796 500 4988 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_26 : fwBasePrefixCheck 13000 4988 500 5179 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_27 : fwBasePrefixCheck 13500 5179 500 5372 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_28 : fwBasePrefixCheck 14000 5372 500 5562 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_29 : fwBasePrefixCheck 14500 5562 500 5756 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fw_base_prefix_chunk_30 : fwBasePrefixCheck 15000 5756 15 5760 := by decide +kernel

theorem fw_base_prefix_full_certificate :
    fwBaseWheelPrefix 15015 = 5760 ∧
      ∀ r ≤ 15015, fwBasePrefixBounds r (fwBaseWheelPrefix r) := by
  have h00 := fw_base_prefix_check_sound 0 0 500 192 rfl fw_base_prefix_chunk_00
  have h01 := fw_base_prefix_check_sound 500 192 500 382 (by simpa using h00.1) fw_base_prefix_chunk_01
  have h02 := fw_base_prefix_check_sound 1000 382 500 575 (by simpa using h01.1) fw_base_prefix_chunk_02
  have h03 := fw_base_prefix_check_sound 1500 575 500 766 (by simpa using h02.1) fw_base_prefix_chunk_03
  have h04 := fw_base_prefix_check_sound 2000 766 500 959 (by simpa using h03.1) fw_base_prefix_chunk_04
  have h05 := fw_base_prefix_check_sound 2500 959 500 1150 (by simpa using h04.1) fw_base_prefix_chunk_05
  have h06 := fw_base_prefix_check_sound 3000 1150 500 1342 (by simpa using h05.1) fw_base_prefix_chunk_06
  have h07 := fw_base_prefix_check_sound 3500 1342 500 1532 (by simpa using h06.1) fw_base_prefix_chunk_07
  have h08 := fw_base_prefix_check_sound 4000 1532 500 1726 (by simpa using h07.1) fw_base_prefix_chunk_08
  have h09 := fw_base_prefix_check_sound 4500 1726 500 1918 (by simpa using h08.1) fw_base_prefix_chunk_09
  have h10 := fw_base_prefix_check_sound 5000 1918 500 2109 (by simpa using h09.1) fw_base_prefix_chunk_10
  have h11 := fw_base_prefix_check_sound 5500 2109 500 2301 (by simpa using h10.1) fw_base_prefix_chunk_11
  have h12 := fw_base_prefix_check_sound 6000 2301 500 2494 (by simpa using h11.1) fw_base_prefix_chunk_12
  have h13 := fw_base_prefix_check_sound 6500 2494 500 2686 (by simpa using h12.1) fw_base_prefix_chunk_13
  have h14 := fw_base_prefix_check_sound 7000 2686 500 2879 (by simpa using h13.1) fw_base_prefix_chunk_14
  have h15 := fw_base_prefix_check_sound 7500 2879 500 3067 (by simpa using h14.1) fw_base_prefix_chunk_15
  have h16 := fw_base_prefix_check_sound 8000 3067 500 3260 (by simpa using h15.1) fw_base_prefix_chunk_16
  have h17 := fw_base_prefix_check_sound 8500 3260 500 3452 (by simpa using h16.1) fw_base_prefix_chunk_17
  have h18 := fw_base_prefix_check_sound 9000 3452 500 3645 (by simpa using h17.1) fw_base_prefix_chunk_18
  have h19 := fw_base_prefix_check_sound 9500 3645 500 3835 (by simpa using h18.1) fw_base_prefix_chunk_19
  have h20 := fw_base_prefix_check_sound 10000 3835 500 4029 (by simpa using h19.1) fw_base_prefix_chunk_20
  have h21 := fw_base_prefix_check_sound 10500 4029 500 4221 (by simpa using h20.1) fw_base_prefix_chunk_21
  have h22 := fw_base_prefix_check_sound 11000 4221 500 4412 (by simpa using h21.1) fw_base_prefix_chunk_22
  have h23 := fw_base_prefix_check_sound 11500 4412 500 4603 (by simpa using h22.1) fw_base_prefix_chunk_23
  have h24 := fw_base_prefix_check_sound 12000 4603 500 4796 (by simpa using h23.1) fw_base_prefix_chunk_24
  have h25 := fw_base_prefix_check_sound 12500 4796 500 4988 (by simpa using h24.1) fw_base_prefix_chunk_25
  have h26 := fw_base_prefix_check_sound 13000 4988 500 5179 (by simpa using h25.1) fw_base_prefix_chunk_26
  have h27 := fw_base_prefix_check_sound 13500 5179 500 5372 (by simpa using h26.1) fw_base_prefix_chunk_27
  have h28 := fw_base_prefix_check_sound 14000 5372 500 5562 (by simpa using h27.1) fw_base_prefix_chunk_28
  have h29 := fw_base_prefix_check_sound 14500 5562 500 5756 (by simpa using h28.1) fw_base_prefix_chunk_29
  have h30 := fw_base_prefix_check_sound 15000 5756 15 5760 (by simpa using h29.1) fw_base_prefix_chunk_30
  constructor
  · simpa using h30.1
  · intro r hr
    have hcases : r ≤ 500 ∨ (500 ≤ r ∧ r ≤ 1000) ∨ (1000 ≤ r ∧ r ≤ 1500) ∨ (1500 ≤ r ∧ r ≤ 2000) ∨ (2000 ≤ r ∧ r ≤ 2500) ∨ (2500 ≤ r ∧ r ≤ 3000) ∨ (3000 ≤ r ∧ r ≤ 3500) ∨ (3500 ≤ r ∧ r ≤ 4000) ∨ (4000 ≤ r ∧ r ≤ 4500) ∨ (4500 ≤ r ∧ r ≤ 5000) ∨ (5000 ≤ r ∧ r ≤ 5500) ∨ (5500 ≤ r ∧ r ≤ 6000) ∨ (6000 ≤ r ∧ r ≤ 6500) ∨ (6500 ≤ r ∧ r ≤ 7000) ∨ (7000 ≤ r ∧ r ≤ 7500) ∨ (7500 ≤ r ∧ r ≤ 8000) ∨ (8000 ≤ r ∧ r ≤ 8500) ∨ (8500 ≤ r ∧ r ≤ 9000) ∨ (9000 ≤ r ∧ r ≤ 9500) ∨ (9500 ≤ r ∧ r ≤ 10000) ∨ (10000 ≤ r ∧ r ≤ 10500) ∨ (10500 ≤ r ∧ r ≤ 11000) ∨ (11000 ≤ r ∧ r ≤ 11500) ∨ (11500 ≤ r ∧ r ≤ 12000) ∨ (12000 ≤ r ∧ r ≤ 12500) ∨ (12500 ≤ r ∧ r ≤ 13000) ∨ (13000 ≤ r ∧ r ≤ 13500) ∨ (13500 ≤ r ∧ r ≤ 14000) ∨ (14000 ≤ r ∧ r ≤ 14500) ∨ (14500 ≤ r ∧ r ≤ 15000) ∨ (15000 ≤ r ∧ r ≤ 15015) := by omega
    rcases hcases with hc00 | hc01 | hc02 | hc03 | hc04 | hc05 | hc06 | hc07 | hc08 | hc09 | hc10 | hc11 | hc12 | hc13 | hc14 | hc15 | hc16 | hc17 | hc18 | hc19 | hc20 | hc21 | hc22 | hc23 | hc24 | hc25 | hc26 | hc27 | hc28 | hc29 | hc30
    · simpa using h00.2 r (by omega)
    · have h := h01.2 (r - 500) (by omega)
      have heq : 500 + (r - 500) = r := by omega
      simpa [heq] using h
    · have h := h02.2 (r - 1000) (by omega)
      have heq : 1000 + (r - 1000) = r := by omega
      simpa [heq] using h
    · have h := h03.2 (r - 1500) (by omega)
      have heq : 1500 + (r - 1500) = r := by omega
      simpa [heq] using h
    · have h := h04.2 (r - 2000) (by omega)
      have heq : 2000 + (r - 2000) = r := by omega
      simpa [heq] using h
    · have h := h05.2 (r - 2500) (by omega)
      have heq : 2500 + (r - 2500) = r := by omega
      simpa [heq] using h
    · have h := h06.2 (r - 3000) (by omega)
      have heq : 3000 + (r - 3000) = r := by omega
      simpa [heq] using h
    · have h := h07.2 (r - 3500) (by omega)
      have heq : 3500 + (r - 3500) = r := by omega
      simpa [heq] using h
    · have h := h08.2 (r - 4000) (by omega)
      have heq : 4000 + (r - 4000) = r := by omega
      simpa [heq] using h
    · have h := h09.2 (r - 4500) (by omega)
      have heq : 4500 + (r - 4500) = r := by omega
      simpa [heq] using h
    · have h := h10.2 (r - 5000) (by omega)
      have heq : 5000 + (r - 5000) = r := by omega
      simpa [heq] using h
    · have h := h11.2 (r - 5500) (by omega)
      have heq : 5500 + (r - 5500) = r := by omega
      simpa [heq] using h
    · have h := h12.2 (r - 6000) (by omega)
      have heq : 6000 + (r - 6000) = r := by omega
      simpa [heq] using h
    · have h := h13.2 (r - 6500) (by omega)
      have heq : 6500 + (r - 6500) = r := by omega
      simpa [heq] using h
    · have h := h14.2 (r - 7000) (by omega)
      have heq : 7000 + (r - 7000) = r := by omega
      simpa [heq] using h
    · have h := h15.2 (r - 7500) (by omega)
      have heq : 7500 + (r - 7500) = r := by omega
      simpa [heq] using h
    · have h := h16.2 (r - 8000) (by omega)
      have heq : 8000 + (r - 8000) = r := by omega
      simpa [heq] using h
    · have h := h17.2 (r - 8500) (by omega)
      have heq : 8500 + (r - 8500) = r := by omega
      simpa [heq] using h
    · have h := h18.2 (r - 9000) (by omega)
      have heq : 9000 + (r - 9000) = r := by omega
      simpa [heq] using h
    · have h := h19.2 (r - 9500) (by omega)
      have heq : 9500 + (r - 9500) = r := by omega
      simpa [heq] using h
    · have h := h20.2 (r - 10000) (by omega)
      have heq : 10000 + (r - 10000) = r := by omega
      simpa [heq] using h
    · have h := h21.2 (r - 10500) (by omega)
      have heq : 10500 + (r - 10500) = r := by omega
      simpa [heq] using h
    · have h := h22.2 (r - 11000) (by omega)
      have heq : 11000 + (r - 11000) = r := by omega
      simpa [heq] using h
    · have h := h23.2 (r - 11500) (by omega)
      have heq : 11500 + (r - 11500) = r := by omega
      simpa [heq] using h
    · have h := h24.2 (r - 12000) (by omega)
      have heq : 12000 + (r - 12000) = r := by omega
      simpa [heq] using h
    · have h := h25.2 (r - 12500) (by omega)
      have heq : 12500 + (r - 12500) = r := by omega
      simpa [heq] using h
    · have h := h26.2 (r - 13000) (by omega)
      have heq : 13000 + (r - 13000) = r := by omega
      simpa [heq] using h
    · have h := h27.2 (r - 13500) (by omega)
      have heq : 13500 + (r - 13500) = r := by omega
      simpa [heq] using h
    · have h := h28.2 (r - 14000) (by omega)
      have heq : 14000 + (r - 14000) = r := by omega
      simpa [heq] using h
    · have h := h29.2 (r - 14500) (by omega)
      have heq : 14500 + (r - 14500) = r := by omega
      simpa [heq] using h
    · have h := h30.2 (r - 15000) (by omega)
      have heq : 15000 + (r - 15000) = r := by omega
      simpa [heq] using h

end Sude
