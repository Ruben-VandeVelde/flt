import data.int.basic
import data.int.parity
import data.nat.gcd
import data.nat.parity
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid
import tactic
import data.nat.modeq
import data.complex.is_R_or_C
import data.complex.exponential
import data.zsqrtd.basic
import data.zsqrtd.gaussian_int

open zsqrtd complex

noncomputable theory

--example : real.sqrt 3 * real.sqrt 3 = 3:= real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 3)

def to_complex : ℤ√-3 →+* ℂ :=
begin
  refine_struct { to_fun := λ x : ℤ√-3, (x.re + x.im * real.sqrt 3 * complex.I : ℂ), .. };
  intros; apply complex.ext;
  simp only [add_zero, int.cast_zero, zero_mul, zsqrtd.zero_re, zsqrtd.zero_im, int.cast_one,
    zsqrtd.one_im, zsqrtd.one_re, zsqrtd.add_re, zsqrtd.mul_re, complex.I_re],
  { simp only [neg_mul_eq_neg_mul_symm, complex.one_re, complex.bit1_re, complex.add_im,
      complex.neg_re, add_zero, mul_one, int.cast_add, complex.mul_re, int.cast_bit1, int.cast_mul,
      zero_mul, complex.of_real_re, complex.add_re, int.cast_one, complex.int_cast_re, sub_zero,
      complex.of_real_im, complex.I_im, zero_add, complex.int_cast_im, complex.I_re, int.cast_neg,
      zsqrtd.mul_re, complex.mul_im, mul_zero],
    rw [←real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)] {occs := occurrences.pos [1]},
    ring },
  { simp only [complex.add_im, bit0_zero, complex.bit1_im, complex.neg_im, add_zero, mul_one,
      int.cast_add, complex.mul_re, int.cast_mul, zero_mul, complex.of_real_re, complex.add_re,
      complex.int_cast_re, sub_zero, zsqrtd.mul_im, complex.of_real_im, complex.I_im, zero_add,
      complex.int_cast_im, complex.I_re, complex.mul_im, mul_zero],
    ring },
  { simp only [complex.add_im, add_zero, int.cast_add, complex.mul_re, zero_mul, complex.add_re,
      sub_zero, zsqrtd.add_re, complex.of_real_im, complex.int_cast_im, complex.I_re,
      complex.mul_im, mul_zero] },
  { simp only [complex.add_im, add_zero, mul_one, int.cast_add, complex.mul_re, complex.of_real_re,
      complex.add_re, complex.int_cast_re, sub_zero, zsqrtd.add_im, complex.of_real_im,
      complex.I_im, zero_add, complex.int_cast_im, complex.I_re, complex.mul_im, mul_zero],
    ring },
end

instance zsqrtdneg3 : has_coe (ℤ√-3) ℂ := ⟨to_complex⟩

lemma to_complex_def (x : ℤ√-3) : (x : ℂ) = x.re + x.im * real.sqrt 3 * I := rfl

lemma to_complex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ√-3) : ℂ) = x + y * real.sqrt 3 * I := by simp [to_complex_def]

lemma to_complex_def₂ (x : ℤ√-3) : (x : ℂ) = ⟨x.re, x.im * real.sqrt 3⟩ :=
by { apply complex.ext; simp [to_complex_def] }

@[simp] lemma to_real_re (x : ℤ√-3) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [to_complex_def]
@[simp] lemma to_real_im (x : ℤ√-3) : ((x.im : ℤ) : ℝ) * real.sqrt 3 = (x : ℂ).im := by simp [to_complex_def]
@[simp] lemma to_complex_re (x y : ℤ) : ((⟨x, y⟩ : ℤ√-3) : ℂ).re = x := by simp [to_complex_def]
--@[simp] lemma to_complex_im (x y : ℤ) : ((⟨x, y⟩ : ℤ√-3) : ℂ).im = y * real.sqrt 3 := by simp [to_complex_def]
@[simp] lemma to_complex_im' (x : ℤ√-3) : (x : ℂ).im = x.2 * real.sqrt 3 := begin
  simp only [to_complex_def],
  simp,
end
@[simp] lemma to_complex_add (x y : ℤ√-3) : ((x + y : ℤ√-3) : ℂ) = x + y := to_complex.map_add _ _
@[simp] lemma to_complex_mul (x y : ℤ√-3) : ((x * y : ℤ√-3) : ℂ) = x * y := to_complex.map_mul _ _
@[simp] lemma to_complex_one : ((1 : ℤ√-3) : ℂ) = 1 := to_complex.map_one
@[simp] lemma to_complex_zero : ((0 : ℤ√-3) : ℂ) = 0 := to_complex.map_zero
@[simp] lemma to_complex_neg (x : ℤ√-3) : ((-x : ℤ√-3) : ℂ) = -x := to_complex.map_neg _
@[simp] lemma to_complex_sub (x y : ℤ√-3) : ((x - y : ℤ√-3) : ℂ) = x - y := to_complex.map_sub _ _

@[simp] lemma to_complex_inj {x y : ℤ√-3} : (x : ℂ) = y ↔ x = y :=
begin
  have : real.sqrt 3 ≠ 0, { norm_num },
  cases x; cases y; simp [to_complex_def₂, this],
end

@[simp] lemma to_complex_eq_zero {x : ℤ√-3} : (x : ℂ) = 0 ↔ x = 0 :=
by rw [← to_complex_zero, to_complex_inj]

--def norm (n : ℤ√d) : ℤ := n.re * n.re - d * n.im * n.im

@[simp] lemma nat_cast_real_norm (x : ℤ√-3) : (x.norm : ℝ) = (x : ℂ).norm_sq :=
begin
  rw [zsqrtd.norm, to_complex_def, norm_sq],
  dsimp,
  simp_rw [mul_zero, mul_one, zero_add, zero_sub, sub_zero, add_zero, ←pow_two],
  norm_cast,
  simp_rw [zero_mul, neg_zero, zero_add, add_zero, mul_pow],
  rw real.sqr_sqrt zero_lt_three.le,
  norm_cast,
  ring,
end

@[simp] lemma nat_cast_complex_norm (x : ℤ√-3) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by rw [←nat_cast_real_norm, of_real_int_cast]

protected def div (x y : ℤ√-3) : ℤ√-3 :=
let n := (3 * rat.of_int (norm y))⁻¹ in let c := y.conj in
⟨3 * round (rat.of_int (x * c).re * n : ℚ),
 round (rat.of_int (x * c).im * n : ℚ)⟩

instance : has_div ℤ√-3 := ⟨div⟩

lemma div_def (x y : ℤ√-3) : x / y = ⟨round ((x * conj y).re / norm y : ℚ),
  round ((x * conj y).im / (3 * norm y) : ℚ)⟩ :=
--show zsqrtd.mk _ _ = _, by simp [rat.of_int_eq_mk, rat.mk_eq_div, div_eq_mul_inv]
sorry
lemma to_complex_div_re (x y : ℤ√-3) : ((x / y : ℤ√-3) : ℂ).re = round ((x / y : ℂ).re) :=
begin
  rw [div_def, ← @rat.cast_round ℝ _ _, to_complex_re],
  apply congr_arg,
  simp only [mul_assoc, div_eq_mul_inv, add_mul, neg_mul_eq_neg_mul_symm, nat_cast_real_norm,
    to_real_re, int.cast_add, zsqrtd.mul_re,
    one_mul, zsqrtd.conj_re, rat.cast_inv, to_real_im, int.cast_mul, rat.cast_add, rat.cast_coe_int, inv_re,
    mul_neg_eq_neg_mul_symm, inv_im, rat.cast_mul, complex.mul_re, neg_neg, zsqrtd.conj_im, sub_neg_eq_add],
--    simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul],
  apply congr_arg,
  congr' 1,
end

lemma to_complex_div_im (x y : ℤ√-3) : ((x / y : ℤ√-3) : ℂ).im = round ((x / y : ℂ).im) :=
by rw [div_def, ← @rat.cast_round ℝ _ _, ← @rat.cast_round ℝ _ _];
  simp [-rat.cast_round, mul_assoc, div_eq_mul_inv, mul_add, add_mul]

local notation `abs'` := _root_.abs

lemma norm_sq_le_norm_sq_of_re_le_of_im_le {x y : ℂ} (hre : abs' x.re ≤ abs' y.re)
  (him : abs' x.im ≤ abs' y.im) : x.norm_sq ≤ y.norm_sq :=
by rw [norm_sq_apply, norm_sq_apply, ← _root_.abs_mul_self, _root_.abs_mul,
  ← _root_.abs_mul_self y.re, _root_.abs_mul y.re,
  ← _root_.abs_mul_self x.im, _root_.abs_mul x.im,
  ← _root_.abs_mul_self y.im, _root_.abs_mul y.im]; exact
(add_le_add (mul_self_le_mul_self (abs_nonneg _) hre)
  (mul_self_le_mul_self (abs_nonneg _) him))

lemma norm_sq_div_sub_div_lt_one' (x y : ℤ√-3) :
((x / y : ℂ) - ((x / y : ℤ√-3) : ℂ)).norm_sq =
    ((x / y : ℂ).re - ((x / y : ℤ√-3) : ℂ).re +
    ((x / y : ℂ).im - ((x / y : ℤ√-3) : ℂ).im) * I : ℂ).norm_sq :=
begin
  apply congr_arg,
  ext,
  { simp_rw [sub_re, complex.add_re, complex.mul_re, I_re, I_im, mul_zero, mul_one, zero_sub],
    simp_rw [sub_re, of_real_re, sub_im, of_real_im, sub_zero, neg_zero, add_zero] },
  { simp_rw [sub_im, complex.add_im, sub_im, of_real_im, complex.mul_im, I_im, I_re, mul_zero],
    simp_rw [add_zero, mul_one, sub_zero, zero_add, sub_re, of_real_re] },
end

lemma norm_sq_div_sub_div_lt_one (x y : ℤ√-3) :
  ((x / y : ℂ) - ((x / y : ℤ√-3) : ℂ)).norm_sq < 1 :=
calc ((x / y : ℂ) - ((x / y : ℤ√-3) : ℂ)).norm_sq =
    ((x / y : ℂ).re - ((x / y : ℤ√-3) : ℂ).re +
    ((x / y : ℂ).im - ((x / y : ℤ√-3) : ℂ).im) * I : ℂ).norm_sq :
      begin
        apply congr_arg,
        ext,
        { simp_rw [sub_re, complex.add_re, complex.mul_re, I_re, I_im, mul_zero, mul_one, zero_sub],
          simp_rw [sub_re, of_real_re, sub_im, of_real_im, sub_zero, neg_zero, add_zero] },
        { simp_rw [sub_im, complex.add_im, sub_im, of_real_im, complex.mul_im, I_im, I_re, mul_zero],
          simp_rw [add_zero, mul_one, sub_zero, zero_add, sub_re, of_real_re] },
      end
  ... ≤ (1 / 2 + 1 / 2 * I).norm_sq :
  have abs' (2⁻¹ : ℝ) = 2⁻¹, from _root_.abs_of_nonneg (by norm_num),
  norm_sq_le_norm_sq_of_re_le_of_im_le
    (by rw [to_complex_div_re]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).re)
    (by rw [to_complex_div_im]; simp [norm_sq, this];
      simpa using abs_sub_round (x / y : ℂ).im)
  ... < 1 : by simp [norm_sq]; norm_num

protected def mod (x y : ℤ√-3) : ℤ√-3 := x - y * (x / y)

instance : has_mod ℤ√-3 := ⟨mod⟩

lemma mod_def (x y : ℤ√-3) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : ℤ√-3) {y : ℤ√-3} (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
(@int.cast_lt ℝ _ _ _ _).1 $
  calc (zsqrtd.norm (x % y) : ℝ)
      = (x - y * (x / y : ℤ√-3) : ℂ).norm_sq : by {simp [mod_def],}
  ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ√-3)) : ℂ).norm_sq :
    by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
  ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
    (norm_sq_pos.2 this)
  ... = zsqrtd.norm y : by simp

lemma nat_abs_norm_mod_lt (x : ℤ√-3) {y : ℤ√-3} (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
int.coe_nat_lt.1 (by simp [-int.coe_nat_lt, norm_mod_lt x hy])

instance : euclidean_domain ℤ√-3 :=
{ quotient := (/),
  remainder := (%),
  quotient_zero := λ _, by simp [div_def]; refl,
  quotient_mul_add_remainder_eq := λ _ _, by simp [mod_def],
  r := _,
  r_well_founded := measure_wf (int.nat_abs ∘ norm),
  remainder_lt := nat_abs_norm_mod_lt,
  mul_left_not_lt := λ a b hb0, not_lt_of_ge $ norm_le_norm_mul_left a hb0,
  .. zsqrtd.comm_ring,
  .. zsqrtd.nontrivial }

lemma l1 (x y d : ℕ) (h : x.coprime y) (h' : d ∣ x ^ 2 + y ^ 2) : true :=
sorry

lemma euler'
  (x y u : nat)
  (hparity : even x ↔ ¬even y)
  (h : u ∣ x ^ 2 +  3 * y ^ 2)
  (hu : 1 < u)
  (hcpr : x.coprime y) :
  ∃ a b,
    x = a ^ 3 - 9 * a * b ^ 2 ∧
    y = 3 * a ^ 2 * b - 3 * b ^ 3
  :=
begin
  have : (⟨x, y⟩ : ℤ√-3) * ⟨x, -y⟩ = x ^ 2 + 3 * y ^ 2,
  {
    rw [pow_two, pow_two],
    rw zsqrtd.ext, --ext,
    split; simp; ring,
  },
  sorry
end

lemma l2 (p q u : int) (u ∣ p ^ 2 + 3 * q ^ 2) :
  ∃ a b : int, (a : ℤ√-3) ∣ ⟨p, q⟩ :=
begin
  classical,
  by_contra H,
end

lemma l3 (p q u : int) (h : p ^ 2 + 3 * q ^ 2 = u ^ 3) :
  ∃ t u, 
    p ^ 2 + 3 * q ^ 2 = (t ^ 2 + 3 * u ^ 2) ^ 3 ∧
    p = t ^ 3 - 9 * t * u ∧ 
    q = 3 * t ^ 2 * u - 3 * u ^ 3 :=
begin
  sorry
end