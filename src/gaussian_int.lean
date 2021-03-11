import data.zsqrtd.gaussian_int

open zsqrtd complex gaussian_int

local notation `ℤ[i]` := gaussian_int

lemma to_complex_div_re' (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round ((x / y : ℂ).re) :=
begin
  rw [div_def, ← @rat.cast_round ℝ _ _, to_complex_re],
  apply congr_arg,
  simp only [mul_assoc, div_eq_mul_inv, add_mul, neg_mul_eq_neg_mul_symm, nat_cast_real_norm,
    to_real_re, int.cast_add, zsqrtd.mul_re,
    one_mul, zsqrtd.conj_re, rat.cast_inv, to_real_im, int.cast_mul, rat.cast_add, rat.cast_coe_int, inv_re,
    mul_neg_eq_neg_mul_symm, inv_im, rat.cast_mul, complex.mul_re, neg_neg, zsqrtd.conj_im, sub_neg_eq_add],
end

@[simp] lemma to_complex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 :=
by rw [← to_complex_zero, to_complex_inj]

@[simp] lemma nat_cast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = (x : ℂ).norm_sq :=
by rw [norm, norm_sq]; simp only [neg_mul_eq_neg_mul_symm, to_real_re, int.cast_add, one_mul, to_real_im, int.cast_mul, sub_neg_eq_add]

@[simp] lemma nat_cast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = (x : ℂ).norm_sq :=
by cases x; rw [norm, norm_sq]; simp only [neg_mul_eq_neg_mul_symm, int.cast_add, one_mul, of_real_add, int.cast_mul, to_complex_re, of_real_int_cast,
 of_real_mul, sub_neg_eq_add, to_complex_im]

lemma norm_mod_lt' (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
have (y : ℂ) ≠ 0, by rwa [ne.def, ← to_complex_zero, to_complex_inj],
(@int.cast_lt ℝ _ _ _).1 $
  calc ↑(norm (x % y)) = (x - y * (x / y : ℤ[i]) : ℂ).norm_sq
      : by simp only [mod_def, nat_cast_real_norm, to_complex_sub, to_complex_mul]
  ... = (y : ℂ).norm_sq * (((x / y) - (x / y : ℤ[i])) : ℂ).norm_sq :
    by rw [← norm_sq_mul, mul_sub, mul_div_cancel' _ this]
  ... < (y : ℂ).norm_sq * 1 : mul_lt_mul_of_pos_left (norm_sq_div_sub_div_lt_one _ _)
    (norm_sq_pos.2 this)
  ... = norm y : by simp
