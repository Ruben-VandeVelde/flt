import data.zsqrtd.basic
import ring_theory.int.basic
import .primes -- int.is_unit_iff_nat_abs

@[simp]
lemma zsqrtd.conj_zero {d : ℤ} : zsqrtd.conj (0 : ℤ√d) = 0 :=
begin
  rw zsqrtd.ext,
  simp only [zsqrtd.conj_re, zsqrtd.zero_im, and_self, zsqrtd.zero_re, neg_zero, zsqrtd.conj_im],
end

@[simp]
lemma zsqrtd.conj_one {d : ℤ} : zsqrtd.conj (1 : ℤ√d) = 1 :=
begin
  rw zsqrtd.ext,
  simp only [zsqrtd.conj_re, zsqrtd.one_im, eq_self_iff_true, and_self, neg_zero, zsqrtd.conj_im]
end

@[simp]
lemma zsqrtd.conj_neg {d : ℤ} (x : ℤ√d) : (-x).conj = -x.conj :=
begin
  rw zsqrtd.ext,
  simp only [zsqrtd.conj_re, eq_self_iff_true, zsqrtd.neg_im, zsqrtd.neg_re, and_self, zsqrtd.conj_im],
end

@[simp]
lemma zsqrtd.conj_conj {d : ℤ} (x : ℤ√d) : x.conj.conj = x :=
by simp only [zsqrtd.ext, true_and, zsqrtd.conj_re, eq_self_iff_true, neg_neg, zsqrtd.conj_im]

@[simp]
lemma zsqrtd.norm_neg {d : ℤ} (x : ℤ√d) : (-x).norm = x.norm :=
begin
  apply zsqrtd.coe_int_inj,
  rw [zsqrtd.norm_eq_mul_conj, zsqrtd.norm_eq_mul_conj, zsqrtd.conj_neg],
  simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg],
end

@[simp]
lemma zsqrtd.norm_conj {d : ℤ} (x : ℤ√d) : x.conj.norm = x.norm :=
begin
  apply zsqrtd.coe_int_inj,
  rw [zsqrtd.norm_eq_mul_conj, zsqrtd.norm_eq_mul_conj, zsqrtd.conj_conj, mul_comm],
end

lemma zsqrtd.is_unit_iff_norm_is_unit {d : ℤ} (z : ℤ√d) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs, zsqrtd.norm_eq_one_iff]

lemma zsqrtd.mul_def {d x y x' y' : ℤ} : (⟨x, y⟩ :  ℤ√d) * ⟨x', y'⟩ = ⟨x * x' + d * y * y', x * y' + y * x'⟩ := rfl
