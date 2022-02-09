import number_theory.zsqrtd.basic
import ring_theory.int.basic

lemma zsqrtd.coe_int_norm {d : ℤ} (z : ℤ) : (z : ℤ√d).norm = z * z :=
by rw [zsqrtd.norm_def, zsqrtd.coe_int_re, zsqrtd.coe_int_im, mul_zero, sub_zero]

@[simp, norm_cast]
lemma zsqrtd.coe_int_dvd_coe_int {d : ℤ} (a b : ℤ) : (a : ℤ√d) ∣ b ↔ a ∣ b :=
begin
  split; rintro ⟨c, hc⟩,
  { simp only [zsqrtd.ext, add_zero, zsqrtd.coe_int_re, zero_mul, zsqrtd.mul_im, zsqrtd.mul_re,
      zero_eq_mul, mul_zero, zsqrtd.coe_int_im] at hc,
    obtain ⟨rfl, (rfl|h2)⟩ := hc;
    exact dvd_mul_right _ _ },
  { simp only [hc, int.cast_mul, dvd_mul_right] },
end

lemma zsqrtd.smul_re {d a : ℤ} {b : ℤ√d} : (↑a * b).re = a * b.re := by simp
lemma zsqrtd.smul_im {d a : ℤ} {b : ℤ√d} : (↑a * b).im = a * b.im := by simp

protected lemma zsqrtd.eq_of_smul_eq_smul_left {d a : ℤ} {b c : ℤ√d}
  (ha : a ≠ 0) (h : ↑a * b = a * c) : b = c :=
begin
  rw zsqrtd.ext at h ⊢,
  apply and.imp _ _ h;
  { simp only [zsqrtd.smul_re, zsqrtd.smul_im],
    exact int.eq_of_mul_eq_mul_left ha },
end

lemma zsqrtd.gcd_eq_zero_iff {d : ℤ} (a : ℤ√d) : int.gcd a.re a.im = 0 ↔ a = 0 :=
by simp only [int.gcd_eq_zero_iff, zsqrtd.ext, eq_self_iff_true, zsqrtd.zero_im, zsqrtd.zero_re]

lemma zsqrtd.gcd_pos_iff {d : ℤ} (a : ℤ√d) : 0 < int.gcd a.re a.im ↔ a ≠ 0 :=
pos_iff_ne_zero.trans $ not_congr a.gcd_eq_zero_iff

lemma zsqrtd.coprime_of_dvd_coprime
  {d : ℤ}
  {a b : ℤ√d}
  (hcoprime : is_coprime a.re a.im)
  (hdvd : b ∣ a) :
  is_coprime b.re b.im :=
begin
  apply is_coprime_of_dvd,
  { rintro ⟨hre, him⟩,
    obtain rfl : b = 0,
    { simp only [zsqrtd.ext, hre, eq_self_iff_true, zsqrtd.zero_im, him, and_self, zsqrtd.zero_re] },
    rw zero_dvd_iff at hdvd,
    simpa only [hdvd, zsqrtd.zero_im, zsqrtd.zero_re, not_coprime_zero_zero] using hcoprime },
  { intros z hz hznezero hzdvdu hzdvdv,
    apply hz,
    obtain ⟨ha, hb⟩ : z ∣ a.re ∧ z ∣ a.im,
    { rw ←zsqrtd.coe_int_dvd_iff,
      apply dvd_trans _ hdvd,
      rw zsqrtd.coe_int_dvd_iff,
      exact ⟨hzdvdu, hzdvdv⟩ },
    exact hcoprime.is_unit_of_dvd' ha hb },
end

lemma zsqrtd.exists_coprime_of_gcd_pos {d : ℤ} {a : ℤ√d} (hgcd : 0 < int.gcd a.re a.im) :
  ∃ b : ℤ√d, a = ((int.gcd a.re a.im : ℤ) : ℤ√d) * b ∧ is_coprime b.re b.im :=
begin
  obtain ⟨re, im, H1, Hre, Him⟩ := int.exists_gcd_one hgcd,
  rw [mul_comm] at Hre Him,
  refine ⟨⟨re, im⟩, _, _⟩,
  { rw [zsqrtd.smul_val, zsqrtd.ext, ←Hre, ←Him], split; refl },
  { rw [←int.gcd_eq_one_iff_coprime, H1] }
end
