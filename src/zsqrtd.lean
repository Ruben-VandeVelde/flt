import data.zsqrtd.basic

lemma zsqrtd.coe_int_dvd_iff {d : ℤ} (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im :=
begin
  split,
  { rintro ⟨x, rfl⟩,
    simp only [add_zero, zsqrtd.coe_int_re, zero_mul, zsqrtd.mul_im, dvd_mul_right, and_self,
      zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] },
  { rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩,
    use ⟨r, i⟩,
    rw [zsqrtd.ext, zsqrtd.smul_val],
    exact ⟨hr, hi⟩ },
end
