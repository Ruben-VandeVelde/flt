import data.zsqrtd.basic

section
variables {d : ℤ}
namespace zsqrtd
/-- `norm` as an `add_monoid_hom`. -/
def norm_hom : ℤ√d →* ℤ :=
{ to_fun := norm,
  map_mul' := norm_mul,
  map_one' := norm_one }
end zsqrtd
end

lemma zsqrtd.is_unit_iff_norm_is_unit {d : ℤ} (z : ℤ√d) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs_eq, zsqrtd.norm_eq_one_iff]

lemma zsqrtd.int_dvd_iff {d : ℤ} (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im :=
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

lemma zsqrtd.norm_eq_one_iff' {d : ℤ} (hd : d ≤ 0) (z : ℤ√d) : z.norm = 1 ↔ is_unit z :=
by rw [←zsqrtd.norm_eq_one_iff, ←int.coe_nat_inj', int.nat_abs_of_nonneg (zsqrtd.norm_nonneg hd z),
  int.coe_nat_one]

lemma zsqrtd.norm_eq_of_associated {d : ℤ} (hd : d ≤ 0) {x y : ℤ√d} (h : associated x y) :
  x.norm = y.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  rw [zsqrtd.norm_mul, (zsqrtd.norm_eq_one_iff' hd _).mpr u.is_unit, mul_one],
end
