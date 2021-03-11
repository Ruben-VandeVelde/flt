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
import .primes
import .spts
import .multiset
import .zsqrtd

lemma zsqrt3.norm (z : ℤ√-3) : z.norm = z.re ^ 2 + 3 * z.im ^ 2 :=
begin
  dsimp [zsqrtd.norm],
  simp only [neg_mul_eq_neg_mul_symm, sub_neg_eq_add, pow_two, mul_assoc],
end
lemma zsqrt3.norm' (a b : ℤ) : a ^ 2 + 3 * b ^ 2 = (⟨a, b⟩ : ℤ√-3).norm :=
begin
  dsimp [zsqrtd.norm],
  ring,
end

lemma zsqrt3.norm_eq_zero_iff (z : ℤ√-3) : z.norm = 0 ↔ z = 0 :=
begin
    rw zsqrt3.norm,
    rw int.sq_plus_three_sq_eq_zero_iff,
    rw zsqrtd.ext,
    rw zsqrtd.zero_re,
    rw zsqrtd.zero_im,
end

lemma abs_pow_bit1 {R:Type*} [linear_ordered_ring R] (x : R) (n : ℕ) : abs x ^ (bit0 n) = x ^ (bit0 n) :=
begin
  rw [←abs_pow, abs_of_nonneg],
  exact pow_bit0_nonneg _ _,
end

lemma abs_pow_two {R:Type*} [linear_ordered_ring R] (x : R) : abs x ^ 2 = x ^ 2 :=
abs_pow_bit1 x 1

lemma zsqrt3.is_unit_iff {z : ℤ√-3} : is_unit z ↔ abs z.re = 1 ∧ z.im = 0 :=
begin
  rw [←zsqrtd.norm_eq_one_iff, zsqrt3.norm, ←int.coe_nat_inj', int.coe_nat_one],
  rw int.nat_abs_of_nonneg (spts.nonneg _ _),
  refine ⟨spts.eq_one, λ h, _⟩,
  rw [h.2, ←abs_pow_two, h.1],
  norm_num,
end

lemma zsqrt3.coe_of_is_unit {z : ℤ√-3} (h : is_unit z) : ∃ u : units ℤ, z = u :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.is_unit_iff.mp h,
  obtain ⟨v, hv⟩ : is_unit z.re,
  { rwa int.is_unit_iff_abs },
  use v,
  rw [zsqrtd.ext, hu, ←hv],
  simp only [zsqrtd.coe_int_re, and_true, eq_self_iff_true, coe_coe, zsqrtd.coe_int_im],
end

lemma zsqrt3.coe_of_is_unit' {z : ℤ√-3} (h : is_unit z) : ∃ u : ℤ, z = u ∧ abs u = 1 :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.coe_of_is_unit h,
  refine ⟨u, _, _⟩,
  { rw [hu, coe_coe] },
  { exact int.is_unit_iff_abs.mp (is_unit_unit u) },
end

lemma zsqrt3.norm_unit {z : ℤ√-3} (h : is_unit z) : z.norm = 1 :=
begin
  rw zsqrt3.is_unit_iff at h,
  rw [zsqrt3.norm, ←abs_pow_two, ←abs_pow_two, h.1, h.2],
  norm_num,
end

lemma zsqrt3.norm_unit' {z : units ℤ√-3} : (z : ℤ√-3).norm = 1 :=
begin
  have := is_unit_unit z,
  exact zsqrt3.norm_unit this,
end

def odd_prime_or_four (z : ℤ) : Prop :=
  z = 4 ∨ (prime z ∧ odd z)

lemma odd_prime_or_four.ne_zero {z : ℤ} (h : odd_prime_or_four z) : z ≠ 0 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_zero }
end

lemma odd_prime_or_four.not_unit {z : ℤ} (h : odd_prime_or_four z) : ¬ is_unit z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw is_unit_iff_dvd_one, norm_num },
  { exact h.not_unit }
end

lemma step1a
  (a b : ℤ)
  (hcoprime : is_coprime a b)
  (heven : even (a ^ 2 + 3 * b ^ 2)) :
  (odd a) ∧ odd b :=
begin
  have : even a ↔ even b,
  { simpa [two_ne_zero] with parity_simps using heven },
  have : ¬(even a ∧ even b),
  { rintro ⟨ha, hb⟩,
    have := hcoprime.is_unit_of_dvd' ha hb,
    rw is_unit_iff_dvd_one at this,
    norm_num at this },
  rw [int.odd_iff_not_even, int.odd_iff_not_even],
  tauto,
end

lemma step1
  (a b : ℤ)
  (hcoprime : is_coprime a b)
  (heven : even (a ^ 2 + 3 * b ^ 2))
  :
  ∃ u v,
    (⟨a, b⟩ : ℤ√-3) = ⟨1, 1⟩ * ⟨u, v⟩ ∨ 
    (⟨a, b⟩ : ℤ√-3) = ⟨1, -1⟩ * ⟨u, v⟩ :=
begin
  obtain ⟨ha, hb⟩ := step1a a b hcoprime heven,
  obtain hdvd|hdvd : 4 ∣ a + b ∨ 4 ∣ a - b := int.four_dvd_add_or_sub_of_odd ha hb,
  { --have : 4 * (a ^ 2 + 3 * b ^ 2) = (a - 3 * b) ^ 2 + 3 * (a + b) ^ 2,
    --{ ring },
-- 4u =  a - 3b = a + b - 4 b = 4v - 4b = 4(v - b)
-- 4v = a + b

    obtain ⟨v, hv⟩ := hdvd,
    --set u := v - b with hu,
--    have : 4 ^ 2 ∣ 4 * (a ^ 2 + 3 * b ^ 2) := sorry,
--   obtain ⟨uv, huv⟩ : 4 ∣ a ^ 2 + 3 * b ^ 2 := sorry,
    use [v - b, v],
    right,
    rw [zsqrtd.mul_def],
    rw zsqrtd.ext,
    dsimp,
    simp,
    ring,
    rw ←hv,
    simp },
  { --have : 4 * (a ^ 2 + 3 * b ^ 2) = (a - 3 * b) ^ 2 + 3 * (a + b) ^ 2,
    --{ ring },

    obtain ⟨v, hv⟩ := hdvd,
    use [b + v, -v],
    left,
    rw [zsqrtd.mul_def],
    rw zsqrtd.ext,
    dsimp,
    simp,
    ring,
    rw ←hv,
    simp },
  
end


lemma step1'
  (a b : ℤ)
  (hcoprime : is_coprime a b)
  (heven : even (a ^ 2 + 3 * b ^ 2))
  :
  ∃ u v,
    is_coprime u v ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨1, 1⟩ * ⟨u, v⟩ ∨  (⟨a, b⟩ : ℤ√-3) = ⟨1, -1⟩ * ⟨u, v⟩) ∧
    a ^ 2 + 3 * b ^ 2 = 4 * (u ^ 2 + 3 * v ^ 2) :=
begin
  obtain ⟨u', v', huv'⟩ := step1 a b hcoprime heven,
  refine ⟨u', v', _, huv', _⟩,
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_def, zsqrtd.mul_def] at huv',
    dsimp only at huv',
    apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      simp only [add_zero, mul_zero, or_self] at huv',
      obtain ⟨rfl, rfl⟩ := huv',
      exact not_coprime_zero_zero hcoprime },
    { intros z hz hznezero hzdvdu hzdvdv,
      apply hz,
      simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, mul_neg_eq_neg_mul_symm, neg_neg,
        ←sub_eq_add_neg] at huv',
      obtain ⟨ha, hb⟩ : z ∣ a ∧ z ∣ b,
      { obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := huv';
          rw [hu, hv];
          split;
          try { apply dvd_sub };
          try { apply dvd_add };
          try { apply dvd_mul_of_dvd_right };
          assumption },
      exact hcoprime.is_unit_of_dvd' ha hb } },
  { cases huv';
    { rw [zsqrtd.ext, zsqrtd.mul_def] at huv',
      dsimp only at huv',
      rw [huv'.1, huv'.2],
      ring } }
end

theorem divides_sq_eq_zero {d x y : ℤ } (hd : d < 0) (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
begin
  rw mul_assoc at h,
  split;
    apply pow_eq_zero;
    rw [pow_two];
    apply le_antisymm _ (mul_self_nonneg _),
  { rw [h], apply mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg _), },
  { apply nonpos_of_mul_nonneg_right _ hd,
    rw [←h],
    exact (mul_self_nonneg _) },
end

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {d : ℤ } (hd : d < 0) : Π {a b : ℤ√d},
  a * b = 0 → a = 0 ∨ b = 0
| ⟨x, y⟩ ⟨z, w⟩ h := by injection h with h1 h2; exact
  have h1 : x*z = -(d*y*w), from eq_neg_of_add_eq_zero h1,
  have h2 : x*w = -(y*z), from eq_neg_of_add_eq_zero h2,
  have fin : x*x = d*y*y → (⟨x, y⟩:ℤ√d) = 0, from
  λe, match x, y, divides_sq_eq_zero hd e with ._, ._, ⟨rfl, rfl⟩ := rfl end,
  if z0 : z = 0 then if w0 : w = 0 then
    or.inr (match z, w, z0, w0 with ._, ._, rfl, rfl := rfl end)
  else
     or.inl $ fin $ mul_right_cancel' w0 $ calc
       x * x * w = -y * (x * z) : by simp [h2, mul_assoc, mul_left_comm]
             ... = d * y * y * w : by simp [h1, mul_assoc, mul_left_comm]
  else
     or.inl $ fin $ mul_right_cancel' z0 $ calc
       x * x * z = d * -y * (x * w) : by simp [h1, mul_assoc, mul_left_comm]
             ... = d * y * y * z : by simp [h2, mul_assoc, mul_left_comm]

protected lemma eq_of_mul_eq_mul_left {a b c : ℤ√-3} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
begin
  rw ←sub_eq_zero_iff_eq,
  apply or.resolve_left _ ha,
  apply eq_zero_or_eq_zero_of_mul_eq_zero (by norm_num : (-3 : ℤ) < 0),
  rw [mul_sub, h],
  exact sub_self _,
end

lemma step2'
  (a b : ℤ)
  (p q : ℤ)
  (hcoprime : is_coprime a b)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpodd : odd (p ^ 2 + 3 * q ^ 2))
  (hpprime : prime (p ^ 2 + 3 * q ^ 2))
  :
  ∃ u v,
    (⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨ 
    (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩ :=
begin
  obtain ⟨f, hf⟩ := hdvd,
  have : ((p * b - a * q) * (p * b + a * q) : ℤ) = b ^ 2 * (p ^ 2 + 3 * q ^ 2) - q ^ 2 * (a ^ 2 + 3 * b ^ 2),
  { ring },
  have : ((p * b - a * q) * (p * b + a * q) : ℤ) = (p ^ 2 + 3 * q ^ 2) * (b ^ 2 - q ^ 2 * f),
  { rw this,
    rw hf,
    ring },
  have h0 : p ^ 2 + 3 * q ^ 2 ∣ p * b - a * q ∨
         p ^ 2 + 3 * q ^ 2 ∣ p * b + a * q,
  { apply int.prime.dvd_mul'' hpprime,
    rw this,
    apply dvd_mul_right },
  have h1 : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
            (p * a - 3 * q * b) ^ 2 + 3 * (p * b + a * q) ^ 2,
  { ring },

  have h1' : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
             (p * a + 3 * q * b) ^ 2 + 3 * (p * b - a * q) ^ 2,
  { ring },
  cases h0 with h0 h0,
  { obtain ⟨v, hv⟩ := h0,
    obtain ⟨u, hu⟩ : (p ^ 2 + 3 * q ^ 2) ∣ (p * a + 3 * q * b),
    { apply @prime.dvd_of_dvd_pow _ _ _ hpprime _ 2,
      rw dvd_add_iff_left,
      { rw ←h1', exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw hv,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [u, v],
    left,
    rw [zsqrtd.mul_def, zsqrtd.ext],
    dsimp only,
    simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg, ←sub_eq_add_neg],
    split; apply int.eq_of_mul_eq_mul_left hpprime.ne_zero,
    { calc (p ^ 2 + 3 * q ^ 2) * a
          = p * (p * a + 3 * q * b) - 3 * q * (p * b - a * q) : by ring
      ... = _ : by { rw [hu, hv], ring } },
    { calc (p ^ 2 + 3 * q ^ 2) * b
          = p * (p * b - a * q) + q * (p * a + 3 * q * b) : by ring
      ... = _ : by { rw [hu, hv], ring } } },
  { obtain ⟨v, hv⟩ := h0,
    obtain ⟨u, hu⟩ : (p ^ 2 + 3 * q ^ 2) ∣ (p * a - 3 * q * b),
    { apply @prime.dvd_of_dvd_pow _ _ _ hpprime _ 2,
      rw dvd_add_iff_left,
      { rw ←h1, exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw hv,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [u, v],
    right,
    rw [zsqrtd.mul_def, zsqrtd.ext],
    dsimp only,
    simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg, ←sub_eq_add_neg],
    split; apply int.eq_of_mul_eq_mul_left hpprime.ne_zero,
    { calc (p ^ 2 + 3 * q ^ 2) * a
          = p * (p * a - 3 * q * b) + 3 * q * (p * b + a * q) : by ring
      ... = _ : by { rw [hu, hv], ring } },
    { calc (p ^ 2 + 3 * q ^ 2) * b
          = p * (p * b + a * q) - q * (p * a - 3 * q * b) : by ring
      ... = _ : by { rw [hu, hv], ring } } },


/-
hv: p * b + a * q = (p ^ 2 + 3 * q ^ 2) * v
hu: p * a - 3 * q * b = (p ^ 2 + 3 * q ^ 2) * u
⊢ a = p * u + 3 * q * v ∧ b = p * v - q * u

⊢ a = p * (p * a - 3 * q * b) / (p ^ 2 + 3 * q ^ 2) + 3 * q * (p * b + a * q) / (p ^ 2 + 3 * q ^ 2)
= (p * (p * a - 3 * q * b) + 3 * q * (p * b + a * q)) / (p ^ 2 + 3 * q ^ 2)
= p ^ 2 * a  + 3 * a * q ^ 2

  obtain ⟨u, v, huv⟩ := sq_plus_three_sq_prime_dvd p q a.nat_abs b.nat_abs
    (by rwa hp at hpprime)
    (by rwa hp at hdvd'),
  refine ⟨u, v, q, r, _⟩,
  rw [zsqrtd.mul_def],
  obtain ⟨d, hd⟩ := hdvd,
  sorry,
  { rwa ←int.gcd_eq_one_iff_coprime at hcoprime },
  { rwa ←nat.odd_iff_not_even },
  

  sorry
-/
end

lemma step2'''
  (a b : ℤ)
  (p q : ℤ)
  (hcoprime : is_coprime a b)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpodd : odd (p ^ 2 + 3 * q ^ 2))
  (hpprime : prime (p ^ 2 + 3 * q ^ 2))
  :
  ∃ u v,
    is_coprime u v ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨ (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩) ∧
    (a ^ 2 + 3 * b ^ 2) = (p ^ 2 + 3 * q ^ 2) * (u ^ 2 + 3 * v ^ 2)  :=
begin
  set P' := (p ^ 2 + 3 * q ^ 2).nat_abs with hP',
  have hdvd' : P' ∣ a.nat_abs ^ 2 + 3 * b.nat_abs ^ 2,
  { convert int.nat_abs_dvd_abs_iff.mpr hdvd,
    zify,
    rw [int.nat_abs_pow_two, int.nat_abs_pow_two],
    rw [int.nat_abs_of_nonneg (spts.nonneg _ _)], },
  have hodd : odd P',
  { rwa [hP', int.nat_abs_odd] },
  have hprime' : nat.prime P',
  { rwa [hP', ←int.prime_iff] },

  have hprime'' : nat.prime (p.nat_abs ^ 2 + 3 * q.nat_abs ^ 2),
  { convert hprime',
    zify,
    rw [int.nat_abs_pow_two, int.nat_abs_pow_two, hP'],
    rw [int.nat_abs_of_nonneg (spts.nonneg _ _)] },
  have hdvd'' : p.nat_abs ^ 2 + 3 * q.nat_abs ^ 2 ∣ a.nat_abs ^ 2 + 3 * b.nat_abs ^ 2,
  { rw ←int.nat_abs_dvd_abs_iff at hdvd,
    convert hdvd;
    { zify,
      rw [int.nat_abs_pow_two, int.nat_abs_pow_two],
      rw [int.nat_abs_of_nonneg (spts.nonneg _ _)] } },

  obtain ⟨u, v, huv⟩ := sq_plus_three_sq_prime_dvd p.nat_abs q.nat_abs a.nat_abs b.nat_abs
    hprime''
    hdvd'',
  obtain ⟨u', v', h⟩ := step2' a b p q hcoprime hdvd hpodd hpprime,
  refine ⟨u', v', _, h, _⟩,
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_def, zsqrtd.mul_def] at h,
    dsimp only at h,
    apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      simp only [add_zero, mul_zero, or_self] at h,
      obtain ⟨rfl, rfl⟩ := h,
      exact not_coprime_zero_zero hcoprime },
    { intros z hz hznezero hzdvdu hzdvdv,
      apply hz,
      simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, mul_neg_eq_neg_mul_symm, neg_neg,
        ←sub_eq_add_neg] at h,
      obtain ⟨ha, hb⟩ : z ∣ a ∧ z ∣ b,
      { obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := h;
          rw [hu, hv];
          split;
          try { apply dvd_sub };
          try { apply dvd_add };
          try { apply dvd_mul_of_dvd_right };
          assumption },
      exact hcoprime.is_unit_of_dvd' ha hb } },
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_def, zsqrtd.mul_def] at h,
    dsimp only at h,
    obtain ⟨rfl, rfl⟩|⟨rfl, rfl⟩ := h; ring },
end

lemma step2
  (a b : ℤ)
  (p : ℕ)
  (hcoprime : is_coprime a b)
  (hdvd : (p : ℤ) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpodd : odd p)
  (hpprime : nat.prime p)
  :
  ∃ u v q r,
    (p : ℤ) = q ^ 2 + 3 * r ^ 2 ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨q, r⟩ * ⟨u, v⟩ ∨ 
     (⟨a, b⟩ : ℤ√-3) = ⟨q, -r⟩ * ⟨u, v⟩) ∧
    0 ≤ q ∧ 
    0 ≤ r :=
begin
  have hdvd' : p ∣ a.nat_abs ^ 2 + 3 * b.nat_abs ^ 2,
  { rw [←int.nat_abs_pow_two a, ←int.nat_abs_pow_two b] at hdvd,
    norm_cast at hdvd,
    assumption },

  obtain ⟨q, r, hp⟩ := factors a.nat_abs b.nat_abs p _ _ hdvd',
  obtain ⟨u, v, huv⟩ := sq_plus_three_sq_prime_dvd q r a.nat_abs b.nat_abs
    (by rwa hp at hpprime)
    (by rwa hp at hdvd'),
  obtain ⟨u', v', h⟩ := step2' a b q r hcoprime _ _ _,
  refine ⟨u', v', q, r, _, h, int.coe_nat_nonneg _, int.coe_nat_nonneg _⟩,
  { norm_cast, exact hp },
  { zify at huv,
    use (u ^ 2 + 3 * v ^ 2),
    rw huv,
    simp only [int.nat_abs_pow_two] },
  { norm_cast, rwa ←hp },
  { norm_cast, rwa [←nat.prime_iff_prime_int, ←hp], },
  { rwa ←int.gcd_eq_one_iff_coprime at hcoprime },
  { rwa ←nat.odd_iff_not_even }
end

lemma step2''
  {a b : ℤ}
  {p : ℕ}
  (hcoprime : is_coprime a b)
  (hdvd : (p : ℤ) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpodd : odd p)
  (hpprime : nat.prime p)
  :
  ∃ u v q r,
    is_coprime u v ∧
    (p : ℤ) = q ^ 2 + 3 * r ^ 2 ∧
    (a ^ 2 + 3 * b ^ 2) = p * (u ^ 2 + 3 * v ^ 2) ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨q, r⟩ * ⟨u, v⟩ ∨ 
     (⟨a, b⟩ : ℤ√-3) = ⟨q, -r⟩ * ⟨u, v⟩) ∧
    0 ≤ q ∧ 
    0 ≤ r :=
begin
  obtain ⟨u, v, q, r, hp, huv', hqnonneg, hrnonneg⟩ := step2 a b p hcoprime hdvd hpodd hpprime,
  refine ⟨u, v, q, r, _, hp, _, huv', hqnonneg, hrnonneg⟩,
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_def, zsqrtd.mul_def] at huv',
    dsimp only at huv',
    apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      simp only [add_zero, mul_zero, or_self] at huv',
      obtain ⟨rfl, rfl⟩ := huv',
      exact not_coprime_zero_zero hcoprime },
    { intros z hz hznezero hzdvdu hzdvdv,
      apply hz,
      simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, mul_neg_eq_neg_mul_symm, neg_neg,
        ←sub_eq_add_neg] at huv',
      obtain ⟨ha, hb⟩ : z ∣ a ∧ z ∣ b,
      { obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := huv';
          rw [hu, hv];
          split;
          try { apply dvd_sub };
          try { apply dvd_add };
          try { apply dvd_mul_of_dvd_right };
          assumption },
      exact hcoprime.is_unit_of_dvd' ha hb } },
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_def, zsqrtd.mul_def] at huv',
    dsimp only at huv',
    rw hp,
    obtain ⟨rfl, rfl⟩|⟨rfl, rfl⟩ := huv'; ring }
end

lemma step1_2
  (a b : ℤ)
  (p q : ℤ)
  (hcoprime : is_coprime a b)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hp : odd_prime_or_four (p ^ 2 + 3 * q ^ 2))
  (hq : q ≠ 0)
  :
  ∃ u v,
    is_coprime u v ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨ (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩) ∧
    (a ^ 2 + 3 * b ^ 2) = (p ^ 2 + 3 * q ^ 2) * (u ^ 2 + 3 * v ^ 2)  :=
begin
  obtain hp|⟨hpprime, hpodd⟩ := hp,
  { rw hp at hdvd,
    have heven : even (a ^ 2 + 3 * b ^ 2),
    { apply dvd_trans _ hdvd,
      norm_num },
    obtain ⟨u, v, h1, h2, h3⟩ := step1' a b hcoprime heven,
    obtain ⟨hpone, hqone⟩ := spts.four hp hq,
    cases int.abs_eq p with hp' hp';
    cases int.abs_eq q with hq' hq';
    rw [hpone] at hp';
    rw [hqone] at hq';
    subst p;
    subst q,
    
    {refine ⟨u, v, h1, h2, _⟩, { rwa hp }},
    {refine ⟨u, v, h1, _, _⟩, { simp only [neg_neg], rwa or_comm, }, { rwa hp }},
    {refine ⟨-u, -v, is_coprime_neg h1, _, _⟩, { rw or_comm, convert h2 using 2;
      {

        rw zsqrtd.mul_def,
        rw zsqrtd.mul_def,
        rw zsqrtd.ext,
      dsimp only,
      simp,
      },
    
     }, { rwa [hp, pow_two_neg, pow_two_neg], }},
    {refine ⟨-u, -v, is_coprime_neg h1, _, _⟩, { convert h2 using 2;
      {

        rw zsqrtd.mul_def,
        rw zsqrtd.mul_def,
        rw zsqrtd.ext,
      dsimp only,
      simp,
      },
    
     }, { rwa [hp, pow_two_neg, pow_two_neg], }},
    
    
     },
  { apply step2''' _ _ _ _ hcoprime hdvd hpodd hpprime }
end

lemma step1_2'
  (a : ℤ√-3)
  (p : ℤ√-3)
  (hcoprime : is_coprime a.re a.im)
  (hdvd : p.norm ∣ a.norm)
  (hp : odd_prime_or_four p.norm)
  (hq : p.im ≠ 0)
  :
  ∃ u v,
    is_coprime u v ∧
    (a = p * ⟨u, v⟩ ∨ a = p.conj * ⟨u, v⟩) ∧
    a.norm = p.norm * (u ^ 2 + 3 * v ^ 2)  :=
begin
  have hdvd : p.re ^ 2 + 3 * p.im ^ 2 ∣ a.re ^ 2 + 3 * a.im ^ 2,
  { convert hdvd; ring },
  have hp : odd_prime_or_four (p.re ^ 2 + 3 * p.im ^ 2),
  { convert hp; ring },
  obtain ⟨u, v, h⟩ := step1_2 a.re a.im p.re p.im hcoprime hdvd hp hq,
  use [u, v],
  convert h,
  { simp only [zsqrtd.ext, eq_self_iff_true, and_self] },
  { simp only [zsqrtd.ext, eq_self_iff_true, and_self] },
  { simp only [zsqrtd.ext, eq_self_iff_true, and_self] },
  { simp only [zsqrtd.ext, zsqrtd.conj_re, eq_self_iff_true, and_self, zsqrtd.conj_im] },
  { simp only [zsqrtd.norm, pow_two, mul_assoc, neg_mul_eq_neg_mul_symm, sub_neg_eq_add] },
  { simp only [zsqrtd.norm, pow_two, mul_assoc, neg_mul_eq_neg_mul_symm, sub_neg_eq_add] },
end

lemma step3
  {a b : ℤ}
  (hcoprime : is_coprime a b)
  :
  ∃ f : multiset ℤ√-3,
    ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
      --(pq.re ^ 2 + 3 * pq.im ^ 2 = 4 ∨
      -- (prime (pq.re ^ 2 + 3 * pq.im ^ 2) ∧ odd (pq.re ^ 2 + 3 * pq.im ^ 2)))
  :=
begin
  suffices : ∀ n : ℕ, a^2 + 3 * b ^ 2 = n →
    ∃ f : multiset ℤ√-3,
    ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
      
      --(pq.re ^ 2 + 3 * pq.im ^ 2 = 4 ∨
      -- (prime (pq.re ^ 2 + 3 * pq.im ^ 2) ∧ odd (pq.re ^ 2 + 3 * pq.im ^ 2)))

  
  ,
  { exact this (a^2 + 3 * b ^ 2).nat_abs (int.nat_abs_of_nonneg (spts.nonneg a b)).symm },

  intros n hn,
  induction n using nat.strong_induction_on with n ih generalizing a b,
  dsimp only at ih,
  have hn' : (a ^ 2 + 3 * b ^ 2).nat_abs = n,
  { rw hn, exact int.nat_abs_of_nat n },

  by_cases h : a^2 + 3 * b ^ 2 = 1,
  { have : abs a = 1 ∧ b = 0 := spts.eq_one h,
    use 0,
    --use ⟨1, 0⟩ ::ₘ 0,
    split,
    { simp only [multiset.prod_zero, zsqrtd.ext, zsqrtd.one_re, zsqrtd.one_im, zsqrtd.neg_im,
        zsqrtd.neg_re, neg_zero],
      rw ←or_and_distrib_right,
      refine ⟨_, this.2⟩,
      by_cases H : 0 ≤ a,
      { left,
        rw [←abs_of_nonneg H, this.1] },
      { right,
        rw [eq_neg_iff_eq_neg, ←abs_of_nonpos (le_of_not_le H), this.1] } },
    { intros pq hpq,
      simpa only [multiset.not_mem_zero] using hpq } },
  { have : 1 < a ^ 2 + 3 * b ^ 2,
    { apply lt_of_le_of_ne _ (ne.symm h),
      have : (0 + 1 : ℤ) = _ := zero_add 1,
      conv_lhs { rw [←this] },
      rw [int.add_one_le_iff],
      apply lt_of_le_of_ne (spts.nonneg a b),
      intro H,
      rw [eq_comm, int.sq_plus_three_sq_eq_zero_iff] at H,
      apply @not_coprime_zero_zero ℤ,
      rwa [H.1, H.2] at hcoprime },
    have : 2 < a ^ 2 + 3 * b ^ 2,
    { apply lt_of_le_of_ne _ (spts.not_two a b).symm,
      exact this },
    have : 2 < n,
    { zify,
      rwa [←hn] },
    obtain ⟨p, hpdvd, (rfl|⟨hpprime, hpodd⟩)⟩ := exists_prime_and_dvd' this,
    -- 4 divides
    { have : even (a ^ 2 + 3 * b ^ 2),
      { rw hn,
        norm_cast,
        apply dvd_trans _ hpdvd,
        norm_num },
      obtain ⟨u, v, huvcoprime, huv, huvdvd⟩ := step1' a b hcoprime this,
      have descent : (u ^ 2 + 3 * v ^ 2).nat_abs < n,
      { rw ←hn',
        apply int.nat_abs_lt_nat_abs_of_nonneg_of_lt (spts.nonneg _ _),
        rw huvdvd,
        apply int.lt_mul_self (spts.pos_of_coprime huvcoprime),
        norm_num },
      obtain ⟨g, hgprod, hgfactors⟩ := ih (u ^ 2 + 3 * v ^ 2).nat_abs descent huvcoprime
        (int.nat_abs_of_nonneg (spts.nonneg _ _)).symm,
      cases huv;
      [use ⟨1, 1⟩ ::ₘ g, use ⟨1, -1⟩ ::ₘ g];
      { split,
        { rw huv,
          cases hgprod; rw [multiset.prod_cons, hgprod],
          { left, refl },    
          { right, simp only [mul_neg_eq_neg_mul_symm], },            
        },
        { rintros pq hpq,
          rw multiset.mem_cons at hpq,
          obtain rfl|ind := hpq,
          { refine ⟨_, _, or.inl ((zsqrt3.norm _).trans _)⟩; norm_num },
          { exact hgfactors pq ind } } } },
    -- odd prime
    { rw ←nat.odd_iff at hpodd, -- TODO fix exists_prime_and_dvd'
      rw [←int.coe_nat_dvd, ←hn] at hpdvd,
      obtain ⟨u, v, q, r, huvcoprime, hp, huvdvd, huv, hqnonneg, hrnonneg⟩ := step2'' hcoprime hpdvd hpodd hpprime,
      have descent : (u ^ 2 + 3 * v ^ 2).nat_abs < n,
      { rw ←hn',
        apply int.nat_abs_lt_nat_abs_of_nonneg_of_lt (spts.nonneg _ _),
        rw huvdvd,
        apply int.lt_mul_self (spts.pos_of_coprime huvcoprime),
        norm_cast,
        exact hpprime.one_lt },
      obtain ⟨g, hgprod, hgfactors⟩ := ih (u ^ 2 + 3 * v ^ 2).nat_abs descent huvcoprime
        (int.nat_abs_of_nonneg (spts.nonneg _ _)).symm,
      cases huv;
      [use ⟨q, r⟩ ::ₘ g, use ⟨q, -r⟩ ::ₘ g];
      { split,
        { rw huv,
          cases hgprod; rw [multiset.prod_cons, hgprod],
          { left, refl },    
          { right, simp only [mul_neg_eq_neg_mul_symm], },            
        },
        { rintros pq hpq,
          rw multiset.mem_cons at hpq,
          obtain rfl|ind := hpq,
          { rw [nat.prime_iff_prime_int, hp] at hpprime,
            rw [zsqrt3.norm],
            try { rw neg_square },
            -- TODO: eq_or_eq_neg_of_pow_two_eq_pow_two for abs
            dsimp only,
            refine ⟨hqnonneg, _, or.inr ⟨hpprime, _⟩⟩,
            { try { rw neg_ne_zero, },
              rintro rfl,
              simp only [zero_pow zero_lt_two, add_zero, mul_zero] at hpprime,
              apply not_prime_pow one_lt_two hpprime, },
            { rwa [←hp, int.coe_nat_odd] } },
          { exact hgfactors pq ind } } } } },
    /-
    { by_cases ha : 0 ≤ a,
      { rw abs_of_nonneg ha at this,
        left,
        simpa using this },
      { rw [abs_of_neg (lt_of_not_ge ha), neg_eq_iff_neg_eq, eq_comm] at this,
        right,
        simp only [mul_one, multiset.prod_cons, multiset.prod_zero],
        rw [zsqrtd.ext],
        simpa using this } },
    { intros pq hpq,
      simp at hpq,
      rw hpq,
    }
    -/
end

lemma step4_1'
  {p q : ℤ}
  (hcoprime : is_coprime p q)
  (hfour : p ^ 2 + 3 * q ^ 2 = 4) :
  abs p = 1 ∧ abs q = 1 :=
begin
  apply spts.four hfour,
  rintro rfl,
  rw [is_coprime_zero_right, int.is_unit_iff_abs] at hcoprime,
  rw [zero_pow zero_lt_two, mul_zero, add_zero, ←int.nat_abs_pow_two, ←int.abs_eq_nat_abs, hcoprime] at hfour,
  norm_num at hfour
end

lemma step4_1'_bis
  {p q : ℤ}
  (hfour : p ^ 2 + 3 * q ^ 2 = 4)
  (hq : q ≠ 0) :
  abs p = 1 ∧ abs q = 1 :=
spts.four hfour hq

lemma step4_1
  (p q p' q' : ℤ)
  (hcoprime : is_coprime p q)
  (hcoprime' : is_coprime p' q')
  (hfour : p ^ 2 + 3 * q ^ 2 = 4)
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain ⟨hp, hq⟩ := step4_1' hcoprime hfour,
  rw heq at hfour,
  obtain ⟨hp', hq'⟩ := step4_1' hcoprime' hfour,
  rw [hp, hq, hp', hq'],
  split; refl,
end

lemma step4_1_bis
  (p q p' q' : ℤ)
  (hq : q ≠ 0)
  (hq' : q' ≠ 0)
  (hfour : p ^ 2 + 3 * q ^ 2 = 4)
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain ⟨hp, hq⟩ := step4_1'_bis hfour hq,
  rw heq at hfour,
  obtain ⟨hp', hq'⟩ := step4_1'_bis hfour hq',
  rw [hp, hq, hp', hq', and_self],
end

example (a b : int) (h : a * b = a) (h' : a ≠ 0) : b = 1 := by {
  exact int.eq_one_of_mul_eq_self_right h' h,


}

lemma step4_2
  (p q p' q' : ℤ)
  (hcoprime : is_coprime p q)
  (hcoprime' : is_coprime p' q')
  (hprime : prime (p ^ 2 + 3 * q ^ 2))
  (hodd : odd (p ^ 2 + 3 * q ^ 2))
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain ⟨u, v, hcoprime'', (H|H), h1⟩ := step2''' p q p' q' hcoprime (by rw heq) (by rwa ←heq) (by rwa ←heq);
  { rw heq at h1,
    have := int.eq_one_of_mul_eq_self_right (spts.not_zero_of_coprime hcoprime') h1.symm,
    obtain ⟨ha, rfl⟩ := spts.eq_one this,
    simp only [zero_pow zero_lt_two, add_zero, mul_zero] at this, 
    clear h1,
    rw [zsqrtd.ext, zsqrtd.mul_def] at H,
    dsimp only at H,
    simp only [add_zero, zero_add, mul_zero] at H,
    rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
    try { rw [abs_neg] },
    split; refl },
/-
{

  rw heq at h1,
  have := int.eq_one_of_mul_eq_self_right (spts.not_zero_of_coprime hcoprime') h1.symm,
  obtain ⟨ha, rfl⟩ := spts.eq_one hcoprime'' this,
  simp only [zero_pow zero_lt_two, add_zero, mul_zero] at this, 
  clear h1,
  rw [zsqrtd.ext, zsqrtd.mul_def] at H,
  dsimp only at H,
  simp only [add_zero, zero_add, mul_zero] at H,
  rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
  simp only [abs_neg, eq_self_iff_true, and_self],
  split; refl,
},
  

  { rw [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im] at H,
    dsimp only at H,
    rw [H.1, H.2],
    
    },


  set P' := (p' ^ 2 + 3 * q' ^ 2).nat_abs with hP',
  have hdvd : (P' : ℤ) ∣ p ^ 2 + 3 * q ^ 2,
  { rw [hP', heq, int.nat_abs_of_nonneg (spts.nonneg _ _)] },
  have hodd : odd P',
  { rwa [hP', int.nat_abs_odd, ←heq] },
  have hprime' : nat.prime P',
  { rwa [hP', ←int.prime_iff, ←heq] },
  obtain ⟨a, b, c, d, hcoprimeab, _, H, h1, _, _⟩ := step2'' hcoprime hdvd hodd hprime',
  rw [heq, hP', int.nat_abs_of_nonneg (spts.nonneg _ _)] at H,
  have := int.eq_one_of_mul_eq_self_right (spts.not_zero_of_coprime hcoprime') H.symm,
  obtain ⟨ha, rfl⟩ := spts.eq_one hcoprimeab this,
  rw [zsqrtd.ext, zsqrtd.ext] at h1,
  simp only [add_zero, zsqrtd.mul_im, zero_add, zsqrtd.mul_re, mul_zero] at h1,
  simp only [neg_mul_eq_neg_mul_symm, ←and_or_distrib_left] at h1,
  rw [h1.1, abs_mul, ha, mul_one],
  sorry,
-/
end

lemma step4_2_bis
  (p q p' q' : ℤ)
  (hcoprime : is_coprime p q)
  (hcoprime' : is_coprime p' q')
  (hprime : prime (p ^ 2 + 3 * q ^ 2))
  (hodd : odd (p ^ 2 + 3 * q ^ 2))
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain ⟨u, v, hcoprime'', (H|H), h1⟩ := step2''' p q p' q' hcoprime (by rw heq) (by rwa ←heq) (by rwa ←heq);
  { rw heq at h1,
    have := int.eq_one_of_mul_eq_self_right (spts.not_zero_of_coprime hcoprime') h1.symm,
    obtain ⟨ha, rfl⟩ := spts.eq_one this,
    simp only [zero_pow zero_lt_two, add_zero, mul_zero] at this, 
    clear h1,
    rw [zsqrtd.ext, zsqrtd.mul_def] at H,
    dsimp only at H,
    simp only [add_zero, zero_add, mul_zero] at H,
    rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
    try { rw [abs_neg] },
    split; refl },
end

lemma step4_3
  (p q p' q' : ℤ)
  (hcoprime : is_coprime p q)
  (hcoprime' : is_coprime p' q')
  (h : odd_prime_or_four (p ^ 2 + 3 * q ^ 2))
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain h|⟨hp, hodd⟩ := h,
  { apply step4_1; assumption },
  { apply step4_2; assumption }
end

lemma prod_map_multiplicative {M N : Type*} [comm_monoid M] [comm_monoid N] {s : multiset M}
  {f : M → N} (fone : f 1 = 1) (fmul : ∀ a b, f (a * b) = f a * f b) :
  (s.map f).prod = f s.prod := 
begin
  refine multiset.induction_on s _ _,
  { simp only [multiset.prod_zero, fone, multiset.map_zero] },
  { intros a s ih,
    rw [multiset.map_cons, multiset.prod_cons, multiset.prod_cons, fmul, ih] },
end

lemma prod_map_norm {s : multiset ℤ√-3} :
  (s.map zsqrtd.norm).prod = zsqrtd.norm s.prod :=
prod_map_multiplicative zsqrtd.norm_one zsqrtd.norm_mul

lemma norm_not_dvd_four_of_odd_prime' {p : ℤ} (hmin : 0 ≤ p) (hp : prime p) (hodd: odd p) :
  ¬(p ∣ 4) :=
begin
  intro h,
  have hmax := int.le_of_dvd (by norm_num) h,
  rw ←int.lt_add_one_iff at hmax,
  interval_cases using hmin hmax,
  { exact hp.ne_zero rfl, },
  { exact hp.ne_one rfl },
  { norm_num at hodd, exact hodd },
  { norm_num at h },
  { norm_num at hodd, exact hodd },
end

lemma norm_not_dvd_four_of_odd_prime {p : ℤ√-3} (hp : prime p.norm) (hodd: odd p.norm) :
  ¬(p.norm ∣ 4) :=
begin
  have hmin := zsqrtd.norm_nonneg (by norm_num : (-3 : ℤ) ≤ 0) p,
  apply norm_not_dvd_four_of_odd_prime'; assumption,
end

lemma associated_of_dvd' {a p : ℤ}
  (ha : odd_prime_or_four (a))
  (hp : odd_prime_or_four (p))
  (h: p ∣ a) : associated p a :=
begin
  cases ha; cases hp,
  { rw [ha, hp] },
  { exfalso,
    rw ha at h,
    have h : abs p ∣ 4,
    { rw int.abs_eq_nat_abs,
      exact int.nat_abs_dvd.mpr h,},
    exact norm_not_dvd_four_of_odd_prime' (abs_nonneg _) (int.abs_prime hp.1) (int.abs_odd hp.2) h },
  { exfalso,
    have : ¬odd a,
    { rw ←int.even_iff_not_odd,
      apply dvd_trans _ h,
      norm_num [hp] },
    exact this ha.2 },
  { rwa prime_dvd_prime_iff_eq hp.1 ha.1 at h }

end

lemma associated_of_dvd {a p : ℤ√-3}
  (ha : odd_prime_or_four (zsqrtd.norm a))
  (hp : odd_prime_or_four (zsqrtd.norm p))
  (h: p.norm ∣ a.norm) : associated p.norm a.norm :=
begin
  apply associated_of_dvd'; assumption,
end

lemma dvd_blah (p a b : ℤ) (hp : prime p) (n : ℕ) (h : ¬(p ∣ a)) (h' : p ^ n ∣ a * b) : p ^ n ∣ b :=
begin
  induction n with n ih,
  { rw pow_zero, exact one_dvd b },
  { have : p ^ n ∣ p ^ n.succ,
    { have : n ≤ n.succ := nat.le_succ n,
      exact pow_dvd_pow p this },
    specialize ih (dvd_trans this h'),
    obtain ⟨c, rfl⟩ := ih,
    clear this,
    
    have : p ∣ a * c,
    { have : p ^ n ≠ 0 := pow_ne_zero _  hp.ne_zero,
      apply int.dvd_of_mul_dvd_mul_left this,
      convert h' using 1,
      { rw pow_succ' },
      { ring } },
    have := (hp.div_or_div this).resolve_left h,
    rw pow_succ',
    exact mul_dvd_mul_left (p ^ n) this }
end 

lemma dvd_or_dvd' {a p x : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (hdvd : p ∣ a * x) : p ∣ a ∨ p ∣ x :=
begin
  cases hp,
  { cases ha,
    { left, rw [ha, hp] },
    { right,
      have : (4 : ℤ) = 2 ^ 2,
      { norm_num },
      rw [hp, this],
      apply dvd_blah,
      { rw int.prime_iff,
        convert nat.prime_two },
      { rw [←even_iff_two_dvd, ←int.odd_iff_not_even], exact ha.2 },
      { rwa [hp, this] at hdvd } } },
  { exact (hp.1.div_or_div hdvd) }
end 

lemma dvd_or_dvd (a p : ℤ√-3) (x : ℤ)
  (ha : odd_prime_or_four (zsqrtd.norm a))
  (hp : odd_prime_or_four (zsqrtd.norm p))
  (hdvd : p.norm ∣ a.norm * x) : p.norm ∣ a.norm ∨ p.norm ∣ x :=
begin
  apply dvd_or_dvd'; assumption,
end 

lemma exists_associated_mem_of_dvd_prod'
  {p : ℤ√-3} (hp : odd_prime_or_four p.norm)
  {s : multiset ℤ√-3} :
  (∀ r ∈ s, odd_prime_or_four (zsqrtd.norm r)) →
  zsqrtd.norm p ∣ (s.map zsqrtd.norm).prod →
  ∃ q ∈ s, associated (zsqrtd.norm p) (zsqrtd.norm q) :=
multiset.induction_on s (by {
  simp only [forall_const, forall_prop_of_false, exists_false, multiset.prod_zero, not_false_iff,
    exists_prop_of_false, multiset.not_mem_zero],
    simp only [int.cast_one, multiset.prod_zero, multiset.map_zero],
    rw ←is_unit_iff_dvd_one,
    exact hp.not_unit })
  (λ a s ih hs hps, begin
    rw [multiset.map_cons, multiset.prod_cons] at hps,
    have hps' : p.norm ∣ (a * s.prod).norm,
    { obtain ⟨x, hx⟩ := hps,
      rw prod_map_norm at hx,
      rw [zsqrtd.norm_mul, hx],
      exact dvd_mul_right _ _ },
    have := hs a (multiset.mem_cons_self _ _),
    have h : p.norm ∣ a.norm ∨ p.norm ∣ (multiset.map zsqrtd.norm s).prod := dvd_or_dvd _ _ _ this hp hps,
--    obtain ⟨u, v, huvcoprime, H1, H2⟩ := step1_2' _ p _ hps' hp _,
    cases h with h h,
    { use [a, by simp],
      apply associated_of_dvd' _ _ h; assumption,
      /-
      cases h with u hu,
      have := irreducible.is_unit_or_is_unit,
      have := (hs a (multiset.mem_cons.2 (or.inl rfl))),
      cases ((irreducible_of_prime ).is_unit_or_is_unit hu).resolve_left hp.not_unit with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
      -/
    },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ} (hp : odd_prime_or_four p)
  {s : multiset ℤ} :
  (∀ r ∈ s, odd_prime_or_four (r)) →
  p ∣ (s).prod →
  ∃ q ∈ s, associated p q :=
multiset.induction_on s (by {
  simp only [forall_const, forall_prop_of_false, exists_false, multiset.prod_zero, not_false_iff,
    exists_prop_of_false, multiset.not_mem_zero],
    rw ←is_unit_iff_dvd_one,
    exact hp.not_unit })
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    have := hs a (multiset.mem_cons_self _ _),
    have h := dvd_or_dvd' this hp hps,
--    obtain ⟨u, v, huvcoprime, H1, H2⟩ := step1_2' _ p _ hps' hp _,
    cases h with h h,
    { use [a, by simp],
      apply associated_of_dvd' _ _ h; assumption,
      /-
      cases h with u hu,
      have := irreducible.is_unit_or_is_unit,
      have := (hs a (multiset.mem_cons.2 (or.inl rfl))),
      cases ((irreducible_of_prime ).is_unit_or_is_unit hu).resolve_left hp.not_unit with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
      -/
    },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma factors_unique_prod' : ∀{f g : multiset ℤ},
  (∀x∈f, odd_prime_or_four x) →
  (∀x∈g, odd_prime_or_four x) →
  (associated f.prod g.prod) →
  multiset.rel associated f g :=
begin
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw [multiset.rel_zero_left],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    apply (hg x hx).not_unit,
    rw is_unit_iff_dvd_one,
    apply dvd.trans (multiset.dvd_prod hx),
    { rw [←is_unit_iff_dvd_one, ←associated_one_iff_is_unit],
      rw [multiset.prod_zero] at h,
      exact h.symm } },
  { intros p f ih g hf hg hfg,
    have hp := hf p (by simp only [multiset.mem_cons_self]),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod'' hp hg hdvd,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons hb,
    apply ih _ _ _,
    exact (λ q hq, hf _ (by simp [hq])),
    exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)),
    { apply associated_mul_left_cancel _ hb hp.ne_zero,
      rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg] } },
end


lemma factors_unique_prod : ∀{f g : multiset ℤ√-3},
  (∀x∈f, odd_prime_or_four (zsqrtd.norm x)) →
  (∀x∈g, odd_prime_or_four (zsqrtd.norm x)) →
  (associated f.prod.norm g.prod.norm) →
  multiset.rel associated (f.map zsqrtd.norm) (g.map zsqrtd.norm) :=
begin
  intros f g hf hg hassoc,
  apply factors_unique_prod',
  { intros x hx,
    rw multiset.mem_map at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    exact hf y hy },
  { intros x hx,
    rw multiset.mem_map at hx,
    obtain ⟨y, hy, rfl⟩ := hx,
    exact hg y hy },
  { rwa [prod_map_norm, prod_map_norm] },
/-
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw [multiset.map_zero, multiset.rel_zero_left],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x' hx',
    rw multiset.mem_map at hx',
    obtain ⟨x, hx, hxnorm⟩ := hx',
    apply (hg x hx).not_unit,
    rw ←zsqrtd.is_unit_iff_norm_is_unit,
    rw is_unit_iff_dvd_one,
    apply dvd.trans (multiset.dvd_prod hx),
    { rw [←is_unit_iff_dvd_one, ←associated_one_iff_is_unit],
      rw [multiset.prod_zero] at h,
      exact h.symm } },
  { intros p f ih g hf hg hfg,
    have hp := hf p (by simp only [multiset.mem_cons_self]),
    --have hprime : prime p := (unique_factorization_monoid.irreducible_iff_prime.1 (hf p (by simp))),
    have hprimeing : ∀ q, q ∈ g → odd_prime_or_four (zsqrtd.norm q)
      := (λ q hq, (hg _ hq)),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    have : p.norm ∣ (multiset.map zsqrtd.norm g).prod,
    { rw prod_map_norm,
      obtain ⟨x, hx⟩ := hdvd, -- TODO lemma
      rw [hx, zsqrtd.norm_mul],
      apply dvd_mul_right },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod' hp hprimeing this,
    rw multiset.map_cons,
    rw ← multiset.cons_erase hbg,
    rw multiset.map_cons,
    apply multiset.rel.cons _,
    apply ih,
    exact (λ q hq, hf _ (by simp [hq])),
    exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)),
    { apply associated_mul_left_cancel,
    },
    exact (associated_mul_left_cancel
        (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
      (hf p (by simp)).ne_zero),
          },

-/
end

noncomputable def factorization
  {a b : ℤ}
  (hcoprime : is_coprime a b)
  : multiset ℤ√-3
 := classical.some (step3 hcoprime)

lemma factorization_prop
  {a b : ℤ}
  (hcoprime : is_coprime a b) :
  ((⟨a, b⟩ : ℤ√-3) = (factorization hcoprime).prod ∨ (⟨a, b⟩ : ℤ√-3) = - (factorization hcoprime).prod) ∧
    ∀ pq : ℤ√-3, pq ∈ (factorization hcoprime) →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm :=
classical.some_spec (step3 hcoprime)

/-
lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ√-3} (hp : odd_prime_or_four p.norm)
  {s : multiset ℤ√-3} :
  (∀ r ∈ s, odd_prime_or_four (zsqrtd.norm r)) →
  p ∣ s.prod →
  ∃ q ∈ s, associated p q :=
multiset.induction_on s (by {
  simp only [forall_const, forall_prop_of_false, exists_false, multiset.prod_zero, not_false_iff,
    exists_prop_of_false, multiset.not_mem_zero],
    rw ←is_unit_iff_dvd_one,
    rw ←zsqrtd.norm_eq_one_iff,
    rw ←int.is_unit_iff_nat_abs,
    exact hp.not_unit })
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    have hps' : p.norm ∣ (a * s.prod).norm,
    { obtain ⟨x, hx⟩ := hps,
      rw [hx, zsqrtd.norm_mul],
      exact dvd_mul_right _ _ },
    have := hs a (multiset.mem_cons_self _ _),
    obtain ⟨u, v, huvcoprime, H⟩ := step1_2' _ p _ hps' hp _,
    have h : _ := sorry,
    obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h,
    exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩,
    cases hp.div_or_div hps with h h,
    { use [a, by simp],
      cases h with u hu,
      have := irreducible.is_unit_or_is_unit,
      have := (hs a (multiset.mem_cons.2 (or.inl rfl))),
      cases ((irreducible_of_prime ).is_unit_or_is_unit hu).resolve_left hp.not_unit with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)
-/

lemma no_conj
  (s : multiset ℤ√-3)
  {p : ℤ√-3}
  (hp : ¬ is_unit p)
  (hcoprime : is_coprime s.prod.re s.prod.im) :
  ¬(p ∈ s ∧ p.conj ∈ s) :=
begin
  contrapose! hp,
  obtain ⟨h1, h2⟩ := hp,
  by_cases him : p.im = 0,
  { obtain ⟨t, rfl⟩ := multiset.exists_cons_of_mem h1,
    rw multiset.prod_cons at hcoprime,
    simp only [him, add_zero, zero_mul, zsqrtd.mul_im, zsqrtd.mul_re, mul_zero] at hcoprime,
    rw zsqrt3.is_unit_iff,
    simp only [him, and_true, eq_self_iff_true],
    rw ←int.is_unit_iff_abs,
    apply is_coprime.is_unit_of_dvd' hcoprime; apply dvd_mul_right },
  { have : p.conj ≠ p,
    { rw [ne.def, zsqrtd.ext],
      rintro ⟨-, H⟩,
      apply him,
      apply eq_zero_of_neg_eq,
      rwa [zsqrtd.conj_im] at H },
    obtain ⟨t1, rfl⟩ := multiset.exists_cons_of_mem h1,
    have : p.conj ∈ t1,
    { rw multiset.mem_cons at h2,
      exact h2.resolve_left this },
    obtain ⟨t2, rfl⟩ := multiset.exists_cons_of_mem this,
    rw [multiset.prod_cons, multiset.prod_cons, ←mul_assoc, ←zsqrtd.norm_eq_mul_conj] at hcoprime,
    rw zsqrtd.is_unit_iff_norm_is_unit,
    apply is_coprime.is_unit_of_dvd' hcoprime;
    simp only [add_zero, zsqrtd.coe_int_re, zero_mul, dvd_mul_right, zsqrtd.mul_re, mul_zero,
      zsqrtd.mul_im, zsqrtd.coe_int_im] },
end

/-
lemma exists_associated_mem_of_dvd_prod'''
  {p : ℤ√-3} (hp : odd_prime_or_four p.norm)
  {s : multiset ℤ√-3}
  (helts : ∀ r ∈ s, odd_prime_or_four (zsqrtd.norm r))
  (hdvd : p ∣ s.prod) :
  ∃ q ∈ s, associated p q :=
begin
  obtain ⟨q, hq, h⟩ := exists_associated_mem_of_dvd_prod' hp helts _,
  use [q, hq],
  obtain ⟨u, hu⟩ := h,
  have := is_unit_unit u,
  rw int.is_unit_iff_abs at this,
  have : (u : ℤ) = 1,
  { rw ←this,
    symmetry,
    apply abs_of_nonneg,
    apply nonneg_of_mul_nonneg_left,
    { rw hu, apply zsqrtd.norm_nonneg, norm_num },
    { apply lt_of_le_of_ne _ hp.ne_zero.symm,
      apply zsqrtd.norm_nonneg,
      norm_num } },
  rw [this, mul_one] at hu,
  have := step4_3 p.re p.im q.re q.im _ _ _ _,
  all_goals { sorry } -- not true
end
-/

def associated' (x y : ℤ√-3) : Prop := associated x y ∨  associated x y.conj

@[refl] theorem associated'.refl (x : ℤ√-3) : associated' x x := or.inl (by refl)


lemma associated'.norm_eq
  {x y : ℤ√-3}
  (h : associated' x y) :
  x.norm = y.norm :=
begin
  cases h;
    obtain ⟨u, hu⟩ := h;
    [skip, rw ←zsqrtd.norm_conj y];
    rw [←hu, zsqrtd.norm_mul, zsqrt3.norm_unit (is_unit_unit u), mul_one],
end

lemma int.abs_eq_abs_iff {a b : ℤ} (h : abs a = abs b) : a = b ∨ a = -b :=
begin
  cases int.abs_iff a with h1 h1;
  cases int.abs_iff b with h2 h2;
  rw [h1, h2] at h,
  { left, exact h },
  { right, exact h },
  { right, rwa [eq_neg_iff_eq_neg, eq_comm] },
  { left, rwa [eq_neg_iff_eq_neg, eq_comm, neg_neg] at h },
end

lemma associated'_of_associated_norm {x y : ℤ√-3} (h : associated (zsqrtd.norm x) (zsqrtd.norm y))
  (hx : is_coprime x.re x.im)
  (hy : is_coprime y.re y.im)
  (h' : odd_prime_or_four (x.re ^ 2 + 3 * x.im ^ 2)) :
  associated' x y :=
begin
  by_cases hx' : x = 0,
  { subst x,
    simp only [zsqrtd.norm_zero] at h,
    obtain ⟨u, hu⟩ := h,
    rw zero_mul at hu,
    rw eq_comm at hu,
    rw zsqrt3.norm_eq_zero_iff at hu,
    rw hu },
  rw [←zsqrt3.norm_eq_zero_iff, ←ne.def] at hx',
  obtain ⟨u, hu⟩ := h,
  have := is_unit_unit u,
  rw int.is_unit_iff_abs at this,
  have : (u : ℤ) = 1,
  { rw ←this,
    symmetry,
    apply abs_of_nonneg,
    apply nonneg_of_mul_nonneg_left,
    { rw hu, apply zsqrtd.norm_nonneg, norm_num },
    { apply lt_of_le_of_ne _ hx'.symm,
      apply zsqrtd.norm_nonneg,
      norm_num } },
  rw [this, mul_one, zsqrt3.norm, zsqrt3.norm] at hu,
  have := step4_3 x.re x.im y.re y.im hx hy h' hu,
  cases int.abs_eq_abs_iff this.1 with h1 h1;
  cases int.abs_eq_abs_iff this.2 with h2 h2,
  { left, use 1, simp only [mul_one, units.coe_one], rw zsqrtd.ext, exact ⟨h1, h2⟩ },
  { right, use 1, simp only [mul_one, units.coe_one], rw [zsqrtd.ext, zsqrtd.conj_re, zsqrtd.conj_im], exact ⟨h1, h2⟩ },
  { right, use -1, simp only [mul_one, units.coe_neg_one, mul_neg_eq_neg_mul_symm],
    rw [zsqrtd.ext, zsqrtd.conj_re, zsqrtd.conj_im],
    simp only [zsqrtd.neg_im, zsqrtd.neg_re, neg_inj],
    rwa [neg_eq_iff_neg_eq, eq_comm], exact ⟨h1, h2⟩ },
  { left, use -1, simp only [mul_one, units.coe_neg_one, mul_neg_eq_neg_mul_symm],
    rw [neg_eq_iff_neg_eq, eq_comm], rw [zsqrtd.ext, zsqrtd.neg_im, zsqrtd.neg_re], exact ⟨h1, h2⟩ },
end

lemma prod_norm_eq_prod_mul_prod_conj {d : ℤ} (f : multiset ℤ√d) :
  f.prod * (f.map zsqrtd.conj).prod = (f.map zsqrtd.norm).prod :=
begin
  refine multiset.induction_on f _ _,
  { simp only [mul_one, int.cast_one, multiset.prod_zero, multiset.map_zero] },
  { intros x t ih,
    simp only [multiset.map_cons, multiset.prod_cons, int.cast_mul],
    rw [zsqrtd.norm_eq_mul_conj, ←ih],
    ring },
end

lemma prod_norm_eq_prod_mul_prod_conj' {d : ℤ} (f : multiset ℤ√d) :
  f.prod * f.prod.conj = (f.map zsqrtd.norm).prod :=
begin
  refine multiset.induction_on f _ _,
  { simp only [mul_one, int.cast_one, multiset.prod_zero, multiset.map_zero, zsqrtd.conj_one] },
  { intros x t ih,
    simp only [multiset.map_cons, multiset.prod_cons, int.cast_mul, zsqrtd.conj_mul],
    rw [zsqrtd.norm_eq_mul_conj, ←ih],
    ring },
end

lemma eq_of_associated_of_nonneg {a b : ℤ} (h : associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b :=
begin
  by_cases ha' : a = 0,
  { subst a, replace h := associated.symm h, rw [associated_zero_iff_eq_zero] at h, exact h.symm },
  { obtain ⟨u, hu⟩ := h,
    rw ←hu,
    have := is_unit_unit u,
    rw int.is_unit_iff_abs at this,
    rw abs_of_nonneg _ at this,
    rw [this, mul_one],

    apply nonneg_of_mul_nonneg_left,
    { rwa hu },
    { apply lt_of_le_of_ne ha, symmetry, exact ha' } }
end

lemma factors_unique : ∀{f g : multiset ℤ√-3},
  (∀x∈f, odd_prime_or_four (zsqrtd.norm x)) →
  (∀x∈f, is_coprime (zsqrtd.re x) (zsqrtd.im x)) →
  (∀x∈g, odd_prime_or_four (zsqrtd.norm x)) →
  (∀x∈g, is_coprime (zsqrtd.re x) (zsqrtd.im x)) →
  (associated f.prod g.prod) →
  multiset.rel associated' f g :=
by {
  intros f g hf hf' hg hg' h,
  have : f.prod.norm  = g.prod.norm,
  {
    apply eq_of_associated_of_nonneg _ (zsqrtd.norm_nonneg _ _) (zsqrtd.norm_nonneg _ _),
    obtain ⟨u, hu⟩ := h,
    rw ←hu,
    simp only [zsqrtd.norm_mul],
    have := is_unit_unit u,
    rw zsqrtd.is_unit_iff_norm_is_unit at this,
    obtain ⟨u', hu'⟩ := this,
    use [u'],
    rw hu',

    norm_num,
    norm_num,
  },
  have : associated f.prod.norm g.prod.norm,
  { rw this },
  have := factors_unique_prod hf hg this,
  --rw multiset.rel_map
  have p : ∀
    (x : ℤ√-3) (hx : x ∈ f)
    (y : ℤ√-3) (hy : y ∈ g),
      associated x.norm y.norm → associated' x y,
  { intros x hx y hy h,
    apply associated'_of_associated_norm h,
    { exact hf' x hx },
    { exact hg' y hy },
    { rw ←zsqrt3.norm, exact hf x hx } },
/-
  have p : ∀
    (x : ℤ√-3) (hx : x ∈ f)
    (y : ℤ√-3) (hy : y ∈ g),
      associated x.norm y.norm ∧ is_coprime x.re x.im ∧ is_coprime y.re y.im ∧
      odd_prime_or_four (x.re ^ 2 + 3 * x.im ^ 2) → associated' x y,
  { intros x hx y hy h,
    exact associated'_of_associated_norm h.1 h.2.1 h.2.2.1 h.2.2.2 },
-/
  refine multiset.rel.mono' p _,
  -- TODO lemma multiset.rel_map_iff
  rwa [multiset.rel_map_left, multiset.rel_map_right] at this,
  /-
  clear p,
  revert f g,
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - - - - - - - h4,
    change multiset.rel associated (multiset.map zsqrtd.norm 0) (multiset.map zsqrtd.norm g) at h4, -- TODO rm
    simp only [multiset.rel_zero_left, multiset.map_eq_zero, multiset.map_zero] at h4,
    rwa multiset.rel_zero_left },
  { intros p f ih g hf hf' hg hg' hfg h1 h2 h3,
    have hp : odd_prime_or_four p.norm := hf p (by simp only [multiset.mem_cons_self]),
    have hprimeing : ∀ q, q ∈ g → odd_prime_or_four (zsqrtd.norm q)
      := (λ q hq, (hg _ hq)),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    have : p.norm ∣ (multiset.map zsqrtd.norm g).prod,
    { rw prod_map_norm,
      obtain ⟨x, hx⟩ := hdvd, -- TODO lemma
      rw [hx, zsqrtd.norm_mul],
      apply dvd_mul_right },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod' hp hprimeing this,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons _,
    { have h5 : associated f.prod.norm (g.erase b).prod.norm,
      { apply associated_mul_left_cancel _ hb hp.ne_zero,
        rw [←prod_map_norm, ←multiset.prod_cons, ←multiset.map_cons, prod_map_norm, h1,
          ←zsqrtd.norm_mul, ←multiset.prod_cons, multiset.cons_erase hbg] },
      apply ih,
      all_goals { clear ih }, -- TODO remove
      { exact (λ q hq, hf _ (multiset.mem_cons_of_mem hq)) },
      { intros x H, apply hf' _ (multiset.mem_cons_of_mem H), },
      { exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))},
      { intros x H, apply hg' _ (multiset.mem_of_mem_erase H), },
      { change associated f.prod (g.erase b).prod,
        sorry },
      { apply eq_of_associated_of_nonneg h5,
        { apply zsqrtd.norm_nonneg, norm_num },
        { apply zsqrtd.norm_nonneg, norm_num } },
      { exact h5 },
      { change  multiset.rel associated (multiset.map zsqrtd.norm f) (multiset.map zsqrtd.norm (g.erase b)),
        sorry } },
    { exact hb } },
  -/
/-
  refine multiset.rel.mono' p _,
  clear p,
  revert f g,
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - - - - - h4,
    simp only [multiset.rel_zero_left, multiset.map_eq_zero, multiset.map_zero] at h4,
    rwa multiset.rel_zero_left },
  { intros p f ih g hf hg hfg h1 h2 h3,
    have hp : odd_prime_or_four p.norm := hf p (by simp only [multiset.mem_cons_self]),
    have hprimeing : ∀ q, q ∈ g → odd_prime_or_four (zsqrtd.norm q)
      := (λ q hq, (hg _ hq)),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    have : p.norm ∣ (multiset.map zsqrtd.norm g).prod,
    { rw prod_map_norm,
      obtain ⟨x, hx⟩ := hdvd, -- TODO lemma
      rw [hx, zsqrtd.norm_mul],
      apply dvd_mul_right },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod' hp hprimeing this,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons _,
    { have h5 : associated f.prod.norm (g.erase b).prod.norm,
      { apply associated_mul_left_cancel _ hb hp.ne_zero,
        rw [←prod_map_norm, ←multiset.prod_cons, ←multiset.map_cons, prod_map_norm, h1,
          ←zsqrtd.norm_mul, ←multiset.prod_cons, multiset.cons_erase hbg] },
      apply ih,
      all_goals { clear ih }, -- TODO remove
      {exact (λ q hq, hf _ (by simp [hq]))},
      {exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))},
      { change associated f.prod (g.erase b).prod,
        sorry },
      { apply eq_of_associated_of_nonneg h5,
        { apply zsqrtd.norm_nonneg, norm_num },
        { apply zsqrtd.norm_nonneg, norm_num } },
      { exact h5 },
      { change  multiset.rel associated (multiset.map zsqrtd.norm f) (multiset.map zsqrtd.norm (g.erase b)),
        sorry } },
    { change associated p.norm b.norm ∧ is_coprime p.re p.im ∧ is_coprime b.re b.im ∧ odd_prime_or_four (p.re ^ 2 + 3 * p.im ^ 2),
      sorry } },
-/
/-
  { intros p f ih g hf hg hfg h1 h2,
    have hp := hf p (by simp only [multiset.mem_cons_self]),
    have hprimeing : ∀ q, q ∈ g → odd_prime_or_four (zsqrtd.norm q)
      := (λ q hq, (hg _ hq)),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    have : p.norm ∣ (multiset.map zsqrtd.norm g).prod,
    { rw prod_map_norm,
      obtain ⟨x, hx⟩ := hdvd, -- TODO lemma
      rw [hx, zsqrtd.norm_mul],
      apply dvd_mul_right },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod' hp hprimeing this,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons _,
    apply ih,
    exact (λ q hq, hf _ (by simp [hq])),
    exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)),
    { sorry },
    { apply associated_mul_left_cancel _ hb hp.ne_zero,
      convert h1,
      { simp only [multiset.prod_cons, zsqrtd.norm_mul] },
      { rw [←zsqrtd.norm_mul, ←multiset.prod_cons, multiset.cons_erase hbg] } }
  },
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw multiset.rel_zero_left,
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    have : is_unit g.prod,
    { simpa [associated_one_iff_is_unit] using h.symm },
    apply (hg x hx).not_unit,
    rw ←zsqrtd.is_unit_iff_norm_is_unit,
    rw is_unit_iff_dvd_one,
    apply dvd.trans,
    { have := multiset.dvd_prod hx, exact this },
    { rw ←is_unit_iff_dvd_one,
      exact this,
    }, },
  { intros p f ih g hf hg hfg,
    have hp := hf p (by simp only [multiset.mem_cons_self]),
    --have hprime : prime p := (unique_factorization_monoid.irreducible_iff_prime.1 (hf p (by simp))),
    have hprimeing : ∀ q, q ∈ g → _
      := (λ q hq, (hg _ hq)),
    have hdvd : p ∣ g.prod := ((dvd_iff_dvd_of_rel_right hfg).1
            (show p ∣ (p ::ₘ f).prod, by simp)),
    have : p.norm ∣ (multiset.map zsqrtd.norm g).prod,
    { rw prod_map_norm,
      obtain ⟨x, hx⟩ := hdvd, -- TODO lemma
      rw [hx, zsqrtd.norm_mul],
      apply dvd_mul_right },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod' hp hprimeing this,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons _,
    apply ih,
    exact (λ q hq, hf _ (by simp [hq])),
    exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)),
    { have := associated_mul_left_cancel,
    },
    exact (associated_mul_left_cancel
        (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
      (hf p (by simp)).ne_zero),
          },
-/
}

/-
lemma step4'
  (a b : ℤ)
  (hcoprime : is_coprime a b)
  (p q : ℤ)
  (hdvd : p ^ 2 + 3 * q ^ 2 ∣ a ^ 2 + 3 * b ^ 2)
  : ∃ p' : ℤ√-3, p' ∈ factorization hcoprime ∧ associated' p' ⟨p, q⟩ :=
begin
  set f := factorization hcoprime,
  obtain ⟨x, hx⟩ := hdvd,
  obtain ⟨u, v, huvcoprime, hab, hdvd'⟩ := step1_2' ⟨a, b⟩ ⟨p, q⟩ hcoprime _ _ _,
  --obtain ⟨g, hgprod, hgmem⟩ := step3 _ _ hcoprime, = factorization
  --associated'_of_associated_norm,
  have := factors_unique,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,

end
-/

/-
lemma step4
  (a b : ℤ)
  (hcoprime : is_coprime a b)
  :
  ∃ f : multiset ℤ√-3,
    ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
  :=
begin
  obtain ⟨f, h1, h2⟩ := step3 hcoprime,
  have : a ^ 2 + 3 * b ^ 2 = f.prod.norm,
  { cases h1; rw [zsqrt3.norm', h1],
    rw zsqrtd.norm_neg },
  rw ←prod_map_norm at this,
  sorry,
end
-/
/-
lemma mul_coprime
(x y : ℤ√-3) 
(n: ℕ)
(hx : is_coprime x.re x.im)
(hy : is_coprime y.re y.im)
: is_coprime (x * y).re (x * y).im :=
begin
  simp only [neg_mul_eq_neg_mul_symm, zsqrtd.mul_im, zsqrtd.mul_re],
end

lemma mul_coprime'
(x : ℤ√-3) 
(n: ℕ)
(hx : is_coprime x.re x.im)
: is_coprime (x * x).re (x * x).im :=
begin
  simp only [neg_mul_eq_neg_mul_symm, zsqrtd.mul_im, zsqrtd.mul_re],
  have := is_coprime.mul_left hx hx,
  have := is_coprime.mul_right this this,
  have := is_coprime.mul_add_right_left this (-3),
  simp [is_coprime] at *,
end

lemma pow_coprime
(x: ℤ√-3) 
(n: ℕ)
(h : is_coprime x.re x.im) :
is_coprime (x ^ n).re (x ^ n).im :=
begin
  induction n,
  sorry,
  rw pow_succ',
end

lemma factors_pow
(x: ℤ√-3) 
(n: ℕ):
 factorization (x ^ n) = n •ℕ factorization x :=

-/

noncomputable def odd_factors (x : ℤ) := multiset.filter odd (unique_factorization_monoid.factors x)

lemma odd_factors.not_two_mem (x : ℤ) : (2 : ℤ) ∉ odd_factors x :=
begin
  simp only [odd_factors, int.even_bit0, not_true, not_false_iff, int.odd_iff_not_even,
    and_false, multiset.mem_filter],
end


noncomputable def even_factor_exp (x : ℤ) := multiset.count 2 (unique_factorization_monoid.factors x)

lemma even_factor_exp.def (x : ℤ) : even_factor_exp x = multiset.count 2 (unique_factorization_monoid.factors x) := rfl

lemma even_and_odd_factors'' (x : ℤ) :
  unique_factorization_monoid.factors x = (unique_factorization_monoid.factors x).filter (eq 2) + odd_factors x :=
begin
  by_cases hx : x = 0,
  { -- todo: lemma even_factor_exp 0 = 0, odd_factors 0 = 0
    simp only [hx, odd_factors, multiset.filter_zero, add_zero,
      unique_factorization_monoid.factors_zero] },
  simp [even_factor_exp, odd_factors],
  rw multiset.filter_add_filter,
  convert (add_zero _).symm,
  { rw multiset.filter_eq_self,
    intros a ha,
    have hprime : prime a := unique_factorization_monoid.prime_of_factor a ha,
    have := unique_factorization_monoid.normalize_factor a ha,
    rw ←int.coe_nat_abs_eq_normalize at this,
    rw ←this at hprime,
    rw ←this,
    norm_cast,
    rw [eq_comm, nat.odd_iff],
    apply nat.prime.eq_two_or_odd,
    exact nat.prime_iff_prime_int.mpr hprime },
  { rw multiset.filter_eq_nil,
    rintros a ha ⟨rfl, hodd⟩,
    norm_num at hodd,
    exact hodd },
end

lemma even_and_odd_factors' (x : ℤ) :
  unique_factorization_monoid.factors x = multiset.repeat 2 (even_factor_exp x) + odd_factors x :=
begin
  convert even_and_odd_factors'' x,
  simp [even_factor_exp],
  ext a,
  by_cases ha : a = 2,
  { simp only [ha, multiset.count_repeat_self, multiset.count_filter_of_pos] },
  { rw [multiset.count_filter_of_neg (ne.symm ha)],
    simp only [multiset.count_eq_zero],
    contrapose! ha,
    exact multiset.eq_of_mem_repeat ha }
end

lemma even_and_odd_factors (x : ℤ) (hx : x ≠ 0) : associated x (2 ^ (even_factor_exp x) * (odd_factors x).prod) :=
begin
  convert (unique_factorization_monoid.factors_prod hx).symm,
  simp [even_factor_exp, odd_factors],
  rw [multiset.pow_count, ←multiset.prod_add],
  congr,
  symmetry,
  exact even_and_odd_factors'' x,
end

lemma int.nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
calc 0 ≤ (z.nat_abs : ℤ) : int.coe_zero_le _
... = normalize z : int.coe_nat_abs_eq_normalize _
... = z : hz

lemma int.factors_nonneg {z a : ℤ} (ha : a ∈ unique_factorization_monoid.factors z) : 0 ≤ a :=
int.nonneg_of_normalize_eq_self (unique_factorization_monoid.normalize_factor a ha)

/-
  have : (unique_factorization_monoid.factors z).filter (λ x, 0 ≤ x) = (unique_factorization_monoid.factors z),
  { rw multiset.filter_eq_self,
    intros a ha,
    exact int.factors_nonneg ha },
-/

lemma int.factors_eq' (z : ℤ) :
  ((unique_factorization_monoid.factors z).map int.nat_abs).map (coe : ℕ → ℤ)
  = unique_factorization_monoid.factors z :=
begin
  conv_rhs { rw ←multiset.map_id (unique_factorization_monoid.factors z) },
  rw multiset.map_map,
  apply multiset.map_congr,
  intros x hx,
  rw [id.def, function.comp_app, int.nat_abs_of_nonneg (int.factors_nonneg hx)],
end

--lemma int.factors_eq'' (z : ℤ) : (unique_factorization_monoid.factors z).map int.nat_abs = 

lemma int.factors_eq (z : ℤ) :
  unique_factorization_monoid.factors z = multiset.map (int.of_nat_hom) (nat.factors z.nat_abs) :=
begin
  --have := nat.factors_eq,
  rw ←nat.factors_eq,
  rw ←multiset.rel_eq,
  have : multiset.rel associated (unique_factorization_monoid.factors z) (multiset.map (int.of_nat_hom : ℕ →* ℤ) (unique_factorization_monoid.factors z.nat_abs)),
  { apply prime_factors_unique,
    { exact unique_factorization_monoid.prime_of_factor },
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      simp only [ring_hom.coe_monoid_hom, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
      rw [←nat.prime_iff_prime_int, ←irreducible_iff_nat_prime],
      exact unique_factorization_monoid.irreducible_of_factor _ hy },
    { by_cases hz: z = 0,
      { simp only [hz, unique_factorization_monoid.factors_zero, multiset.map_zero, int.nat_abs_zero] },
      apply associated.trans (unique_factorization_monoid.factors_prod hz),
      have : associated z z.nat_abs,
      { rw int.associated_iff, simp only [int.nat_abs_of_nat] },
      apply associated.trans this,
      rw multiset.prod_hom,
      simp only [ring_hom.coe_monoid_hom, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
      rw int.associated_iff,
      simp only [int.nat_abs_of_nat],
      rw ←associated_iff_eq,
      exact (unique_factorization_monoid.factors_prod (int.nat_abs_ne_zero_of_ne_zero hz)).symm } },
  apply multiset.rel.mono' _ this,
  intros a ha b hb hab,
  apply eq_of_associated_of_nonneg hab,
  { exact int.factors_nonneg ha },
  { obtain ⟨b', hb', rfl⟩ := multiset.mem_map.mp hb,
    simp only [ring_hom.coe_monoid_hom, int.coe_nat_nonneg, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat] },
end

lemma factors_2_even {z : ℤ} (hz : z ≠ 0) : even_factor_exp (4 * z) = 2 + even_factor_exp z :=
begin
  simp [even_factor_exp],
  rw unique_factorization_monoid.factors_mul (by norm_num : (4 : ℤ) ≠ 0) hz,
  rw multiset.count_add,
  congr,
  rw int.factors_eq,
  have : [2, 2] ~ nat.factors (int.nat_abs 4),
  { apply nat.factors_unique,
    { norm_num, norm_cast },
    intros p hp,
    convert nat.prime_two,
    rw [list.mem_cons_iff, list.mem_cons_iff] at hp,
    simp only [list.not_mem_nil, or_false, or_self] at hp,
    exact hp, },
  rw ←multiset.coe_eq_coe at this,
  rw ←this,
  simp only [multiset.coe_map, int.coe_nat_zero, zero_add, ring_hom.eq_nat_cast,
    int.nat_cast_eq_coe_nat, list.map, multiset.coe_count],
  dec_trivial,
end

lemma unique_factorization_monoid.dvd_of_mem_factors
  {α : Type*}
  [comm_cancel_monoid_with_zero α] [decidable_eq α] [nontrivial α] [normalization_monoid α]
  [unique_factorization_monoid α]
  {a p : α}
  (hm : p ∈ unique_factorization_monoid.factors a) : p ∣ a :=
begin
  by_cases ha : a = 0,
  { simp only [ha, dvd_zero] },
  apply dvd_trans (multiset.dvd_prod hm),
  apply dvd_of_associated,
  exact unique_factorization_monoid.factors_prod ha,
end

lemma factors_2_even' (a b : ℤ) (hcoprime : is_coprime a b) : even (even_factor_exp (a ^ 2 + 3 * b ^ 2)) :=
begin
  suffices : ∀ n : ℕ, a^2 + 3 * b ^ 2 = n → even (even_factor_exp n),
  { have h := (int.nat_abs_of_nonneg (spts.nonneg a b)).symm,
    convert this (a^2 + 3 * b ^ 2).nat_abs h },
  intros n hn,
  induction n using nat.strong_induction_on with n ih generalizing a b,
  dsimp only at ih,
  by_cases hparity : even (a ^ 2 +3 * b ^ 2),
  { obtain ⟨u, v, huvcoprime, -, huvprod⟩ := step1' a b hcoprime hparity,
    set m := (u ^ 2 + 3 * v ^ 2).nat_abs with hm,
    have hm' : (m : ℤ) = u ^ 2 + 3 * v ^ 2 := int.nat_abs_of_nonneg (spts.nonneg u v),
    rw [←hn, huvprod, factors_2_even (spts.not_zero_of_coprime huvcoprime), nat.even_add, ←hm'],
    apply iff_of_true (dvd_refl _),
    apply ih _ _ u v huvcoprime hm'.symm,
    zify,
    rw [hm', ←hn, huvprod],
    apply int.lt_mul_self (spts.pos_of_coprime huvcoprime),
    norm_num },
  { rw hn at hparity,
    convert nat.even_zero, 
    simp [even_factor_exp],
    contrapose! hparity with hfactor,
    exact unique_factorization_monoid.dvd_of_mem_factors hfactor }
end

/-
lemma factors_odd (a b : ℤ)
  (hcoprime : is_coprime a b)
  (p : ℤ)
  (hprime : prime p)
  (hp : odd p) :
  multiset.count p (unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2)) = 
  multiset.count p ((factorization a b hcoprime).map zsqrtd.norm) :=
begin
  set f := factorization a b hcoprime,
  have : ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
    := classical.some_spec (step3 hcoprime),
  set f' := multiset.filter (λ pq : ℤ√-3, odd pq.norm) f,
  set g := unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2),
  set g' := multiset.filter odd g,
  have h0 : multiset.count p g = multiset.count p g',
  { rw multiset.count_filter_of_pos hp },
  have h1 : multiset.count p (multiset.map zsqrtd.norm f) = multiset.count p (multiset.map zsqrtd.norm f'),
  { rw ←multiset.map_filter,
    rw multiset.count_filter_of_pos hp, },
  rw [h0, h1],
end

lemma factors_four (a b : ℤ)
  (hcoprime : is_coprime a b) :
  multiset.count 2 (unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2)) = 
  2 * multiset.count 4 ((factorization a b hcoprime).map zsqrtd.norm) :=
begin
  set f := factorization a b hcoprime,
  have : ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧ -- <?
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
    := classical.some_spec (step3 hcoprime),
  rw [even_and_odd_factors' _, multiset.count_add,
    multiset.count_repeat_self,
    multiset.count_eq_zero_of_not_mem (odd_factors.not_two_mem _), add_zero],
  obtain ⟨n, hn⟩ := factors_2_even' a b hcoprime,
  rw hn,
  rw mul_right_inj',
  set f' := multiset.filter (λ pq : ℤ√-3, odd pq.norm) f,
  set g := unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2),
  set g' := multiset.filter odd g,
end
-/

-- most useful with  (hz : even (even_factor_exp z))
noncomputable def factors_odd_prime_or_four (z : ℤ) : multiset ℤ :=
multiset.repeat 4 (even_factor_exp z / 2) + odd_factors z

/-
noncomputable def factors_odd_prime_or_four
  (a b : ℤ)
  (hcoprime : is_coprime a b) : multiset ℤ :=
  multiset.repeat 4 ((multiset.count 2 (unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2))) / 2) +
  odd_factors (a ^ 2 + 3 * b ^ 2)
-/

/-
lemma factors_odd_prime_or_four.one_le
  (a b : ℤ)
  (hcoprime : is_coprime a b) :
  1 ≤ (factors_odd_prime_or_four a b hcoprime).prod :=
begin
  simp only [factors_odd_prime_or_four],
  apply @multiset.one_le_prod_of_one_le ℤ _,
end
-/

lemma factors_odd_prime_or_four.nonneg {z a : ℤ} (ha : a ∈ factors_odd_prime_or_four z) : 0 ≤ a :=
begin
  simp only [factors_odd_prime_or_four, multiset.mem_add] at ha,
  cases ha,
  { rw multiset.eq_of_mem_repeat ha, norm_num },
  { simp only [odd_factors, multiset.mem_filter] at ha,
    exact int.factors_nonneg ha.1 }
end

lemma factors_odd_prime_or_four.prod
  {a b : ℤ}
  (hcoprime : is_coprime a b) :
  (factors_odd_prime_or_four (a ^ 2 + 3 * b ^ 2)).prod = a ^ 2 + 3 * b ^ 2 :=
begin
  apply eq_of_associated_of_nonneg,
  { have := unique_factorization_monoid.factors_prod (spts.not_zero_of_coprime hcoprime),
    apply associated.trans _ this,
    rw [even_and_odd_factors' _, multiset.prod_add],
    simp [factors_odd_prime_or_four],
    apply associated_mul_mul,
    { obtain ⟨m, hm⟩ := factors_2_even' a b hcoprime,
      rw [hm, nat.mul_div_right _ zero_lt_two, pow_mul],
      refl },
    { refl } },
  { apply multiset.prod_nonneg,
    apply factors_odd_prime_or_four.nonneg },
  { exact spts.nonneg _ _ },
end

lemma factors_odd_prime_or_four.associated
  {a b : ℤ}
  (hcoprime : is_coprime a b)
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hassoc : associated f.prod (a ^ 2 + 3 * b ^ 2)) :
  multiset.rel associated f (factors_odd_prime_or_four (a ^ 2 + 3 * b ^ 2)) :=
begin
  apply factors_unique_prod' hf,
  { intros x hx,
    simp only [factors_odd_prime_or_four, multiset.mem_add] at hx,
    cases hx,
    { left, exact multiset.eq_of_mem_repeat hx },
    { right,
      simp only [odd_factors, multiset.mem_filter] at hx,
      exact and.imp_left (unique_factorization_monoid.prime_of_factor _) hx } },
  { rwa factors_odd_prime_or_four.prod hcoprime }
end

lemma factors_odd_prime_or_four.unique
  {a b : ℤ}
  (hcoprime : is_coprime a b)
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hf' : ∀x∈f, (0 : ℤ) ≤ x)
  (hassoc : associated f.prod (a ^ 2 + 3 * b ^ 2)) :
  f = (factors_odd_prime_or_four (a ^ 2 + 3 * b ^ 2)) :=
begin
  rw ←multiset.rel_eq,
  apply multiset.rel.mono' _ (factors_odd_prime_or_four.associated hcoprime hf hassoc),
  intros x hx y hy hxy,
  exact eq_of_associated_of_nonneg hxy (hf' x hx) (factors_odd_prime_or_four.nonneg hy)
end

lemma even_factor_exp.pow (z : ℤ) (n : ℕ) : even_factor_exp (z ^ n) = n * even_factor_exp z :=
begin
  simp only [even_factor_exp],
  rw [unique_factorization_monoid.factors_pow, multiset.count_smul]
end

lemma factors_odd_prime_or_four.pow
  (z : ℤ) (n : ℕ) (hz : even (even_factor_exp z)) :
  factors_odd_prime_or_four (z ^ n) = n •ℕ factors_odd_prime_or_four z :=
begin
  simp only [factors_odd_prime_or_four, nsmul_add],
  congr,
  { rw multiset.nsmul_repeat,
    congr,
    rw even_factor_exp.pow,
    obtain ⟨m, hm⟩ := hz,
    rw [hm],
    by_cases hm' : m = 0,
    { simp only [hm', nat.zero_div, mul_zero] },
    have := pos_iff_ne_zero.mpr hm',
    calc n * (2 * m) / 2 = 2 * (n * m) / 2 : by { congr' 1, ring }
    ... = n * m : nat.mul_div_right (n * m) zero_lt_two
    ... = n * (2 * m / 2) : by rw nat.mul_div_right m zero_lt_two },
  {
    simp only [odd_factors],
    rw unique_factorization_monoid.factors_pow,
    rw multiset.nsmul_filter,
  },
end

lemma multiset.xxz
  {α β : Type*}
  [decidable_eq α]
  {f : α → β}
  {s : multiset α}
  (a : α)
  (h' : (∀ b ∈ s, b = a))
  (h : ∀ x ∈ s, 3 ∣ multiset.count x s) :
  ∃ t : multiset α, s = 3 •ℕ t :=
begin
  by_cases ha : a ∈ s,
  { have h1 := multiset.eq_repeat_of_mem h',
    have h2 : multiset.card s = multiset.count a s,
    { conv_rhs { rw h1 },
      rw multiset.count_repeat_self },
    obtain ⟨n, hn⟩ := h a ha,
    rw hn at h2,
    use multiset.repeat a n,
    rw h1,
    rw multiset.nsmul_repeat,
    congr,
    exact h2 },
  { use 0,
    simp only [nsmul_zero],
    apply multiset.eq_zero_of_forall_not_mem,
    intros b hb,
    obtain rfl := h' b hb,
    contradiction },
end

lemma multiset.xxy
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (h : ∀ x ∈ s, 3 ∣ multiset.count x s) :
  ∃ t : multiset α, s = 3 •ℕ t :=
begin
  revert h,
  refine s.strong_induction_on _,
--  { intros t h, use 0, simp only [nsmul_zero]},
  intros s ih h,
  change ∀ v, _ at ih,
  by_cases ht : s = 0,
  { use 0, simp only [nsmul_zero, ht] },
  obtain ⟨b, hb⟩ := multiset.exists_mem_of_ne_zero ht,
--  rw [←multiset.mem_nsmul three_ne_zero] at ha,
  --, ←h, multiset.mem_map] at ha,
  --obtain ⟨b, hb, rfl⟩ := ha,

  set q := s.filter (ne b) with hq,
  have : q < s,
  { rw hq, apply lt_of_le_of_ne, simp only [multiset.filter_le],
    intro H,
    rw multiset.filter_eq_self at H,
    exact H b hb rfl },
  obtain ⟨r, hr⟩ := ih q this _,
--  rw hq at hr,

  set d := multiset.repeat b (multiset.count b s) with hd,

  have hd' : d = s.filter (eq b),
  { rw hd,
  
    ext a,
    rw multiset.count_repeat,
    split_ifs with ha,
    { subst a,
      rw multiset.count_filter_of_pos rfl, },
    { rw multiset.count_filter_of_neg (ne.symm ha) } },

  have : s = d + q,
  { rw [hd', hq],
    rw multiset.filter_add_filter,
    convert (add_zero _).symm,
    { rw multiset.filter_eq_self, exact λ x hx, em _ },
    { rw multiset.filter_eq_nil,
      rintros x hx ⟨h1, h2⟩,
      exact h2 h1 } },
  -- multiset.pow_count
  rw hr at this,
  obtain ⟨k, hk⟩ := h b hb,
  rw hk at hd,
  rw ←multiset.nsmul_repeat at hd,
  rw hd at this,
  rw ←nsmul_add at this,
  exact ⟨_, this⟩,

  intros x hx,
  rw hq,
  rw multiset.count_filter_of_pos,
  apply h,
  rw hq at hx,
  exact multiset.mem_of_mem_filter hx,
  exact multiset.of_mem_filter hx,
end
/-
lemma multiset.xx
  {α β : Type*}
  [decidable_eq α]
  {f : α → β}
  {s : multiset α}
  {t : multiset β}
  (n : ℕ)
  (h : multiset.map f s = n •ℕ t) :
  ∃ u : multiset α, s = n •ℕ u :=
begin
  -- FALSE unless f injective
  sorry,
/-
/-
  induction n with n ih generalizing s t,
  { simpa only [zero_nsmul, exists_const, multiset.map_eq_zero] using h },
  rw nat.succ_eq_add_one at *,
-/
  revert t,
  refine s.strong_induction_on _,
--  { intros t h, use 0, simp only [nsmul_zero]},
  intros s ih t h,
  change ∀ v, _ → ∀ w, _ at ih,
  by_cases ht : t = 0,
  { sorry },
  obtain ⟨a, ha⟩ := multiset.exists_mem_of_ne_zero ht,
  rw [←multiset.mem_nsmul, ←h, multiset.mem_map] at ha,
  obtain ⟨b, hb, rfl⟩ := ha,

  set q := s.filter (ne b) with hq,
  have : q < s,
  { rw hq, apply lt_of_le_of_ne, simp only [multiset.filter_le],
    intro H,
    rw multiset.filter_eq_self at H,
    exact H b hb rfl },
  have := ih q this,
  obtain ⟨r, hr⟩ := this _ _,
  rw hq at hr,

  set d := multiset.repeat b (multiset.count b s),


  set q := s.erase b with hq,
  have : q < s,
  { rw hq, simp only [multiset.erase_lt], exact hb },
  have := ih q this,
  obtain ⟨r, hr⟩ := this _ _,
  rw hq at hr,
  


  obtain ⟨q, rfl⟩ := multiset.exists_cons_of_mem hb,
  clear hb,
  have := ih q _,
  rw [multiset.mem_nsmul] at hb,
  cases n,
  { simp only [imp_self, zero_nsmul, multiset.map_eq_zero, forall_true_iff, exists_const] at *, exact h },
  rw nat.succ_eq_add_one at *,
  simp_rw [succ_nsmul] at *,
-/
end
-/

-- TODO generalize n
lemma zsqrtd.int_dvd_iff (z : ℤ) (a : ℤ√-3) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im :=
begin
  split,
  { rintro ⟨d, rfl⟩,
    simp only [add_zero, zsqrtd.coe_int_re, zero_mul, zsqrtd.mul_im, dvd_mul_right, and_self,
      zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] },
  { rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩,
    use ⟨r, i⟩,
    rw [zsqrtd.ext, zsqrtd.smul_val],
    exact ⟨hr, hi⟩ },
end 

section
variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}
lemma multiset.count_map (b : β )
  [decidable_eq β]
  (f : α → β) :
  multiset.count b (s.map f) = multiset.countp (λ x, f x = b) s :=
begin
  refine s.induction_on _ _,
  { simp only [multiset.countp_zero, multiset.count_zero, multiset.map_zero] },
  { intros a ha ih,
    simp only [multiset.map_cons],
    by_cases hb : f a = b,
    { simp only [hb, add_left_inj, multiset.countp_cons_of_pos, multiset.count_cons_self, ih] },
    { rw [multiset.count_cons_of_ne (ne.symm hb)],
      simp only [hb, ih, multiset.countp_cons_of_neg, not_false_iff] } },
end

-- TODO: should be countp_congr?
lemma multiset.countp_eq (p1 p2 : α → Prop)
  [decidable_pred p1] [decidable_pred p2]
  (h : ∀ x ∈ s, p1 x ↔ p2 x) :
  multiset.countp p1 s = multiset.countp p2 s :=
begin
  revert h,
  refine s.induction_on _ _,
  { rintro -, simp only [multiset.countp_zero] },
  { intros a t ih h,
    specialize ih _,
    { by_cases ha1 : p1 a,
      { have ha2 : p2 a,
        { rwa ←h a (multiset.mem_cons_self a t) },
        simp only [ha1, ha2, multiset.countp_cons_of_pos, ih] },
      { have ha2 : ¬p2 a,
        { rwa ←h a (multiset.mem_cons_self a t) },
        rw [multiset.countp_cons_of_neg _ ha1, multiset.countp_cons_of_neg _ ha2, ih] } },
    -- todo move up for new mathlib
    { intros x hx,
      apply h,
      rw multiset.mem_cons,
      right,
      assumption } },
end

end

lemma step5' -- lemma page 54
  (a b r : ℤ)
  (hcoprime : is_coprime a b)
  (hcube : r ^ 3 = a ^ 2 + 3 * b ^ 2) :
  ∃ g : multiset ℤ√-3, factorization hcoprime = 3 •ℕ g :=
begin
  obtain ⟨h1, h2⟩ := factorization_prop hcoprime,
  set f := factorization hcoprime with hf,
  have h1' : f.prod = ⟨a, b⟩ ∨ f.prod = -⟨a, b⟩,
  { cases h1,
    { left, rw h1, },
    { right, rw h1, simp only [neg_neg] } },
  set f' := multiset.map zsqrtd.norm f with hf',
  have heqnsmulthree : factors_odd_prime_or_four (a ^ 2 + 3 * b ^ 2) = 
    3 •ℕ factors_odd_prime_or_four r,
  { rw ←hcube,
    apply factors_odd_prime_or_four.pow,
    suffices : even (3 * even_factor_exp r),
    { rw nat.even_mul at this,
      apply this.resolve_left,
      norm_num },
    rw [←even_factor_exp.pow r 3, hcube],
    exact factors_2_even' a b hcoprime },

  have heqprod : a ^ 2 + 3 * b ^ 2 = f.prod.norm,
  { cases h1; rw [zsqrt3.norm', h1],
    rw zsqrtd.norm_neg },

  have : f' = factors_odd_prime_or_four (a ^ 2 + 3 * b ^ 2),
  { apply factors_odd_prime_or_four.unique hcoprime,
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      exact (h2 y hy).2.2 },
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      apply zsqrtd.norm_nonneg,
      norm_num },
    { rw [prod_map_norm, heqprod] } },
  rw [heqnsmulthree, hf'] at this,
--  have := factors_odd_prime_or_four.unique,

--  have := factors_unique,
  apply multiset.xxy,

  intros x hx,
  have h2x := h2 x hx,

  have : 3 ∣ multiset.count x.norm f',
  { rw [hf', this, multiset.count_smul],
    apply dvd_mul_right },

  have hcoprime' : ∀ A  : ℤ√-3, A ∈ f → is_coprime A.re A.im,
  { intros A HA,
    have hdvd : A ∣ f.prod := multiset.dvd_prod HA, 
    apply is_coprime_of_dvd,
    { rintro ⟨-, H⟩,
      exact (h2 A HA).2.1 H },
    { intros z hznu hznz hzr hzi,
      apply hznu,
      obtain ⟨d, hd⟩ : (z : ℤ√-3) ∣ f.prod,
      { apply dvd_trans _ hdvd,
        rw zsqrtd.int_dvd_iff,
        exact ⟨hzr, hzi⟩ },
      rw hd at h1,
      have : (z : ℤ√-3) ∣ ⟨a, b⟩,
      { cases h1; rw h1; simp only [dvd_neg, dvd_mul_right] },
      rw zsqrtd.int_dvd_iff at this,
      exact is_coprime.is_unit_of_dvd' hcoprime this.1 this.2 } },

  have hassociated : ∀ A B : ℤ√-3, A ∈ f → B ∈ f → A.norm = B.norm → associated' A B,
  { intros A B HA HB H,
    have HA' := h2 A HA,
    have HB' := h2 B HB,
    apply associated'_of_associated_norm,
    { rw H },
    { exact hcoprime' A HA },
    { exact hcoprime' B HB },
    { rw ←zsqrt3.norm,
      exact HA'.2.2, } },

  classical,
  have : 3 ∣ multiset.countp (associated' x) f,
  { rw multiset.count_map at this,
    convert this using 1,
    apply multiset.countp_eq,
    intros A HA,
    split; intro H,
    { symmetry,
      exact associated'.norm_eq H },
    { apply hassociated x A hx HA H.symm } }, 

  dsimp only [multiset.count],
  convert this using 1,
  apply multiset.countp_eq,
  intros A HA,
  split,
  { rintro rfl, refl },
  { rintro (⟨u, hu⟩|⟨u, hu⟩),
    -- associated x A
    { have := zsqrt3.coe_of_is_unit' (is_unit_unit u),
      obtain ⟨v, hv1, hv2⟩ := this,
      rw hv1 at hu,
      by_cases hxre : x.re = 0,
      { rw zsqrtd.ext at hu,
        simp only [add_zero, zsqrtd.coe_int_re, zsqrtd.mul_im, zero_add, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] at hu,
        simp only [hxre, zero_mul] at hu,
        rw zsqrtd.ext,
        split,
        { rw [←hu.1, hxre] },
        rw ←hu.2,
        convert (mul_one _).symm,
        rw ←hv2,
        apply (abs_of_nonneg _).symm,
        by_contradiction H,
        push_neg at H,
        have : v = -1,
        { rw [←hv2, abs_of_neg H, neg_neg] },
        have : A = x.conj,
        { rw zsqrtd.ext,
          simp only [zsqrtd.conj_re, zsqrtd.conj_im],
          split,
          { rw [←hu.1, hxre] },
          rw [←hu.2, this],
          simp only [mul_one, mul_neg_eq_neg_mul_symm],
        },
        have : x ∈ f ∧ x.conj ∈ f,
        { split,
          exact hx,
          rwa ←this },
        apply no_conj _ _ _ this,
        { change ¬is_unit x,
          intro HH,
          apply h2x.2.1,
          rw [zsqrt3.is_unit_iff] at HH,
          exact HH.2 },
        {cases h1'; rw h1',
          simp only [hcoprime],

          simp only [zsqrtd.neg_im, mul_neg_eq_neg_mul_symm, zsqrtd.neg_re],
          exact is_coprime_neg hcoprime },


      },
      rw ←hu,
      rw zsqrtd.ext,
      have : v = 1,
      { 
        rw ←hv2,
        apply (abs_of_nonneg _).symm,
        simp only [zsqrtd.ext, add_zero, zsqrtd.coe_int_re, zsqrtd.mul_im, zero_add, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] at hu,
        apply nonneg_of_mul_nonneg_left,
        { rw hu.1,
          exact (h2 A HA).1 },
        { apply lt_of_le_of_ne h2x.1,
          symmetry,
          exact hxre,} },
      split,
      { simp only [add_zero, zsqrtd.coe_int_re, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im],
        convert (mul_one _).symm },
      { simp only [zsqrtd.coe_int_re, zsqrtd.mul_im, zero_add, mul_zero, zsqrtd.coe_int_im],
        rw [this, mul_one] } },
  
    -- associated x A.conj
    { have := zsqrt3.coe_of_is_unit' (is_unit_unit u),
      obtain ⟨v, hv1, hv2⟩ := this,
      rw hv1 at hu,
      by_cases hxre : x.re = 0,
      { rw zsqrtd.ext at hu,
        simp only [add_zero, zsqrtd.coe_int_re, zsqrtd.mul_im, zero_add, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] at hu,
        simp only [zsqrtd.conj_re, zsqrtd.conj_im] at hu,
        simp only [hxre, zero_mul] at hu,
        rw zsqrtd.ext,
        split,
        { rw [←hu.1, hxre] },
        rw eq_neg_iff_eq_neg at hu,
        rw hu.2,
        rw neg_mul_eq_mul_neg,
        convert (mul_one _).symm,
        rw ←hv2,
        apply (abs_of_nonpos _).symm,
        by_contradiction H,
        push_neg at H,
        have : v = 1,
        { rw [←hv2, abs_of_pos H] },
        rw [this, mul_one] at hu,
        have : A = x.conj,
        { rw zsqrtd.ext,
          simp only [zsqrtd.conj_re, zsqrtd.conj_im],
          split,
          { rw [←hu.1, hxre] },
          exact hu.2 },
        have : x ∈ f ∧ x.conj ∈ f,
        { split,
          exact hx,
          rwa ←this },
        apply no_conj _ _ _ this,
        { intro HH,
          apply h2x.2.1,
          rw [zsqrt3.is_unit_iff] at HH,
          exact HH.2 },
        {cases h1'; rw h1',
          simp only [hcoprime],

          simp only [zsqrtd.neg_im, mul_neg_eq_neg_mul_symm, zsqrtd.neg_re],
          exact is_coprime_neg hcoprime } },

      exfalso,
      apply no_conj f,
      { change ¬is_unit A,
        intro HH,
        apply (h2 A HA).2.1,
        rw [zsqrt3.is_unit_iff] at HH,
        exact HH.2 },
      { cases h1'; rw h1',
        simp only [hcoprime],

        simp only [zsqrtd.neg_im, mul_neg_eq_neg_mul_symm, zsqrtd.neg_re],
        exact is_coprime_neg hcoprime },
      refine ⟨HA, _⟩,
      rw ←hu,
      convert hx,
      have : v = 1,
      { 
        rw ←hv2,
        apply (abs_of_nonneg _).symm,
        simp only [zsqrtd.ext, add_zero, zsqrtd.coe_int_re, zsqrtd.mul_im, zero_add, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] at hu,
        apply nonneg_of_mul_nonneg_left,
        { rw hu.1,
          simp only [zsqrtd.conj_re],
          exact (h2 A HA).1 },
        { apply lt_of_le_of_ne h2x.1,
          symmetry,
          exact hxre,} },
      simp only [this, mul_one, int.cast_one],
    } },
/-
  have : unique_factorization_monoid.factors (a ^ 2 + 3 * b ^ 2) =
    3 •ℕ unique_factorization_monoid.factors r,
  { rw ←hcube, apply unique_factorization_monoid.factors_pow, },
  have : ∀ p : ℤ, odd p → prime p → 3 ∣ multiset.count p f',
  { intros p podd pprime,
    sorry },
  have : 3 ∣ multiset.count 4 f',
  { sorry },
  sorry,
-/
end

lemma zsqrt3.even_pow_neg (x : ℤ√-3) : (-x) ^ 2 = (x ^ 2) :=
begin
  exact neg_square x,

end

lemma zsqrt3.odd_pow_neg (x : ℤ√-3) : (-x) ^ 3 = - (x ^ 3) :=
begin
  --rw zsqrtd.ext,
  
  rw pow_succ _ 2,
  rw pow_succ _ 2,
  rw neg_square,
  simp only [neg_mul_eq_neg_mul_symm],
end




lemma step5 -- lemma page 54
  (a b r : ℤ)
  (hcoprime : is_coprime a b)
  (hcube : r ^ 3 = a ^ 2 + 3 * b ^ 2)
  :
  ∃ p q : ℤ, (⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ ^ 3 :=
begin
  obtain ⟨f, hf⟩ := step5' a b r hcoprime hcube, 
  obtain ⟨h1, h2⟩ := factorization_prop hcoprime,
  set f' := factorization hcoprime with hf',
  set x := f.prod with hx,
  cases h1,
  { use [x.re, x.im],
    have xxx : x = ⟨x.re, x.im⟩ := by simp only [zsqrtd.ext, eq_self_iff_true, and_self],
    rw ←xxx,
    rw [h1, hf, multiset.prod_smul] },
  { use [-x.re, -x.im],
    have xxx : -x = ⟨-x.re, -x.im⟩ := by simp only [zsqrtd.ext, eq_self_iff_true, and_self, zsqrtd.neg_im, zsqrtd.neg_re],
    rw ←xxx,
    rw [h1, hf, multiset.prod_smul, hx, zsqrt3.odd_pow_neg] },
end

lemma step6
  (a b r : ℤ)
  (hcoprime : is_coprime a b)
  (hcube : r ^ 3 = a ^ 2 + 3 * b ^ 2)
  :
  ∃ p q,
    a = p ^ 3 - 9 * p * q ^ 2 ∧
    b = 3 * p ^ 2 * q - 3 * q ^ 3
  :=
begin
  obtain ⟨p, q, hpq⟩ := step5 a b r hcoprime hcube,
  use [p, q],
  rw zsqrtd.ext at hpq,
  rw [pow_succ', pow_two, zsqrtd.mul_def, zsqrtd.mul_def] at hpq,
  dsimp at hpq,
  obtain ⟨rfl, rfl⟩ := hpq,
  split; ring,
end
