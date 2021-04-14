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

lemma pow_two_abs {R:Type*} [linear_ordered_ring R] (x : R) : abs x ^ 2 = x ^ 2 :=
pow_bit0_abs x 1

lemma zsqrt3.is_unit_iff {z : ℤ√-3} : is_unit z ↔ abs z.re = 1 ∧ z.im = 0 :=
begin
  rw [←zsqrtd.norm_eq_one_iff, zsqrt3.norm, ←int.coe_nat_inj', int.coe_nat_one],
  rw int.nat_abs_of_nonneg (spts.nonneg _ _),
  refine ⟨spts.eq_one, λ h, _⟩,
  rw [h.2, ←pow_two_abs, h.1],
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
  { exact int.is_unit_iff_abs.mp u.is_unit },
end

def odd_prime_or_four (z : ℤ) : Prop :=
  z = 4 ∨ (prime z ∧ odd z)

lemma odd_prime_or_four.ne_zero {z : ℤ} (h : odd_prime_or_four z) : z ≠ 0 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_zero }
end

lemma odd_prime_or_four.ne_one {z : ℤ} (h : odd_prime_or_four z) : z ≠ 1 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_one }
end

lemma odd_prime_or_four.one_lt_abs {z : ℤ} (h : odd_prime_or_four z) : 1 < abs z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw int.abs_eq_nat_abs, norm_cast, norm_num },
  { rw int.abs_eq_nat_abs,
    rw int.prime_iff_nat_abs_prime at h,
    norm_cast,
    exact h.one_lt, }
end

lemma odd_prime_or_four.not_unit {z : ℤ} (h : odd_prime_or_four z) : ¬ is_unit z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw is_unit_iff_dvd_one, norm_num },
  { exact h.not_unit }
end

lemma odd_prime_or_four.abs {z : ℤ} (h : odd_prime_or_four z) : odd_prime_or_four (abs z) :=
begin
  obtain rfl|⟨hp, ho⟩ := h,
  { left, rw abs_eq_self, norm_num },
  { right, exact ⟨hp.abs, int.abs_odd ho⟩ }
end

lemma odd_prime_or_four.exists_and_dvd
  {n : ℤ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ odd_prime_or_four p :=
begin
  lift n to ℕ using (zero_lt_two.trans n2).le,
  norm_cast at n2,
  obtain ⟨k, h2⟩|⟨p, hp, hdvd, hodd⟩ := exists_odd_prime_and_dvd_or_two_pow n2.le,
  { refine ⟨4, _, _⟩,
    { use 2 ^ (k - 2),
      norm_cast,

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : h2
      ... = 2 ^ 2 * 2 ^ (k - 2) : (pow_mul_pow_sub _ h3).symm
      ... = 4 * 2 ^ (k - 2) : by norm_num },
    { left, refl } },
  { rw nat.prime_iff_prime_int at hp,
    rw ←int.odd_coe_nat at hodd,
    exact ⟨p, int.coe_nat_dvd.mpr hdvd, or.inr ⟨hp, hodd⟩⟩ },
end

lemma odd_prime_or_four.factors
  (a b x : ℤ)
  (hcoprime : is_coprime a b)
  (hx : odd_prime_or_four x)
  (hfactor : x ∣ (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, abs x = c ^ 2 + 3 * d ^ 2 ∧ 0 ≤ c ∧ 0 < d :=
begin
  obtain rfl|⟨hprime, hodd⟩ := hx,
  { use [1, 1], norm_num },
  { rw ←int.nat_abs_dvd at hfactor,
    obtain ⟨c, d, hcd⟩ := factors a.nat_abs b.nat_abs x.nat_abs _ _ _,
    refine ⟨c, d, _, _, _⟩,
    { rw int.abs_eq_nat_abs,
      norm_cast,
      assumption },
    { exact int.coe_zero_le c },
    { apply lt_of_le_of_ne (int.coe_zero_le d),
      norm_cast,
      rintro rfl,
      simp only [zero_lt_two, zero_pow, add_zero, mul_zero] at hcd,
      rw [int.prime_iff_nat_abs_prime, hcd] at hprime,
      exact nat.prime.pow_not_prime le_rfl hprime },
    { rwa ←int.gcd_eq_one_iff_coprime at hcoprime, },
    { rwa [int.nat_abs_even, ←int.odd_iff_not_even] },
    { rw [←int.nat_abs_pow_two a, ←int.nat_abs_pow_two b] at hfactor,
      norm_cast at hfactor,
      assumption } }
end

lemma odd_prime_or_four.im_ne_zero
  {p q : ℤ}
  (h: odd_prime_or_four (p ^ 2 + 3 * q ^ 2))
  (hcoprime: is_coprime p q) :
  q ≠ 0 :=
begin
  rintro rfl,
  simp only [zero_pow, zero_lt_two, add_zero, mul_zero] at h,
  obtain h|⟨hp, hodd⟩ := h,
  { rw [is_coprime_zero_right, int.is_unit_iff_abs] at hcoprime,
    rw [←pow_two_abs, hcoprime] at h,
    norm_num at h },
  { exact pow_not_prime one_lt_two hp }
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
  { obtain ⟨v, hv⟩ := hdvd,
    rw ←eq_sub_iff_add_eq at hv,
    use [v - b, v],
    right,
    rw [hv, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
  { obtain ⟨v, hv⟩ := hdvd,
    rw sub_eq_iff_eq_add at hv,
    use [b + v, -v],
    left,
    rw [hv, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
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
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_re, zsqrtd.mul_im, zsqrtd.mul_im] at huv',
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
    { rw [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im] at huv',
      dsimp only at huv',
      rw [huv'.1, huv'.2],
      ring } }
end

lemma step2
  (a b : ℤ)
  (p q : ℤ)
  (hcoprime : is_coprime a b)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpprime : prime (p ^ 2 + 3 * q ^ 2))
  :
  ∃ u v,
    is_coprime u v ∧
    ((⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨ (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩) ∧
    (a ^ 2 + 3 * b ^ 2) = (p ^ 2 + 3 * q ^ 2) * (u ^ 2 + 3 * v ^ 2)  :=
begin
  obtain ⟨u', v', h, h'⟩ := spts.mul_of_dvd a b p q hdvd hpprime,
  refine ⟨u', v', _, h, h'.symm⟩,
  { rw [zsqrtd.ext, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_re, zsqrtd.mul_im, zsqrtd.mul_im] at h,
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
      exact hcoprime.is_unit_of_dvd' ha hb } }
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
    obtain ⟨hp', hq'⟩ := spts.four hp hq,
    rw (abs_eq $ @zero_le_one ℤ _) at hp' hq',
    cases hp';
    cases hq';
    subst p;
    subst q,

    { refine ⟨u, v, h1, h2, _⟩,
      { rwa hp } },
    { refine ⟨u, v, h1, _, _⟩,
      { simp only [neg_neg], rwa or_comm, },
      { rwa hp } },
    { refine ⟨-u, -v, h1.neg_neg, _, _⟩,
      { rw or_comm,
        convert h2 using 2;
        { rw [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_re, zsqrtd.mul_im, zsqrtd.mul_im],
          simp only [neg_mul_eq_neg_mul_symm, eq_self_iff_true, mul_neg_eq_neg_mul_symm, and_self,
            neg_neg] } },
      { rwa [hp, neg_pow_bit0, neg_pow_bit0] } },
    { refine ⟨-u, -v, h1.neg_neg, _, _⟩,
      { convert h2 using 2;
        { rw [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_re, zsqrtd.mul_im, zsqrtd.mul_im],
          simp only [neg_mul_eq_neg_mul_symm, eq_self_iff_true, mul_neg_eq_neg_mul_symm, and_self,
            neg_neg] } },
      { rwa [hp, neg_pow_bit0, neg_pow_bit0] } } },
  { apply step2 _ _ _ _ hcoprime hdvd hpprime }
end

-- todo: unused, but try to use in step3 below
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

lemma odd_prime_or_four.factors'
  {a b : ℤ}
  (h2 : 2 < a ^ 2 + 3 * b ^ 2)
  (hcoprime : is_coprime a b) :
  ∃ (u v : ℤ) (q : ℤ√-3),
    0 ≤ q.re ∧
    q.im ≠ 0 ∧
    odd_prime_or_four q.norm ∧
    (⟨a, b⟩ : ℤ√-3) = q * ⟨u, v⟩ ∧
    is_coprime u v ∧
    (u ^ 2 + 3 * v ^ 2) < (a ^ 2 + 3 * b ^ 2) :=
begin
  obtain ⟨p, hpdvd, hp⟩ := odd_prime_or_four.exists_and_dvd h2,
  obtain ⟨q, r, hcd, hc, hd⟩ := odd_prime_or_four.factors a b p hcoprime hp hpdvd,
  set q' : ℤ√-3 := ⟨q, r⟩ with hq',
  have hdvd' : q ^ 2 + 3 * r ^ 2 ∣ a ^ 2 + 3 * b ^ 2,
  { apply dvd_trans _ hpdvd,
    rw [←hcd, int.abs_eq_nat_abs, int.nat_abs_dvd] },
  have hp' := hp.abs,
  rw hcd at hp',
  obtain ⟨u, v, huvcoprime, huv, huvdvd⟩ := step1_2 a b q r hcoprime hdvd' hp' hd.ne.symm,
  rw [zsqrt3.norm', ←hq'] at hp',
  cases huv; use [u, v]; [use q', use q'.conj];
  { try { rw [zsqrtd.conj_re, zsqrtd.conj_im, neg_ne_zero, zsqrtd.norm_conj] },
    use [hc, hd.ne.symm, hp', huv, huvcoprime],
    rw huvdvd,
    apply int.lt_mul_self (spts.pos_of_coprime huvcoprime),
    rw ←hcd,
    exact hp.one_lt_abs },
end

lemma step3
  {a b : ℤ}
  (hcoprime : is_coprime a b)
  :
  ∃ f : multiset ℤ√-3,
    ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
  :=
begin
  suffices : ∀ n : ℕ, a^2 + 3 * b ^ 2 = n →
    ∃ f : multiset ℤ√-3,
    ((⟨a, b⟩ : ℤ√-3) = f.prod ∨ (⟨a, b⟩ : ℤ√-3) = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm,
  { exact this (a^2 + 3 * b ^ 2).nat_abs (int.nat_abs_of_nonneg (spts.nonneg a b)).symm },

  intros n hn,
  induction n using nat.strong_induction_on with n ih generalizing a b,
  dsimp only at ih,
  have hn' : (a ^ 2 + 3 * b ^ 2).nat_abs = n,
  { rw hn, exact int.nat_abs_of_nat n },

  by_cases h : a^2 + 3 * b ^ 2 = 1,
  { have : abs a = 1 ∧ b = 0 := spts.eq_one h,
    use 0,
    split,
    { simp only [multiset.prod_zero, zsqrtd.ext, zsqrtd.one_re, zsqrtd.one_im, zsqrtd.neg_im,
        zsqrtd.neg_re, neg_zero],
      rwa [←or_and_distrib_right, ←abs_eq],
      exact zero_le_one },
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
      rw [H.1, H.2] at hcoprime,
      exact not_coprime_zero_zero hcoprime },
    have : 2 < a ^ 2 + 3 * b ^ 2,
    { apply lt_of_le_of_ne _ (spts.not_two a b).symm,
      exact this },
    obtain ⟨u, v, q, hc, hd, hp, huv, huvcoprime, descent⟩ := odd_prime_or_four.factors'
      this hcoprime,
    replace descent := int.nat_abs_lt_nat_abs_of_nonneg_of_lt (spts.nonneg _ _) descent,
    rw hn' at descent,
    obtain ⟨g, hgprod, hgfactors⟩ := ih (u ^ 2 + 3 * v ^ 2).nat_abs descent huvcoprime
      (int.nat_abs_of_nonneg (spts.nonneg _ _)).symm,
    use q ::ₘ g,
    split,
    { rw huv,
      cases hgprod; rw [multiset.prod_cons, hgprod],
      { left, refl },
      { right, simp only [mul_neg_eq_neg_mul_symm] } },
    { rintros pq hpq,
      rw multiset.mem_cons at hpq,
      obtain rfl|ind := hpq,
      { exact ⟨hc, hd, hp⟩ },
      { exact hgfactors pq ind } } },
end

lemma step4_3
  (p q p' q' : ℤ)
  (hcoprime : is_coprime p q)
  (hcoprime' : is_coprime p' q')
  (h : odd_prime_or_four (p ^ 2 + 3 * q ^ 2))
  (heq : p ^ 2 + 3 * q ^ 2 = p' ^ 2 + 3 * q' ^ 2) :
  abs p = abs p' ∧ abs q = abs q' :=
begin
  obtain ⟨u, v, hcoprime'', (H|H), h1⟩ := step1_2 p q p' q' hcoprime (by rw heq) (by rwa ←heq)
    (odd_prime_or_four.im_ne_zero (by rwa heq at h) hcoprime');
  { rw heq at h1,
    have := int.eq_one_of_mul_eq_self_right (spts.not_zero_of_coprime hcoprime') h1.symm,
    obtain ⟨ha, rfl⟩ := spts.eq_one this,
    simp only [zero_pow zero_lt_two, add_zero, mul_zero] at this, 
    rw [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im] at H,
    dsimp only at H,
    simp only [add_zero, zero_add, mul_zero] at H,
    rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
    try { rw [abs_neg] },
    split; refl },
end

lemma prod_map_norm {s : multiset ℤ√-3} :
  (s.map zsqrtd.norm).prod = zsqrtd.norm s.prod :=
multiset.prod_hom s zsqrtd.norm_monoid_hom

lemma norm_not_dvd_four_of_odd_prime {p : ℤ} (hmin : 0 ≤ p) (hp : prime p) (hodd: odd p) :
  ¬(p ∣ 4) :=
begin
  intro h,
  have hmax := int.le_of_dvd (by norm_num) h,
  rw ←int.lt_add_one_iff at hmax,
  interval_cases using hmin hmax,
  { exact hp.ne_zero rfl, },
  { exact hp.ne_one rfl },
  { norm_num at hodd },
  { norm_num at h },
  { norm_num at hodd },
end

lemma associated_of_dvd {a p : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (h: p ∣ a) : associated p a :=
begin
  obtain (rfl|ha) := ha;
  obtain (rfl|hp) := hp,
  { refl },
  { exfalso,
    have h : abs p ∣ 4,
    { rwa [int.abs_eq_nat_abs, int.nat_abs_dvd] },
    exact norm_not_dvd_four_of_odd_prime (abs_nonneg _) hp.1.abs (int.abs_odd hp.2) h },
  { exfalso,
    rw int.odd_iff_not_even at ha,
    refine ha.2 (dvd_trans _ h),
    norm_num },
  { rwa prime_dvd_prime_iff_eq hp.1 ha.1 at h }

end

lemma dvd_blah {p a b : ℤ} (hp : prime p) (n : ℕ) (h : ¬(p ∣ a)) (h' : p ^ n ∣ a * b) : p ^ n ∣ b :=
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

lemma dvd_or_dvd {a p x : ℤ}
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
      apply dvd_blah int.prime_two,
      { rw [←even_iff_two_dvd, ←int.odd_iff_not_even], exact ha.2 },
      { rwa [hp, this] at hdvd } } },
  { exact (hp.1.div_or_div hdvd) }
end 

lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ} (hp : odd_prime_or_four p)
  {s : multiset ℤ}
  (hs : ∀ r ∈ s, odd_prime_or_four r)
  (hdvd : p ∣ s.prod) :
  ∃ q ∈ s, associated p q :=
begin
  revert hs hdvd,
  refine s.induction_on _ _,
  { simp [forall_const, forall_prop_of_false, exists_false, multiset.prod_zero, not_false_iff,
      exists_prop_of_false, multiset.not_mem_zero, ←is_unit_iff_dvd_one, hp.not_unit] },
  { intros a s ih hs hps,
    rw [multiset.prod_cons] at hps,
    have := hs a (multiset.mem_cons_self _ _),
    have h := dvd_or_dvd this hp hps,
    cases h with h h,
    { exact ⟨a, multiset.mem_cons_self _ _, associated_of_dvd this hp h⟩ },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ } }
end

lemma factors_unique_prod' : ∀{f g : multiset ℤ},
  (∀x∈f, odd_prime_or_four x) →
  (∀x∈g, odd_prime_or_four x) →
  (associated f.prod g.prod) →
  multiset.rel associated f g :=
begin
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw [multiset.prod_zero] at h,
    rw [multiset.rel_zero_left],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    apply (hg x hx).not_unit,
    rw is_unit_iff_dvd_one,
    exact dvd.trans (multiset.dvd_prod hx) (dvd_of_associated h.symm) },
  { intros p f ih g hf hg hfg,
    have hp := hf p (multiset.mem_cons_self _ _),
    have hdvd : p ∣ g.prod,
    { rw [←dvd_iff_dvd_of_rel_right hfg, multiset.prod_cons],
      exact dvd_mul_right _ _ },
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
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm :=
classical.some_spec (step3 hcoprime)

lemma factorization_prop'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  (a = (factorization hcoprime).prod ∨ a = - (factorization hcoprime).prod) ∧
    ∀ pq : ℤ√-3, pq ∈ (factorization hcoprime) →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm :=
begin
  convert factorization_prop hcoprime;
  { rw zsqrtd.ext, dsimp only, split; refl },
end

lemma factorization.coprime_of_mem
  {a b : ℤ√-3} (h : is_coprime a.re a.im) (hmem : b ∈ factorization h) :
  is_coprime b.re b.im :=
begin
  obtain ⟨h1, h2⟩ := factorization_prop' h,
  set f := factorization h,
  apply is_coprime_of_dvd,
  { rintro ⟨-, H⟩,
    exact (h2 b hmem).2.1 H },
  { intros z hznu hznz hzr hzi,
    apply hznu,
    have : (z : ℤ√-3) ∣ f.prod,
    { apply dvd_trans _ (multiset.dvd_prod hmem),
      rw zsqrtd.coe_int_dvd_iff,
      exact ⟨hzr, hzi⟩ },
    have : (z : ℤ√-3) ∣ a,
    { cases h1; simp only [h1, dvd_neg, this] },
    rw zsqrtd.coe_int_dvd_iff at this,
    exact is_coprime.is_unit_of_dvd' h this.1 this.2 } ,
end

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

def associated' (x y : ℤ√-3) : Prop := associated x y ∨  associated x y.conj

@[refl] theorem associated'.refl (x : ℤ√-3) : associated' x x := or.inl (by refl)

lemma associated'.norm_eq
  {x y : ℤ√-3}
  (h : associated' x y) :
  x.norm = y.norm :=
begin
  cases h; simp only [zsqrtd.norm_eq_of_associated (by norm_num) h, zsqrtd.norm_conj],
end

lemma associated'_of_abs_eq {x y : ℤ√-3} (hre : abs x.re = abs y.re) (him : abs x.im = abs y.im) :
  associated' x y :=
begin
  cases int.abs_eq_abs_iff hre with h1 h1;
  cases int.abs_eq_abs_iff him with h2 h2;
  [{ left, use 1}, {right, use 1}, {right, use -1}, {left, use -1}];
  simp only [units.coe_one, mul_one, units.coe_neg_one, mul_neg_one, zsqrtd.ext, zsqrtd.neg_im,
    zsqrtd.neg_re, h1, h2, neg_neg, zsqrtd.conj_re, zsqrtd.conj_im];
  split;
  refl,
end

lemma associated'_of_associated_norm {x y : ℤ√-3} (h : associated (zsqrtd.norm x) (zsqrtd.norm y))
  (hx : is_coprime x.re x.im)
  (hy : is_coprime y.re y.im)
  (h' : odd_prime_or_four x.norm) :
  associated' x y :=
begin
  have heq : x.norm = y.norm,
  { have hd : (-3 : ℤ) ≤ 0,
    { norm_num },
    exact eq_of_associated_of_nonneg h (zsqrtd.norm_nonneg hd _) (zsqrtd.norm_nonneg hd _) },
  rw [zsqrt3.norm, zsqrt3.norm] at heq,
  rw zsqrt3.norm at h',
  obtain ⟨hre, him⟩ := step4_3 x.re x.im y.re y.im hx hy h' heq,
  exact associated'_of_abs_eq hre him,
end

lemma factorization.associated'_of_norm_eq
  {a b c : ℤ√-3} (h : is_coprime a.re a.im)
  (hbmem : b ∈ factorization h) (hcmem : c ∈ factorization h)
  (hnorm : b.norm = c.norm) :
  associated' b c :=
begin
  apply associated'_of_associated_norm,
  { rw hnorm },
  { exact factorization.coprime_of_mem h hbmem },
  { exact factorization.coprime_of_mem h hcmem },
  { exact ((factorization_prop h).2 b hbmem).2.2 },
end

lemma factors_unique
  {f g : multiset ℤ√-3}
  (hf : ∀x∈f, odd_prime_or_four (zsqrtd.norm x))
  (hf' : ∀x∈f, is_coprime (zsqrtd.re x) (zsqrtd.im x))
  (hg : ∀x∈g, odd_prime_or_four (zsqrtd.norm x))
  (hg' : ∀x∈g, is_coprime (zsqrtd.re x) (zsqrtd.im x))
  (h : associated f.prod g.prod) :
  multiset.rel associated' f g :=
begin
  have p : ∀ (x : ℤ√-3) (hx : x ∈ f) (y : ℤ√-3) (hy : y ∈ g),
    associated x.norm y.norm → associated' x y,
  { intros x hx y hy hxy,
    apply associated'_of_associated_norm hxy,
    { exact hf' x hx },
    { exact hg' y hy },
    { exact hf x hx } },

  refine multiset.rel.mono _ p,
  rw ←multiset.rel_map,
  apply factors_unique_prod hf hg,
  have hd : (-3 : ℤ) ≤ 0,
  { norm_num },
  obtain ⟨u, hu⟩ := h,
  rw [←hu, zsqrtd.norm_mul, (zsqrtd.norm_eq_one_iff' hd u).mpr u.is_unit, mul_one],
end

noncomputable def odd_factors (x : ℤ) := multiset.filter odd (unique_factorization_monoid.factors x)

lemma odd_factors.zero : odd_factors 0 = 0 := rfl

lemma odd_factors.not_two_mem (x : ℤ) : (2 : ℤ) ∉ odd_factors x :=
begin
  simp only [odd_factors, int.even_bit0, not_true, not_false_iff, int.odd_iff_not_even,
    and_false, multiset.mem_filter],
end

noncomputable def even_factor_exp (x : ℤ) := multiset.count 2 (unique_factorization_monoid.factors x)

lemma even_factor_exp.def (x : ℤ) : even_factor_exp x = multiset.count 2 (unique_factorization_monoid.factors x) := rfl

lemma even_factor_exp.zero : even_factor_exp 0 = 0 := rfl

lemma even_and_odd_factors'' (x : ℤ) :
  unique_factorization_monoid.factors x = (unique_factorization_monoid.factors x).filter (eq 2) + odd_factors x :=
begin
  by_cases hx : x = 0,
  { rw [hx, unique_factorization_monoid.factors_zero, odd_factors.zero, multiset.filter_zero,
    add_zero] },
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
    norm_num at hodd },
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

lemma factors_2_even {z : ℤ} (hz : z ≠ 0) : even_factor_exp (4 * z) = 2 + even_factor_exp z :=
begin
  simp [even_factor_exp],
  rw unique_factorization_monoid.factors_mul (by norm_num : (4 : ℤ) ≠ 0) hz,
  rw multiset.count_add,
  congr,
  rw int.factors_eq,
  have : [2, 2] ~ nat.factors (int.nat_abs 4),
  { apply nat.factors_unique,
    { norm_num },
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

-- most useful with  (hz : even (even_factor_exp z))
noncomputable def factors_odd_prime_or_four (z : ℤ) : multiset ℤ :=
multiset.repeat 4 (even_factor_exp z / 2) + odd_factors z

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
  apply multiset.rel.mono (factors_odd_prime_or_four.associated hcoprime hf hassoc),
  intros x hx y hy hxy,
  exact eq_of_associated_of_nonneg hxy (hf' x hx) (factors_odd_prime_or_four.nonneg hy)
end

lemma even_factor_exp.pow (z : ℤ) (n : ℕ) : even_factor_exp (z ^ n) = n * even_factor_exp z :=
begin
  simp only [even_factor_exp],
  rw [unique_factorization_monoid.factors_pow, multiset.count_nsmul]
end

lemma factors_odd_prime_or_four.pow
  (z : ℤ) (n : ℕ) (hz : even (even_factor_exp z)) :
  factors_odd_prime_or_four (z ^ n) = n • factors_odd_prime_or_four z :=
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
  { simp only [odd_factors],
    rw unique_factorization_monoid.factors_pow,
    rw multiset.nsmul_filter },
end

lemma eq_or_eq_conj_of_associated_of_re_zero
  {x A : ℤ√-3}
  (hx : x.re = 0)
  (h : associated x A) :
  x = A ∨ x = A.conj :=
begin
  obtain ⟨u, hu⟩ := h,
  obtain ⟨v, hv1, hv2⟩ := zsqrt3.coe_of_is_unit' u.is_unit,
  have hA : A.re = 0,
  { simp only [←hu, hv1, hx, add_zero, zero_mul, zsqrtd.mul_re, mul_zero, zsqrtd.coe_int_im] },
  rw (abs_eq $ @zero_le_one ℤ _) at hv2,
  cases hv2 with hv2 hv2,
  { left,
    simpa only [hv1, hv2, mul_one, int.cast_one] using hu },
  { right,
    simp only [hv1, hv2, mul_one, int.cast_one, mul_neg_eq_neg_mul_symm, int.cast_neg] at hu,
    simp only [←hu, hx, zsqrtd.conj_neg, zsqrtd.ext, zsqrtd.neg_re, zsqrtd.neg_im, zsqrtd.conj_re,
      zsqrtd.conj_im, neg_neg, neg_zero, eq_self_iff_true, and_self] }
end

lemma eq_or_eq_conj_iff_associated'_of_nonneg
  {x A : ℤ√-3}
  (hx : 0 ≤ x.re)
  (hA : 0 ≤ A.re) :
  associated' x A ↔ (x = A ∨ x = A.conj) :=
begin
  split,
  { rintro (⟨u, hu⟩|⟨u, hu⟩); obtain ⟨v, hv1, hv2⟩ := zsqrt3.coe_of_is_unit' u.is_unit,
    -- associated x A
    { by_cases hxre : x.re = 0,
      { apply eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩ },
      { rw hv1 at hu,
        rw (abs_eq $ @zero_le_one ℤ _) at hv2,
        cases hv2 with habsv habsv,
        { left,
          rw [←hu, habsv, int.cast_one, mul_one] },
        { exfalso,
          simp only [habsv, mul_one, int.cast_one, mul_neg_eq_neg_mul_symm, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 < A.re : _
          ... = -x.re : _
          ... < 0 : _,
          { apply lt_of_le_of_ne hA,
            rw ←hu,
            simp only [zsqrtd.neg_re, ne.def, zero_eq_neg, hxre, not_false_iff] },
          { simp only [←hu, zsqrtd.neg_re] },
          { simp only [neg_neg_iff_pos],
            exact lt_of_le_of_ne hx (ne.symm hxre) } } } },

    -- associated x A.conj
    { by_cases hxre : x.re = 0,
      { convert (eq_or_eq_conj_of_associated_of_re_zero hxre ⟨u, hu⟩).symm,
        rw zsqrtd.conj_conj },
      { rw hv1 at hu,
        rw (abs_eq $ @zero_le_one ℤ _) at hv2,
        cases hv2 with habsv habsv,
        { right,
          rw [←hu, habsv, int.cast_one, mul_one] },
        { exfalso,
          simp only [habsv, mul_one, int.cast_one, mul_neg_eq_neg_mul_symm, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 < A.re : _
          ... = -x.re : _
          ... < 0 : _,
          { apply lt_of_le_of_ne hA,
            rw [←zsqrtd.conj_conj A, ←hu],
            simp only [hxre, zsqrtd.conj_re, zsqrtd.neg_re, ne.def, not_false_iff, zero_eq_neg] },
          { rw [←zsqrtd.conj_conj A, ←hu],
            simp only [zsqrtd.conj_re, zsqrtd.neg_re] },
          { simp only [neg_neg_iff_pos],
            apply lt_of_le_of_ne hx (ne.symm hxre) } } } } },
  { rintro (rfl|rfl),
    { refl },
    { right, refl } },
end

lemma associated'_iff_eq
  {x A : ℤ√-3}
  (hx : 0 ≤ x.re)
  (hA : 0 ≤ A.re)
  (h : x ≠ A.conj) :
  x = A ↔ associated' x A :=
by simp only [eq_or_eq_conj_iff_associated'_of_nonneg hx hA, h, or_false]

lemma step5' -- lemma page 54
  (a : ℤ√-3)
  (r : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hcube : r ^ 3 = a.norm) :
  ∃ g : multiset ℤ√-3, factorization hcoprime = 3 • g :=
begin
  obtain ⟨h1, h2⟩ := factorization_prop' hcoprime,
  set f := factorization hcoprime with hf,
  have h1' : f.prod = a ∨ f.prod = -a,
  { cases h1; simp only [eq_self_iff_true, or_true, true_or, neg_neg, h1] },
  set f' := multiset.map zsqrtd.norm f with hf',
  have heqnsmulthree : factors_odd_prime_or_four a.norm =
    3 • factors_odd_prime_or_four r,
  { rw ←hcube,
    apply factors_odd_prime_or_four.pow,
    suffices : even (3 * even_factor_exp r),
    { rw nat.even_mul at this,
      apply this.resolve_left,
      norm_num },
    rw [←even_factor_exp.pow r 3, hcube, zsqrt3.norm],
    exact factors_2_even' a.re a.im hcoprime },

  have heqprod : a.norm = f.prod.norm,
  { cases h1; simp only [h1, zsqrtd.norm_neg] },

  have : f' = factors_odd_prime_or_four a.norm,
  { rw zsqrt3.norm,
    apply factors_odd_prime_or_four.unique hcoprime,
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      exact (h2 y hy).2.2 },
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      apply zsqrtd.norm_nonneg,
      norm_num },
    { rw [←zsqrt3.norm, prod_map_norm, heqprod] } },
  rw [heqnsmulthree, hf'] at this,

  apply multiset.exists_nsmul_of_dvd,

  intros x hx,
  have h2x := h2 x hx,

  have : 3 ∣ multiset.count x.norm f',
  { rw [hf', this, multiset.count_nsmul],
    apply dvd_mul_right },

  classical,
  have : 3 ∣ multiset.countp (associated' x) f,
  { rw multiset.count_map at this,
    convert this using 1,
    apply multiset.countp_eq,
    intros A HA,
    split; intro H,
    { exact associated'.norm_eq H },
    { exact factorization.associated'_of_norm_eq hcoprime hx HA H } },

  dsimp only [multiset.count],
  convert this using 1,
  apply multiset.countp_eq,
  intros A HA,
  apply associated'_iff_eq h2x.1 (h2 A HA).1,
  intro H,
  have : x ∈ f ∧ x.conj ∈ f,
  { split,
    { exact hx },
    { rwa [H, zsqrtd.conj_conj] } },
  apply no_conj _ _ _ this,
  { intro HH,
    apply h2x.2.1,
    rw [zsqrt3.is_unit_iff] at HH,
    exact HH.2 },
  { cases h1'; rw h1',
    { simp only [hcoprime] },
    { simp only [zsqrtd.neg_im, mul_neg_eq_neg_mul_symm, zsqrtd.neg_re],
      exact hcoprime.neg_neg } },
end

lemma step5 -- lemma page 54
  (a : ℤ√-3)
  (r : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hcube : r ^ 3 = a.norm) :
  ∃ p : ℤ√-3, a = p ^ 3 :=
begin
  obtain ⟨f, hf⟩ := step5' a r hcoprime hcube,
  obtain ⟨h1, -⟩ := factorization_prop' hcoprime,
  cases h1,
  { use f.prod,
    rw [h1, hf, multiset.prod_nsmul] },
  { use -f.prod,
    rw [h1, hf, multiset.prod_nsmul, neg_pow_bit1] },
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
  obtain ⟨p, hp⟩ := step5 ⟨a, b⟩ r hcoprime (hcube.trans (zsqrt3.norm' a b)),
  use [p.re, p.im],
  simp only [zsqrtd.ext, pow_succ', pow_two, zsqrtd.mul_re, zsqrtd.mul_im] at hp,
  obtain ⟨rfl, rfl⟩ := hp,
  split; ring,
end
