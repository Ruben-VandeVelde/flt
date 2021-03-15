import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid
import tactic
import data.nat.modeq
import ring_theory.int.basic
import data.zsqrtd.basic
import .primes

lemma factors2
  {a b : ℕ}
  (heven : even (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, a ^ 2 + 3 * b ^ 2 = 4 * (c ^ 2 + 3 * d ^ 2) :=
begin
  have hparity : even a ↔ even b,
  { simpa [two_ne_zero] with parity_simps using heven },

  by_cases h : even a,
  { obtain ⟨d, hd⟩ := hparity.mp h,
    obtain ⟨c, hc⟩ := h,
    use [c, d],
    rw [hc, hd],
    ring },
  { have : ¬even b,
    { rwa ←hparity },

    have h4 : (4 : ℤ) ∣ a + b ∨ (4 : ℤ) ∣ a - b,
    { apply int.four_dvd_add_or_sub_of_odd,
      { rwa [←nat.odd_iff_not_even, ←int.coe_nat_odd] at h },
      { rwa [←nat.odd_iff_not_even, ←int.coe_nat_odd] at this } },
    cases h4,
    { obtain ⟨u, hu⟩ : (4 : ℤ) ∣ a - 3 * b,
      { convert dvd_sub h4 (dvd_mul_right 4 b) using 1,
        ring },
      obtain ⟨v, hv⟩ := h4,
      use [u.nat_abs, v.nat_abs],
      apply nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4),
      zify,
      rw [int.nat_abs_pow_two u, int.nat_abs_pow_two v],
      calc (4 * (a ^ 2 + 3 * b ^ 2) : ℤ)
          = (a - 3 * b) ^ 2 + 3 * (a + b) ^ 2 : by ring
      ... = (4 * u) ^ 2 + 3 * (4 * v) ^ 2 : by rw [hu, hv]
      ... = 4 * (4 * (u ^ 2 + 3 * v ^ 2)) : by ring },
    { obtain ⟨u, hu⟩ : (4 : ℤ) ∣ a + 3 * b,
      { convert dvd_add h4 (dvd_mul_right 4 b) using 1,
        ring },
      obtain ⟨v, hv⟩ := h4,
      use [u.nat_abs, v.nat_abs],
      apply nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4),
      zify,
      rw [int.nat_abs_pow_two u, int.nat_abs_pow_two v],
      calc (4 * (a ^ 2 + 3 * b ^ 2) : ℤ)
          = (a + 3 * b) ^ 2 + 3 * (a - b) ^ 2 : by ring
      ... = (4 * u) ^ 2 + 3 * (4 * v) ^ 2 : by rw [hu, hv]
      ... = 4 * (4 * (u ^ 2 + 3 * v ^ 2)) : by ring } }
end

lemma int.sq_plus_three_sq_eq_zero_iff {a b : ℤ} : a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 :=
begin
  split,
  { intro h,
    have hposleft := pow_two_nonneg a,
    have hposright := mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) (pow_two_nonneg b),
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_eq_zero_of_nonneg hposleft hposright).mp h,
    split,
    { exact pow_eq_zero ha },
    { rw [mul_eq_zero, eq_false_intro (by norm_num : (3 : ℤ) ≠ 0), false_or] at hb,
      exact pow_eq_zero hb } },
  { rintro ⟨rfl, rfl⟩, norm_num }
end

lemma nat.sq_plus_three_sq_eq_zero_iff {a b : ℕ} : a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 :=
begin
  zify,
  exact int.sq_plus_three_sq_eq_zero_iff
end

lemma spts.mul_of_dvd'
  (a b : ℤ)
  (p q : ℤ)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpprime : prime (p ^ 2 + 3 * q ^ 2)) :
  ∃ u v,
    (⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨
    (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩ :=
begin
  obtain ⟨f, hf⟩ := hdvd,
  have h0 : p ^ 2 + 3 * q ^ 2 ∣ p * b - a * q ∨
         p ^ 2 + 3 * q ^ 2 ∣ p * b + a * q,
  { apply int.prime.dvd_mul'' hpprime,
    convert dvd_mul_right (p ^ 2 + 3 * q ^ 2) (b ^ 2 - q ^ 2 * f) using 1,
    calc (p * b - a * q) * (p * b + a * q)
        = b ^ 2 * (p ^ 2 + 3 * q ^ 2) - q ^ 2 * ((p ^ 2 + 3 * q ^ 2) * f) : by { rw ←hf, ring }
    ... = _ : by ring },

  cases h0 with h0 h0,
  { obtain ⟨v, hv⟩ := h0,
    obtain ⟨u, hu⟩ : (p ^ 2 + 3 * q ^ 2) ∣ (p * a + 3 * q * b),
    { apply @prime.dvd_of_dvd_pow _ _ _ hpprime _ 2,
      rw dvd_add_iff_left,
      { have h1 : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
          (p * a + 3 * q * b) ^ 2 + 3 * (p * b - a * q) ^ 2,
        { ring },
        rw ←h1,
        exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw hv,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [u, v],
    left,
    simp only [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im, neg_mul_eq_neg_mul_symm,
      mul_neg_eq_neg_mul_symm, neg_neg, ←sub_eq_add_neg],
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
      { have h1 : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
          (p * a - 3 * q * b) ^ 2 + 3 * (p * b + a * q) ^ 2,
        { ring },
        rw ←h1,
        exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw hv,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [u, v],
    right,
    simp only [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im, neg_mul_eq_neg_mul_symm,
      mul_neg_eq_neg_mul_symm, neg_neg, ←sub_eq_add_neg],
    split; apply int.eq_of_mul_eq_mul_left hpprime.ne_zero,
    { calc (p ^ 2 + 3 * q ^ 2) * a
          = p * (p * a - 3 * q * b) + 3 * q * (p * b + a * q) : by ring
      ... = _ : by { rw [hu, hv], ring } },
    { calc (p ^ 2 + 3 * q ^ 2) * b
          = p * (p * b + a * q) - q * (p * a - 3 * q * b) : by ring
      ... = _ : by { rw [hu, hv], ring } } },
end

lemma spts.mul_of_dvd
  (a b : ℤ)
  (p q : ℤ)
  (hdvd : (p ^ 2 + 3 * q ^ 2) ∣ (a ^ 2 + 3 * b ^ 2))
  (hpprime : prime (p ^ 2 + 3 * q ^ 2)) :
  ∃ u v,
    ((⟨a, b⟩ : ℤ√-3) = ⟨p, q⟩ * ⟨u, v⟩ ∨ (⟨a, b⟩ : ℤ√-3) = ⟨p, -q⟩ * ⟨u, v⟩) ∧
    (p ^ 2 + 3 * q ^ 2) * (u ^ 2 + 3 * v ^ 2) = a ^ 2 + 3 * b ^ 2 :=
begin
  obtain ⟨u, v, huv⟩ := spts.mul_of_dvd' a b p q hdvd hpprime,
  use [u, v, huv],
  simp only [zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im] at huv,
  obtain ⟨rfl, rfl⟩|⟨rfl, rfl⟩ := huv; ring
end

lemma sq_plus_three_sq_prime_dvd (p q a b: ℕ)
  (hprime : nat.prime (p ^ 2 + 3 * q ^ 2))
  (h : p ^ 2 + 3 * q ^ 2 ∣ a ^ 2 + 3 * b ^ 2) :
  ∃ c d, (p ^ 2 + 3 * q ^ 2) * (c ^ 2 + 3 * d ^ 2) = a ^ 2 + 3 * b ^ 2 :=
begin
  obtain ⟨u, v, -, huv⟩ := spts.mul_of_dvd a b p q _ _,
  { use [u.nat_abs, v.nat_abs],
    zify,
    simp only [←huv, int.nat_abs_pow_two] },
  { norm_cast, exact h },
  { rw nat.prime_iff_prime_int at hprime, convert hprime }
end

lemma factors'
  (a b f g : ℕ)
  (hodd : ¬even f)
  (hgpos : 0 < g)
  (hfactor : f * g = a ^ 2 + 3 * b ^ 2)
  (hnotform : ∀ (f' : ℕ),
                f' ∣ g →
                ¬even f' → (∃ (p q : ℕ), f' = p ^ 2 + 3 * q ^ 2)) :
  ∃ (p q : ℕ), f = p ^ 2 + 3 * q ^ 2 :=
begin
  induction g using nat.strong_induction_on with g IH a b generalizing a b,
  dsimp at IH,
  by_cases H : 2 ∣ a ^ 2 + 3 * b ^ 2,
  { obtain ⟨c, d, hcd⟩ := factors2 H,
    obtain ⟨g', hg'⟩ : 2 ^ 2 ∣ g,
    { apply @nat.coprime.dvd_of_dvd_mul_left f _ (2 ^ 2) _ _,
      { apply nat.coprime.symm,
        exact nat.prime.coprime_pow_of_not_dvd nat.prime_two hodd },
      { rw [hfactor, hcd],
        exact dvd_mul_right _ _ } },
    have hgcdcd : 0 < nat.gcd c d,
    { rw pos_iff_ne_zero,
      intro H',
      obtain ⟨rfl, rfl⟩ := nat.gcd_eq_zero_iff.mp H',
      simp only [zero_pow, zero_lt_two, nat.mul_eq_zero, add_eq_zero_iff, mul_zero,
        pow_eq_zero_iff, three_ne_zero, false_or] at hcd,
      obtain ⟨rfl, rfl⟩ := hcd,
      norm_num at hfactor,
      rcases hfactor with (rfl|rfl),
      { exact hodd nat.even_zero },
      { exact (lt_irrefl 0) hgpos } },
    refine IH g' _ _ _ c d _,
    { rw hg',
      apply nat.lt_mul_left; linarith },
    { rw hg' at hgpos,
      linarith, },
    { intros f' hf'dvd hf'odd,
      refine hnotform f' _ hf'odd,
      rw hg',
      apply dvd_mul_of_dvd_right hf'dvd },
    { rw [←nat.mul_right_inj (by norm_num : 0 < 4), ←hcd, ←hfactor, hg'],
      ring } },
  { by_cases g = 1,
    { subst h,
      rw mul_one at hfactor,
      exact ⟨_, _, hfactor⟩ },
    { rw ←ne.def at h,
      have : 2 ≤ g,
      { rw nat.succ_le_iff,
        apply lt_of_le_of_ne _ h.symm,
        rw nat.succ_le_iff,
        exact hgpos },
      obtain ⟨p, pprime, pdvd⟩ := nat.exists_prime_and_dvd this,
      have podd : ¬even p,
      { rcases pprime.eq_two_or_odd with (rfl|hodd),
        { contrapose! H,
          rw ←hfactor,
          apply dvd_mul_of_dvd_right pdvd },
        { exact nat.not_even_iff.mpr hodd } },
      obtain ⟨A, B, hAB⟩ := hnotform p pdvd podd,
      have pdvd' : A ^ 2 + 3 * B ^ 2 ∣ a ^ 2 + 3 * b ^ 2,
      { rw ←hAB,
        apply dvd_trans pdvd,
        rw ←hfactor,
        exact dvd_mul_left g f },
      rw hAB at pprime,
      obtain ⟨c, d, hcd⟩ := sq_plus_three_sq_prime_dvd A B _ _ pprime pdvd',
      obtain ⟨q, hq⟩ := pdvd,
      refine IH q _ _ _ c d _,
      { rw [hq, hAB],
        apply nat.lt_mul_left _ _ pprime.one_lt,
        rw hq at hgpos,
        rw pos_iff_ne_zero at hgpos ⊢,
        contrapose! hgpos,
        subst hgpos,
        rw mul_zero },
      { rw hq at hgpos,
        rw pos_iff_ne_zero,
        rintro rfl,
        norm_num at hgpos },
      { intros f' hf'dvd hf'odd,
        refine hnotform f' _ hf'odd,
        rw hq,
        apply dvd_mul_of_dvd_right hf'dvd },
      { rw ←nat.mul_right_inj pprime.pos,
        rw hcd,
        rw ←hfactor,
        rw hq,
        rw ←hAB,
        ring } } }
end

lemma factor_div (a x : ℕ)
  (hodd : ¬even x)
  (h0' : 0 < x) :
  ∃ (m : ℕ) (c : ℤ), c + ↑m * ↑x = ↑a ∧ 2 * c.nat_abs < x :=
begin
    set c : ℤ := a % x with hc,
    have : c < x,
    { rw hc,
      exact int.mod_lt_of_pos a (int.coe_nat_lt.mpr h0') },
    by_cases H : 2 * c.nat_abs < x,
    {
      refine ⟨a/x, c, _, H⟩,
      rw hc,
      norm_cast,
      rw mul_comm,
      exact nat.mod_add_div a x },
    { push_neg at H,
      set c' : ℤ := c - x with hc',
      refine ⟨a / x + 1, c', _, _⟩,
      { rw [←int.coe_nat_mul, add_mul, one_mul],
        push_cast,
        rw hc',
        conv_rhs { rw ←nat.mod_add_div a x },
        ring },
      { rw hc',
        rw ←int.nat_abs_neg,
        rw neg_sub,
        zify,
        rw ←int.abs_eq_nat_abs,
        rw abs_of_nonneg _,
        { rw mul_sub,
          rw sub_lt_iff_lt_add,
          rw two_mul,
          rw add_lt_add_iff_left,
          rw hc, norm_cast,
          apply lt_of_le_of_ne,
          { convert H, },
          { contrapose! hodd with heqtwomul,
            exact ⟨_, heqtwomul⟩ } },
        rw sub_nonneg,
        exact le_of_lt this,
      } },
end

lemma factors
  (a b x : ℕ)
  (hcoprime : nat.gcd a b = 1)
  (hodd : ¬even x)
  (hfactor : x ∣ (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, x = c ^ 2 + 3 * d ^ 2 :=
begin
  revert x a b,
  intro x',
  apply nat.strong_induction_on x',
  clear x',
  intros x IH a b hcoprime hodd hfactor,
  have hneg1 : 1 ≤ a ^ 2 + 3 * b ^ 2,
  { rw [nat.succ_le_iff, pos_iff_ne_zero],
    intro H,
    obtain ⟨rfl, rfl⟩ := nat.sq_plus_three_sq_eq_zero_iff.mp H,
    simp only [nat.gcd_zero_right, zero_ne_one] at hcoprime,
    assumption },
  by_cases h : x = 1,
  { subst h,
    refine ⟨1, 0, _⟩,
    ring },
  have h0' : 0 < x,
  { rw pos_iff_ne_zero,
    rintro rfl,
    exact hodd nat.even_zero },

  have h0 : 1 < x,
  { apply lt_of_le_of_ne _ _,
    { apply nat.succ_le_of_lt,
      exact h0' },
    { symmetry,
      exact h } },

  obtain ⟨m, c, ha, hc⟩ := factor_div a x hodd h0',
  obtain ⟨n, d, hb, hd⟩ := factor_div b x hodd h0',

  set e : ℤ := m ^ 2 * x + 2 * m * c + 3 * n ^ 2 * x + 6 * n * d with he,

  have h1 : (a ^ 2 + 3 * b ^ 2 : ℤ) = x * e + c ^ 2 + 3 * d ^ 2,
  { rw [he, ←ha, ←hb],
    ring },

  have h2 : (x : ℤ) ∣ c ^ 2 + 3 * d ^ 2,
  { have : c ^ 2 + 3 * d ^ 2 = x * e + c ^ 2 + 3 * d ^ 2 - x * e,
    { ring },
    rw this,
    apply dvd_sub,
    { rw ←h1,
      norm_cast,
      exact hfactor },
    { exact dvd_mul_right _ _ }
  },

  obtain ⟨y, hy⟩ : x ∣ c.nat_abs ^ 2 + 3 * d.nat_abs ^ 2,
  { rw ←int.coe_nat_dvd,
    push_cast,
    rw [int.nat_abs_pow_two c, int.nat_abs_pow_two d],
    exact h2 },

  have h3 : y < x,
  {
    rw ←mul_lt_mul_left h0',
    rw ←mul_lt_mul_left (by norm_num : 0 < 4),
    calc 4 * (x * y)
        = 4 * (c.nat_abs ^ 2 + 3 * d.nat_abs ^ 2) : by rw hy
    ... = (2 * c.nat_abs) ^ 2 + 3 * (2 * d.nat_abs) ^ 2 : by ring
    ... < x ^ 2 + 3 * x ^ 2 : add_lt_add _ _
    ... = 4 * (x * x) : by ring,
    { exact nat.pow_lt_pow_of_lt_left hc zero_lt_two },
    { rw mul_lt_mul_left (by norm_num : 0 < 3),
      exact nat.pow_lt_pow_of_lt_left hd zero_lt_two },
  },

  have h4 : c ^ 2 + 3 * d ^ 2 ≠ 0,
  { contrapose! hcoprime with H,
    obtain ⟨rfl, rfl⟩ := int.sq_plus_three_sq_eq_zero_iff.mp H,
    norm_num at ha hb,
    norm_cast at ha hb,
    apply nat.not_coprime_of_dvd_of_dvd h0,
    { rw ←ha, exact dvd_mul_left _ _ },
    { rw ←hb, exact dvd_mul_left _ _ } },

  set g := nat.gcd c.nat_abs d.nat_abs with hg,
  have hgpos : 0 < g,
  { rw hg,
    suffices H : 0 < c.nat_abs ∨ 0 < d.nat_abs,
    { cases H,
      { exact nat.gcd_pos_of_pos_left _ H },
      { exact nat.gcd_pos_of_pos_right _ H } },

    contrapose! h4 with H,
    obtain ⟨H1, H2⟩ := H,
    rw [nat.le_zero_iff, int.nat_abs_eq_zero] at H1 H2,
    subst H1,
    subst H2,
    norm_num },
  obtain ⟨C, D, HCDcoprime, HC, HD⟩ := nat.exists_coprime hgpos,
  rw ←hg at HC HD,
  have h5 : x * y = (C ^ 2 + 3 * D ^ 2) * g ^ 2,
  { rw [←hy, HC, HD],
    ring },
  obtain ⟨z, hz⟩ : g ^ 2 ∣ y,
  { have : g ^ 2 ∣ x * y,
    { rw h5, exact dvd_mul_left _ _ },
    apply nat.coprime.dvd_of_dvd_mul_left _ this,
    apply nat.coprime_of_dvd',
    rintros p hpprime hpdvdleft ⟨X, hX⟩,
    obtain ⟨G, hG⟩ := hpprime.dvd_of_dvd_pow hpdvdleft,
    rw ←hcoprime,
    apply nat.dvd_gcd,
    { rw [←int.coe_nat_dvd, ←ha],
      apply dvd_add,
      { rw [int.coe_nat_dvd_left, HC, hG],
        apply dvd_mul_of_dvd_right,
        exact dvd_mul_right _ _ },
      { apply dvd_mul_of_dvd_right,
        rw [int.coe_nat_dvd, hX],
        exact dvd_mul_right _ _ } },
    { rw [←int.coe_nat_dvd, ←hb],
      apply dvd_add,
      { rw [int.coe_nat_dvd_left, HD, hG],
        apply dvd_mul_of_dvd_right,
        exact dvd_mul_right _ _ },
      { apply dvd_mul_of_dvd_right,
        rw [int.coe_nat_dvd, hX],
        exact dvd_mul_right _ _ } } },

  have h6 : x * z = C ^ 2 + 3 * D ^ 2,
  { apply nat.eq_of_mul_eq_mul_right (pow_pos hgpos 2),
    rw [←h5, hz],
    ring },
  have h6' : z ∣ C ^ 2 + 3 * D ^ 2 := h6 ▸ dvd_mul_left z x,

  have h7 : C ^ 2 + 3 * D ^ 2 ≠ 0,
  { contrapose! hcoprime with H,
    obtain ⟨rfl, rfl⟩ := nat.sq_plus_three_sq_eq_zero_iff.mp H,
    rw [zero_mul, int.nat_abs_eq_zero] at HC HD,
    subst HC,
    subst HD,
    norm_num at h4 },
  have h8 : 0 < z,
  { rw pos_iff_ne_zero,
    rintro rfl,
    rw ←h6 at h7,
    norm_num at h7 },
  apply factors' C D x z hodd h8 h6,
  intros w hwdvd hwodd,
  refine IH w _ C D HCDcoprime hwodd (dvd_trans hwdvd h6'),
  { calc w
        ≤ z : nat.le_of_dvd h8 hwdvd
    ... ≤ y : by { rw hz, exact nat.le_mul_of_pos_left (pow_pos hgpos 2) }
    ... < x : h3 },
end

theorem spts.eq_one
  {a b : ℤ}
  (h : a^2 + 3 * b ^ 2 = 1) :
  abs a = 1 ∧ b = 0 :=
begin
  contrapose! h,
  by_cases H : abs a = 1,
  { specialize h H,
    rw [←int.nat_abs_pow_two a, ←int.abs_eq_nat_abs, H, one_pow],
    contrapose! h,
    apply pow_eq_zero,
    apply (int.eq_zero_or_eq_zero_of_mul_eq_zero _).resolve_left three_ne_zero,
    apply int.add_left_cancel,
    rw [h, int.add_zero] },
  { cases lt_or_gt_of_ne H with H H,
    have : abs a < 0 + 1 := H,
    rw [int.lt_add_one_iff] at this,
    have := le_antisymm this (abs_nonneg _),
    rw abs_eq_zero at this,
    subst this,
    rw [zero_pow zero_lt_two, zero_add],
    rw [←int.nat_abs_pow_two b, ←int.abs_eq_nat_abs],
    by_cases hb : abs b = 0,
    { norm_num [hb] },
    { apply ne_of_gt,
      rw gt_iff_lt,
      have : 1 ≤ abs b,
      { apply le_of_not_gt,
        intro hb',
        apply hb,
        change abs b < 0 + 1 at hb',
        rw [int.lt_add_one_iff] at hb',
        exact le_antisymm hb' (abs_nonneg _) },
      have : 1 ≤ (abs b) ^ 2,
      { rw ←one_pow 2,
        apply pow_le_pow_of_le_left zero_le_one this, },
      linarith },
    { apply ne_of_gt,
      have : 0 ≤ 3 * b ^ 2,
      { apply mul_nonneg,
        { norm_num },
        { apply pow_two_nonneg } },
      apply lt_add_of_lt_of_nonneg _ this,
      rw [←int.nat_abs_pow_two, ←int.abs_eq_nat_abs, ←one_pow 2],
      apply pow_lt_pow_of_lt_left H zero_le_one zero_lt_two } }
end

lemma spts.nonneg
  (a b : ℤ) :
  0 ≤ a ^ 2 + 3 * b ^ 2 :=
add_nonneg (pow_two_nonneg a) (mul_nonneg zero_lt_three.le (pow_two_nonneg b))

lemma spts.not_zero_of_coprime -- TODO ne_zero
  {a b : ℤ}
  (hcoprime : is_coprime a b) :
  a ^ 2 + 3 * b ^ 2 ≠ 0 :=
begin
  contrapose! hcoprime with H,
  obtain ⟨rfl, rfl⟩ := int.sq_plus_three_sq_eq_zero_iff.mp H,
  exact not_coprime_zero_zero,
end

lemma spts.pos_of_coprime
  {a b : ℤ}
  (hcoprime : is_coprime a b) :
  0 < a ^ 2 + 3 * b ^ 2 :=
lt_of_le_of_ne (spts.nonneg _ _) (spts.not_zero_of_coprime hcoprime).symm

lemma spts.not_two
  (a b : ℤ) :
  a ^ 2 + 3 * b ^ 2 ≠ 2 :=
begin
  by_cases hb : b = 0,
  { subst hb,
    rw [zero_pow zero_lt_two, mul_zero, add_zero, ←int.nat_abs_pow_two],
    norm_cast,
    apply (nat.pow_left_strict_mono one_le_two).monotone.ne_of_lt_of_lt_nat 1; norm_num },
  { apply ne_of_gt,
    apply lt_add_of_nonneg_of_lt,
    apply (pow_two_nonneg _),
    rw [←int.nat_abs_pow_two],
    norm_cast,
    have := int.nat_abs_ne_zero_of_ne_zero hb,
    rw [←pos_iff_ne_zero] at this,
    have := nat.pow_lt_pow_of_lt_left this zero_lt_two,
    linarith }
end

lemma spts.four
  {p q : ℤ}
  (hfour : p ^ 2 + 3 * q ^ 2 = 4)
  (hq : q ≠ 0) :
  abs p = 1 ∧ abs q = 1 :=
begin
  rw [←int.nat_abs_pow_two p, ←int.nat_abs_pow_two q, ←int.abs_eq_nat_abs, ←int.abs_eq_nat_abs] at hfour,
  have hq' : abs q = 1,
  { apply le_antisymm,
    { contrapose! hfour with hq',
      have : 2 ≤ abs q,
      { rwa ←int.add_one_le_iff at hq' },
      have : 2 ^ 2 ≤ (abs q) ^ 2 := pow_le_pow_of_le_left zero_le_two this 2,
      apply ne_of_gt,
      calc 4 < 3 * 2 ^ 2 : by norm_num
      ... ≤ 3 * (abs q) ^ 2 : int.mul_le_mul_of_nonneg_left this (by norm_num)
      ... ≤ abs p ^ 2 + 3 * abs q ^ 2 : le_add_of_nonneg_left (pow_two_nonneg (abs p)) },
    { rwa [←int.zero_add 1, int.add_one_le_iff, abs_pos] } },
  have : (4 - 3 : ℤ) = 1 ^ 2,
  { norm_num },
  rw [hq', one_pow, mul_one, ←eq_sub_iff_add_eq, this] at hfour,
  refine ⟨(eq_or_eq_neg_of_pow_two_eq_pow_two _ _ hfour).resolve_right _, hq'⟩,
  apply ne_of_gt,
  calc -1 < 0 : by norm_num
  ... ≤ abs p : abs_nonneg _,
end

lemma spts.four_of_coprime
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
