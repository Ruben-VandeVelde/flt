import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid.basic
import tactic
import data.nat.modeq
import ring_theory.int.basic
import number_theory.zsqrtd.basic
import .primes

lemma zsqrtd.norm_def' {d : ℤ} (n : ℤ√d) : n.norm = n.re * n.re - d * (n.im * n.im) :=
by rw [zsqrtd.norm_def, mul_assoc]

lemma zsqrtd.exists {d : ℤ} (a : ℤ√d) (him : a.im ≠ 0) :
  ∃ (c : ℤ√d), a.norm = c.norm ∧ 0 ≤ c.re ∧ c.im ≠ 0 :=
begin
  cases le_or_lt a.re 0 with hre hre,
  { use -a,
    simp only [hre, him, zsqrtd.norm_neg, eq_self_iff_true, zsqrtd.neg_im, zsqrtd.neg_re, and_self,
      neg_nonneg, ne.def, not_false_iff, neg_eq_zero] },
  { use a, simp only [hre.le, him, eq_self_iff_true, and_self, ne.def, not_false_iff] },
end

lemma zsqrtd.coe_int_norm {d : ℤ} (z : ℤ) : (z : ℤ√d).norm = z * z :=
by rw [zsqrtd.norm_def, zsqrtd.coe_int_re, zsqrtd.coe_int_im, mul_zero, sub_zero]

@[simp, norm_cast]
lemma zsqrtd.coe_int_dvd_coe_int {d : ℤ} (a b : ℤ) : (a : ℤ√d) ∣ b ↔ a ∣ b :=
begin
  split; rintro ⟨d, hd⟩,
  { simp only [zsqrtd.ext, add_zero, zsqrtd.coe_int_re, zero_mul, zsqrtd.mul_im, zsqrtd.mul_re,
      zero_eq_mul, mul_zero, zsqrtd.coe_int_im] at hd,
    obtain ⟨rfl, (rfl|h2)⟩ := hd;
    exact dvd_mul_right _ _ },
  { simp only [hd, int.cast_mul, dvd_mul_right] },
end

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

-- Edwards p49 step (2')
lemma factors2
  {a : ℤ√-3}
  (heven : even a.norm) :
  ∃ b : ℤ√-3, a.norm = 4 * b.norm :=
begin
  have hparity : even a.re ↔ even a.im,
  { simpa [two_ne_zero, zsqrtd.norm_def] with parity_simps using heven },
  simp only [iff_iff_and_or_not_and_not, ←int.odd_iff_not_even] at hparity,

  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩|⟨hre, him⟩ := hparity,
  { use ⟨c, d⟩,
    simp only [zsqrtd.norm_def, hc, hd],
    ring },
  { cases int.four_dvd_add_or_sub_of_odd hre him with h4 h4,
    { obtain ⟨v, hv⟩ := h4,
      use ⟨v - a.im, v⟩,
      rw [eq_comm, ←sub_eq_iff_eq_add] at hv,
      simp only [zsqrtd.norm_def, ←hv],
      ring },
    { obtain ⟨v, hv⟩ := h4,
      use ⟨v + a.im, v⟩,
      rw [sub_eq_iff_eq_add] at hv,
      simp only [zsqrtd.norm_def, hv],
      ring } }
end

lemma zsqrtd.smul_re {d a : ℤ} {b : ℤ√d} : (↑a * b).re = a * b.re := by simp
lemma zsqrtd.smul_im {d a : ℤ} {b : ℤ√d} : (↑a * b).im = a * b.im := by simp

protected lemma zsqrtd.eq_of_smul_eq_smul_left {d a : ℤ} {b c : ℤ√d}
  (ha : a ≠ 0) (h : ↑a * b = a * c) : b = c :=
begin
  rw zsqrtd.ext at h ⊢,
  apply and.imp _ _ h;
  simp only [zsqrtd.smul_re, zsqrtd.smul_im];
  apply int.eq_of_mul_eq_mul_left ha,
end

lemma spts.mul_of_dvd'
  {a p : ℤ√-3}
  (hdvd : p.norm ∣ a.norm)
  (hpprime : prime p.norm) :
  ∃ u : ℤ√-3, a = p * u ∨ a = p.conj * u :=
begin
  obtain ⟨f, hf⟩ := hdvd,
  have h0 : p.norm ∣ p.re * a.im - a.re * p.im ∨
         p.norm ∣ p.re * a.im + a.re * p.im,
  { apply hpprime.dvd_or_dvd,
    convert dvd_mul_right p.norm (a.im ^ 2 - p.im ^ 2 * f) using 1,
    transitivity a.im ^ 2 * p.norm - p.im ^ 2 * (p.norm * f),
    { rw [←hf, zsqrtd.norm_def, zsqrtd.norm_def], ring },
    { rw [zsqrtd.norm_def], ring } },

  obtain ⟨A, HA⟩ : ∃ A : units ℤ, p.norm ∣ p.re * a.im + A * a.re * p.im,
  { cases h0 with h0 h0;
    [use -1, use 1];
    convert h0;
    simp, },

  have HAsq : (A : ℤ) ^ 2 = 1,
  { calc (A : ℤ) ^ 2
        = ((A ^ 2 : units ℤ) : ℤ) : (units.coe_pow _ _).symm
    ... = ((1 : units ℤ) : ℤ) : congr_arg _ (int.units_sq A)
    ... = 1 : units.coe_one },

  { set X : ℤ√-3 := ⟨p.re * a.re - A * 3 * p.im * a.im, p.re * a.im + A * a.re * p.im⟩ with HX,
    obtain ⟨U, HU⟩ : (p.norm : ℤ√-3) ∣ X,
    { rw zsqrtd.coe_int_dvd_iff,
      refine ⟨_, HA⟩,
      apply @prime.dvd_of_dvd_pow _ _ _ hpprime _ 2,
      have : X.re ^ 2 = X.norm - 3 * X.im ^ 2,
      { rw [zsqrtd.norm_def], ring },
      rw this,
      apply dvd_sub,
      { use a.norm,
        transitivity (p.re * a.re) ^ 2 + (A : ℤ) ^ 2 * (3 * p.im * a.im) ^ 2 +
          3 * ((p.re * a.im) ^ 2 + (A : ℤ) ^ 2 * (a.re * p.im) ^ 2),
        { simp only [zsqrtd.norm_def],
          ring },
        { simp only [zsqrtd.norm_def, HAsq],
          ring } },
      { apply dvd_mul_of_dvd_right,
        exact dvd_pow HA two_ne_zero } },
    use U,
    suffices : a = ⟨p.re, -A * p.im⟩ * U,
    { apply or.imp _ _ (int.units_eq_one_or A).symm; rintro rfl; simpa [zsqrtd.ext] using this },
    apply zsqrtd.eq_of_smul_eq_smul_left hpprime.ne_zero,
    have : p.norm = p.re ^ 2 + 3 * ↑A ^ 2 * p.im ^ 2,
    { rw [zsqrtd.norm_def, HAsq], ring },
    rw [mul_comm _ U, ←mul_assoc, ←HU, HX],
    simp only [zsqrtd.ext, neg_mul_eq_neg_mul_symm, add_zero, zsqrtd.coe_int_re, zero_mul,
      mul_neg_eq_neg_mul_symm, zsqrtd.mul_im, zsqrtd.mul_re, neg_neg, mul_zero, neg_zero,
      zsqrtd.coe_int_im, this],
    split; ring },
end

-- Edwards p49 step (3')
lemma spts.mul_of_dvd''
  {a p : ℤ√-3}
  (hdvd : p.norm ∣ a.norm)
  (hpprime : prime p.norm) :
  ∃ u : ℤ√-3,
    (a = p * u ∨ a = p.conj * u) ∧
    a.norm = p.norm * u.norm :=
begin
  obtain ⟨u, hu⟩ := spts.mul_of_dvd' hdvd hpprime,
  refine ⟨u, hu, _⟩,
  obtain (rfl|rfl) := hu,
  { rw [zsqrtd.norm_mul] },
  { rw [zsqrtd.norm_mul, zsqrtd.norm_conj] },
end

-- Edwards p49 step (4'), contraposed
lemma factors'
  (a : ℤ√-3)
  (f : ℤ)
  (g : ℤ)
  (hodd : odd f)
  (hgpos : g ≠ 0)
  (hfactor : abs (f * g) = a.norm)
  (hnotform : ∀ (f' : ℤ), f' ∣ g → odd f' → (∃ (p : ℤ√-3), abs f' = p.norm)) :
  ∃ (p : ℤ√-3), abs f = p.norm :=
begin
  induction hg : g.nat_abs using nat.strong_induction_on with g'' IH a generalizing a g,
  dsimp at IH,
  by_cases H : even (zsqrtd.norm a),
  { obtain ⟨c, hc⟩ := factors2 H,
    obtain ⟨g', rfl⟩ : 4 ∣ g,
    { apply is_coprime.dvd_of_dvd_mul_left,
      { show is_coprime _ f,
        rw [int.odd_iff_not_even, even_iff_two_dvd, ←prime.coprime_iff_not_dvd int.prime_two] at hodd,
        convert hodd.pow_left,
        rw sq,
        norm_num },
      { rw [←dvd_abs, hfactor, hc],
        exact dvd_mul_right _ _ } },
    have hg'pos : g' ≠ 0 := right_ne_zero_of_mul hgpos,
    have hgcdcd : 0 < int.gcd c.re c.im,
    { rw [pos_iff_ne_zero, ne.def, int.gcd_eq_zero_iff],
      intro H',
      obtain rfl : c = 0,
      { simp only [zsqrtd.ext, eq_self_iff_true, zsqrtd.zero_im, and_self, zsqrtd.zero_re, H'] },
      rw [zsqrtd.norm_zero, mul_zero] at hc,
      rw [hc, abs_eq_zero, mul_eq_zero] at hfactor,
      obtain (rfl|hg) := hfactor,
      { rw int.odd_iff_not_even at hodd,
        exact hodd int.even_zero },
      { exact hgpos hg } },
    refine IH g'.nat_abs _ c g' hg'pos _ _ rfl,
    { rw [←hg, int.nat_abs_mul],
      apply lt_mul_of_one_lt_left (int.nat_abs_pos_of_ne_zero hg'pos),
      norm_num },
    { rw [←mul_right_inj' (@four_ne_zero ℤ _ _), ←hc, ←hfactor, mul_left_comm,
        abs_mul (4 : ℤ), abs_of_nonneg (@zero_lt_four ℤ _ _).le] },
    { intros f' hf'dvd hf'odd,
      refine hnotform f' _ hf'odd,
      exact hf'dvd.mul_left _ } },
  { by_cases h : |g| = 1,
    { rw [abs_mul, h, mul_one] at hfactor,
      exact ⟨_, hfactor⟩ },
    { replace h : 2 ≤ g.nat_abs,
      { rw nat.succ_le_iff,
        apply lt_of_le_of_ne,
        { rw nat.succ_le_iff,
          exact int.nat_abs_pos_of_ne_zero hgpos },
        { zify,
          rwa [ne_comm, ←int.abs_eq_nat_abs] } },
      obtain ⟨p, pprime, pdvd⟩ := int.exists_prime_and_dvd h,
      have : p ∣ a.norm,
      { rw [←hfactor, dvd_abs],
        exact pdvd.mul_left _ },
      have podd : odd p := int.odd_iff_not_even.mpr (λ X, H (dvd_trans X this)),
      obtain ⟨A, HA⟩ := hnotform p pdvd podd,
      have pprime' := pprime.abs,
      rw [HA] at pprime',
      have pdvd' : A.norm ∣ a.norm,
      { rw [←hfactor, ←HA, abs_dvd_abs],
        exact dvd_mul_of_dvd_right pdvd _ },
      obtain ⟨c, -, hcd⟩ := spts.mul_of_dvd'' pdvd' pprime',
      obtain ⟨q, rfl⟩ := pdvd,
      have hqpos : q ≠ 0 := right_ne_zero_of_mul hgpos,
      refine IH q.nat_abs _ c _ hqpos _ _ rfl,
      { rw [←hg, int.nat_abs_mul],
        apply lt_mul_of_one_lt_left (int.nat_abs_pos_of_ne_zero hqpos),
        rw int.prime_iff_nat_abs_prime at pprime,
        exact pprime.one_lt },
      { rw [←mul_right_inj' pprime'.ne_zero, ←hcd, ←hfactor, ←HA, mul_left_comm, ←abs_mul] },
      { intros f' hf'dvd hf'odd,
        refine hnotform f' _ hf'odd,
        exact hf'dvd.mul_left _ } } }
end

lemma int.factors'
  {a : ℤ√-3}
  (f g : ℤ)
  (hodd : odd f)
  (hgpos : g ≠ 0)
  (hfactor : f * g = a.norm)
  (hnotform : ∀ (f' : ℤ),
                f' ∣ g →
                ¬even f' → (∃ (p : ℤ√-3), abs f' = p.norm)) :
  ∃ (p : ℤ√-3), abs f = p.norm :=
begin
  refine factors' a f g hodd hgpos _ _,
  { rw [hfactor],
    refine abs_of_nonneg _,
    apply zsqrtd.norm_nonneg,
    norm_num },
  { intros f fdvd fodd,
    rw int.odd_iff_not_even at fodd,
    exact hnotform f fdvd fodd },
end

lemma zqrtd.factor_div (a : ℤ√-3) {x : ℤ} (hodd : odd x) :
  ∃ c m : ℤ√-3, a = c + m * x ∧ c.norm < x ^ 2 :=
begin
  obtain ⟨m, c, ha, hc⟩ := int.factor_div a.re x hodd,
  obtain ⟨n, d, hb, hd⟩ := int.factor_div a.im x hodd,
  set c' : ℤ√-3 := ⟨c, d⟩,
  refine ⟨c', ⟨m, n⟩, _, _⟩,
  { simp only [zsqrtd.ext, ha, hb, add_zero, zsqrtd.coe_int_re, eq_self_iff_true, zsqrtd.mul_im,
      zero_add, zsqrtd.add_im, and_self, zsqrtd.mul_re, mul_zero, zsqrtd.add_re, zsqrtd.coe_int_im] },
  { rw ←mul_lt_mul_left (by norm_num : (0 : ℤ) < 4),
    calc 4 * c'.norm
        = (2 * c) ^ 2 + 3 * (2 * d) ^ 2 : by { rw zsqrtd.norm_def, ring }
    ... < x ^ 2 + 3 * x ^ 2 : add_lt_add _ _
    ... = 4 * x ^ 2 : by ring,
    { rw [mul_pow, ←int.nat_abs_pow_two c, ←int.nat_abs_pow_two x],
      norm_cast,
      rw [←mul_pow],
      exact nat.pow_lt_pow_of_lt_left hc zero_lt_two },
    { rw [mul_pow, ←int.nat_abs_pow_two d, ←int.nat_abs_pow_two x],
      rw mul_lt_mul_left (by norm_num : (0 : ℤ) < 3),
      norm_cast,
      rw [←mul_pow],
      exact nat.pow_lt_pow_of_lt_left hd zero_lt_two } },
end

-- Edwards p50 step (5')
lemma factors
  (a : ℤ√-3)
  (x : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hodd : odd x)
  (hfactor : x ∣ a.norm) :
  ∃ c : ℤ√-3, abs x = c.norm :=
begin
  induction hx' : x.nat_abs using nat.strong_induction_on with x' IH generalizing a x,
  subst hx',
  have hneg1 : 1 ≤ a.norm,
  { rw [←int.sub_one_lt_iff, sub_self],
    apply lt_of_le_of_ne (zsqrtd.norm_nonneg (by norm_num) a),
    symmetry,
    intro H,
    rw zsqrtd.norm_eq_zero_iff (by norm_num : (-3 : ℤ) < 0) at H,
    simpa only [H, not_coprime_zero_zero, add_zero, zsqrtd.zero_im, zsqrtd.zero_re] using hcoprime },

  have h0 : x ≠ 0,
  { rintro rfl,
    simpa only [int.even_zero, not_true, int.odd_iff_not_even] using hodd },
  have h0' : 1 ≤ abs x,
  { rwa [←int.sub_one_lt_iff, sub_self, abs_pos] },
  cases h0'.eq_or_lt with h h,
  { rw ←h,
    refine ⟨⟨1, 0⟩, _⟩; norm_num [zsqrtd.norm_def] },
  have h0'' : 0 < x.nat_abs := int.nat_abs_pos_of_ne_zero h0,

  obtain ⟨c', m, h2, h2'⟩ := zqrtd.factor_div a hodd,

  have h1 : c' ≠ 0,
  { contrapose! h with H,
    apply le_of_eq,
    simp only [H, zero_add] at h2,
    have : (x : ℤ√-3) ∣ a,
    { rw h2, exact dvd_mul_left _ _ },
    rw zsqrtd.coe_int_dvd_iff at this,
    rw ←int.is_unit_iff_abs_eq,
    exact hcoprime.is_unit_of_dvd' this.1 this.2 },

  obtain ⟨y, hy⟩ : x ∣ c'.norm,
  { set e : ℤ := m.re ^ 2 * x + 2 * m.re * c'.re + 3 * m.im ^ 2 * x + 6 * m.im * c'.im with he,
    convert dvd_sub hfactor (dvd_mul_right x e),
    rw [he, zsqrtd.norm_def, zsqrtd.norm_def, h2],
    simp only [zsqrtd.coe_int_re, zsqrtd.mul_im, zsqrtd.add_im, zsqrtd.mul_re, zsqrtd.add_re,
      zsqrtd.coe_int_im],
    ring },

  have h3 : y.nat_abs < x.nat_abs,
  { rw [←mul_lt_mul_left h0'', ←pow_two, ←int.nat_abs_mul, ←hy],
    zify,
    rwa [int.nat_abs_pow_two x, int.nat_abs_of_nonneg (zsqrtd.norm_nonneg (by norm_num) c')] },

  have h4 : c'.norm ≠ 0,
  { rwa [ne.def, zsqrtd.norm_eq_zero_iff (by norm_num) c'] },

  set g := int.gcd c'.re c'.im with hg,
  have hgpos : 0 < g,
  { rw [hg, pos_iff_ne_zero],
    contrapose! h4 with H,
    obtain ⟨H1, H2⟩ := int.gcd_eq_zero_iff.mp H,
    simp only [neg_mul_eq_neg_mul_symm, eq_self_iff_true, H1, H2, mul_zero, sub_self, neg_zero,
      zsqrtd.norm] },
  have hgnezero := int.coe_nat_ne_zero_iff_pos.mpr hgpos,
  obtain ⟨C', HC', HCDcoprime⟩ :
    ∃ C' : ℤ√-3, c' = ((g : ℤ) : ℤ√-3) * C' ∧ is_coprime C'.re C'.im,
  { obtain ⟨re, im, H1, Hre, Him⟩ := int.exists_gcd_one hgpos,
    rw [←hg, mul_comm] at Hre Him,
    use ⟨re, im⟩,
    split,
    { rw [zsqrtd.smul_val, zsqrtd.ext, Hre, Him], split; refl },
    { simp only [←int.gcd_eq_one_iff_coprime, H1] } },
  have h5 : x * y = g ^ 2 * C'.norm,
  { rw [←hy, HC', zsqrtd.norm_mul, zsqrtd.coe_int_norm, ←pow_two] },
  obtain ⟨z, hz⟩ : (g ^ 2 : ℤ) ∣ y,
  { have : (g ^ 2 : ℤ) ∣ x * y,
    { rw h5, exact dvd_mul_right _ _ },
    apply is_coprime.dvd_of_dvd_mul_left _ this,
    apply is_coprime_of_prime_dvd,
    { contrapose! h0, exact h0.2 },
    rintros p hpprime hpdvdleft ⟨X, hX⟩,
    obtain hG := hpprime.dvd_of_dvd_pow hpdvdleft,
    apply hpprime.not_unit,
    have : ↑p ∣ a,
    { rw [h2, hX, HC'],
      apply dvd_add,
      { apply dvd_mul_of_dvd_left,
        norm_cast,
        exact hG },
      { rw [zsqrtd.coe_int_mul],
        exact (dvd_mul_right _ _).mul_left _ } },
    rw zsqrtd.coe_int_dvd_iff at this,
    exact hcoprime.is_unit_of_dvd' this.1 this.2 },

  have h6 : x * z = C'.norm,
  { apply int.eq_of_mul_eq_mul_left (pow_ne_zero 2 hgnezero),
    rw [←h5, hz],
    ring },

  have h8 : z ≠ 0,
  { apply right_ne_zero_of_mul,
    rw h6,
    apply right_ne_zero_of_mul,
    rwa [←h5, ←hy] },
  refine int.factors' x z hodd h8 h6 _,
  intros w hwdvd hwodd,
  rw ←int.odd_iff_not_even at hwodd,
  refine IH w.nat_abs _ C' w HCDcoprime hwodd _ rfl,
  { calc w.nat_abs
        ≤ z.nat_abs : nat.le_of_dvd (int.nat_abs_pos_of_ne_zero h8) (int.nat_abs_dvd_iff_dvd.mpr hwdvd)
    ... ≤ y.nat_abs : by { rw [hz, int.nat_abs_mul], exact nat.le_mul_of_pos_left (pow_pos hgpos 2) }
    ... < x.nat_abs : h3 },
  { rw ←h6,
    exact dvd_mul_of_dvd_right hwdvd x },
end

theorem spts.eq_one
  {a : ℤ√-3}
  (h : a.norm = 1) :
  abs a.re = 1 ∧ a.im = 0 :=
begin
  suffices H : abs a.re = 1,
  { refine ⟨H, _⟩,
    rw [zsqrtd.norm_def', ←int.nat_abs_mul_self' a.re, ←int.abs_eq_nat_abs, H, one_mul,
      neg_mul_eq_neg_mul_symm, sub_neg_eq_add, add_right_eq_self, mul_eq_zero,
      mul_self_eq_zero] at h,
    exact h.resolve_left three_ne_zero },
  contrapose! h,
  cases lt_or_gt_of_ne h with H H,
  { have : a.re = 0,
    { rwa [←abs_nonpos_iff, ←int.lt_add_one_iff, zero_add] },
    simp only [zsqrtd.norm_def, this, zero_mul, zero_sub, neg_mul_eq_neg_mul_symm, neg_neg],
    by_cases hb : a.im = 0,
    { simp only [hb, not_false_iff, zero_ne_one, mul_zero] },
    { have : 1 ≤ abs a.im,
      { rwa [←abs_nonpos_iff, ←int.lt_add_one_iff, zero_add, not_lt] at hb },
      have : 1 ≤ a.im ^ 2,
      { rw ←sq_abs,
        exact pow_le_pow_of_le_left zero_le_one this 2 },
      linarith } },
  { apply ne_of_gt,
    rw [zsqrtd.norm_def, neg_mul_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm, sub_neg_eq_add],
    apply lt_add_of_lt_of_nonneg,
    { rw [←sq, ←sq_abs],
      exact pow_lt_pow_of_lt_left H zero_le_one zero_lt_two },
    { rw mul_assoc,
      exact mul_nonneg zero_lt_three.le (mul_self_nonneg _) } }
end

theorem spts.eq_one'
  {a : ℤ√-3}
  (h : a.norm = 1) :
  a = 1 ∨ a = -1 :=
begin
  simp only [zsqrtd.ext, zsqrtd.one_re, zsqrtd.one_im, zsqrtd.neg_im, zsqrtd.neg_re, neg_zero,
    ←or_and_distrib_right, ←abs_eq (@zero_le_one ℤ _), spts.eq_one h, eq_self_iff_true, and_self],
end

lemma spts.ne_zero_of_coprime'
  (a : ℤ√-3)
  (hcoprime : is_coprime a.re a.im) :
  a.norm ≠ 0 :=
begin
  contrapose! hcoprime with H,
  obtain ⟨rfl, rfl⟩ := (zsqrtd.norm_eq_zero_iff (by norm_num) _).mp H,
  exact not_coprime_zero_zero,
end

lemma spts.pos_of_coprime'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  0 < a.norm :=
begin
  apply lt_of_le_of_ne,
  { apply zsqrtd.norm_nonneg, norm_num },
  { symmetry, exact spts.ne_zero_of_coprime' _ hcoprime }
end

lemma spts.one_lt_of_im_ne_zero
  (a : ℤ√-3)
  (hb : a.im ≠ 0) :
  1 < a.norm :=
begin
  apply lt_of_le_of_ne,
  { rw [←int.sub_one_lt_iff, sub_self],
    apply lt_of_le_of_ne (zsqrtd.norm_nonneg (by norm_num) a),
    contrapose! hb,
    rw [eq_comm, zsqrtd.norm_eq_zero_iff (by norm_num) a] at hb,
    rw [hb, zsqrtd.zero_im] },
  { intro H,
    exact hb (spts.eq_one H.symm).2 }
end

lemma spts.not_two
  (a b : ℤ) :
  a ^ 2 + 3 * b ^ 2 ≠ 2 :=
begin
  obtain rfl|hb := eq_or_ne b 0,
  { rw [zero_pow zero_lt_two, mul_zero, add_zero, ←int.nat_abs_pow_two],
    norm_cast,
    apply (nat.pow_left_strict_mono one_le_two).monotone.ne_of_lt_of_lt_nat 1; norm_num },
  { apply ne_of_gt,
    apply lt_add_of_nonneg_of_lt (pow_two_nonneg a),
    rw [←int.nat_abs_pow_two],
    norm_cast,
    have := int.nat_abs_ne_zero_of_ne_zero hb,
    rw [←pos_iff_ne_zero] at this,
    have := nat.pow_lt_pow_of_lt_left this zero_lt_two,
    linarith }
end

lemma spts.not_two'
  (a : ℤ√-3) :
  a.norm ≠ 2 :=
begin
  rw zsqrt3.norm,
  exact spts.not_two a.re a.im,
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
  refine ⟨(eq_or_eq_neg_of_sq_eq_sq _ _ hfour).resolve_right _, hq'⟩,
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
  rw [is_coprime_zero_right, int.is_unit_iff_abs_eq] at hcoprime,
  rw [zero_pow zero_lt_two, mul_zero, add_zero, ←int.nat_abs_pow_two, ←int.abs_eq_nat_abs, hcoprime] at hfour,
  norm_num at hfour
end
