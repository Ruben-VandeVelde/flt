import data.int.basic
import data.int.parity
import tactic
import .primes
import .spts
import .odd_prime_or_four

lemma odd_prime_or_four.im_ne_zero
  {p : ℤ√-3}
  (h: odd_prime_or_four p.norm)
  (hcoprime: is_coprime p.re p.im) :
  p.im ≠ 0 :=
begin
  intro H,
  rw [zsqrtd.norm_def, H, mul_zero, sub_zero, ←pow_two] at h,
  obtain h|⟨hp, hodd⟩ := h,
  { rw [H, is_coprime_zero_right, int.is_unit_iff_abs_eq] at hcoprime,
    rw [←sq_abs, hcoprime] at h,
    norm_num at h },
  { exact pow_not_prime one_lt_two.ne' hp }
end

lemma zsqrt3.is_unit_iff {z : ℤ√-3} : is_unit z ↔ abs z.re = 1 ∧ z.im = 0 :=
begin
  rw [←zsqrtd.norm_eq_one_iff, ←int.coe_nat_inj', int.coe_nat_one,
    int.nat_abs_of_nonneg (zsqrtd.norm_nonneg (by norm_num) z)],
  refine ⟨spts.eq_one, λ h, _⟩,
  rw [zsqrtd.norm_def, h.2, mul_zero, sub_zero, ←sq, ←sq_abs, h.1, one_pow]
end

lemma zsqrt3.coe_of_is_unit {z : ℤ√-3} (h : is_unit z) : ∃ u : units ℤ, z = u :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.is_unit_iff.mp h,
  obtain ⟨v, hv⟩ : is_unit z.re,
  { rwa int.is_unit_iff_abs_eq },
  use v,
  rw [zsqrtd.ext, hu, ←hv],
  simp only [zsqrtd.coe_int_re, and_true, eq_self_iff_true, coe_coe, zsqrtd.coe_int_im],
end

lemma zsqrt3.coe_of_is_unit' {z : ℤ√-3} (h : is_unit z) : ∃ u : ℤ, z = u ∧ abs u = 1 :=
begin
  obtain ⟨u, hu⟩ := zsqrt3.coe_of_is_unit h,
  refine ⟨u, _, _⟩,
  { rw [hu, coe_coe] },
  { exact int.is_unit_iff_abs_eq.mp u.is_unit },
end

lemma odd_prime_or_four.factors
  (a : ℤ√-3)
  (x : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hx : odd_prime_or_four x)
  (hfactor : x ∣ a.norm) :
  ∃ c : ℤ√-3, abs x = c.norm ∧ 0 ≤ c.re ∧ c.im ≠ 0 :=
begin
  obtain rfl|⟨hprime, hodd⟩ := hx,
  { refine ⟨⟨1, 1⟩, _, zero_le_one, one_ne_zero⟩,
    simp only [zsqrtd.norm_def, mul_one, abs_of_pos, zero_lt_four, sub_neg_eq_add],
    norm_num },
  { obtain ⟨c, hc⟩ := factors a x hcoprime hodd hfactor,
    rw hc,
    apply zsqrtd.exists c,
    intro H,
    apply pow_not_prime one_lt_two.ne',
    convert hprime.abs,
    rwa [zsqrtd.norm_def, H, mul_zero, sub_zero, ←pow_two, eq_comm] at hc }
end

lemma step1a
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  odd a.re ∧ odd a.im :=
begin
  rw [int.odd_iff_not_even, int.odd_iff_not_even],
  have : even a.re ↔ even a.im,
  { simpa [zsqrtd.norm_def] with parity_simps using heven },
  apply (iff_iff_and_or_not_and_not.mp this).resolve_left,
  rintro ⟨hre, him⟩,
  have := hcoprime.is_unit_of_dvd' hre him,
  rw is_unit_iff_dvd_one at this,
  norm_num at this,
end

lemma step1
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  ∃ u : ℤ√-3, (a = ⟨1, 1⟩ * u ∨ a = ⟨1, -1⟩ * u) :=
begin
  obtain ⟨ha, hb⟩ := step1a hcoprime heven,
  obtain hdvd|hdvd := int.four_dvd_add_or_sub_of_odd ha hb,
  { obtain ⟨v, hv⟩ := hdvd,
    rw ←eq_sub_iff_add_eq at hv,
    use ⟨v - a.im, v⟩,
    right,
    rw [zsqrtd.ext, hv, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
  { obtain ⟨v, hv⟩ := hdvd,
    rw sub_eq_iff_eq_add at hv,
    use ⟨a.im + v, -v⟩,
    left,
    rw [zsqrtd.ext, hv, zsqrtd.mul_re, zsqrtd.mul_im],
    dsimp only,
    split; ring },
end

lemma is_coprime.mul_unit_left {R : Type*} [comm_semiring R] (x y z : R)
  (hu : is_unit x) : is_coprime (x * y) (x * z) ↔ is_coprime y z :=
⟨λ ⟨a, b, h⟩, ⟨a * x, b * x, by { rwa [mul_assoc, mul_assoc] }⟩,
  λ ⟨a, b, h⟩,
    let ⟨x', hx⟩ := hu.exists_left_inv in
    ⟨a * x', b * x', by rwa
      [←mul_assoc (a * x'), mul_assoc a, ←mul_assoc (b * x'), mul_assoc b, hx, mul_one, mul_one]⟩⟩

lemma step1'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (heven : even a.norm) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    a.norm = 4 * u.norm :=
begin
  obtain ⟨u', hu'⟩ := step1 hcoprime heven,
  refine ⟨u', _, _⟩,
  { apply zsqrtd.coprime_of_dvd_coprime hcoprime,
    obtain (rfl|rfl) := hu'; apply dvd_mul_left },
  { cases hu';
    { rw [hu', zsqrtd.norm_mul], congr } }
end

lemma step1'' {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hp : p.norm = 4)
  (hq : p.im ≠ 0)
  (heven : even a.norm) :
  ∃ (u : ℤ√-3),
    is_coprime u.re u.im ∧
      (a = p * u ∨ a = p.conj * u) ∧ a.norm = 4 * u.norm :=
begin
  obtain ⟨u, h2⟩ := step1 hcoprime heven,
  set q : ℤ√-3 := ⟨1, 1⟩,
  replace h2 : a = q * u ∨ a = q.conj * u := h2,
  obtain ⟨hp', hq'⟩ := spts.four hp hq,
  refine ⟨p.re * u, _, _, _⟩,
  { rw ←int.is_unit_iff_abs_eq at hp',
    rwa [zsqrtd.smul_re, zsqrtd.smul_im, is_coprime.mul_unit_left _ _ _ hp'],
    apply zsqrtd.coprime_of_dvd_coprime hcoprime,
    obtain (rfl|rfl) := h2; apply dvd_mul_left },
  { rw (abs_eq $ @zero_le_one ℤ _) at hp' hq',
    cases hp',
    { have h4 : p = q ∨ p = q.conj,
      { apply or.imp _ _ hq';
        { intro h5, simp [zsqrtd.ext, hp', h5] } },
      simp only [hp', one_mul, int.cast_one],
      cases h4; simp [h4, h2, zsqrtd.conj_conj, or_comm] },
    { have h4 : p = -q ∨ p = -q.conj,
      { apply or.imp _ _ hq'.symm,
        { intro h5, simp [zsqrtd.ext, hp', h5] },
        { intro h5, simp [zsqrtd.ext, hp', h5] } },
      simp only [hp', one_mul, zsqrtd.norm_neg, int.cast_one, int.cast_neg, neg_one_mul],
      cases h4,
      simp [h4, h2],
      simp [h4, h2, or_comm] } },
  { rw [zsqrtd.norm_mul, zsqrtd.norm_int_cast, ←sq, ←sq_abs, hp', one_pow, one_mul],
    cases h2;
    { rw [h2, zsqrtd.norm_mul], congr } },
end

lemma step2
  {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hdvd : p.norm ∣ a.norm)
  (hpprime : prime p.norm) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    (a = p * u ∨ a = p.conj * u) ∧
    a.norm = p.norm * u.norm :=
begin
  obtain ⟨u', h, h'⟩ := spts.mul_of_dvd'' hdvd hpprime,
  refine ⟨u', _, h, h'⟩,
  apply zsqrtd.coprime_of_dvd_coprime hcoprime,
  obtain (rfl|rfl) := h; apply dvd_mul_left
end

lemma step1_2
  {a p : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  (hdvd : p.norm ∣ a.norm)
  (hp : odd_prime_or_four p.norm)
  (hq : p.im ≠ 0) :
  ∃ u : ℤ√-3,
    is_coprime u.re u.im ∧
    (a = p * u ∨ a = p.conj * u) ∧
    a.norm = p.norm * u.norm :=
begin
  obtain hp|⟨hpprime, hpodd⟩ := hp,
  { rw hp at hdvd ⊢,
    have heven : even a.norm,
    { apply dvd_trans _ hdvd,
      norm_num },
    exact step1'' hcoprime hp hq heven },
  { apply step2 hcoprime hdvd hpprime }
end

lemma odd_prime_or_four.factors'
  {a : ℤ√-3}
  (h2 : a.norm ≠ 1)
  (hcoprime : is_coprime a.re a.im) :
  ∃ (u q : ℤ√-3),
    0 ≤ q.re ∧
    q.im ≠ 0 ∧
    odd_prime_or_four q.norm ∧
    a = q * u ∧
    is_coprime u.re u.im ∧
    u.norm < a.norm :=
begin
  obtain h1|h1 := h2.lt_or_lt,
  { have := spts.pos_of_coprime' hcoprime,
    rw [←int.add_one_le_iff, zero_add, ←not_lt] at this,
    exact (this h1).elim },
  rw [←int.add_one_le_iff, ←mul_two, one_mul] at h1,
  obtain h2|h2 := h1.eq_or_lt,
  { exact (spts.not_two _ h2.symm).elim },
  obtain ⟨p, hpdvd, hp⟩ := odd_prime_or_four.exists_and_dvd h2,
  obtain ⟨q', hcd, hc, hd⟩ := odd_prime_or_four.factors a p hcoprime hp hpdvd,
  rw [←abs_dvd, hcd] at hpdvd,
  have hp' := hp.abs,
  rw hcd at hp',

  obtain ⟨u, huvcoprime, huv, huvdvd⟩ := step1_2 hcoprime hpdvd hp' hd,
  use u,
  cases huv; [use q', use q'.conj];
  try { rw [zsqrtd.conj_re, zsqrtd.conj_im, neg_ne_zero, zsqrtd.norm_conj] };
  use [hc, hd, hp', huv, huvcoprime];
  { rw [huvdvd, lt_mul_iff_one_lt_left (spts.pos_of_coprime' huvcoprime), ←hcd],
    exact hp.one_lt_abs },
end

lemma step3
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  :
  ∃ f : multiset ℤ√-3,
    (a = f.prod ∨ a = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm
  :=
begin
  suffices : ∀ n : ℕ, a.norm.nat_abs = n →
    ∃ f : multiset ℤ√-3,
    (a = f.prod ∨ a = - f.prod) ∧
    ∀ pq : ℤ√-3, pq ∈ f →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm,
  { exact this a.norm.nat_abs rfl },

  intros n hn,
  induction n using nat.strong_induction_on with n ih generalizing a,
  dsimp only at ih,

  cases eq_or_ne a.norm 1 with h h,
  { use 0,
    split,
    { simp only [multiset.prod_zero, spts.eq_one' h] },
    { intros pq hpq,
      exact absurd hpq (multiset.not_mem_zero _) } },
  { obtain ⟨U, q, hc, hd, hp, huv, huvcoprime, descent⟩ := odd_prime_or_four.factors'
      h hcoprime,
    replace descent := int.nat_abs_lt_nat_abs_of_nonneg_of_lt (zsqrtd.norm_nonneg (by norm_num) _) descent,
    rw [hn] at descent,
    obtain ⟨g, hgprod, hgfactors⟩ := ih U.norm.nat_abs descent huvcoprime rfl,
    refine ⟨q ::ₘ g, _, _⟩,
    { rw huv,
      cases hgprod; rw [multiset.prod_cons, hgprod],
      { left, refl },
      { right, simp only [mul_neg] } },
    { rintros pq hpq,
      rw multiset.mem_cons at hpq,
      obtain rfl|ind := hpq,
      { exact ⟨hc, hd, hp⟩ },
      { exact hgfactors pq ind } } },
end

lemma step4_3
  {p p' : ℤ√-3}
  (hcoprime : is_coprime p.re p.im)
  (hcoprime' : is_coprime p'.re p'.im)
  (h : odd_prime_or_four p.norm)
  (heq : p.norm = p'.norm) :
  abs p.re = abs p'.re ∧ abs p.im = abs p'.im :=
begin
  have hdvd : p'.norm ∣ p.norm,
  { rw heq },
  have him : p'.im ≠ 0,
  { apply odd_prime_or_four.im_ne_zero _ hcoprime',
    rwa [←heq] },
  obtain ⟨u, hcoprime'', (H|H), h1⟩ := step1_2 hcoprime hdvd (by rwa ←heq) him;
  { rw heq at h1,
    have := int.eq_one_of_mul_eq_self_right (spts.ne_zero_of_coprime' _ hcoprime') h1.symm,
    obtain ⟨ha, hb⟩ := spts.eq_one this,
    simp only [hb, zsqrtd.ext, zsqrtd.mul_re, zsqrtd.mul_im, add_zero, zero_add, mul_zero] at H,
    rw [H.1, H.2, abs_mul, abs_mul, ha, mul_one, mul_one],
    try { rw [zsqrtd.conj_re, zsqrtd.conj_im, abs_neg] },
    split; refl },
end

lemma prod_map_norm {d : ℤ} {s : multiset ℤ√d} :
  (s.map zsqrtd.norm).prod = zsqrtd.norm s.prod :=
multiset.prod_hom s zsqrtd.norm_monoid_hom

lemma associated_of_dvd {a p : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (h: p ∣ a) : associated p a :=
begin
  obtain (rfl|⟨ap, aodd⟩) := ha;
  obtain (rfl|⟨pp, podd⟩) := hp,
  { refl },
  { exfalso,
    have h0 : (4 : ℤ) = 2 ^ 2,
    { norm_num },
    rw h0 at h,
    refine int.even_iff_not_odd.mp (associated.dvd _) podd,
    exact ((pp.dvd_prime_iff_associated int.prime_two).mp (pp.dvd_of_dvd_pow h)).symm },
  { exfalso,
    rw int.odd_iff_not_even at aodd,
    refine aodd (dvd_trans _ h),
    norm_num },
  { rwa prime.dvd_prime_iff_associated pp ap at h }
end

lemma dvd_or_dvd {a p x : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (hdvd : p ∣ a * x) : p ∣ a ∨ p ∣ x :=
begin
  obtain (rfl|⟨pp, podd⟩) := hp,
  { obtain (rfl|⟨ap, aodd⟩) := ha,
    { exact or.inl dvd_rfl },
    { right,
      have : (4 : ℤ) = 2 ^ 2,
      { norm_num },
      rw this at hdvd ⊢,
      apply int.prime_two.pow_dvd_of_dvd_mul_left _ _ hdvd,
      rwa [←even_iff_two_dvd, ←int.odd_iff_not_even] } },
  { exact (pp.dvd_or_dvd hdvd) }
end 

lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ} (hp : odd_prime_or_four p)
  {s : multiset ℤ}
  (hs : ∀ r ∈ s, odd_prime_or_four r)
  (hdvd : p ∣ s.prod) :
  ∃ q ∈ s, associated p q :=
begin
  induction s using multiset.induction_on with a s ih hs generalizing hs hdvd,
  { simpa [hp.not_unit, ←is_unit_iff_dvd_one] using hdvd },
  { rw [multiset.prod_cons] at hdvd,
    have := hs a (multiset.mem_cons_self _ _),
    obtain h|h := dvd_or_dvd this hp hdvd,
    { exact ⟨a, multiset.mem_cons_self _ _, associated_of_dvd this hp h⟩ },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons_of_mem hr)) h,
      exact ⟨q, multiset.mem_cons_of_mem hq₁, hq₂⟩ } }
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
    exact dvd_trans (multiset.dvd_prod hx) h.symm.dvd },
  { intros p f ih g hf hg hfg,
    have hp := hf p (multiset.mem_cons_self _ _),
    have hdvd : p ∣ g.prod,
    { rw [←hfg.dvd_iff_dvd_right, multiset.prod_cons],
      exact dvd_mul_right _ _ },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod'' hp hg hdvd,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons hb,
    apply ih _ _ _,
    { exact (λ q hq, hf _ (multiset.mem_cons_of_mem hq)) },
    { exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)) },
    { apply associated.of_mul_left _ hb hp.ne_zero,
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

noncomputable def factorization'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  : multiset ℤ√-3
 := classical.some (step3 hcoprime)

lemma factorization'_prop
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  (a = (factorization' hcoprime).prod ∨ a = - (factorization' hcoprime).prod) ∧
    ∀ pq : ℤ√-3, pq ∈ (factorization' hcoprime) →
      0 ≤ pq.re ∧
      pq.im ≠ 0 ∧
      odd_prime_or_four pq.norm :=
classical.some_spec (step3 hcoprime)

lemma factorization'.coprime_of_mem
  {a b : ℤ√-3} (h : is_coprime a.re a.im) (hmem : b ∈ factorization' h) :
  is_coprime b.re b.im :=
begin
  obtain ⟨h1, h2⟩ := factorization'_prop h,
  set f := factorization' h,
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
    rw ←int.is_unit_iff_abs_eq,
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
  rw abs_eq_abs at hre him,
  cases hre with h1 h1;
  cases him with h2 h2;
  [{ left, use 1}, {right, use 1}, {right, use -1}, {left, use -1}];
  simp only [units.coe_one, mul_one, units.coe_neg_one, mul_neg_one, zsqrtd.ext, zsqrtd.neg_im,
    zsqrtd.neg_re, h1, h2, neg_neg, zsqrtd.conj_re, zsqrtd.conj_im, eq_self_iff_true, and_self],
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
    exact int.eq_of_associated_of_nonneg h (zsqrtd.norm_nonneg hd _) (zsqrtd.norm_nonneg hd _) },
  obtain ⟨hre, him⟩ := step4_3 hx hy h' heq,
  exact associated'_of_abs_eq hre him,
end

lemma factorization'.associated'_of_norm_eq
  {a b c : ℤ√-3} (h : is_coprime a.re a.im)
  (hbmem : b ∈ factorization' h) (hcmem : c ∈ factorization' h)
  (hnorm : b.norm = c.norm) :
  associated' b c :=
begin
  apply associated'_of_associated_norm,
  { rw hnorm },
  { exact factorization'.coprime_of_mem h hbmem },
  { exact factorization'.coprime_of_mem h hcmem },
  { exact ((factorization'_prop h).2 b hbmem).2.2 },
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

noncomputable def odd_factors (x : ℤ) := multiset.filter odd (unique_factorization_monoid.normalized_factors x)

lemma odd_factors.zero : odd_factors 0 = 0 := rfl

lemma odd_factors.not_two_mem (x : ℤ) : (2 : ℤ) ∉ odd_factors x :=
begin
  simp only [odd_factors, int.even_bit0, not_true, not_false_iff, int.odd_iff_not_even,
    and_false, multiset.mem_filter],
end

lemma odd_factors.nonneg {z a : ℤ} (ha : a ∈ odd_factors z) : 0 ≤ a :=
begin
  simp only [odd_factors, multiset.mem_filter] at ha,
  exact int.nonneg_of_normalize_eq_self
    (unique_factorization_monoid.normalize_normalized_factor a ha.1)
end

noncomputable def even_factor_exp (x : ℤ) := multiset.count 2 (unique_factorization_monoid.normalized_factors x)

lemma even_factor_exp.def (x : ℤ) : even_factor_exp x = multiset.count 2 (unique_factorization_monoid.normalized_factors x) := rfl

lemma even_factor_exp.zero : even_factor_exp 0 = 0 := rfl

lemma even_and_odd_factors'' (x : ℤ) :
  unique_factorization_monoid.normalized_factors x = (unique_factorization_monoid.normalized_factors x).filter (eq 2) + odd_factors x :=
begin
  by_cases hx : x = 0,
  { rw [hx, unique_factorization_monoid.normalized_factors_zero, odd_factors.zero, multiset.filter_zero,
    add_zero] },
  simp [even_factor_exp, odd_factors],
  rw multiset.filter_add_filter,
  convert (add_zero _).symm,
  { rw multiset.filter_eq_self,
    intros a ha,
    have hprime : prime a := unique_factorization_monoid.prime_of_normalized_factor a ha,
    have := unique_factorization_monoid.normalize_normalized_factor a ha,
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
  unique_factorization_monoid.normalized_factors x = multiset.repeat 2 (even_factor_exp x) + odd_factors x :=
begin
  convert even_and_odd_factors'' x,
  simp [even_factor_exp, ←multiset.filter_eq],
end

lemma even_and_odd_factors (x : ℤ) (hx : x ≠ 0) : associated x (2 ^ (even_factor_exp x) * (odd_factors x).prod) :=
begin
  convert (unique_factorization_monoid.normalized_factors_prod hx).symm,
  simp [even_factor_exp],
  rw [multiset.pow_count, ←multiset.prod_add, ←even_and_odd_factors'' x]
end

lemma factors_2_even {z : ℤ} (hz : z ≠ 0) : even_factor_exp (4 * z) = 2 + even_factor_exp z :=
begin
  have h₀ : (4 : ℤ) ≠ 0 := four_ne_zero,
  have h₁ : (2 : int) ^ 2 = 4,
  { norm_num },
  simp [even_factor_exp],
  rw [unique_factorization_monoid.normalized_factors_mul h₀ hz, multiset.count_add, ←h₁,
    unique_factorization_monoid.normalized_factors_pow, multiset.count_nsmul,
    unique_factorization_monoid.normalized_factors_irreducible int.prime_two.irreducible,
    int.normalize_of_nonneg zero_le_two, multiset.count_singleton_self, mul_one],
end

lemma factors_2_even'
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  even (even_factor_exp a.norm) :=
begin
  induction hn : a.norm.nat_abs using nat.strong_induction_on with n ih generalizing a,
  dsimp only at ih,
  by_cases hparity : even a.norm,
  { obtain ⟨u, huvcoprime, huvprod⟩ := step1' hcoprime hparity,
    have huv := spts.ne_zero_of_coprime' _ huvcoprime,
    rw [huvprod, factors_2_even huv, nat.even_add],
    apply iff_of_true (dvd_refl _),
    apply ih _ _ huvcoprime rfl,
    rw [←hn, huvprod, int.nat_abs_mul, lt_mul_iff_one_lt_left (int.nat_abs_pos_of_ne_zero huv)],
    norm_num },
  { convert nat.even_zero,
    simp only [even_factor_exp, multiset.count_eq_zero, hn],
    contrapose! hparity with hfactor,
    exact unique_factorization_monoid.dvd_of_mem_normalized_factors hfactor }
end

-- most useful with  (hz : even (even_factor_exp z))
noncomputable def factors_odd_prime_or_four (z : ℤ) : multiset ℤ :=
multiset.repeat 4 (even_factor_exp z / 2) + odd_factors z

lemma factors_odd_prime_or_four.nonneg {z a : ℤ} (ha : a ∈ factors_odd_prime_or_four z) : 0 ≤ a :=
begin
  simp only [factors_odd_prime_or_four, multiset.mem_add] at ha,
  cases ha,
  { rw multiset.eq_of_mem_repeat ha, norm_num },
  { exact odd_factors.nonneg ha }
end

lemma factors_odd_prime_or_four.prod
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im) :
  (factors_odd_prime_or_four a.norm).prod = a.norm :=
begin
  apply int.eq_of_associated_of_nonneg,
  { have := unique_factorization_monoid.normalized_factors_prod (spts.ne_zero_of_coprime' _ hcoprime),
    apply associated.trans _ this,
    obtain ⟨m, hm⟩ := factors_2_even' hcoprime,
    rw [even_and_odd_factors' _, multiset.prod_add, factors_odd_prime_or_four, multiset.prod_add,
      hm, nat.mul_div_right _ zero_lt_two, multiset.prod_repeat, multiset.prod_repeat, pow_mul],
    exact associated.refl _ },
  { apply multiset.prod_nonneg,
    apply factors_odd_prime_or_four.nonneg },
  { exact zsqrtd.norm_nonneg (by norm_num) _ },
end

lemma factors_odd_prime_or_four.associated
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hassoc : associated f.prod a.norm) :
  multiset.rel associated f (factors_odd_prime_or_four a.norm) :=
begin
  apply factors_unique_prod' hf,
  { intros x hx,
    simp only [factors_odd_prime_or_four, multiset.mem_add] at hx,
    cases hx,
    { left, exact multiset.eq_of_mem_repeat hx },
    { right,
      simp only [odd_factors, multiset.mem_filter] at hx,
      exact and.imp_left (unique_factorization_monoid.prime_of_normalized_factor _) hx } },
  { rwa factors_odd_prime_or_four.prod hcoprime }
end

lemma factors_odd_prime_or_four.unique
  {a : ℤ√-3}
  (hcoprime : is_coprime a.re a.im)
  {f : multiset ℤ}
  (hf : ∀x∈f, odd_prime_or_four x)
  (hf' : ∀x∈f, (0 : ℤ) ≤ x)
  (hassoc : associated f.prod a.norm) :
  f = (factors_odd_prime_or_four a.norm) :=
begin
  rw ←multiset.rel_eq,
  apply multiset.rel.mono (factors_odd_prime_or_four.associated hcoprime hf hassoc),
  intros x hx y hy hxy,
  exact int.eq_of_associated_of_nonneg hxy (hf' x hx) (factors_odd_prime_or_four.nonneg hy)
end

lemma even_factor_exp.pow (z : ℤ) (n : ℕ) : even_factor_exp (z ^ n) = n * even_factor_exp z :=
begin
  simp only [even_factor_exp],
  rw [unique_factorization_monoid.normalized_factors_pow, multiset.count_nsmul]
end

lemma odd_factors.pow (z : ℤ) (n : ℕ) : odd_factors (z ^ n) = n • odd_factors z :=
begin
  simp only [odd_factors],
  rw [unique_factorization_monoid.normalized_factors_pow, multiset.filter_nsmul],
end

lemma factors_odd_prime_or_four.pow
  (z : ℤ) (n : ℕ) (hz : even (even_factor_exp z)) :
  factors_odd_prime_or_four (z ^ n) = n • factors_odd_prime_or_four z :=
begin
  simp only [factors_odd_prime_or_four, nsmul_add, multiset.nsmul_repeat, even_factor_exp.pow,
    nat.mul_div_assoc _ hz, odd_factors.pow],
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
    simp only [hv1, hv2, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
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
          simp only [habsv, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 ≤ A.re : hA
          ... = -x.re : _
          ... < 0 : _,
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
          simp only [habsv, mul_one, int.cast_one, mul_neg, int.cast_neg] at hu,
          apply lt_irrefl (0 : ℤ),
          calc 0 ≤ A.re : hA
          ... = -x.re : _
          ... < 0 : _,
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
  ∃ g : multiset ℤ√-3, factorization' hcoprime = 3 • g :=
begin
  classical,

  obtain ⟨h1, h2⟩ := factorization'_prop hcoprime,
  set f := factorization' hcoprime with hf,
  apply multiset.exists_smul_of_dvd_count,

  intros x hx,
  convert dvd_mul_right _ _,
  have : even (even_factor_exp r),
  { suffices : even (3 * even_factor_exp r),
    { rw nat.even_mul at this,
      apply this.resolve_left,
      norm_num },
    rw [←even_factor_exp.pow r 3, hcube],
    exact factors_2_even' hcoprime },
  rw [←multiset.count_nsmul x.norm, ←factors_odd_prime_or_four.pow _ _ this, hcube, multiset.count,
    multiset.countp_eq_card_filter, multiset.filter_congr,
    ←multiset.countp_map zsqrtd.norm f (λ y, x.norm = y), multiset.count],
  congr',
  { apply factors_odd_prime_or_four.unique hcoprime,
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      exact (h2 y hy).2.2 },
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      apply zsqrtd.norm_nonneg,
      norm_num },
    { rw [prod_map_norm],
      cases h1; rw [h1],
      rw zsqrtd.norm_neg } },
  intros A HA,
  have h2x := h2 x hx,

  rw associated'_iff_eq h2x.1 (h2 A HA).1,
  { exact ⟨associated'.norm_eq, factorization'.associated'_of_norm_eq hcoprime hx HA⟩ },

  intro H,
  apply no_conj f,
  { intro HH,
    apply h2x.2.1,
    rw [zsqrt3.is_unit_iff] at HH,
    exact HH.2 },
  { cases h1; rw h1 at hcoprime,
    { exact hcoprime },
    { rwa [←is_coprime.neg_neg_iff, ←zsqrtd.neg_im, ←zsqrtd.neg_re] } },
  { refine ⟨hx, _⟩,
    rwa [H, zsqrtd.conj_conj] },
end

lemma step5 -- lemma page 54
  (a : ℤ√-3)
  (r : ℤ)
  (hcoprime : is_coprime a.re a.im)
  (hcube : r ^ 3 = a.norm) :
  ∃ p : ℤ√-3, a = p ^ 3 :=
begin
  obtain ⟨f, hf⟩ := step5' a r hcoprime hcube,
  obtain ⟨h1, -⟩ := factorization'_prop hcoprime,
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
  set A : ℤ√-3 := ⟨a, b⟩,
  have hcube' : r ^ 3 = A.norm,
  { simp only [hcube, zsqrtd.norm_def, A], ring },
  obtain ⟨p, hp⟩ := step5 A r hcoprime hcube',
  use [p.re, p.im],
  simp only [zsqrtd.ext, pow_succ', pow_two, zsqrtd.mul_re, zsqrtd.mul_im] at hp,
  convert hp; ring,
end
