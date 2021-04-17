import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid
import tactic
import data.nat.modeq
import ring_theory.int.basic
import .primes
import .edwards

def flt_solution
  (n : ℕ)
  (a b c : ℤ) :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
  a ^ n + b ^ n = c ^ n

def flt_coprime
  (n : ℕ)
  (a b c : ℤ) :=
  flt_solution n a b c ∧
  is_coprime a b ∧
  is_coprime a c ∧
  is_coprime b c

lemma exists_coprime
  {n : ℕ}
  (hn : 0 < n)
  {a b c : ℤ}
  (ha' : a ≠ 0)
  (hb' : b ≠ 0)
  (hc' : c ≠ 0)
  (h : a ^ n + b ^ n = c ^ n) :
  ∃ a' b' c' : ℤ,
    a'.nat_abs ≤ a.nat_abs ∧ b'.nat_abs ≤ b.nat_abs ∧ c'.nat_abs ≤ c.nat_abs ∧
    flt_coprime n a' b' c' :=
begin
  set d := int.gcd a b with hd',
  have ha : ↑d ∣ a := int.gcd_dvd_left a b,
  have hb : ↑d ∣ b := int.gcd_dvd_right a b,
  have hc : ↑d ∣ c,
  { rw [←int.pow_dvd_pow_iff hn, ←h],
    apply dvd_add; rwa int.pow_dvd_pow_iff hn },
  have hdpos : 0 < d := int.gcd_pos_of_non_zero_left _ ha',
  have hd := int.coe_nat_ne_zero_iff_pos.mpr hdpos,
  have hsoln : (a / d) ^ n + (b / d) ^ n = (c / d) ^ n,
  { apply int.eq_of_mul_eq_mul_right (pow_ne_zero n hd),
    calc ((a / d) ^ n + (b / d) ^ n) * d ^ n
        = (a / d * d) ^ n  + (b / d * d) ^ n : by rw [add_mul, mul_pow (a / d), mul_pow (b / d)]
    ... = a ^ n + b ^ n : by rw [int.div_mul_cancel ha, int.div_mul_cancel hb]
    ... = c ^ n : h
    ... = (c / d * d) ^ n : by rw [int.div_mul_cancel hc]
    ... = (c / d) ^ n * d ^ n : by rw mul_pow },
  have hsoln' : (b / d) ^ n + (a / d) ^ n = (c / d) ^ n,
  { rwa add_comm at hsoln },
  have hcoprime_div : is_coprime (a / d) (b / d) := int.coprime_div_gcd_div_gcd hdpos,
  exact ⟨
    a / d,
    b / d,
    c / d,
    (int.nat_abs_div _ _ ha).trans_le (nat.div_le_self _ _),
    (int.nat_abs_div _ _ hb).trans_le (nat.div_le_self _ _),
    (int.nat_abs_div _ _ hc).trans_le (nat.div_le_self _ _),
    ⟨
      int.div_ne_zero_of_dvd ha' hd ha,
      int.div_ne_zero_of_dvd hb' hd hb,
      int.div_ne_zero_of_dvd hc' hd hc,
      hsoln
    ⟩,
    hcoprime_div,
    coprime_add_self_pow hn hsoln hcoprime_div,
    coprime_add_self_pow hn hsoln' hcoprime_div.symm
  ⟩
end

lemma descent1a {a b c : ℤ}
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (habcoprime : is_coprime a b)
  (haccoprime : is_coprime a c)
  (hbccoprime : is_coprime b c) :
  (even a ∧ ¬even b ∧ ¬even c ∨
   ¬even a ∧ even b ∧ ¬even c) ∨
  ¬even a ∧ ¬even b ∧ even c :=
begin
  have contra : ∀ {x y : ℤ}, is_coprime x y → even x → even y → false,
  { intros x y hcoprime hx hy,
    rw even_iff_two_dvd at hx hy,
    have := int.dvd_gcd hx hy,
    rw ←int.gcd_eq_one_iff_coprime at hcoprime,
    rw hcoprime at this,
    norm_num at this },
  by_cases haparity : even a;
  by_cases hbparity : even b;
  by_cases hcparity : even c,
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra haccoprime ‹_› ‹_›) },
  { tauto },
  { exact false.elim (contra hbccoprime ‹_› ‹_›) },
  { tauto },
  { tauto },
  { exfalso,
    apply hcparity,
    rw [←int.even_pow' three_ne_zero, ←h],
    simp [haparity, hbparity, three_ne_zero] with parity_simps },
end

lemma flt_not_add_self {a b c : ℤ} (ha : a ≠ 0) (h : a ^ 3 + b ^ 3 = c ^ 3) : a ≠ b :=
begin
  rintro rfl,
  rw ←mul_two at h,
  obtain ⟨d, rfl⟩ : a ∣ c,
  { rw [←int.pow_dvd_pow_iff (by norm_num : 0 < 3), ←h],
    apply dvd_mul_right },
  apply int.two_not_cube d,
  rwa [mul_pow, mul_right_inj' (pow_ne_zero 3 ha), eq_comm] at h,
end

lemma descent1left {a b c : ℤ}
  (hapos : a ≠ 0)
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (hbccoprime : is_coprime b c)
  (hb : ¬even b)
  (hc : ¬even c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
      q ≠ 0 ∧
        is_coprime p q ∧
          (even p ↔ ¬even q) ∧
            2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 :=
begin
  obtain ⟨p, hp⟩ : even (c - b),
  { simp [hb, hc] with parity_simps},
  obtain ⟨q, hq⟩ : even (c + b),
  { simp [hb, hc] with parity_simps},
  have hadd : p + q = c,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_add, ←hp, ←hq],
    ring },
  have hsub : q - p = b,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_sub, ←hp, ←hq],
    ring },
  have hpnezero : p ≠ 0,
  { rintro rfl,
    rw [mul_zero, sub_eq_zero] at hp,
    subst hp,
    rw add_left_eq_self at h,
    exact hapos (pow_eq_zero h) },

  have hqnezero : q ≠ 0,
  { rintro rfl,
    simp only [add_zero, zero_sub] at hadd hsub,
    rw [←hadd, ←hsub, neg_pow_bit1, ←sub_eq_add_neg, sub_eq_iff_eq_add] at h,
    exact flt_not_add_self hpnezero h.symm rfl },

  refine ⟨p, q, hpnezero, hqnezero, _, _, _⟩,
  { apply is_coprime_of_dvd,
    { exact not_and_of_not_or_not (or.inl hpnezero) },
    intros z hznu hznz hzp hzq,
    apply hznu,
    apply hbccoprime.is_unit_of_dvd',
    { rw ←hsub,
      exact dvd_sub hzq hzp },
    { rw ←hadd,
      exact dvd_add hzp hzq } },
  { have : ¬even (p + q),
    { rwa [hadd] },
    split; intro H; simpa [H] with parity_simps using this },
  { rw [eq_sub_of_add_eq h, ←hadd, ←hsub],
    ring },
end

lemma descent1 (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
    q ≠ 0 ∧
    is_coprime p q ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,

  obtain (⟨ha, hb, hc⟩|⟨ha, hb, hc⟩)|⟨ha, hb, hc⟩ := descent1a h habcoprime haccoprime hbccoprime,
  { obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hapos h hbccoprime hb hc,
    exact ⟨p, q, hp, hq, hcoprime, hodd, or.inl hcube⟩ },
  { rw add_comm at h,
    obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hbpos h haccoprime ha hc,
    refine ⟨p, q, hp, hq, hcoprime, hodd, or.inr $ or.inl hcube⟩ },
  { obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1left hcpos _ habcoprime.neg_left _ hb,
    exact ⟨p, q, hp, hq, hcoprime, hodd, or.inr $ or.inr hcube⟩,
    { rw ←h, ring },
    { simp [ha] with parity_simps } },
end

lemma descent11 {a b c d : ℤ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { apply dvd_mul_of_dvd_left, apply dvd_mul_right },
  { apply dvd_mul_of_dvd_left, apply dvd_mul_left },
  { apply dvd_mul_left }
end

lemma descent2 (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
    q ≠ 0 ∧
    is_coprime p q ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    ((2 * p).nat_abs < (a ^ 3 * b ^ 3 * c ^ 3).nat_abs) :=
begin
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1 a b c h,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,

  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, -⟩ := h,
  have : (2 * p).nat_abs < (2 * p * (p ^ 2 + 3 * q ^ 2)).nat_abs,
  { rw [int.nat_abs_mul (2 * p)],
    apply lt_mul_of_one_lt_right,
    { rw [pos_iff_ne_zero, int.nat_abs_ne_zero],
      exact mul_ne_zero two_ne_zero hp },
    { zify,
      rw int.nat_abs_of_nonneg (spts.nonneg _ _),
      exact spts.one_lt_of_right_ne_zero hq  } },
  apply lt_of_lt_of_le this,
  { apply nat.le_of_dvd,
    { rw [pos_iff_ne_zero, int.nat_abs_ne_zero, ←mul_pow, ←mul_pow],
      exact pow_ne_zero 3 (mul_ne_zero (mul_ne_zero hapos hbpos) hcpos) },
    { rw int.nat_abs_dvd_abs_iff,
      exact descent11 hcube } }
end

lemma gcd1or3
  (p q : ℤ)
  (hp : p ≠ 0) (hq : q ≠ 0)
  (hcoprime : is_coprime p q)
  (hparity : even p ↔ ¬even q) :
  int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  set g := int.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) with hg',
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2,
  { obtain ⟨k, hg, hk⟩ := H,
    rcases k with (_|_|_),
    { left, norm_num at hg, exact hg },
    { right, norm_num at hg, exact hg },
    { change k + 2 < 2 at hk,
      linarith } },

  have basic : ∀ f, nat.prime f → (f : ℤ) ∣ 2 * p → (f : ℤ) ∣ (p ^ 2 + 3 * q ^ 2) → f = 3,
  { intros d hdprime hdleft hdright,
    by_contra hne3,
    rw ←ne.def at hne3,
    apply (nat.prime_iff_prime_int.mp hdprime).not_unit,

    have hne2 : d ≠ 2,
    { rintro rfl,
      change even _ at hdright,
      simpa [hparity, two_ne_zero] with parity_simps using hdright },
    have : 2 < d := lt_of_le_of_ne (hdprime.two_le) hne2.symm,
    have : 3 < d := lt_of_le_of_ne (this) hne3.symm,
    obtain ⟨P, hP⟩ := hdleft,
    obtain ⟨Q, hQ⟩ := hdright,
    obtain ⟨H, hH⟩ : 2 ∣ P,
    { have H := dvd_mul_right 2 p,
      rw [hP] at H,
      apply (prime.div_or_div int.prime_two H).resolve_left,
      rw ←int.nat_abs_dvd,
      rw int.coe_nat_dvd,
      change ¬(2 ∣ d),
      rw ←nat.prime_two.coprime_iff_not_dvd,
      rw nat.coprime_primes nat.prime_two hdprime,
      exact hne2.symm },
    have : p = d * H,
    { rw [←mul_right_inj', hP, hH],
      ring,
      exact two_ne_zero },
    have : 3 * q ^ 2 = d * (Q - d * H ^ 2),
    { calc 3 * q ^ 2
          = d * Q - p ^ 2 : (sub_eq_of_eq_add' hQ.symm).symm
      ... = d * Q - d ^ 2 * H ^ 2 : by rw [this, mul_pow]
      ... = d * (Q - d * H ^ 2) : by ring },

    apply hcoprime.is_unit_of_dvd',
    { rw ‹p = _›, exact dvd_mul_right d H },
    { have h000 : (d : ℤ) ∣ 3 * q ^ 2,
      { rw this,
        apply dvd_mul_right },
      rw nat.prime_iff_prime_int at hdprime,
      cases prime.div_or_div hdprime h000 with h000 h000,
      { exfalso,
        rw ←int.nat_abs_dvd_abs_iff at h000,
        have := nat.le_of_dvd (by norm_num) h000,
        apply lt_irrefl 3,
        apply lt_of_lt_of_le _ this,
        assumption },
      { exact prime.dvd_of_dvd_pow hdprime h000 } } },

  set k := g.factors.length,
  have hg : g = 3 ^ k,
  { apply eq_pow,
    { apply nat.gcd_pos_of_pos_left,
      rw int.nat_abs_mul,
      apply nat.mul_pos zero_lt_two,
      rwa [pos_iff_ne_zero, int.nat_abs_ne_zero], },
    intros d hdprime hddvdg,
    rw ←int.coe_nat_dvd at hddvdg,
    apply basic _ hdprime; apply dvd_trans hddvdg; rw hg',
    exacts [int.gcd_dvd_left _ _, int.gcd_dvd_right _ _] },
  refine ⟨k, hg, _⟩,
  by_contra H,
  push_neg at H,
  rw ←pow_mul_pow_sub _ H at hg,
  have : ¬is_unit (3 : ℤ),
  { rw int.is_unit_iff_nat_abs_eq, norm_num },
  apply this,
  have hdvdp : 3 ∣ p,
  { suffices : 3 ∣ 2 * p,
    { apply int.dvd_mul_cancel_prime _ nat.prime_two int.prime_three this,
      norm_num },
    have : 3 ∣ (g : ℤ),
    { rw [hg, pow_two, mul_assoc, int.coe_nat_mul],
      apply dvd_mul_right },
    exact dvd_trans this (int.gcd_dvd_left _ _) },
  apply is_coprime.is_unit_of_dvd' hcoprime hdvdp,
  { rw ←int.pow_dvd_pow_iff zero_lt_two at hdvdp,
    apply prime.dvd_of_dvd_pow int.prime_three,
    rw [←mul_dvd_mul_iff_left (@three_ne_zero ℤ _ _), ←pow_two, dvd_add_iff_right hdvdp],
    refine dvd_trans _ (int.gcd_dvd_right (2 * p) (p ^ 2 + 3 * q ^ 2)),
    rw [←hg', hg, int.coe_nat_mul],
    apply dvd_mul_right }
end

lemma obscure'
  (p q : ℤ)
  (hp : p ≠ 0) (hq : q ≠ 0)
  (hcoprime : is_coprime p q)
  (hparity : even p ↔ ¬even q)
  (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
  ∃ a b : ℤ,
    (p : ℤ) = a ^ 3 - 9 * a * b ^ 2 ∧
    (q : ℤ) = 3 * a ^ 2 * b - 3 * b ^ 3 ∧
    is_coprime a b ∧
    (even a ↔ ¬even b) :=
begin
  obtain ⟨u, hu⟩ := hcube,

  obtain ⟨a, b, hp', hq'⟩ := step6 p q u hcoprime hu.symm,
  refine ⟨a, b, hp', hq', _, _⟩,
  { apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      norm_num at hp' },

    intros k hknu hknezero hkdvdleft hkdvdright,
    apply hknu,
    apply hcoprime.is_unit_of_dvd',
    { rw hp',
      apply dvd_sub,
      { exact dvd_pow hkdvdleft (by norm_num) },
      { rw [mul_comm (9 : ℤ), mul_assoc],
        exact dvd_mul_of_dvd_left hkdvdleft _ } },
    { rw hq',
      apply dvd_sub,
      { exact dvd_mul_of_dvd_right hkdvdright _ },
      { apply dvd_mul_of_dvd_right,
        exact dvd_pow hkdvdright (by norm_num) } } },

  { by_cases haparity : even a; by_cases hbparity : even b;
    [skip, tauto, tauto, skip];
    { exfalso,
      have : even p,
      { rw [hp'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      have : even q,
      { rw [hq'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      tauto } }
end

lemma int.cube_of_coprime (a b c s : ℤ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (hcoprimeab : is_coprime a b)
  (hcoprimeac : is_coprime a c)
  (hcoprimebc : is_coprime b c)
  (hs : a * b * c = s ^ 3) :
  ∃ A B C, A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧ a = A ^ 3 ∧ b = B ^ 3 ∧ c = C ^ 3 :=
begin
  obtain ⟨⟨AB, HAB⟩, ⟨C, HC⟩⟩ := int.eq_pow_of_mul_eq_pow_bit1 (mul_ne_zero ha hb) hc
    (is_coprime.mul_left hcoprimeac hcoprimebc) hs,
  obtain ⟨⟨A, HA⟩, ⟨B, HB⟩⟩ := int.eq_pow_of_mul_eq_pow_bit1 ha hb hcoprimeab HAB,
  refine ⟨A, B, C, _, _, _, HA, HB, HC⟩; apply ne_zero_pow three_ne_zero,
  { rwa [←HA] },
  { rwa [←HB] },
  { rwa [←HC] },
end

lemma int.gcd1_coprime12 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (not_3_dvd_2 : ¬3 ∣ u - 3 * v) :
  is_coprime (2 * u) (u - 3 * v) :=
begin
  apply int.is_coprime_of_dvd',
  { rintro ⟨-, h2⟩,
    norm_num [h2] at notdvd_2_2 },
  intros k hknu hknz hkprime hkdvdleft hkdvdright,
  apply hknu,
  apply huvcoprime.is_unit_of_dvd',
  { exact int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright int.prime_two hkprime hkdvdleft },
  { apply int.dvd_mul_cancel_prime' not_3_dvd_2 hkdvdright int.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright int.prime_two hkprime,
    convert dvd_sub hkdvdleft (dvd_mul_of_dvd_right hkdvdright 2),
    ring },
end

lemma int.gcd1_coprime13 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (this : ¬even (u + 3 * v))
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  is_coprime (2 * u) (u + 3 * v) :=
begin
  apply int.is_coprime_of_dvd',
  { rintro ⟨-, h2⟩,
    norm_num [h2] at this },
  intros k hknu hknz hkprime hkdvdleft hkdvdright,
  apply hknu,
  apply huvcoprime.is_unit_of_dvd',
  { exact int.dvd_mul_cancel_prime' this hkdvdright int.prime_two hkprime hkdvdleft },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright int.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' this hkdvdright int.prime_two hkprime,
    convert dvd_sub (dvd_mul_of_dvd_right hkdvdright 2) hkdvdleft,
    ring },
end

lemma int.gcd1_coprime23 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  is_coprime (u - 3 * v) (u + 3 * v) :=
begin
  apply int.is_coprime_of_dvd',
  { rintro ⟨h1, -⟩,
    norm_num [h1] at notdvd_2_2 },
  intros k hknu hknz hkprime hkdvdleft hkdvdright,
  apply hknu,
  apply huvcoprime.is_unit_of_dvd',
  { apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft int.prime_two hkprime,
    convert dvd_add hkdvdleft hkdvdright,
    ring },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright int.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft int.prime_two hkprime,
    convert dvd_sub hkdvdright hkdvdleft,
    ring },
end

lemma descent_gcd1 (a b c p q : ℤ)
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hcoprime : is_coprime p q)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime 3 a b c)
  (hgcd : is_coprime (2 * p) (p ^ 2 + 3 * q ^ 2)) :
  ∃ (a' b' c' : ℤ),
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 2.
  have h' := h,
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have hposleft : 2 * p ≠ 0 := mul_ne_zero two_ne_zero hp,
  have hposright : p ^ 2 + 3 * q ^ 2 ≠ 0 := spts.not_zero_of_coprime hcoprime,
  obtain ⟨hcubeleft, hcuberight⟩ := int.eq_pow_of_mul_eq_pow_bit1 hposleft hposright hgcd hr,
  -- todo shadowing hp hq
  obtain ⟨u, v, hp, hq, huvcoprime, huvodd⟩ := obscure' p q hp hq hcoprime hodd hcuberight,
  have u_ne_zero : u ≠ 0,
  { rintro rfl,
    apply ‹p ≠ 0›,
    rwa [zero_pow zero_lt_three, mul_zero, zero_mul, sub_zero] at hp },
  have hpfactor : p = u * (u - 3 * v) * (u + 3 * v),
  { rw hp, ring },
  have haaa : 2 * p = (2 * u) * (u - 3 * v) * (u + 3 * v),
  { rw hp, ring },
  have : ¬even (u - 3 * v),
  { simp [huvodd] with parity_simps },
  have : ¬even (u + 3 * v),
  { simp [huvodd] with parity_simps },
  have notdvd_2_2 : ¬(2 ∣ u - 3 * v),
  { exact ‹¬even (u - 3 * v)› },
  have hddd : ¬(3 ∣ p),
  { intro H,
    have : 3 ∣ p ^ 2 + 3 * q ^ 2,
    { apply dvd_add,
      { rw pow_two,
        apply dvd_mul_of_dvd_right H },
      { apply dvd_mul_right } },
    have : 3 ∣ 2 * p := dvd_mul_of_dvd_right H 2,
    have := is_coprime.is_unit_of_dvd' hgcd ‹_› ‹_›,
    rw is_unit_iff_dvd_one at this,
    norm_num at this },
  have not_3_dvd_2 : ¬(3 ∣ (u - 3 * v)),
  { intro hd2,
    apply hddd,
    rw hpfactor,
    apply dvd_mul_of_dvd_left _,
    apply dvd_mul_of_dvd_right hd2 },
  have notdvd_3_3 : ¬(3 ∣ (u + 3 * v)),
  { intro hd3,
    apply hddd,
    rw hpfactor,
    apply dvd_mul_of_dvd_right hd3 },

  obtain ⟨s, hs⟩ := hcubeleft,
  obtain ⟨C, A, B, HCpos, HApos, HBpos, HC, HA, HB⟩ : ∃ X Y Z : ℤ,
    X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    2 * u = X ^ 3 ∧ u - 3 * v = Y ^ 3 ∧ u + 3 * v = Z ^ 3,
  { apply int.cube_of_coprime (2 * u) (u - 3 * v) (u + 3 * v) s,
    { apply mul_ne_zero two_ne_zero u_ne_zero },
    { rw sub_ne_zero,
      rintro rfl,
      simpa only [int.not_even_bit1, false_or, iff_not_self] with parity_simps using huvodd },
    { intro H,
      rw add_eq_zero_iff_eq_neg at H,
      simpa [H] with parity_simps using huvodd },
    { apply int.gcd1_coprime12 u v; assumption },
    { apply int.gcd1_coprime13 u v; assumption },
    { apply int.gcd1_coprime23 u v; assumption },
    { rw ←haaa, exact hs } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,
  { rw [mul_comm, ←mul_assoc (C ^ 3), ←HA, ←HB, ←HC, ←haaa] },
  { rw [←HA, ←HB, ←HC], ring },
end

lemma gcd3_coprime
  {u v : ℤ}
  (huvcoprime: is_coprime u v)
  (huvodd : even u ↔ ¬even v) :
  is_coprime (2 * v) (u + v) ∧ is_coprime (2 * v) (u - v) ∧ is_coprime (u - v) (u + v) :=
begin
  have haddodd : ¬even (u + v),
  { simp [huvodd] with parity_simps },
  have hsubodd : ¬even (u - v),
  { simp [huvodd] with parity_simps },

  have haddcoprime : is_coprime (u + v) (2 * v),
  { apply int.is_coprime_of_dvd',
    { rintro ⟨h1, -⟩,
      norm_num [h1] at haddodd },
    intros k hknu hknz hkprime hkdvdleft hkdvdright,
    apply hknu,
    have hkdvdright' : k ∣ v,
    { exact int.dvd_mul_cancel_prime' haddodd hkdvdleft int.prime_two hkprime hkdvdright },

    apply huvcoprime.is_unit_of_dvd' _ hkdvdright',
    rw [←add_sub_cancel u v],
    apply dvd_sub hkdvdleft hkdvdright' },
  have hsubcoprime : is_coprime (u - v) (2 * v),
  { apply int.is_coprime_of_dvd',
    { rintro ⟨h1, -⟩,
      norm_num [h1] at hsubodd },
    intros k hknu hknz hkprime hkdvdleft hkdvdright,
    apply hknu,

    have hkdvdright' : k ∣ v,
    { exact int.dvd_mul_cancel_prime' hsubodd hkdvdleft int.prime_two hkprime hkdvdright },

    apply huvcoprime.is_unit_of_dvd' _ hkdvdright',
    rw [←sub_add_cancel u v],
    exact dvd_add hkdvdleft hkdvdright' },
  have haddsubcoprime : is_coprime (u + v) (u - v),
  { apply int.is_coprime_of_dvd',
    { rintro ⟨h1, -⟩,
      norm_num [h1] at haddodd },
    intros k hknu hknz hkprime hkdvdleft hkdvdright,
    apply hknu,
    apply huvcoprime.is_unit_of_dvd';
      apply int.dvd_mul_cancel_prime' haddodd hkdvdleft int.prime_two hkprime,

    { convert dvd_add hkdvdleft hkdvdright,
      ring },
    { convert dvd_sub hkdvdleft hkdvdright,
      ring } },
  exact ⟨haddcoprime.symm, hsubcoprime.symm, haddsubcoprime.symm⟩,
end

lemma descent_gcd3_coprime {q s : ℤ}
  (h3_ndvd_q : ¬3 ∣ q)
  (hspos : s ≠ 0)
  (hcoprime' : is_coprime s q)
  (hodd' : even q ↔ ¬even s) :
  is_coprime (3 ^ 2 * 2 * s) (q ^ 2 + 3 * s ^ 2) :=
begin
  have h2ndvd : ¬(2 ∣ (q ^ 2 + 3 * s ^ 2)),
  { change ¬(even _),
    simp [two_ne_zero, hodd'] with parity_simps },

  have h3ndvd : ¬(3 ∣ (q ^ 2 + 3 * s ^ 2)),
  { intro H,
    apply h3_ndvd_q,
    rw ←dvd_add_iff_left (dvd_mul_right _ _) at H,
    exact prime.dvd_of_dvd_pow int.prime_three H },

  apply int.is_coprime_of_dvd',
  { rintro ⟨h1, -⟩,
    rw mul_eq_zero at h1,
    exact hspos (h1.resolve_left (by norm_num)) },
  intros k hknu hknz hkprime hkdvdleft hkdvdright,
  apply hknu,
  have : k ∣ s,
  { apply int.dvd_mul_cancel_prime' h2ndvd hkdvdright int.prime_two hkprime,
    apply int.dvd_mul_cancel_prime' h3ndvd hkdvdright int.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' h3ndvd hkdvdright int.prime_three hkprime,
    convert hkdvdleft using 1,
    ring },
  apply hcoprime'.is_unit_of_dvd' this,
  apply hkprime.dvd_of_dvd_pow,
  rw dvd_add_iff_left (dvd_mul_of_dvd_right (dvd_pow this two_ne_zero) _),
  exact hkdvdright
end

lemma descent_gcd3 (a b c p q : ℤ)
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hcoprime : is_coprime p q)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime 3 a b c)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
  ∃ (a' b' c' : ℤ),
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 1.
  have h3_dvd_p : 3 ∣ p,
  { apply int.dvd_mul_cancel_prime _ nat.prime_two int.prime_three,
    { zify at hgcd,
      rw ← hgcd,
      convert int.gcd_dvd_left _ _},
    { norm_num } },
  have h3_ndvd_q : ¬(3 ∣ q),
  { intro H,
    have := hcoprime.is_unit_of_dvd' h3_dvd_p H,
    rw int.is_unit_iff_nat_abs_eq at this,
    norm_num at this },
  -- 2.
  obtain ⟨s, hs⟩ := h3_dvd_p,
  have hspos : s ≠ 0,
  { apply right_ne_zero_of_mul,
    rwa ←hs },
  have hps : 2 * p * (p ^ 2 + 3 * q ^ 2) = 3 ^ 2 * 2 * s * (q ^ 2 + 3 * s ^ 2),
  { calc 2 * p * (p ^ 2 + 3 * q ^ 2)
        = 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) : by rw hs
    ... = _ : by ring },
  -- 3.
  have hcoprime' : is_coprime s q,
  { apply int.is_coprime_of_dvd',
    { rintro ⟨h1, -⟩,
      exact hspos h1 },
    intros k hknu hknz hkprime hkdvdleft hkdvdright,
    apply hknu,
    apply hcoprime.is_unit_of_dvd' _ hkdvdright,
    rw hs,
    exact dvd_mul_of_dvd_right hkdvdleft 3 },

  have hodd' : even q ↔ ¬even s,
  { have : even p ↔ even s,
    { simp [hs] with parity_simps },
    rw this at hodd,
    tauto },
  have hcoprime'' : is_coprime (3^2 * 2 * s) (q ^ 2 + 3 * s ^ 2),
  { exact descent_gcd3_coprime h3_ndvd_q hspos hcoprime' hodd' },
  -- 4.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have h1 : 3 ^ 2 * 2 * s ≠ 0,
  { apply mul_ne_zero _ hspos,
    norm_num },
  have h2 : q ^ 2 + 3 * s ^ 2 ≠ 0 := spts.not_zero_of_coprime hcoprime'.symm,
  rw hps at hr,
  obtain ⟨hcubeleft, hcuberight⟩ := int.eq_pow_of_mul_eq_pow_bit1 h1 h2 hcoprime'' hr,

  -- 5.
  -- todo shadows hq hq
  obtain ⟨u, v, hq, hs, huvcoprime, huvodd⟩ := obscure' q s hq hspos hcoprime'.symm hodd' hcuberight,
  have hu : u ≠ 0,
  { rintro rfl,
    norm_num at hq },
  have hv : v ≠ 0,
  { rintro rfl,
    norm_num at hs },

  -- 6.
  obtain ⟨haddcoprime, hsubcoprime, haddsubcoprime⟩ := gcd3_coprime huvcoprime huvodd,

  -- 7.
  obtain ⟨t, ht⟩ : ∃ t, 2 * v * (u - v) * (u + v) = t ^ 3,
  { obtain ⟨e, he⟩ := hcubeleft,
    have hxxx : 3 ^ 3 * (2 * (u ^ 2 * v - v ^ 3)) = e ^ 3,
    { rw [←he, hs],
      ring },
    obtain ⟨g, rfl⟩ : 3 ∣ e,
    { rw ←int.pow_dvd_pow_iff (by norm_num : 0 < 3),
      rw ←hxxx,
      exact dvd_mul_right _ _ },
    use g,
    have : (3 ^ 3 : ℤ) ≠ 0,
    { norm_num },
    rw [←mul_right_inj' this, ←mul_pow],
    convert hxxx using 1,
    ring },

  obtain ⟨A, B, C, HApos, HBpos, HCpos, HA, HB, HC⟩ : ∃ X Y Z : ℤ,
    X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    2 * v = X ^ 3 ∧ u - v = Y ^ 3 ∧ u + v = Z ^ 3,
  { apply int.cube_of_coprime,
    { exact mul_ne_zero two_ne_zero hv, },
    { intro H, rw sub_eq_zero at H, simpa [H] with parity_simps using huvodd, },
    { intro H, rw add_eq_zero_iff_eq_neg at H, simpa [H] with parity_simps using huvodd },
    { exact hsubcoprime },
    { exact haddcoprime },
    { exact haddsubcoprime },
    { exact ht } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,
  -- 9.
  { rw [mul_comm, ←mul_assoc (C ^ 3), ←HA, ←HB, ←HC],
    set x := v * (u - v) * (u + v) with hx,
    calc ((u + v) * (2 * v) * (u - v)).nat_abs
        = (2 * x).nat_abs : by { rw hx, congr' 1, ring }
    ... = 2 * x.nat_abs : by { rw [int.nat_abs_mul 2], refl }
    ... ≤ 3 * x.nat_abs : nat.mul_le_mul_right _ (by norm_num)
    ... = (3 * x).nat_abs : by { rw [int.nat_abs_mul 3], refl }
    ... = s.nat_abs : by { rw [hx, hs], congr' 1, ring }
    ... ≤ 3 * s.nat_abs : nat.le_mul_of_pos_left (by norm_num)
    ... = (3 * s).nat_abs : by { rw [int.nat_abs_mul 3], refl }
    ... = p.nat_abs : by rw ‹p = 3 * s›
    ... ≤ 2 * p.nat_abs : nat.le_mul_of_pos_left (by norm_num)
    ... = (2 * p).nat_abs : by { rw [int.nat_abs_mul 2], refl } },
  { rw [←HA, ←HB, ←HC], ring },
end

lemma descent
  (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ a' b' c' : ℤ,
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' * b' * c').nat_abs < (a * b * c).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,

  suffices : ∃ a' b' c' : ℤ,
    a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧
    (a' ^ 3 * b' ^ 3 * c' ^ 3).nat_abs ≤ (2 * p).nat_abs ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3,
  { obtain ⟨a', b', c', ha', hb', hc', hsmaller, hsolution⟩ := this,
    refine ⟨a', b', c', ha', hb', hc', _, hsolution⟩,
    rw ←nat.pow_lt_iff_lt_left (by norm_num : 1 ≤ 3),
    convert lt_of_le_of_lt hsmaller haaa;
      simp [mul_pow, int.nat_abs_mul, int.nat_abs_pow] },

  -- 4.
  cases gcd1or3 p q hp hq hcoprime hodd with hgcd hgcd,
  -- 5.
  { rw int.gcd_eq_one_iff_coprime at hgcd,
    apply descent_gcd1 a b c p q hp hq hcoprime hodd hcube h hgcd },
  { apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube h hgcd },
end

lemma flt_three
  {a b c : ℤ}
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  suffices h : ∀ (k : ℕ) (a b c : ℤ),
    k = (a * b * c).nat_abs →
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { exact h (a * b * c).nat_abs a b c rfl ha hb hc },
  intro k,
  refine nat.strong_induction_on k _,
  intros k' IH x y z hk hxpos hypos hzpos H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ :=
    exists_coprime zero_lt_three hxpos hypos hzpos H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH (x' * y' * z').nat_abs _ _ _ _ rfl hx'pos hy'pos hz'pos hsolution,
  apply lt_of_lt_of_le hsmaller,
  rw hk,
  simp only [int.nat_abs_mul],
  apply nat.mul_le_mul _ hzle,
  apply nat.mul_le_mul hxle hyle,
end
