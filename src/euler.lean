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

def flt_coprime
  (a b c n : ℕ) :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  a ^ n + b ^ n = c ^ n ∧ 
  nat.coprime a b ∧
  nat.coprime a c ∧
  nat.coprime b c

lemma exists_coprime
  (a b c n : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
  (hn : 0 < n)
  (h : a ^ n + b ^ n = c ^ n) :
  ∃ a' b' c', a' ≤ a ∧ b' ≤ b ∧ c' ≤ c ∧ flt_coprime a' b' c' n :=
begin
  obtain ⟨hapos, hbpos, hcpos⟩ := hpos,
  let d := nat.gcd a b,
  obtain ⟨ha : d ∣ a, hb : d ∣ b⟩ := nat.gcd_dvd a b,
  have hc : d ∣ c,
  { rw [←nat.pow_dvd_pow_iff hn, ←h],
    apply dvd_add; rw nat.pow_dvd_pow_iff hn; assumption },
  have hdpos : 0 < d := nat.gcd_pos_of_pos_left _ hapos,
  have hsoln : (a / d) ^ n + (b / d) ^ n = (c / d) ^ n,
  { apply nat.eq_of_mul_eq_mul_right (pow_pos hdpos n),
    calc ((a / d) ^ n + (b / d) ^ n) * d ^ n
        = (a / d * d) ^ n  + (b / d * d) ^ n : by rw [add_mul, mul_pow (a / d), mul_pow (b / d)]
    ... = a ^ n + b ^ n : by rw [nat.div_mul_cancel ha, nat.div_mul_cancel hb]
    ... = c ^ n : h
    ... = (c / d * d) ^ n : by rw [nat.div_mul_cancel hc]
    ... = (c / d) ^ n * d ^ n : by rw mul_pow },
  have hsoln' : (b / d) ^ n + (a / d) ^ n = (c / d) ^ n,
  { rwa add_comm at hsoln },
  have hcoprime_div : nat.coprime (a / d) (b / d) := nat.coprime_div_gcd_div_gcd hdpos,
  exact ⟨
    a / d,
    b / d,
    c / d,
    nat.div_le_self a d,
    nat.div_le_self b d,
    nat.div_le_self c d,
    nat.div_pos (nat.le_of_dvd hapos ha) hdpos,
    nat.div_pos (nat.le_of_dvd hbpos hb) hdpos,
    nat.div_pos (nat.le_of_dvd hcpos hc) hdpos,
    hsoln,
    hcoprime_div,
    nat.coprime_add_self_pow hn hsoln hcoprime_div,
    nat.coprime_add_self_pow hn hsoln' hcoprime_div.symm
  ⟩
end

lemma descent1a {a b c : ℕ}
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (habcoprime : a.coprime b)
  (haccoprime : a.coprime c)
  (hbccoprime : b.coprime c) :
  (even a ∧ ¬even b ∧ ¬even c ∨
   ¬even a ∧ even b ∧ ¬even c) ∨
  ¬even a ∧ ¬even b ∧ even c :=
begin
  have contra : ∀ {x y}, nat.coprime x y → even x → even y → false,
  { intros x y hcoprime hx hy,
    have : 2 ∣ nat.gcd x y := nat.dvd_gcd hx hy,
    rw hcoprime.gcd_eq_one at this,
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
    rw [←nat.even_pow' three_ne_zero, ←h],
    simp [haparity, hbparity, three_ne_zero] with parity_simps },
end

lemma descent1left {a b c : ℕ}
  (hapos : 0 < a)
  (hbpos : 0 < b)
  (hcpos : 0 < c)
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (habcoprime : a.coprime b)
  (haccoprime : a.coprime c)
  (hbccoprime : b.coprime c)
  (ha : even a)
  (hb : ¬even b)
  (hc : ¬even c) :
  ∃ (p q : ℕ),
    0 < p ∧
      0 < q ∧
        p.gcd q = 1 ∧
          (even p ↔ ¬even q) ∧
            (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
                 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  obtain ⟨p, hp⟩ : even (c - b : ℤ),
  { simp [hb, hc] with parity_simps},
  obtain ⟨q, hq⟩ : even (c + b : ℤ),
  { simp [hb, hc] with parity_simps},
  have hadd : p + q = c,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_add, ←hp, ←hq],
    ring },
  have hsub : q - p = b,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_sub, ←hp, ←hq],
    ring },
  have hqpos : 0 < q,
  { apply pos_of_mul_pos_left,
    { rw ←hq,
      norm_cast,
      apply nat.add_pos_left hcpos },
    { norm_num } },

  have : p ≠ 0,
  { have : c ≠ b,
    { rintro rfl,
      conv_rhs at h { rw [←zero_add (c ^ 3)] },
      rw [add_left_inj] at h,
      exact ne_of_gt hapos (pow_eq_zero h) },
    rintro rfl,
    rw mul_zero at hp,
    rw sub_eq_zero at hp,
    norm_cast at hp },

  have hppos : 0 < p,
  { apply pos_of_mul_pos_left,
    { rw ←hp,
      rw sub_pos,
      norm_cast,
      rw ←nat.pow_lt_iff_lt_left (by norm_num : 1 ≤ 3),
      rw ←h,
      apply nat.lt_add_of_pos_left,
      apply pow_pos,
      exact hapos },
    { norm_num } },

  refine ⟨p.nat_abs, q.nat_abs, _, _, _, _, _⟩,
  { rw pos_iff_ne_zero,
    rw int.nat_abs_ne_zero,
    assumption, },
  { rw pos_iff_ne_zero,
    rw int.nat_abs_ne_zero,
    apply ne_of_gt,
    assumption, },
  { rw [←nat.dvd_one, ←hbccoprime.gcd_eq_one],
    apply nat.dvd_gcd; rw ←int.coe_nat_dvd,
    { rw ← hsub,
      apply dvd_sub; rw int.coe_nat_dvd_left,
      { apply nat.gcd_dvd_right },
      { apply nat.gcd_dvd_left } },
    { rw ← hadd,
      apply dvd_add; rw int.coe_nat_dvd_left,
      { apply nat.gcd_dvd_left },
      { apply nat.gcd_dvd_right } } },
  { have : ¬even (p + q),
    { rwa [hadd, int.even_coe_nat] },
    simp with parity_simps at this ⊢,
    tauto },
  { left,
    zify,
    zify at h,
    rw eq_sub_of_add_eq h,
    rw [←hadd, ←hsub],
    have : p = p.nat_abs,
    { lift p to ℕ using hppos.le,
      rw [int.nat_abs_of_nat] },
    rw ←this,
    have : q = q.nat_abs,
    { lift q to ℕ using hqpos.le,
      rw [int.nat_abs_of_nat] },
    rw ←this,
    ring },
end

lemma flt_not_add_self {a b c : ℕ} (hapos : 0 < a) (h : a ^ 3 + b ^ 3 = c ^ 3) : a ≠ b :=
begin
  rintro rfl,
  rw ←mul_two at h,
  apply two_not_cube (c/a),
  rw div_pow',
  { rw [←h, mul_comm, nat.mul_div_cancel],
    exact pow_pos hapos 3 },

  { rw [←nat.pow_dvd_pow_iff (by norm_num : 0 < 3), ←h],
    apply dvd_mul_right },
end

lemma descent1 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  have := descent1a h habcoprime haccoprime hbccoprime,
  cases this,
  { cases this,
    { rcases this with ⟨ha, hb, hc⟩,
      exact descent1left hapos hbpos hcpos h habcoprime haccoprime hbccoprime ha hb hc },
    { rw add_comm at h,
      rcases this with ⟨ha, hb, hc⟩,
      have := descent1left hbpos hapos hcpos h habcoprime.symm hbccoprime haccoprime hb ha hc,
      obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := this,
      refine ⟨p, q, hp, hq, hcoprime, hodd, _⟩,
      tauto } },
  { rcases this with ⟨ha, hb, hc⟩,
    obtain ⟨p, hp⟩ : even (a + b : ℤ),
    { simp [ha, hb] with parity_simps},
    obtain ⟨q, hq⟩ : even (a - b : ℤ),
    { simp [ha, hb] with parity_simps},
    have hadd : p + q = a,
    { apply int.eq_of_mul_eq_mul_left two_ne_zero,
      rw [mul_add, ←hp, ←hq],
      ring },
    have hsub : p - q = b,
    { apply int.eq_of_mul_eq_mul_left two_ne_zero,
      rw [mul_sub, ←hp, ←hq],
      ring },
    have : p ≠ 0,
    { rintro rfl,
      rw [mul_zero, ←int.coe_nat_zero, ←int.coe_nat_add, int.coe_nat_eq_coe_nat_iff] at hp,
      exact ne_of_gt hapos (nat.eq_zero_of_add_eq_zero_right hp) },
    have : int.gcd p q = 1,
    { rw [←nat.dvd_one, ←habcoprime.gcd_eq_one],
      apply nat.dvd_gcd; rw ←int.coe_nat_dvd,
      { rw ← hadd,
        apply dvd_add; rw int.coe_nat_dvd_left,
        { apply nat.gcd_dvd_left },
        { apply nat.gcd_dvd_right } },
      { rw ← hsub,
        apply dvd_sub; rw int.coe_nat_dvd_left,
        { apply nat.gcd_dvd_left },
        { apply nat.gcd_dvd_right } } },
    have : 0 < p,
    { refine pos_of_mul_pos_left _ zero_lt_two.le,
      { rw ←hp,
        norm_cast,
        apply nat.add_pos_left hapos } },
    have : p = p.nat_abs,
    { rw ←int.abs_eq_nat_abs,
      symmetry,
      apply abs_of_nonneg,
      exact this.le },
    have : q ≠ 0,
    { rintro rfl,
      apply flt_not_add_self hapos h,
      rwa [mul_zero, sub_eq_zero, int.coe_nat_inj'] at hq },
    refine ⟨p.nat_abs, q.nat_abs, _, _, _, _, _⟩,
    { rw pos_iff_ne_zero,
      rw int.nat_abs_ne_zero,
      apply ne_of_gt,
      assumption, },
    { rw pos_iff_ne_zero,
      rw int.nat_abs_ne_zero,
      assumption, },
    { assumption },
    { have : ¬even (p + q),
      { rwa [hadd, int.even_coe_nat] },
      simp with parity_simps at this ⊢,
      tauto },
    { right, right,
      rw  ←h,
      zify,
      rw [←‹p = _›, int.nat_abs_square q, ←hadd, ←hsub],
      ring } },
end

lemma descent11 {a b c d : ℕ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { apply dvd_mul_of_dvd_left, apply dvd_mul_right },
  { apply dvd_mul_of_dvd_left, apply dvd_mul_left },
  { apply dvd_mul_left }
end

lemma descent12 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
 (h : d = a ∨ d = b ∨ d = c) : d ≤ (a * b * c) :=
nat.le_of_dvd (mul_pos (mul_pos ha hb) hc) (descent11 h)

lemma descent2 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    (2 * p < a ^ 3 * b ^ 3 * c ^ 3) :=
begin
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1 a b c h,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,

  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  apply lt_of_lt_of_le,
  swap,
  { refine descent12 _ _ _ hcube;
    rwa ←nat.pos_pow_iff zero_lt_three },
  { apply lt_mul_of_one_lt_right,
    { linarith },
    { rw nat.pos_pow_iff zero_lt_two at hp hq,
      linarith } }
end

lemma gcd1or3
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.coprime p q)
  (hparity : even p ↔ ¬even q) :
  nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  set g := nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) with hg',
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2,
  { obtain ⟨k, hg, hk⟩ := H,
    rcases k with (_|_|_),
    { left, norm_num at hg, exact hg },
    { right, norm_num at hg, exact hg },
    { change k + 2 < 2 at hk,
      linarith } },

  have basic : ∀ f, nat.prime f → f ∣ 2 * p → f ∣ (p ^ 2 + 3 * q ^ 2) → f = 3,
  { intros d hdprime hdleft hdright,
    have hne2 : d ≠ 2,
    { rintro rfl,
      change even _ at hdright,
      simp [hparity, two_ne_zero] with parity_simps at hdright,
      assumption },
    have : 2 < d := lt_of_le_of_ne (hdprime.two_le) hne2.symm,
    by_contra hne3,
    change d ≠ 3 at hne3,
    have : 3 < d := lt_of_le_of_ne (this) hne3.symm,
    obtain ⟨P, hP⟩ := hdleft,
    obtain ⟨Q, hQ⟩ := hdright,
    obtain ⟨H, hH⟩ : 2 ∣ P,
    { have H := dvd_mul_right 2 p,
      rw [hP, nat.prime.dvd_mul nat.prime_two] at H,
      cases H,
      { rw nat.dvd_prime hdprime at H,
        cases H,
        { norm_num at H },
        { exfalso,
          exact hne2 H.symm } },
      { assumption } },
    have : p = d * H,
    { rw [←nat.mul_right_inj zero_lt_two, hP, hH],
      ring },
    have : 3 * q ^ 2 = d * (Q - d * H ^ 2),
    { calc 3 * q ^ 2
          = d * Q - p ^ 2 : (nat.sub_eq_of_eq_add hQ.symm).symm
      ... = d * Q - d ^ 2 * H ^ 2 : by rw [this, mul_pow]
      ... = d * Q - d * (d * H ^ 2) : by ring
      ... = d * (Q - d * H ^ 2) : by rw nat.mul_sub_left_distrib },
    have : d ∣ q,
    { have h000 : d ∣ 3 * q ^ 2,
      { rw this,
        apply dvd_mul_right },
      rw nat.prime.dvd_mul hdprime at h000,
      cases h000,
      { linarith [nat.le_of_dvd (by norm_num) h000] },
      { exact nat.prime.dvd_of_dvd_pow hdprime h000 } },
    have : d ∣ p,
    { rw ‹p = _›, exact dvd_mul_right d H },
    have := nat.not_coprime_of_dvd_of_dvd hdprime.one_lt ‹d ∣ p› ‹d ∣ q›,
    contradiction },

  set k := g.factors.length,
  have hg : g = 3 ^ k,
  { apply eq_pow,
   { apply nat.gcd_pos_of_pos_left,
     apply nat.mul_pos zero_lt_two hp },
    intros d hdprime hddvdg,
    apply basic _ hdprime,
    exact dvd_trans hddvdg (nat.gcd_dvd_left _ _),
    exact dvd_trans hddvdg (nat.gcd_dvd_right _ _) },
  refine ⟨k, hg, _⟩,
  by_contra H,
  push_neg at H,
  rw ←pow_mul_pow_sub _ H at hg,
  have hdvdp : 3 ∣ p,
  { suffices : 3 ∣ 2 * p,
    { apply dvd_mul_cancel_prime this (by norm_num) nat.prime_two nat.prime_three },
    have : 3 ∣ g,
    { rw [hg, pow_two, mul_assoc],
      apply dvd_mul_right },
    exact dvd_trans this (nat.gcd_dvd_left _ _) }, 
  have hdvdq : 3 ∣ q,
  { have dvdpsq : 3 ^ 2 ∣ p ^ 2,
    { rwa nat.pow_dvd_pow_iff zero_lt_two },
    suffices : 3 ∣ q ^ 2,
    { apply nat.prime.dvd_of_dvd_pow nat.prime_three this },
    suffices : 3 ^ 2 ∣ 3 * q ^ 2,
    { rwa [pow_two, nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)] at this },
    suffices : 3 ^ 2 ∣ p ^ 2 + 3 * q ^ 2,
    { rwa nat.dvd_add_iff_right dvdpsq },
    refine dvd_trans _ (nat.gcd_dvd_right (2 * p) _),
    rw [←hg', hg],
    apply dvd_mul_right },

  exact nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) hdvdp hdvdq hcoprime,
end

lemma obscure'
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.gcd p q = 1)
  (hparity : even p ↔ ¬even q)
  (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
  ∃ a b : ℤ,
    (p : ℤ) = a ^ 3 - 9 * a * b ^ 2 ∧
    (q : ℤ) = 3 * a ^ 2 * b - 3 * b ^ 3 ∧
    is_coprime a b ∧
    (even a ↔ ¬even b) :=
begin
  obtain ⟨u, hu⟩ := hcube,

  have hcoprime' : is_coprime (p : ℤ) q,
  { rw ←int.gcd_eq_one_iff_coprime,
    simp only [int.gcd],
    rwa [int.nat_abs_of_nat] },

  obtain ⟨a, b, hp', hq'⟩ := step6 p q u hcoprime' _,
  refine ⟨a, b, hp', hq', _, _⟩,
  { apply is_coprime_of_dvd,
    { rintro ⟨rfl, rfl⟩,
      norm_num at hp',
      exact hp.ne.symm hp' },

    intros k hknu hknezero hkdvdleft hkdvdright,
    apply hknu,
    apply hcoprime'.is_unit_of_dvd',
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
      { rw [←int.even_coe_nat, hp'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      have : even q,
      { rw [←int.even_coe_nat, hq'],
        simp [haparity, hbparity, three_ne_zero] with parity_simps },
      tauto } },
  { norm_cast, exact hu.symm }
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
  obtain ⟨A, HA⟩ : ∃ A, a = A ^ 3,
  { rw [mul_assoc] at hs,
    apply int.eq_pow_of_mul_eq_pow_bit1 ha _ _ hs,
    { exact mul_ne_zero hb hc },
    { exact is_coprime.mul_right hcoprimeab hcoprimeac } },
  obtain ⟨B, HB⟩ : ∃ B, b = B ^ 3,
  { rw [mul_comm a b, mul_assoc] at hs,
    apply int.eq_pow_of_mul_eq_pow_bit1 hb _ _ hs,
    { exact mul_ne_zero ha hc },
    { exact is_coprime.mul_right hcoprimeab.symm hcoprimebc } },
  obtain ⟨C, HC⟩ : ∃ C, c = C ^ 3,
  { rw [mul_comm] at hs,
    apply int.eq_pow_of_mul_eq_pow_bit1 hc _ _ hs,
    { exact mul_ne_zero ha hb },
    { exact is_coprime.mul_right hcoprimeac.symm hcoprimebc.symm } },
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
  { exact int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright nat.prime_two hkprime hkdvdleft },
  { apply int.dvd_mul_cancel_prime' not_3_dvd_2 hkdvdright nat.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdright nat.prime_two hkprime,
    convert dvd_sub hkdvdleft (dvd_mul_of_dvd_right hkdvdright 2),
    norm_num,
    ring },
end

lemma int.gcd1_coprime13 (u v : ℤ)
  (huvcoprime : is_coprime u v)
  (this : ¬even (u + 3 * v))
  (not_3_dvd_2 : ¬3 ∣ u - 3 * v)
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  is_coprime (2 * u) (u + 3 * v) :=
begin
  apply int.is_coprime_of_dvd',
  { rintro ⟨-, h2⟩,
    norm_num [h2] at this },
  intros k hknu hknz hkprime hkdvdleft hkdvdright,
  apply hknu,
  apply huvcoprime.is_unit_of_dvd',
  { exact int.dvd_mul_cancel_prime' this hkdvdright nat.prime_two hkprime hkdvdleft },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright nat.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' this hkdvdright nat.prime_two hkprime,
    convert dvd_sub (dvd_mul_of_dvd_right hkdvdright 2) hkdvdleft,
    norm_num,
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
  { apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft nat.prime_two hkprime,
    convert dvd_add hkdvdleft hkdvdright,
    norm_num,
    ring },
  { apply int.dvd_mul_cancel_prime' notdvd_3_3 hkdvdright nat.prime_three hkprime,
    apply int.dvd_mul_cancel_prime' notdvd_2_2 hkdvdleft nat.prime_two hkprime,
    norm_num,
    convert dvd_sub hkdvdright hkdvdleft,
    ring },
end

lemma nat_solution_of_int_solution
  {a b c : ℤ}
  (u : ℕ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (hu : (a ^ 3 * b ^ 3 * c ^ 3).nat_abs ≤ u)
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  :
  ∃ a' b' c' : ℕ,
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧ a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ u ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  have hu' : a.nat_abs ^ 3 * b.nat_abs ^ 3 * c.nat_abs ^ 3 ≤ u,
  { rwa [←int.nat_abs_pow, ←int.nat_abs_pow, ←int.nat_abs_pow, ←int.nat_abs_mul, ←int.nat_abs_mul] },
  have ha': 0 < a.nat_abs := nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero ha),
  have hb': 0 < b.nat_abs := nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero hb),
  have hc': 0 < c.nat_abs := nat.pos_of_ne_zero (int.nat_abs_ne_zero_of_ne_zero hc),
  cases ha.lt_or_lt with haneg hapos;
  cases hb.lt_or_lt with hbneg hbpos;
  cases hc.lt_or_lt with hcneg hcpos,
  { use [a.nat_abs, b.nat_abs, c.nat_abs, ‹_›, ‹_›, ‹_›, hu'],
    zify,
    rw [int.of_nat_nat_abs_of_nonpos haneg.le, neg_pow_bit1],
    rw [int.of_nat_nat_abs_of_nonpos hbneg.le, neg_pow_bit1],
    rw [int.of_nat_nat_abs_of_nonpos hcneg.le, neg_pow_bit1],
    rw [←h, neg_add] },
  { exfalso,
    apply lt_irrefl (0 : ℤ),
    rw ←pow_bit1_neg_iff at haneg hbneg,
    rw ←pow_bit1_pos_iff at hcpos,
    calc 0 < c ^ 3 : hcpos
    ... = a ^ 3 + b ^ 3 : h.symm
    ... < 0 : add_neg haneg hbneg },
  { refine ⟨b.nat_abs, c.nat_abs, a.nat_abs, ‹_›, ‹_›, ‹_›, _, _⟩,
    { convert hu' using 1, ring },
    zify,
    rw [int.of_nat_nat_abs_of_nonpos haneg.le, neg_pow_bit1],
    rw [int.nat_abs_of_nonneg hbpos.le],
    rw [int.of_nat_nat_abs_of_nonpos hcneg.le, neg_pow_bit1],
    rw ←h,
    ring },
  { refine ⟨a.nat_abs, c.nat_abs, b.nat_abs, ‹_›, ‹_›, ‹_›, _, _⟩,
    { convert hu' using 1, ring },
    zify,
    rw [int.of_nat_nat_abs_of_nonpos haneg.le, neg_pow_bit1],
    rw [int.nat_abs_of_nonneg hbpos.le],
    rw [int.nat_abs_of_nonneg hcpos.le],
    rw ←h,
    ring },
  { refine ⟨a.nat_abs, c.nat_abs, b.nat_abs, ‹_›, ‹_›, ‹_›, _, _⟩,
    { convert hu' using 1, ring },
    zify,
    rw [int.nat_abs_of_nonneg hapos.le],
    rw [int.of_nat_nat_abs_of_nonpos hbneg.le, neg_pow_bit1],
    rw [int.of_nat_nat_abs_of_nonpos hcneg.le, neg_pow_bit1],
    rw ←h,
    ring },
  { refine ⟨b.nat_abs, c.nat_abs, a.nat_abs, ‹_›, ‹_›, ‹_›, _, _⟩,
    { convert hu' using 1, ring },
    zify,
    rw [int.nat_abs_of_nonneg hapos.le],
    rw [int.of_nat_nat_abs_of_nonpos hbneg.le, neg_pow_bit1],
    rw [int.nat_abs_of_nonneg hcpos.le],
    rw ←h,
    ring },
  { exfalso,
    apply lt_irrefl (0 : ℤ),
    rw ←pow_bit1_pos_iff at hapos hbpos,
    rw ←pow_bit1_neg_iff at hcneg,
    calc 0 < a ^ 3 + b ^ 3 : add_pos hapos hbpos
    ... = c ^ 3 : h
    ... < 0 : hcneg },
  { use [a.nat_abs, b.nat_abs, c.nat_abs, ‹_›, ‹_›, ‹_›, hu'],
    zify,
    rw [int.nat_abs_of_nonneg hapos.le],
    rw [int.nat_abs_of_nonneg hbpos.le],
    rw [int.nat_abs_of_nonneg hcpos.le],
    exact h },
end

lemma descent_gcd1 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 1) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 2.
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have hposleft : 0 < 2 * p := nat.mul_pos zero_lt_two hp,
  have hposright : 0 < p ^ 2 + 3 * q ^ 2 := nat.add_pos_left (pow_pos hp 2) _,
  have hcubeleft : ∃ s, 2 * p = s ^ 3 := nat.eq_pow_of_mul_eq_pow hposleft hposright hgcd hr,
  have hcuberight : ∃ t, p ^ 2 + 3 * q ^ 2 = t ^ 3,
  { rw mul_comm at hr,
    rw nat.gcd_comm at hgcd,
    exact nat.eq_pow_of_mul_eq_pow hposright hposleft hgcd hr },
  -- todo shadowing hp hq
  obtain ⟨u, v, hp, hq, huvcoprime, huvodd⟩ := obscure' p q hp hq hcoprime hodd hcuberight,
  have u_ne_zero : u ≠ 0,
  { rintro rfl, apply ‹0 < p›.ne.symm, norm_num at hp, assumption },
  have hpfactor : (p : ℤ) = u * (u - 3 * v) * (u + 3 * v),
  { rw hp, ring },
  have haaa : (2 * p : ℤ) = (2 * u) * (u - 3 * v) * (u + 3 * v),
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
    { apply nat.dvd_add,
      { rw pow_two,
        apply dvd_mul_of_dvd_right H },
      { apply dvd_mul_right } },
    have : 3 ∣ 2 * p := dvd_mul_of_dvd_right H 2,
    have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
    rw hgcd at this,
    have := nat.eq_one_of_dvd_one this,
    norm_num at this },
  have not_3_dvd_2 : ¬(3 ∣ (u - 3 * v)),
  { intro hd2,
    apply hddd,
    rw ←int.coe_nat_dvd,
    rw hpfactor,
    apply dvd_mul_of_dvd_left _,
    apply dvd_mul_of_dvd_right hd2 },
  have notdvd_3_3 : ¬(3 ∣ (u + 3 * v)),
  { intro hd3,
    apply hddd,
    rw ←int.coe_nat_dvd,
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
    { rw ←haaa, norm_cast, exact hs } },

  apply nat_solution_of_int_solution (2 * p) HApos HBpos HCpos,
  { rw [mul_comm, ←mul_assoc (C ^ 3), ←HA, ←HB, ←HC, ←haaa],
    norm_cast },
  { rw [←HA, ←HB, ←HC], ring },
end

lemma descent_gcd3 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 1.
  have h3_dvd_p : 3 ∣ p,
  { apply dvd_mul_cancel_prime _ (by norm_num) nat.prime_two nat.prime_three,
    rw ← hgcd,
    apply nat.gcd_dvd_left },
  have h3_ndvd_q : ¬(3 ∣ q),
  { intro H,
    apply nat.prime.not_dvd_one nat.prime_three,
    conv_rhs { rw ←hcoprime },
    exact nat.dvd_gcd h3_dvd_p H },
  -- 2.
  obtain ⟨s, hs⟩ := h3_dvd_p,
  have hspos : 0 < s,
  { linarith },
  have hps : 2 * p * (p ^ 2 + 3 * q ^ 2) = 3 ^ 2 * 2 * s * (q ^ 2 + 3 * s ^ 2),
  calc 2 * p * (p ^ 2 + 3 * q ^ 2)
      = 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) : by rw hs
  ... = _ : by ring,
  -- 3.
  have hcoprime' : nat.coprime s q,
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    have hkdvdp : k ∣ p,
    { rw hs,
      exact dvd_mul_of_dvd_right hkdvdleft 3 },
    rw ←hcoprime,
    exact nat.dvd_gcd hkdvdp hkdvdright },
  
  have hodd' : even q ↔ ¬even s,
  { have : even p ↔ even s,
    { simp [hs] with parity_simps },
    rw this at hodd,
    tauto },
  have hcoprime'' : nat.coprime (3^2 * 2 * s) (q ^ 2 + 3 * s ^ 2),
  { have : ¬(2 ∣ (q ^ 2 + 3 * s ^ 2)),
    { change ¬(even _),
      simp [hs, two_ne_zero, hodd'] with parity_simps },

    have : ¬(3 ∣ (q ^ 2 + 3 * s ^ 2)),
    { intro H,
      apply h3_ndvd_q,
      rw ←nat.dvd_add_iff_left (dvd_mul_right _ _) at H,
      exact nat.prime.dvd_of_dvd_pow nat.prime_three H },

    apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    rw ←hcoprime'.gcd_eq_one,
    have hkne2 : k ≠ 2,
    { rintro rfl, contradiction },
    have hkne3 : k ≠ 3,
    { rintro rfl, contradiction },
    have : k ∣ s,
    { apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      convert hkdvdleft using 1,
      ring },
    have : k ∣ q,
    { have : k ∣ 3 * s ^ 2 := dvd_mul_of_dvd_right (dvd_pow this two_ne_zero) _,
      rw ←nat.dvd_add_iff_left this at hkdvdright,
      exact hkprime.dvd_of_dvd_pow hkdvdright },
    exact nat.dvd_gcd ‹_› ‹_›,
  },
  -- 4.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have : 0 < 3 ^ 2 * 2 * s,
  { linarith },
  have : 0 < q ^ 2 + 3 * s ^ 2,
  { apply nat.add_pos_right,
    apply nat.mul_pos (by norm_num : 0 < 3) (pow_pos hspos _) },
  have hcubeleft : ∃ e, 3 ^ 2 * 2 * s = e ^ 3,
  { rw hps at hr,
    exact nat.eq_pow_of_mul_eq_pow ‹_› ‹_› hcoprime'' hr },
  have hcuberight : ∃ f, q ^ 2 + 3 * s ^ 2 = f ^ 3,
  { rw [hps, mul_comm] at hr,
    exact nat.eq_pow_of_mul_eq_pow ‹_› ‹_› hcoprime''.symm hr },

  -- 5.
  -- todo shadows hq hq
  obtain ⟨u, v, hq, hs, huvcoprime, huvodd⟩ := obscure' q s hq hspos hcoprime'.symm hodd' hcuberight,
  have hu : u ≠ 0,
  { rintro rfl,
    norm_num at hq,
    exact ‹0 < q›.ne.symm hq },
  have hv : v ≠ 0,
  { rintro rfl,
    norm_num at hs,
    exact ‹0 < s›.ne.symm hs },

  -- 6.
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
    { exact int.dvd_mul_cancel_prime' haddodd hkdvdleft nat.prime_two hkprime hkdvdright },

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
    { exact int.dvd_mul_cancel_prime' hsubodd hkdvdleft nat.prime_two hkprime hkdvdright },

    apply huvcoprime.is_unit_of_dvd' _ hkdvdright',
    rw [←sub_add_cancel u v],
    exact dvd_add hkdvdleft hkdvdright' },
  have haddsubcoprime : is_coprime (u + v) (u - v),
  { apply int.is_coprime_of_dvd',
    { rintro ⟨h1, -⟩,
      norm_num [h1] at haddodd },
    intros k hknu hknz hkprime hkdvdleft hkdvdright,
    have kne2 : abs k ≠ 2,
    { rintro hk,
      rw [int.dvd_iff_abs_dvd, hk] at hkdvdleft,
      exact haddodd hkdvdleft },

    apply hknu,
    apply huvcoprime.is_unit_of_dvd';
      apply int.dvd_mul_cancel_prime' haddodd hkdvdleft nat.prime_two hkprime,

    { convert dvd_add hkdvdleft hkdvdright,
      norm_num,
      ring },
    { convert dvd_sub hkdvdleft hkdvdright,
      norm_num,
      ring } },

  -- 7.
  obtain ⟨t, ht⟩ : ∃ t, 2 * v * (u - v) * (u + v) = t ^ 3,
  { obtain ⟨e, he⟩ := hcubeleft,
    obtain ⟨f, hf⟩ := hcuberight,
    have hxxx : 3 ^ 3 * (2 * (u ^ 2 * v - v ^ 3)) = e ^ 3,
    { zify at he,
      rw [←he, hs],
      ring },
    have : 3 ∣ e,
    { rw ←int.coe_nat_dvd,
      rw ←int.pow_dvd_pow_iff (by norm_num : 0 < 3),
      rw ←hxxx,
      exact dvd_mul_right _ _ },
    have : (e / 3) ^ 3 = e ^ 3 / 3 ^ 3 := div_pow' _ _ _ this,
    zify at this,
    use e / 3,
    symmetry,
    calc ((e : ℤ) / 3) ^ 3
        = (e : ℤ) ^ 3 / 3 ^ 3 : this
    ... = (3 ^ 3 * (2 * (u ^ 2 * v - v ^ 3))) / 3 ^ 3 : by rw hxxx
    ... = ((2 * (u ^ 2 * v - v ^ 3)) * 3 ^ 3) / 3 ^ 3 : by rw mul_comm
    ... = 2 * (u ^ 2 * v - v ^ 3) : int.mul_div_cancel _ (by norm_num : (3 ^ 3 : ℤ) ≠ 0)
    ... = 2 * v * (u ^ 2 - v ^ 2) : by rw [mul_assoc, mul_comm v, mul_sub_right_distrib, pow_succ' v]
    ... = 2 * v * (u - v) * (u + v) : by { rw pow_two_sub_pow_two, ring } },

  obtain ⟨A, B, C, HApos, HBpos, HCpos, HA, HB, HC⟩ : ∃ X Y Z : ℤ,
    X ≠ 0 ∧ Y ≠ 0 ∧ Z ≠ 0 ∧
    2 * v = X ^ 3 ∧ u - v = Y ^ 3 ∧ u + v = Z ^ 3,
  { apply int.cube_of_coprime,
    { exact mul_ne_zero two_ne_zero hv, },
    { intro H, norm_num [H] at hsubodd },
    { intro H, norm_num [H] at haddodd },
    { exact hsubcoprime.symm },
    { exact haddcoprime.symm },
    { exact haddsubcoprime.symm },
    { exact ht } },

  apply nat_solution_of_int_solution (2 * p) HApos HBpos HCpos,

  -- 9.
  { apply le_of_lt,
    calc (A ^ 3 * B ^ 3 * C ^ 3).nat_abs
        ≤ s : _
    ... < 3 * s : nat.lt_mul_left s 3 (by norm_num) hspos
    ... = p : eq.symm ‹_›
    ... < 2 * p : nat.lt_mul_left p 2 (by norm_num) hp,

    rw [←HA, ←HB, ←HC],
    set x := v * (u - v) * (u + v) with hx,

    calc (2 * v * (u - v) * (u + v)).nat_abs
        = (2 * x).nat_abs : by { rw hx, congr' 1, ring }
    ... = 2 * x.nat_abs : by { rw [int.nat_abs_mul 2], refl }
    ... ≤ 3 * x.nat_abs : nat.mul_le_mul_right _ (by norm_num)
    ... = (3 * x).nat_abs : by { rw [int.nat_abs_mul 3], refl }
    ... = s : by { rw [hx, ←int.nat_abs_of_nat s, hs], congr' 1, ring } },

  -- 8.
  { calc A ^ 3 + B ^ 3
        = 2 * v + (u - v) : by rw [HA, HB]
    ... = u + v : by ring
    ... = C ^ 3 : HC },
end

lemma descent
  (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ a' b' c', 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ (a' * b' * c' < a * b * c) ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,

  suffices : ∃ a' b' c',
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3,
  { obtain ⟨a', b', c', ha', hb', hc', hsmaller, hsolution⟩ := this,
    refine ⟨a', b', c', ha', hb', hc', _, hsolution⟩,
    rw ←nat.pow_lt_iff_lt_left (by norm_num : 1 ≤ 3),
    iterate 4 {rw mul_pow},
    exact lt_of_le_of_lt hsmaller haaa },

  -- 4.
  cases gcd1or3 p q hp hq hcoprime hodd with hgcd hgcd,
  -- 5.
  { apply descent_gcd1 a b c p q hp hq hcoprime hodd hcube h hgcd },
  { apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube h hgcd },
end

lemma flt_three
  (a b c : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  suffices h : ∀ k a b c : ℕ, k = a * b * c → (0 < a ∧ 0 < b ∧ 0 < c) → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { exact h (a * b * c) a b c rfl hpos },
  intro k,
  refine nat.strong_induction_on k _,
  intros k' IH x y z hk hpos H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ := exists_coprime x y z 3 hpos (by norm_num) H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH (x' * y' * z') _ _ _ _ rfl ⟨hx'pos, hy'pos, hz'pos⟩ hsolution,
  apply lt_of_lt_of_le hsmaller,
  rw hk,
  apply nat.mul_le_mul _ hzle,
  apply nat.mul_le_mul hxle hyle,
end
