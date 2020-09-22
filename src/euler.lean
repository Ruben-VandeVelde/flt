import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic
import .primes

example (a b : int) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := sq_sub_sq a b
example (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
begin
  rw nat.pow_two,
  rw nat.pow_two,
  exact nat.mul_self_sub_mul_self_eq a b,
end
theorem nat.sq_sub_sq (a b : nat) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
nat.pow_two_sub_pow_two _ _

example (a b : nat) : (a + b) % 2 = (a + (b % 2)) % 2 := (nat.add_mod_mod a b 2).symm
--example (a b : nat) : (a - b) % 2 = (a - (b % 2)) % 2 := by library_search
example (P Q : Prop) (h: ¬(P ↔ Q)) : (P ↔ ¬Q) := by {tauto!,}
example (d x n : nat) (h: 0 < n) : d ^ n ∣ x ^ n → d ∣ x := by refine (nat.pow_dvd_pow_iff h).mp

theorem coprime_div_gcd_div_gcd' {m n : ℕ} (H : 0 < nat.gcd m n) :
  nat.coprime (m / nat.gcd m n) (n / nat.gcd m n) :=
begin
  delta nat.coprime,
  rw nat.gcd_div (nat.gcd_dvd_left m n) (nat.gcd_dvd_right m n),
  rw nat.div_self H,
end

def flt_coprime
  (a b c n : ℕ) :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  a ^ n + b ^ n = c ^ n ∧ 
  nat.coprime a b ∧
  nat.coprime a c ∧
  nat.coprime b c

--example (d c : nat) (h : d ∣ c) : d ≤ c := by refine nat.le_of_dvd _ h
--example (c d n : nat) (h : d ∣ c) : c ^ n / d ^ n = (c / d) ^ n := by suggest
example (a b : nat) : a / b ≤ a := nat.div_le_self a b


lemma exists_coprime
  (a b c n : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
  (hn : 0 < n)
  (h : a ^ n + b ^ n = c ^ n) :
  ∃ a' b' c', a' ≤ a ∧ b' ≤ b ∧ c' ≤ c ∧ flt_coprime a' b' c' n :=
begin
  by_cases h' : ¬nat.coprime a b ∨ ¬nat.coprime a c ∨ ¬nat.coprime b c,
  { 
    let d := nat.gcd a b,
    obtain ⟨ha : d ∣ a, hb : d ∣ b⟩ := nat.gcd_dvd a b,
    have hc : d ∣ c,
    { rw ←nat.pow_dvd_pow_iff hn,
      rw ←h,
      apply dvd_add; rw nat.pow_dvd_pow_iff hn; assumption },
    use [a / d, b / d, c / d],
    unfold flt_coprime,
    have hdpos : 0 < d := nat.gcd_pos_of_pos_left _ hpos.1,
    have hdnpos : 0 < d ^ n := nat.pow_pos hdpos n,
    have hsoln : (a / d) ^ n + (b / d) ^ n = (c / d) ^ n,
    { apply nat.eq_of_mul_eq_mul_right hdnpos,
      calc ((a / d) ^ n + (b / d) ^ n) * d ^ n
          = (a / d) ^ n * d ^ n + (b / d) ^ n * d ^ n : add_mul _ _ _
      ... = (a / d * d) ^ n  + (b / d) ^ n * d ^ n : by rw nat.mul_pow
      ... = (a / d * d) ^ n  + (b / d * d) ^ n : by rw nat.mul_pow (b / d)
      ... = a ^ n + b ^ n : by rw [nat.div_mul_cancel ha, nat.div_mul_cancel hb]
      ... = c ^ n : h
      ... = (c / d * d) ^ n : by rw [nat.div_mul_cancel hc]
      ... = (c / d) ^ n * d ^ n : by rw nat.mul_pow },
    have hsoln' : (a / d) ^ n = (c / d) ^ n - (b / d) ^ n,
    {
      rw ←hsoln,
      rw nat.add_sub_cancel,
    },
    have hsoln'' : (b / d) ^ n = (c / d) ^ n - (a / d) ^ n,
    {
      have := hsoln,
      rw add_comm at this,
      rw ←this,
      rw nat.add_sub_cancel,
    },
    refine ⟨_, _, _, _, _, _, _, _, _, _⟩,
    { apply nat.div_le_self },
    { apply nat.div_le_self },
    { apply nat.div_le_self },
    { refine nat.div_pos (nat.le_of_dvd hpos.1 ‹_›) hdpos },
    { refine nat.div_pos (nat.le_of_dvd hpos.2.1 ‹_›) hdpos },
    { refine nat.div_pos (nat.le_of_dvd hpos.2.2 ‹_›) hdpos },
    { exact hsoln },
    {exact nat.coprime_div_gcd_div_gcd hdpos,},
    { refine nat.coprime_of_dvd' _,
      intros,
      have : k ∣ (b / d),
      { rw ←nat.pow_dvd_pow_iff hn,
        rw hsoln'',
        apply nat.dvd_sub,
        { rw  ←hsoln,
          refine le_add_right _,
          refl },
        { rw nat.pow_dvd_pow_iff hn, assumption },
        { rw nat.pow_dvd_pow_iff hn, assumption } },
      have : k ∣ nat.gcd (a/d) (b/d),
      { exact nat.dvd_gcd a_1 this ,},
      convert this,
      symmetry,
      change nat.coprime _ _,
      exact coprime_div_gcd_div_gcd' hdpos },
    { refine nat.coprime_of_dvd' _,
      intros,
      have : k ∣ (a / d),
      { rw ←nat.pow_dvd_pow_iff hn,
        rw hsoln',
        apply nat.dvd_sub,
        { rw  ←hsoln,
          refine le_add_left _,
          refl },
        { rw nat.pow_dvd_pow_iff hn, assumption },
        { rw nat.pow_dvd_pow_iff hn, assumption } },
      have : k ∣ nat.gcd (a/d) (b/d),
      { exact nat.dvd_gcd this a_1,},
      convert this,
      symmetry,
      change nat.coprime _ _,
      exact coprime_div_gcd_div_gcd' hdpos },
  },
  { use [a, b, c], unfold flt_coprime, tauto },
end

example (a b : nat) (h : b ≤ a): a - (a - b) = b := nat.sub_sub_self h
example (a b c : nat) (h : b ≤ a) (h' : b ≤ c ): (a + c) - b = a + (c - b) := nat.add_sub_assoc h' a
--example (a b c : nat) (h : b ≤ a) (h' : a-b ≤ a+c ): (a + c) - (a - b) = c+ b := by suggest

lemma nat.pos_pow_iff {b : ℕ} (n : ℕ) (h : 0 < n) : 0 < b ↔ 0 < b ^ n :=
begin
  split,
  apply nat.pos_pow_of_pos,
  rw [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero],
  contrapose!,
  rintro rfl,
  apply nat.zero_pow h,
end
lemma x {m n : ℕ} (h : 0 < n - m) : m < n :=
begin
  exact nat.lt_of_sub_pos h,
end

lemma descent1 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (p.even ↔ ¬q.even) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  sorry,
end

lemma descent11 {a b c d : ℕ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  apply dvd_mul_of_dvd_left, apply dvd_mul_right,
  apply dvd_mul_of_dvd_left, apply dvd_mul_left,
  apply dvd_mul_left,
end

lemma descent12 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
 (h : d = a ∨ d = b ∨ d = c) : d ≤ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul _ hc,
    conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul_of_nonneg_left hb},
  { conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul _ hc,
    conv_lhs { rw ←one_mul d },
    apply nat.mul_le_mul_of_nonneg_right ha},
  { conv_lhs { rw ←one_mul d },
    apply nat.mul_le_mul_of_nonneg_right,
    change 0 < _,
    exact mul_pos ha hb },  
end

lemma descent2 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (p.even ↔ ¬q.even) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    (2 * p < a ^ 3 * b ^ 3 * c ^ 3) :=
begin
  have := descent1 a b c h,
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := this,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,
  have : 1 < (p ^ 2 + 3 * q ^ 2),
  { have : 0 < p ^ 2 := (nat.pos_pow_iff 2 (by norm_num)).mp hp,
    have : 0 < q ^ 2 := (nat.pos_pow_iff 2 (by norm_num)).mp hq,
    linarith },
  have : (2 * p) * 1 < 2 * p * (p ^ 2 + 3 * q ^ 2),
  { refine (mul_lt_mul_left _).mpr this,
    linarith },
  have := descent12 _ _ _ hcube,
  linarith,
  all_goals {
    rw ←nat.pos_pow_iff 3 (by norm_num),
    assumption,
  },

end

/-
lemma nat.pow_lt (a b n : ℕ) (h : 0 < n) : a < b ↔ a ^ n < b ^ n := begin
  split; intro h',
  { induction n,
    {norm_num at h},
    {
    rw pow_succ,
    rw pow_succ,

    apply nat.mul_lt_mul h',
    assumption},
  },

end
-/
lemma nat.pow_lt2 (a b : ℕ) : a < b ↔ a ^ 2 < b ^ 2 := begin
  rw [pow_two, pow_two],
  split,
  { intro h',
    apply nat.mul_lt_mul'; linarith,
  },
  { contrapose!,
    intro h',
    apply nat.mul_le_mul h' h',
  }

end
lemma nat.pow_lt3 (a b : ℕ) : a < b ↔ a ^ 3 < b ^ 3 := begin
  rw pow_succ a,
  rw pow_succ b,
  split,
  { intro h,
    have := (nat.pow_lt2 a b).mp h,
    apply nat.mul_lt_mul'; linarith,
  },
  {
    contrapose!,
    intro h',
    apply nat.mul_le_mul h',
    cases lt_or_eq_of_le h',
    { apply le_of_lt,
      rw ←nat.pow_lt2 b a,
      exact h },
    { subst h },
  }

end

lemma nat.even_pow' {m n : nat} (h : n ≠ 0) : nat.even (m^n) ↔ nat.even m :=
begin
  rw [nat.even_pow], tauto,
end

example (a b : nat) : (0 ∣ b) ↔ b = 0 := zero_dvd_iff

namespace nat
theorem xcoprime_of_dvd {m n : ℕ} (H : ∀ k, 1 < k → k ∣ m → ¬ k ∣ n) : coprime m n :=
begin
  cases eq_zero_or_pos (gcd m n) with g0 g1,
  { rw [eq_zero_of_gcd_eq_zero_left g0, eq_zero_of_gcd_eq_zero_right g0] at H,
    exfalso,
    exact (H 2 one_lt_two (dvd_zero _) (dvd_zero _))},
  { change 1 ≤ _ at g1,
    exact (eq.symm $ (lt_or_eq_of_le g1).resolve_left $ λg2,
    H _ g2 (gcd_dvd_left _ _) (gcd_dvd_right _ _))}
end
end nat

theorem xcoprime_of_dvd' {m n : ℕ} (H : ∀ k, k ∣ m → k ∣ n → k ∣ 1) : nat.coprime m n :=
begin
  apply nat.coprime_of_dvd,
  intros k kl km kn,
  apply not_le_of_gt kl,
  apply nat.le_of_dvd,
  exact zero_lt_one,
  exact H k km kn,
end

lemma nat.coprime_of_dvd'' {m n : ℕ} (H : ∀ k, nat.prime k → k ∣ m → k ∣ n → k ∣ 1) : nat.coprime m n :=
begin
  cases nat.eq_zero_or_pos (nat.gcd m n) with g0 g1,
  {
    rw [nat.eq_zero_of_gcd_eq_zero_left g0, nat.eq_zero_of_gcd_eq_zero_right g0] at H,
    have := (H 2 dec_trivial (dvd_zero _) (dvd_zero _)),
    rw nat.dvd_one at this,
    norm_num at this,    
  },
  apply nat.coprime_of_dvd',
  intros d hdleft hdright,
  rw nat.dvd_one,
  by_contra h,
  have : d ≠ 0,
  {
    rintro rfl,
    rw zero_dvd_iff at *,
    rw [hdleft, hdright] at g1,
    rw [nat.gcd_zero_right] at g1,
    exact irrefl 0 g1,
  },
  have : 2 ≤ d,
  {
    rcases d with (_|_|_),
    simp at this, contradiction,
    simp at h, contradiction,
    change 2 ≤ d + 2,
    rw [le_add_iff_nonneg_left],
    exact zero_le d,
  },
  obtain ⟨p, hp, hpdvd⟩ := nat.exists_prime_and_dvd this,
  have := H p hp (dvd_trans hpdvd hdleft) (dvd_trans hpdvd hdright),
  rw nat.dvd_one at this,
  have := nat.prime.ne_one hp,
  contradiction,
--  have := dvd_trans 
--  have : (0 ∣ d) := by refine zero_dvd_iff.mpr _,
--  obtain ⟨d, hd, hdleft, hdright⟩ := nat.prime.not_coprime_iff_dvd.mp sorry,

--  exact coprime_of_dvd $ λk kl km kn, not_le_of_gt kl $ le_of_dvd zero_lt_one (H k km kn)
end

lemma gcd_eq_of_dvd
  (p q g : ℕ)
  (hp' : g ∣ p) (hq' : g ∣ q)
  (h : ∀ x, x ∣ p → x ∣ q → x ∣ g)
  : nat.gcd p q = g := begin
--    library_search,
    apply nat.dvd_antisymm,
    { apply h,
      exact nat.gcd_dvd_left p q,
      exact nat.gcd_dvd_right p q},
    exact nat.dvd_gcd hp' hq',
  end
  --by library_search
example
  (p q g : ℕ)
  (hp : 0 < p) (hq : 0 < q)
 : ∀ x, x ∣ p → x ∣ q → x ∣ nat.gcd p q := λ x, nat.dvd_gcd
example (p n : nat) (hp : nat.prime p) : n ∣ p → (n = 1 ∨ n = p) := (nat.dvd_prime hp).mp
example (a b c : nat) : a = b + c → a - b = c := nat.sub_eq_of_eq_add
lemma dvd_of_dvd_add (a b c : nat) : a ∣ b + c → a ∣ b → a ∣ c := begin
  intros H G,
  have : b + c - b = c := by rw add_comm; exact nat.add_sub_cancel c b,
  rw ← this,
  apply nat.dvd_sub,
  exact nat.le.intro rfl,
  exact H,
  exact G,
end


lemma gcd1or3
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.coprime p q)
  (hparity : nat.even p ↔ ¬nat.even q) :
  nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  let g := nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2),
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2,
  {
    obtain ⟨k, hg, hk⟩ := H,
    rcases k with (_|_|_),
    { left, norm_num at hg, exact hg },
    { right, norm_num at hg, exact hg },
    {
      change k + 2 < 2 at hk,
      linarith,
    },
  },

  have basic : ∀ f, nat.prime f → f ∣ 2 * p → f ∣ (p ^ 2 + 3 * q ^ 2) → f = 3,
  {
    intros d hdprime hdleft hdright,
    have hne2 : d ≠ 2,
    {
      rintro rfl,
      change nat.even _ at hdright,
      simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps at hdright,
      assumption,
    },
    have : 2 < d := lt_of_le_of_ne (hdprime.two_le) hne2.symm,
    by_contra hne3,
    change d ≠ 3 at hne3,
    have : 3 < d := lt_of_le_of_ne (this) hne3.symm,
    obtain ⟨P, hP⟩ := hdleft,
    obtain ⟨Q, hQ⟩ := hdright,
    have : 2 ∣ P,
    {
      have := dvd_mul_right 2 p,
      rw hP at this,
      rw nat.prime.dvd_mul nat.prime_two at this,
      cases this,
      { rw nat.dvd_prime hdprime at this_1, cases this_1,
        {norm_num at this_1},
        exfalso,
        exact hne2 this_1.symm,
       },
      {assumption},
    },
    obtain ⟨H, hH⟩ := this,
    have : p = d * H,
    {
      rw ←nat.mul_right_inj two_pos,
      rw [hP, hH],
      ring,
    },
    have : 3 * q ^ 2 = d * (Q - d * H ^ 2),
    { calc 3 * q ^ 2
          = d * Q - p ^ 2 : (nat.sub_eq_of_eq_add hQ.symm).symm
      ... = d * Q - d ^ 2 * H ^ 2 : by rw [this, mul_pow]
      ... = d * Q - d * (d * H ^ 2) : by ring
      ... = d * (Q - d * H ^ 2) : by rw nat.mul_sub_left_distrib },
    have : d ∣ q,
    {
      have h000 : d ∣ 3 * q ^ 2,
      {
        rw this,
        apply dvd_mul_right,
      },
      rw nat.prime.dvd_mul hdprime at h000,
      cases h000,
      { linarith [nat.le_of_dvd (by norm_num) h000] },
      { exact nat.prime.dvd_of_dvd_pow hdprime h000 },
    },
    have : d ∣ p,
    { rw ‹p = _›, exact dvd_mul_right d H },
    have := nat.not_coprime_of_dvd_of_dvd (by linarith : 1 < d) ‹d ∣ p› ‹d ∣ q›,
    contradiction,
  },

  set k := g.factors.length,
  have hg : g = 3 ^ k,
  { apply eq_pow,
   { apply nat.gcd_pos_of_pos_left,
     apply nat.mul_pos two_pos hp },
    intros d hdprime hddvdg,
    apply basic _ hdprime,
    exact dvd_trans hddvdg (nat.gcd_dvd_left _ _),
    exact dvd_trans hddvdg (nat.gcd_dvd_right _ _),
  },
  refine ⟨k, hg, _⟩,
  by_contra H,
  push_neg at H,
  rw ←nat.pow_eq_mul_pow_sub _ H at hg,
  have hdvdp : 3 ∣ p,
  {
    suffices : 3 ∣ 2 * p,
    {
      rw nat.prime.dvd_mul nat.prime_three at this,
      cases this with G G,
      { norm_num at G },
      { exact G },
    },
    have : 3 ∣ g,
    {
      rw [hg, pow_two, mul_assoc],
      apply dvd_mul_right,
    },
    exact dvd_trans this (nat.gcd_dvd_left _ _),
  }, 
  have hdvdq : 3 ∣ q,
  {
    have : 3 ^ 2 ∣ p ^ 2,
    { rwa nat.pow_dvd_pow_iff two_pos },
    suffices : 3 ∣ q ^ 2,
    {
      apply nat.prime.dvd_of_dvd_pow nat.prime_three,
      exact this,    
    },
    suffices : 3 ^ 2 ∣ 3 * q ^ 2,
    {
      rwa [pow_two, nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)] at this,
    },
    suffices : 3 ^ 2 ∣ p ^ 2 + 3 * q ^ 2,
    {
      apply dvd_of_dvd_add _ _ _ this,
      assumption,
    },
    refine dvd_trans _ (nat.gcd_dvd_right _ _),
    exact 2 * p,
    change 3 ^ 2 ∣ g,
    rw hg,
    apply dvd_mul_right,
  },

  apply nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) hdvdp hdvdq hcoprime,
/-
  by_cases g = 3,
  { right, assumption },
  left,
  change nat.coprime _ _,
  apply nat.coprime_of_dvd'',
  intros d hdprime hdleft hdright,
  have hddvdg : d ∣ g := nat.dvd_gcd hdleft hdright,
  rw nat.dvd_one,
  have : d ≠ 2,
  {
    rintro rfl,
    change nat.even _ at hdright,
    simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps at hdright,
    assumption,
  },
  have : d ≠ 3,
  {
    rintro rfl,
    sorry,

  },
  have : ∀ m, nat.prime m → m ∣ g → m = 3,
  {
    intros m hmprime hmdvd,
    exact basic m hmprime
      (dvd_trans hmdvd (nat.gcd_dvd_left _ _))
      (dvd_trans hmdvd (nat.gcd_dvd_right _ _)),
  },
  apply eq_pow,
--  have : ∀ f g, f ∣ 2 * p → f ∣ p ^ 2 + 3 * q ^ 2 → 3 ∣ 
-/
--  obtain ⟨d, hd, hdleft, hdright⟩ := nat.prime.not_coprime_iff_dvd.mp h,


--  suffices h : g ≠ 1 → g ≠ 3 → prime g → false,
--  sorry,
/-
  by_cases g = 1,
  { left, assumption },
  right,
  apply gcd_eq_of_dvd,
  have : 3 ∣ g,
  {
    sorry,
  },
  obtain ⟨d, hd, hdleft, hdright⟩ := nat.prime.not_coprime_iff_dvd.mp h,
  have : d ∣ g, exact nat.dvd_gcd hdleft hdright,
  have : d ≠ 2,
  {
    rintro rfl,
    change nat.even _ at hdright,
    simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps at hdright,
    assumption,
  },
-/
/-
  have : ¬nat.even (p ^ 2 + 3 * q ^ 2),
  { simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps },
  have : ¬(2 ∣ (p ^ 2 + 3 * q ^ 2)) := sorry,

  },
  have : ∃ p, nat.prime p ∧ p ∣ g,
  refine nat.exists_prime_and_dvd  _,
  have : ∀ f, f ∣ (2 * p) ∧ f ∣ (p ^ 2 + 3 * q ^ 2) → f ≠ 2,
  sorry,
  have : ¬(2 ∣ g),
  {
    dsimp [g],
  },
-/
end

lemma factors
  (a b f : ℕ)
  (hcoprime : nat.gcd a b = 1)
  (hodd : ¬nat.even f)
  (hfactor : f ∣ (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, f = c ^ 2 + 3 * d ^ 2 := sorry

example (x y z : ℤ) : (x + y + z) ^ 3 =
  x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (x + z) * (y + z)
:= by ring

lemma obscure
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.gcd p q = 1)
  (hparity : nat.even p ↔ ¬nat.even q)
  (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
  ∃ a b,
    3 * b < a ∧
    p = a ^ 3 - 9 * a * b ^ 2 ∧
    q = 3 * a ^ 2 * b - 3 * b ^ 3 ∧
    nat.gcd a b = 1 ∧
    (nat.even a ↔ ¬nat.even b) :=
begin
  -- (1)
  obtain ⟨u, hu⟩ := hcube,

  -- (2)
  have hodd : ¬nat.even u,
  { rw ←nat.even_pow' (dec_trivial : ¬ 3 = 0),
    rw ←hu,
    simp [(dec_trivial : ¬ 3 = 0)] with parity_simps,
    tauto },
  
  -- (3)
  have hfactor : u ∣ p ^ 2 + 3 * q ^ 2,
  { rw hu,
    refine dvd_pow (dvd_refl u) dec_trivial },
  obtain ⟨a, b, hab⟩ := factors p q u hcoprime hodd hfactor,

  have : (p ^ 2 + 3 * q ^ 2 : ℤ) = (a ^ 3 - 9 * a * b ^ 2) ^ 2 + 3 * (3 * a ^ 2 * b - 3 * b ^ 3) ^ 2,
  {
    zify at hu,
    zify at hab,
    rw [hu, hab],
--    have A : 9 * a * b ^ 2 ≤ a ^ 3 := sorry, -- (3b)^2 ≤ a ^ 2
--    have B : 3 * b ^ 3 ≤ 3 * a ^ 2 * b := sorry, -- b ^ 2 ≤ a ^ 2
--    zify [A, B],
    ring,
  },

  use [a, b],
  refine ⟨_, _, _, _, _⟩,
  { sorry },
  { sorry },
  { sorry },
  { sorry },


  -- (4)
  have : (a ^ 2 + 3 * b ^ 2) ^ 3 = (a ^ 2 + 3 * b ^ 2) * ((a ^ 2 - 3 * b ^ 2) ^ 2 + 3 * (2 * a * b) ^ 2),
  {
    have : 3 * b ^ 2 ≤ a ^ 2, 
    {sorry},
    zify [this],
    ring,
  },
/-
(4) Now, (a2 + 3b2)3 = (a2 + 3b2)[(a2 - 3b2)2 + 3(2ab)2]

    since (a2 + 3b2)2 = a4 + 6a2b2 + 9b4 =
    = a4 + 12a2b2 - 6a2b2 + 9b4 =
    (a2 - 3b2)2 + 3(2ab)2


(5) And, (a2 + 3b2)[(a2 - 3b2)2 + 3(2ab)2] =
[ a(a2 - 3b2) - 3b(2ab)]2 + 3[a(2ab)+b(a2-3b2)]2 [See here for the proof.]

(6) And: [ a(a2 - 3b2) - 3b(2ab)]2 + 3[a(2ab)+b(a2-3b2)]2 =
= [a3 - 3ab2 - 6ab2]2 + 3(2a2b + a2b - 3b3)2 =
=[a3 -9ab2]2 + 3(3a2b - 3b3)2.


(7) Which combined with step (1) gives us:
p2 + 3q2 = [a3 -9ab2]2 + 3(3a2b - 3b3)2

(8) Which means that we could define a,b such that:
p = a3 -9ab2.
q = 3a2b - 3b3.
gcd(a,b)=1 [since otherwise, any common factor would divide p and q].

(9) We also know that a,b have opposite parities since:

(a) If a,b are both odd, then, p is even since p = odd - odd and q is even since q = odd - odd which is impossible since p,q have opposite parities.

(b) If a,b are both even, then p is even since p = even - even and q is even since q = even - even which is impossible.
-/
  sorry,
end

example {p n k : ℕ}
  (h : k ∣ p)
  (hp : nat.prime p)
  (hk : nat.prime k) : k = p := (nat.prime_dvd_prime_iff_eq hk hp).mp h
lemma dvd_mul_cancel_prime {p n k : ℕ}
  (h : k ∣ p * n)
  (hne : k ≠ p)
  (hp : nat.prime p)
  (hk : nat.prime k) : k ∣ n :=
begin
  rw hk.dvd_mul at h,
  cases h,
  { exfalso,
    rw nat.prime_dvd_prime_iff_eq hk hp at h,
    contradiction },
  { assumption },
end


lemma descent_gcd1 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : p.even ↔ ¬q.even)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (haaa : 2 * p < a ^ 3 * b ^ 3 * c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 1) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧
      0 < b' ∧
        0 < c' ∧ a' * b' * c' < a * b * c ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 2.
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  {
    rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube,
  },
  have hposleft : 0 < 2 * p,
  {
    apply nat.mul_pos two_pos hp,
  },
  have hposright : 0 < p ^ 2 + 3 * q ^ 2,
  {
    apply nat.add_pos_left,
    exact nat.pos_pow_of_pos 2 hp,
  },
  have hcubeleft : ∃ s, 2 * p = s ^ 3 := nat.eq_pow_of_mul_eq_pow hposleft hposright hgcd hr,
  have hcuberight : ∃ t, p ^ 2 + 3 * q ^ 2 = t ^ 3,
  {
    rw mul_comm at hr,
    rw nat.gcd_comm at hgcd,
    exact nat.eq_pow_of_mul_eq_pow hposright hposleft hgcd hr,
  },
  have : ∃ u v,
    3 * v < u ∧
    p = u ^ 3 - 9 * u * v ^ 2 ∧
    q = 3 * u ^ 2 * v - 3 * v ^ 3 ∧
    nat.gcd u v = 1 ∧
    (nat.even u ↔ ¬nat.even v) := obscure p q hp hq hcoprime hodd hcuberight,
  obtain ⟨u, v, huv, hp, hq, huvcoprime, huvodd⟩ := this,
  have upos : 0 < u := lt_of_le_of_lt (nat.zero_le _) huv,
  have,
  calc 9 * v ^ 2
      = 3 ^ 2 * v ^ 2 : by norm_num
  ... = (3 * v) ^ 2 : by rw nat.mul_pow,
  have,
  calc u ^ 2 - 9 * v ^ 2
      = u ^ 2 - (3 * v) ^ 2 : by rw this --congr_arg (has_sub.sub (u ^ 2)) (mul_pow 3 v)
  ... = (u + 3 * v) * (u - 3 * v) : nat.sq_sub_sq _ _
  ... = (u - 3 * v) * (u + 3 * v) : mul_comm _ _,
  have hpfactor,
  calc p
      = (u ^ 3 - 9 * u * v ^ 2) : by rw hp
  ... = (u ^ 3 - u * 9 * v ^ 2) : by ring
  ... = (u * u ^ 2 - u * 9 * v ^ 2) : by ring
  ... = (u * u ^ 2 - u * (9 * v ^ 2)) : by ring
  ... = (u * (u ^ 2 - 9 * v ^ 2)) : by rw ←nat.mul_sub_left_distrib
  ... = u * ((u - 3 * v) * (u + 3 * v)) : by rw this
  ... = u * (u - 3 * v) * (u + 3 * v) : by rw mul_assoc u _ _,
  have,
  calc 2 * p
      = 2 * (u * (u - 3 * v) * (u + 3 * v)) : by rw hpfactor
  ... = (2 * u) * (u - 3 * v) * (u + 3 * v) : by ring,
  have : ¬ nat.even (u - 3 * v),
  { rw [nat.even_sub (le_of_lt ‹ 3 * v < u›), nat.even_mul],
    norm_num,
    tauto,
  },
  have : ¬ nat.even (u + 3 * v),
  {
    rw [nat.even_add, nat.even_mul],
    norm_num,
    tauto,
  },
  have husub_le_uadd : (u - 3 * v) ≤ (u + 3 * v),
  {
    transitivity u,
    exact nat.sub_le u (3 * v),
    exact nat.le.intro rfl,
  },
  have notdvd_2_2 : ¬(2 ∣ u - 3 * v),
  { intro hd2,
    exact ‹¬ nat.even (u - 3 * v)› hd2 },
  have huadd_add_usub : 2 * u = (u + 3 * v) + (u - 3 * v),
  { zify [(le_of_lt huv)],
    ring },
  have huadd_sub_usub : 2 * 3 * v = (u + 3 * v) - (u - 3 * v),
  { zify [(le_of_lt huv), husub_le_uadd],
    ring },
  have hccc : 2 * (u - 3 * v) ≤ 2 * u := nat.mul_le_mul (le_refl _) (nat.sub_le _ _),
  have hbbb : 2 * 3 * v = 2 * u - 2 * (u - 3 * v),
  { zify [(le_of_lt huv), husub_le_uadd, hccc],
    ring },
  have not_3_dvd_2 : ¬(3 ∣ (u - 3 * v)),
  { intro hd2,
    have : 3 ∣ p,
    { rw hpfactor,
      apply dvd_mul_of_dvd_left _,
      apply dvd_mul_of_dvd_right hd2,
    },
    have : 3 ∣ 2 * p := dvd_mul_of_dvd_right this 2,
    have : 3 ∣ p ^ 2 + 3 * q ^ 2,
    {
      apply nat.dvd_add,
      { rw nat.pow_two, apply dvd_mul_of_dvd_right, assumption, },
      apply dvd_mul_right,
    },
    have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
    rw hgcd at this,
    have := nat.eq_one_of_dvd_one this,
    norm_num at this },
  have notdvd_3_3 : ¬(3 ∣ (u + 3 * v)),
  { intro hd3,
    have : 3 ∣ p,
    { rw hpfactor,
      apply dvd_mul_of_dvd_right hd3,
    },
    have : 3 ∣ 2 * p := dvd_mul_of_dvd_right this 2,
    have : 3 ∣ p ^ 2 + 3 * q ^ 2,
    {
      apply nat.dvd_add,
      { rw nat.pow_two, apply dvd_mul_of_dvd_right, assumption, },
      apply dvd_mul_right,
    },
    have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
    rw hgcd at this,
    have := nat.eq_one_of_dvd_one this,
    norm_num at this },
  have hcoprime12 : nat.coprime (2 * u) (u - 3 * v),
  {
    apply nat.coprime_of_dvd'',
    intros k hkprime hkdvdleft hkdvdright,
    have : k ≠ 2,
    { rintro rfl, contradiction },
    have : k ≠ 3,
    { rintro rfl, contradiction },
    have : k ∣ u := dvd_mul_cancel_prime hkdvdleft ‹_› nat.prime_two hkprime,
    have : k ∣ v,
    {
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
      rw [←mul_assoc, hbbb],
      apply nat.dvd_sub hccc hkdvdleft,
      apply dvd_mul_of_dvd_right hkdvdright },    
    have : k ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
    rwa huvcoprime at this,
  },
  have hcoprime13 : nat.coprime (2 * u) (u + 3 * v),
  {
    apply nat.coprime_of_dvd'',
    intros k hkprime hkdvdleft hkdvdright,
    have : k ≠ 2,
    { rintro rfl, contradiction },
    have : k ≠ 3,
    { rintro rfl, contradiction },
    have : k ∣ u := dvd_mul_cancel_prime hkdvdleft ‹_› nat.prime_two hkprime,
    have : k ∣ v,
    {
      have : 2 * u ≤ 2 * (u + 3 * v), linarith,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
      have : 2 * (u + 3 * v) - 2 * u = 2 * (3 * v),
      { zify [this],
        ring },
      rw ←this,
      apply nat.dvd_sub ‹_› _ hkdvdleft,
      apply dvd_mul_of_dvd_right hkdvdright },    
    have : k ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
    rwa huvcoprime at this,
  },
  have hcoprime23 : nat.coprime (u - 3 * v) (u + 3 * v),
  {
    apply nat.coprime_of_dvd'',
    intros k hkprime hkdvdleft hkdvdright,
    have : k ≠ 2,
    { rintro rfl, contradiction },
    have : k ≠ 3,
    { rintro rfl, contradiction },
    have : k ∣ u,
    {
      refine dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
      rw huadd_add_usub,
      apply nat.dvd_add hkdvdright hkdvdleft },
    have : k ∣ v,
    {
      have : k ∣ 2 * 3 * v,
      {
        rw huadd_sub_usub,
        apply nat.dvd_sub husub_le_uadd ‹_› ‹_›,
      },
      rw mul_assoc at this,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      exact dvd_mul_cancel_prime this ‹_› nat.prime_two hkprime,
    },
    have : k ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
    rwa huvcoprime at this,
  },
/-
  have hnotdvd : ¬∃ d > 1, d ∣ (2 * u) ∧ d ∣ (u - 3 * v) ∧ d ∣ (u + 3 * v),
  { suffices : ¬∃ d > 1, nat.prime d ∧ d ∣ (2 * u) ∧ d ∣ (u - 3 * v) ∧ d ∣ (u + 3 * v),
    {
      contrapose! this,
      obtain ⟨d', hd'pos, hd'1, hd'2, hd'3⟩ := this,
      refine ⟨nat.min_fac d', _, _, _, _, _⟩,
      { apply lt_of_le_of_ne,
        { rw nat.succ_le_iff, apply nat.min_fac_pos },
        { symmetry, rw [ne.def, nat.min_fac_eq_one_iff], apply ne_of_gt hd'pos },
      },
      {apply nat.min_fac_prime, apply ne_of_gt hd'pos },
      all_goals { transitivity d', apply nat.min_fac_dvd, assumption },
    },
    have notdvd_all_2 : ¬(2 ∣ (2 * u) ∧ 2 ∣ (u - 3 * v) ∧ 2 ∣ (u + 3 * v)),
    { rintro ⟨hd1, hd2, hd3⟩,
      exact notdvd_2_2 hd2 },
    have notdvd_all_3 : ¬(3 ∣ (2 * u) ∧ 3 ∣ (u - 3 * v) ∧ 3 ∣ (u + 3 * v)),
    { rintro ⟨hd1, hd2, hd3⟩,
      exact notdvd_3_3 hd3 },

    rintro ⟨d, hdpos, hdprime, hd1, hd2, hd3⟩,
    have : d ≠ 2,
    { rintro rfl, contradiction },
    have : d ≠ 3,
    { rintro rfl, contradiction },

    have : d ∣ u,
    { rw nat.prime.dvd_mul hdprime at hd1,
      cases hd1,
      {
        exfalso,
        apply nat.lt_le_antisymm _ (nat.add_one_le_iff.mpr hdpos),
        have := nat.le_of_dvd two_pos hd1,
        exact (lt_of_le_of_ne ‹_› ‹_›),
      },
      { assumption } },
    have : d ∣ v,
    {
      have : d ∣ 2 * 3 * v,
      {
        rw huadd_sub_usub,
        apply nat.dvd_sub husub_le_uadd ‹_› ‹_›,
      },
      have := (nat.prime.dvd_mul hdprime).mp this,
      cases this,
      { rw nat.prime.dvd_mul hdprime at this_1,
        cases this_1;
        {have := (nat.prime_dvd_prime_iff_eq hdprime (by norm_num : nat.prime _)).mp this_1,
        contradiction} },
      {assumption},
    },
    have : d ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
    rw huvcoprime at this,
    exact nat.prime.not_dvd_one hdprime this,
  },
-/
  have : ∃ A B C, A ^ 3 = u - 3 * v ∧ B ^ 3 = u + 3 * v ∧ C ^ 3 = 2 * u,
  { obtain ⟨A, HA⟩ : ∃ A, u - 3 * v = A ^ 3,
    { obtain ⟨s, hs⟩ := hcubeleft,
      rw [‹2 * p = _›, mul_comm (2 * u), mul_assoc] at hs,
      apply nat.eq_pow_of_mul_eq_pow (nat.sub_pos_of_lt huv) _ _ hs,
      { apply nat.mul_pos,
        apply nat.mul_pos two_pos upos,
        apply nat.add_pos_left upos },
      { rw nat.coprime_mul_iff_right,
        exact ⟨nat.coprime.symm ‹_›, ‹_›⟩ },
    },
    obtain ⟨B, HB⟩ : ∃ B, u + 3 * v = B ^ 3,
    { obtain ⟨s, hs⟩ := hcubeleft,
      rw [‹2 * p = _›, mul_comm _ (u + 3 * v)] at hs,
      apply nat.eq_pow_of_mul_eq_pow (nat.add_pos_left upos _) _ _ hs,
      { apply nat.mul_pos,
        apply nat.mul_pos two_pos upos,
        apply nat.sub_pos_of_lt huv },
      { rw nat.coprime_mul_iff_right,
        exact ⟨nat.coprime.symm ‹_›, nat.coprime.symm ‹_›⟩ },
    },
    obtain ⟨C, HC⟩ : ∃ C, 2 * u = C ^ 3,
    { obtain ⟨s, hs⟩ := hcubeleft,
      rw [‹2 * p = _›, mul_assoc] at hs,
      have doubleupos : 0 < 2 * u := nat.mul_pos two_pos upos,
      apply nat.eq_pow_of_mul_eq_pow doubleupos _ _ hs,
      { apply nat.mul_pos,
        apply nat.sub_pos_of_lt huv,
        apply nat.add_pos_left upos },
      { rw nat.coprime_mul_iff_right,
        exact ⟨‹_›, ‹_›⟩ },
    },
    exact ⟨A, B, C, HA.symm, HB.symm, HC.symm⟩ },
  obtain ⟨A, B, C, HA, HB, HC⟩ := this, 
  use [A, B, C],
  refine ⟨_, _, _, _, _⟩,
  { rw [nat.pos_pow_iff 3 (by norm_num), HA],
    apply nat.sub_pos_of_lt,
    apply huv },
  { rw [nat.pos_pow_iff 3 (by norm_num), HB],
    rw nat.pos_iff_ne_zero,
    intro H,
    obtain ⟨rfl, HR⟩ := nat.eq_zero_of_add_eq_zero H,
    linarith },
  { rw [nat.pos_pow_iff 3 (by norm_num), HC],
    norm_num,
    rw nat.pos_iff_ne_zero,
    rintro rfl,
    rw nat.gcd_zero_left at huvcoprime,
    subst huvcoprime,
    norm_num at huv,
    },
  { rw nat.pow_lt3,
    iterate 4 {rw mul_pow},
    rw [mul_comm, ←mul_assoc (C^3)],
    rw [HA, HB, HC],
    rw ←‹2 * p = _›,
    assumption },
  { rw [HA, HB, HC],
    zify [le_of_lt huv],
    ring },
end

lemma descent_gcd3 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : p.even ↔ ¬q.even)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (haaa : 2 * p < a ^ 3 * b ^ 3 * c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧
      0 < b' ∧
        0 < c' ∧ a' * b' * c' < a * b * c ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  sorry,
end

lemma descent
  (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ a' b' c', 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ (a' * b' * c' < a * b * c) ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,
  -- 4.
  cases gcd1or3 p q hp hq hcoprime hodd with hgcd hgcd,
  -- 5.
  { apply descent_gcd1 a b c p q hp hq hcoprime hodd hcube haaa h hgcd },
  { apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube haaa h hgcd },
end

-- lemma no_solutions' : ∀ x, ¬(∃ y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^4 = y^4 + z^2) :=
lemma flt_three
  (a b c : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  revert a b c,
  suffices h : ∀ k a b c : ℕ, k = a * b * c → (0 < a ∧ 0 < b ∧ 0 < c) → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { intros a b c hpos,
    exact h (a * b * c) a b c rfl hpos },
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
  
/-
  revert a b c,
  suffices h : ∀ k a b c : ℕ, k = a ^ 3 * b ^ 3 * c ^ 3 → (0 < a ∧ 0 < b ∧ 0 < c) → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { intros a b c hpos,
    exact h (a ^ 3 * b ^ 3 * c ^ 3) a b c rfl hpos },
  intro k,
  refine nat.strong_induction_on k _,
  intros k' IH x y z hk hpos H,
-/
/-
  let k' := a ^ 3 * b ^ 3 * c ^ 3,
-/
/-
  rw ne.def,
  revert b c,
  refine nat.strong_induction_on a _,
  intros x IH y z hpos H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ := exists_coprime x y z 3 hpos (by norm_num) H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH x' _ _ _ ⟨hx'pos, hy'pos, hz'pos⟩ hsolution,
--  linarith,
  sorry,
-/
end
