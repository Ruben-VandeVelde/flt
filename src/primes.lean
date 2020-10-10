import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic

lemma nat.mem_factors' {n p} (hn : 0 < n) : p ∈ nat.factors n ↔ nat.prime p ∧ p ∣ n :=
⟨λ h, ⟨nat.mem_factors h, (nat.mem_factors_iff_dvd hn (nat.mem_factors h)).mp h⟩,
 λ ⟨hprime, hdvd⟩, (nat.mem_factors_iff_dvd hn hprime).mpr hdvd⟩

lemma eq_pow
  {n p : ℕ}
  (hpos : 0 < n)
  (h : ∀ {d}, nat.prime d → d ∣ n → d = p) :
  n = p ^ n.factors.length :=
begin
  set k := n.factors.length,
  rw [←nat.prod_factors hpos],
  transitivity,
  {
    suffices : n.factors = list.repeat p k, { rw this },
    apply list.eq_repeat_of_mem,
    intros d hd,
    rw nat.mem_factors' hpos at hd,
    apply h hd.left hd.right,
  },
  { exact list.prod_repeat p k },
end

lemma l0 {n : ℕ} (h : 2 < 2 ^ n) : 2 ≤ n :=
begin
  rcases n with (_|_|_),
  { exfalso, norm_num at h },
  { exfalso, exact lt_irrefl _ h, },
  { rw le_add_iff_nonneg_left (2 : nat),
    exact zero_le _ }
end

lemma exists_prime_and_dvd'
  {n : ℕ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ (p = 4 ∨ (nat.prime p ∧ p % 2 = 1)) :=
begin
  by_cases ∃ p, p ∣ n ∧ nat.prime p ∧ p % 2 = 1,
  { obtain ⟨p, hdvd, hp, hodd⟩ := h,
    have pnetwo : p ≠ 2,
    { intro ptwo,
      subst ptwo,
      norm_num at hodd },
    exact ⟨p, hdvd, or.inr ⟨hp, hodd⟩⟩ },
  { use 4,
    split,
    { push_neg at h,
      have h0 : 0 < n := by linarith,
      set k := n.factors.length,
      use 2 ^ (k - 2),

      have h2 : n = 2 ^ k,
      { apply eq_pow h0,
        intros d hdprime hddvd,
        cases nat.prime.eq_two_or_odd hdprime with H H,
        { assumption },
        { have := h d hddvd hdprime, contradiction } },

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : h2
      ... = 2 ^ 2 * 2 ^ (k - 2) : (pow_mul_pow_sub _ h3).symm
      ... = 4 * 2 ^ (k - 2) : by norm_num,
      },
    { left, refl } },
end

theorem nat.eq_pow_of_mul_eq_pow {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
  (hab : nat.coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, a = d ^ k := sorry

/-
universe u

open nat
protected def strong_rec_on {p : nat → Sort u} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
suffices ∀ n m, m < n → p m, from this (succ n) n (lt_succ_self _),
begin
  intros n, induction n with n ih,
    {intros m h₁, exact absurd h₁ (not_lt_zero _)},
    {intros m h₁,
      apply or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁)),
        {intros, apply ih, assumption},
        {intros, subst m, apply h _ ih}}
end

lemma pnat.strong_induction_on {p : pnat → Prop} (n : pnat) (h : ∀ k, (∀ m, m < k → p m) → p k) : p n :=
begin
  induction n',

  suffices : ∀ n m, m < n → p m, from this (n + 1) n (nat.lt_succ_self _),
  intros n, induction (n : ℕ) with n ih,
  intros m h₁,
  apply h,
  intros k hk,
  {
    apply or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁)),
      {intros, apply ih, assumption},
      {intros, subst m, apply h _ ih}}
end
-/
lemma pnat.strong_induction_on {p : pnat → Prop} (n : pnat) (h : ∀ k, (∀ m, m < k → p m) → p k) : p n :=
begin
  let p' : nat → Prop := λ n, if h : 0 < n then p ⟨n, h⟩ else true,
  have : ∀ n', p' n',
  {
    intro n',
    refine nat.strong_induction_on n' _,
    intro k,
    dsimp [p'],
    split_ifs,
    {
      intros a,
      apply h,
      intros m hm,
      have := a m.1 hm,
      split_ifs at this,
      {
        convert this,
        simp only [subtype.coe_eta, subtype.val_eq_coe],
      },
      {exfalso,
      exact h_2 m.2}},
    {intros, trivial}    
  },
  have a := this n.1,
  dsimp [p'] at a,
  split_ifs at a,
  { convert a, simp only [subtype.coe_eta], },
  { exfalso, exact h_1 n.pos },
end.

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

lemma nat.even_pow' {m n : nat} (h : n ≠ 0) : even (m^n) ↔ even m :=
begin
  rw [nat.even_pow], tauto,
end

namespace nat

theorem coprime_of_dvd_prime {m n : ℕ} (H : ∀ k, prime k → k ∣ m → ¬ k ∣ n) : coprime m n :=
begin
  cases eq_zero_or_pos (gcd m n) with g0 g1,
  { rw [eq_zero_of_gcd_eq_zero_left g0, eq_zero_of_gcd_eq_zero_right g0] at H,
    exfalso,
    exact H 2 prime_two (dvd_zero _) (dvd_zero _) },
  apply eq.symm,
  change 1 ≤ _ at g1,
  apply (lt_or_eq_of_le g1).resolve_left,
  intro g2,
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2,
  apply H p hp; apply dvd_trans hpdvd,
  { exact gcd_dvd_left _ _ },
  { exact gcd_dvd_right _ _ }
end

lemma coprime_of_dvd'' {m n : ℕ} (H : ∀ k, prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
coprime_of_dvd_prime $ λk kp km kn, not_le_of_gt kp.one_lt $ le_of_dvd zero_lt_one $ H k kp km kn

end nat

lemma gcd_eq_of_dvd
  (p q g : ℕ)
  (hp' : g ∣ p) (hq' : g ∣ q)
  (h : ∀ x, x ∣ p → x ∣ q → x ∣ g)
  : nat.gcd p q = g :=
begin
  apply nat.dvd_antisymm,
  { apply h,
    exact nat.gcd_dvd_left p q,
    exact nat.gcd_dvd_right p q},
  exact nat.dvd_gcd hp' hq',
end

lemma dvd_of_dvd_add (a b c : nat) : a ∣ b + c → a ∣ b → a ∣ c :=
begin
  intros H G,
  rw [←nat.add_sub_cancel c b, add_comm],
  exact nat.dvd_sub (nat.le_add_right b c) H G,
end

lemma dvd_of_dvd_add' (a b c : nat) : a ∣ b + c → a ∣ c → a ∣ b :=
begin
  intros H G,
  rw [←nat.add_sub_cancel b c],
  exact nat.dvd_sub (nat.le_add_left c b) H G,
end
lemma nat.pos_pow_iff {b : ℕ} (n : ℕ) (h : 0 < n) : 0 < b ↔ 0 < b ^ n :=
begin
  split,
  { intro h,
    apply pow_pos h },
  { rw [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero],
    contrapose!,
    rintro rfl,
    apply zero_pow h }
end

theorem pos_pow_of_pos {b : ℕ} (n : ℕ) (h : 0 < b) : 0 < b^n := pow_pos h n

/-
theorem not_coprime_of_dvd_gcd {m n d : ℕ} (dgt1 : 1 < d) (H : d ∣ nat.gcd m n) :
  ¬ nat.coprime m n :=
λ (co : nat.gcd m n = 1),
not_lt_of_ge (nat.le_of_dvd zero_lt_one $ by rw ←co; exact H) dgt1
-/

theorem int.nat_abs_ne_zero {a : ℤ} : a.nat_abs ≠ 0 ↔ a ≠ 0 := not_congr int.nat_abs_eq_zero

lemma nat.split_factors
  {a b : ℕ}
  (a_pos : 0 < a)
  (one_lt_b : 1 < b) :
  ∃ k l : ℕ, a = b ^ k * l ∧ ¬(b ∣ l) :=
begin
  by_cases hdvd : b ∣ a,
  { revert a_pos hdvd,
    apply nat.strong_induction_on a,
    intros a' IH a'_pos hdvd,
    obtain ⟨c, hc⟩ := hdvd,
    have c_pos : 0 < c,
    { rw nat.pos_iff_ne_zero,
      rintro rfl,
      rw mul_zero at hc,
      subst hc,
      exact lt_irrefl _ a'_pos },
    have hsmaller : c < a',
    { rw [hc, lt_mul_iff_one_lt_left c_pos],
      exact one_lt_b },
    by_cases H : b ∣ c,
    { obtain ⟨k', l', heqb, hnotdvd⟩ := IH c hsmaller c_pos H,
      refine ⟨k' + 1, l', _, hnotdvd⟩,
      rw [hc, heqb, pow_succ, mul_assoc] },
    { refine ⟨1, c, _, H⟩,
      rwa pow_one } },
  { refine ⟨0, a, _, hdvd⟩,
    rwa [pow_zero, one_mul] }
end

lemma nat.dvd_sub_of_mod_eq {a b c : ℕ} (h : a % b = c) : b ∣ a - c :=
begin
  have : c ≤ a,
  { rw ←h, exact nat.mod_le a b },
  rw [←int.coe_nat_dvd, int.coe_nat_sub this],
  apply int.dvd_sub_of_mod_eq,
  rw ←int.coe_nat_mod, rw h,
end

theorem nat.one_le_of_not_even {n : ℕ} (h : ¬even n) : 1 ≤ n :=
begin
  apply nat.succ_le_of_lt,
  rw nat.pos_iff_ne_zero,
  rintro rfl,
  exact h nat.even_zero
end

lemma two_mul_add_one_iff_not_odd (n : ℕ) : ¬even n ↔ ∃ m, n = 2 * m + 1 :=
begin
  rw ←nat.odd_iff_not_even,
  refl,
end

lemma mod_four_of_odd {n : nat} (hodd: ¬even n) : ∃ m, n = 4 * m - 1 ∨ n = 4 * m + 1 :=
begin
  rw two_mul_add_one_iff_not_odd at hodd,
  obtain ⟨m, hm⟩ := hodd,
  by_cases even m,
  { obtain ⟨k, hk⟩ := h,
    use k,
    right,
    rw [hm, hk, ←mul_assoc],
    norm_num },
  { rw two_mul_add_one_iff_not_odd at h,
    obtain ⟨k, hk⟩ := h,
    use k + 1,
    left,
    rw [hm, hk],
    ring }
end

lemma mod_four_of_odd' {n : nat} (hodd: ¬even n) : ∃ m, n = 4 * m + 3 ∨ n = 4 * m + 1 :=
begin
  rw two_mul_add_one_iff_not_odd at hodd,
  obtain ⟨m, hm⟩ := hodd,
  by_cases even m,
  { obtain ⟨k, hk⟩ := h,
    use k,
    right,
    rw [hm, hk, ←mul_assoc],
    norm_num },
  { rw two_mul_add_one_iff_not_odd at h,
    obtain ⟨k, hk⟩ := h,
    use k,
    left,
    rw [hm, hk],
    ring, }
end

@[simp] theorem nat.gcd_eq_zero_iff {a b : ℕ} : nat.gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
iff.intro
  (assume h, let ⟨ca, ha⟩ := nat.gcd_dvd_left a b, ⟨cb, hb⟩ := nat.gcd_dvd_right a b in
    by rw [h, nat.zero_mul] at ha hb; exact ⟨ha, hb⟩)
  (assume ⟨ha, hb⟩, by rw [ha, hb, nat.gcd_zero_left])

theorem nat.pow_two_sub_pow_two (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by { simp only [pow_two], exact nat.mul_self_sub_mul_self_eq a b }

lemma div_pow (n m k : nat) (h : m ∣ n) (hpos : 0 < m) : (n / m) ^ k = (n ^ k) / (m ^ k) :=
begin
  obtain ⟨d, hd⟩ := h,
  rw hd,
  rw mul_comm,
  rw mul_pow,
  rw nat.mul_div_cancel _ hpos,
  rw nat.mul_div_cancel _ (pow_pos hpos k),
end.

theorem nat.coprime.pow' {k l : ℕ} (m n : ℕ)
 (hm : m ≠ 0)
 (hn : n ≠ 0)
 (h : k ≠ 0 ∨ l ≠ 0) (H1 : nat.coprime (k ^ m) (l ^ n)) : nat.coprime k l :=
begin
  unfold nat.coprime at *,
  contrapose! H1,
  rw ←ne.def at *,
  apply ne_of_gt,
  apply lt_of_lt_of_le,
  { apply lt_of_le_of_ne _ H1.symm,
    rw [nat.succ_le_iff, nat.pos_iff_ne_zero],
    intro H,
    obtain ⟨rfl, rfl⟩ := nat.gcd_eq_zero_iff.mp H,
    rw [or_self] at h,
    contradiction },
  { apply nat.le_of_dvd,
    { contrapose! h,
      rw [nat.le_zero_iff, nat.gcd_eq_zero_iff] at h,
      obtain ⟨hk, hl⟩ := h,
      split; apply pow_eq_zero; assumption },
    { apply nat.dvd_gcd; refine dvd_trans _ (dvd_pow (dvd_refl _) _),
      { exact nat.gcd_dvd_left _ _ },
      { exact hm },
      { exact nat.gcd_dvd_right _ _ },
      { exact hn } } }
end

lemma coprime_add_self
  (a b : ℕ)
  (h : nat.coprime a b) :
  nat.coprime a (a + b) :=
begin
  apply nat.coprime_of_dvd',
  rintros k - a_1 a_2,
  rw ←h.gcd_eq_one,
  apply nat.dvd_gcd a_1 _,
  rw [←nat.add_sub_cancel b a, add_comm],
  apply nat.dvd_sub _ a_2 a_1 ,
  apply nat.le_add_right
end

lemma coprime_add_self_pow
  {a b c n : ℕ}
  (hn : 0 < n)
  (hsoln : (a) ^ n + (b) ^ n = (c) ^ n)
  (hxx : (a).coprime (b))
   : (a).coprime (c) :=
begin
  have hn' := nat.pos_iff_ne_zero.mp hn,
  apply nat.coprime.pow' n n hn' hn',
  { contrapose! hxx,
    obtain ⟨rfl, rfl⟩ := hxx,
    rw [zero_pow hn, zero_add] at hsoln,
    obtain rfl := pow_eq_zero hsoln,
    norm_num },
  rw ←hsoln,
  apply coprime_add_self,
  exact nat.coprime.pow n n hxx
end
