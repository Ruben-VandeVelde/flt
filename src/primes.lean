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
      ... = 2 ^ 2 * 2 ^ (k - 2) : (nat.pow_eq_mul_pow_sub _ h3).symm
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

lemma nat.coprime_of_dvd'' {m n : ℕ} (H : ∀ k, nat.prime k → k ∣ m → k ∣ n → k ∣ 1) :
  nat.coprime m n :=
begin
  cases nat.eq_zero_or_pos (nat.gcd m n) with g0 g1,
  { rw [nat.eq_zero_of_gcd_eq_zero_left g0, nat.eq_zero_of_gcd_eq_zero_right g0] at H,
    have := (H 2 dec_trivial (dvd_zero _) (dvd_zero _)),
    rw nat.dvd_one at this,
    norm_num at this,    
  },
  apply nat.coprime_of_dvd',
  intros d hdleft hdright,
  rw nat.dvd_one,
  by_contra h,
  have : d ≠ 0,
  { rintro rfl,
    rw zero_dvd_iff at *,
    rw [hdleft, hdright] at g1,
    rw [nat.gcd_zero_right] at g1,
    exact irrefl 0 g1,
  },
  have : 2 ≤ d,
  { rcases d with (_|_|_),
    { simp at this, contradiction },
    { simp at h, contradiction },
    { change 2 ≤ d + 2,
      rw [le_add_iff_nonneg_left],
      exact zero_le d },
  },
  obtain ⟨p, hp, hpdvd⟩ := nat.exists_prime_and_dvd this,
  have := H p hp (dvd_trans hpdvd hdleft) (dvd_trans hpdvd hdright),
  rw nat.dvd_one at this,
  have := nat.prime.ne_one hp,
  contradiction,
end

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
  exact nat.dvd_sub (nat.le.intro rfl) H G,
end

lemma nat.pos_pow_iff {b : ℕ} (n : ℕ) (h : 0 < n) : 0 < b ↔ 0 < b ^ n :=
begin
  split,
  apply nat.pos_pow_of_pos,
  rw [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero],
  contrapose!,
  rintro rfl,
  apply nat.zero_pow h,
end
