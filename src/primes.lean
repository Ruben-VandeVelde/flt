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
