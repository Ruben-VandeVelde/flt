import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic

lemma nat.mem_factors' {n p} (hn : 0 < n) : p ∈ nat.factors n ↔ nat.prime p ∧ p ∣ n :=
⟨λ h, ⟨nat.mem_factors h, (nat.mem_factors_iff_dvd hn (nat.mem_factors h)).mp h⟩,
 λ ⟨hprime, hdvd⟩, (nat.mem_factors_iff_dvd hn hprime).mpr hdvd⟩

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
      { rw [←nat.prod_factors h0, ←nat.pow_eq_pow],
        have := list.prod_repeat 2 k,
        refine trans _ this,
        suffices : n.factors = list.repeat 2 k, { rw this },
        apply list.eq_repeat_of_mem,
        intros p hp,
        rw nat.mem_factors' h0 at hp,
        cases nat.prime.eq_two_or_odd hp.left,
        { assumption },
        { have := h p hp.right hp.left,
          contradiction } },

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : _
      ... = 2 ^ (2 + (k - 2)) : _
      ... = 2 ^ 2 * 2 ^ (k - 2) : nat.pow_add 2 2 (k - 2)
      ... = 4 * 2 ^ (k - 2) : by norm_num,
      exact h2,
      rw nat.add_sub_of_le,
      exact h3,
      },
    { left, refl } },
end
