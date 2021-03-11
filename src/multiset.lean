import data.multiset

section
variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}
lemma multiset.rel.mono'
  (h : ∀(a ∈ s) (b ∈ t), r a b → p a b) (hst : multiset.rel r s t) : multiset.rel p s t :=
begin
  induction hst,
  case rel.zero { exact multiset.rel.zero },
  case rel.cons : a b s t hab hst ih {
    have := h a  (multiset.mem_cons_self _ _) b  (multiset.mem_cons_self _ _) hab,
    apply multiset.rel.cons this,
    apply ih,
    intros a' ha' b' hb' h',
    apply h _ (multiset.mem_cons_of_mem ha') _ (multiset.mem_cons_of_mem hb') h' }
end

-- https://github.com/leanprover-community/mathlib/commit/be6753ca1b464625abb386d4e0e71b569d88163f
lemma multiset.map_filter
  (f : α → β) (p : β → Prop) [decidable_pred p] :
  multiset.filter p (multiset.map f s) = multiset.map f (multiset.filter (p ∘ f) s) :=
begin
  refine multiset.induction_on s _ _,
  { simp only [multiset.filter_zero, multiset.map_zero] },
  { intros a t ih,
    simp only [multiset.map_cons],
    by_cases h': (p ∘ f) a,
    { have h'' : p (f a) := h',
      rw [multiset.filter_cons_of_pos _ h', multiset.map_cons, ←ih, multiset.filter_cons_of_pos _ h''] },
    { have h'' : ¬p (f a) := h',
      rw [multiset.filter_cons_of_neg _ h', ←ih, multiset.filter_cons_of_neg _ h''] } }
end

lemma multiset.pow_count [comm_monoid α] (a : α) [decidable_eq α] :
  a ^ (multiset.count a s) = (multiset.filter (eq a) s).prod :=
begin
  rw ←multiset.prod_repeat,
  congr,
  symmetry,
  rw multiset.eq_repeat,
  split,
  { rw [←multiset.countp_eq_card_filter],
    refl },
  { intros b hb, 
    exact (multiset.of_mem_filter hb).symm },
end

lemma multiset.prod_nonneg [ordered_comm_semiring α] (f : multiset α) (h : ∀ a ∈ f, (0 : α) ≤ a) : 0 ≤ f.prod :=
begin
  revert h,
  refine f.induction_on _ _,
  { rintro -, simp only [multiset.prod_zero], exact zero_le_one },
  { intros a s hs ih,
    rw multiset.prod_cons,
    apply mul_nonneg,
    { exact ih _ (multiset.mem_cons_self _ _) },
    { apply hs,
      intros a ha,
      exact ih _ (multiset.mem_cons_of_mem ha) } }
end

lemma multiset.nsmul_repeat {a : α} (n m : ℕ) : n •ℕ (multiset.repeat a m) = multiset.repeat a (n * m) :=
begin
  by_cases hn : n = 0,
  { simp only [hn, zero_mul, zero_nsmul, multiset.repeat_zero] },
  rw multiset.eq_repeat,
  simp only [true_and, nat.cast_id, nsmul_eq_mul, multiset.card_repeat, eq_self_iff_true, add_monoid_hom.map_nsmul],
  intros b hb,
  rw multiset.mem_nsmul hn at hb,
  exact multiset.eq_of_mem_repeat hb,
end

-- multiset.count_smul → multiset.count_nsmul

lemma multiset.nsmul_cons (n : ℕ) (a : α) : n •ℕ (a ::ₘ s) = n •ℕ (↑[a]) +  n •ℕ s :=
begin
  induction n with n ih,
  { simp only [add_zero, zero_nsmul] },
  { rw nat.succ_eq_add_one,
    rw [add_nsmul, add_nsmul, one_nsmul, ih],
    rw [add_assoc, add_assoc],
    congr' 1,
    rw [one_nsmul, add_nsmul, one_nsmul, ←multiset.singleton_add],
    rw [add_comm _ s, ←add_assoc, add_comm], }
end
lemma multiset.nsmul_cons' (n : ℕ) (a : α) : n •ℕ (a ::ₘ s) = n •ℕ (a ::ₘ 0) +  n •ℕ s :=
multiset.nsmul_cons n a

lemma multiset.nsmul_filter (n : ℕ)
  (p : α → Prop) [decidable_pred p] :
  multiset.filter p (n •ℕ s) = n •ℕ multiset.filter p s :=
begin
  by_cases hn : n = 0,
  { simp only [hn, multiset.filter_zero, zero_nsmul] },
  refine s.induction_on _ _,
  { simp only [multiset.filter_zero, nsmul_zero] },
  { intros a ha ih,
    by_cases hp : p a,
    { simp only [hp, multiset.filter_cons_of_pos],
      rw multiset.nsmul_cons,
      rw multiset.nsmul_cons,
      rw multiset.filter_add,
      rw ih,
      congr,
      rw multiset.filter_eq_self,
      intros b hb,
      convert hp,
      rwa [multiset.mem_nsmul hn, multiset.mem_coe, list.mem_singleton] at hb },
    { rw [multiset.filter_cons_of_neg _ hp],
      rw multiset.nsmul_cons,
      rw multiset.filter_add,
      rw ih,
      convert zero_add _,
      rw multiset.filter_eq_nil,
      intros b hb,
      convert hp,
      rwa [multiset.mem_nsmul hn, multiset.mem_coe, list.mem_singleton] at hb } }
end

end
