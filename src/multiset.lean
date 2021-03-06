import data.multiset

section
variables {α : Type*} {s : multiset α}

lemma multiset.filter_eq
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (b : α) :
  s.filter (eq b) = multiset.repeat b (multiset.count b s) :=
begin
  ext a,
  rw multiset.count_repeat,
  split_ifs with ha,
  { subst a,
    rw multiset.count_filter_of_pos rfl, },
  { rw multiset.count_filter_of_neg (ne.symm ha) }
end

lemma multiset.pow_count [comm_monoid α] (a : α) [decidable_eq α] :
  a ^ (multiset.count a s) = (multiset.filter (eq a) s).prod :=
by rw [multiset.filter_eq, multiset.prod_repeat]

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

lemma multiset.nsmul_repeat {a : α} (n m : ℕ) : n • (multiset.repeat a m) = multiset.repeat a (n * m) :=
begin
  rw [multiset.eq_repeat],
  split,
  { rw [add_monoid_hom.map_nsmul, multiset.card_repeat, nat.nsmul_eq_mul] },
  { intros b hb,
    by_cases hn : n = 0,
    { rw [hn, zero_nsmul] at hb,
      exact absurd hb (multiset.not_mem_zero b) },
    { rw multiset.mem_nsmul hn at hb,
      exact multiset.eq_of_mem_repeat hb } },
end

lemma multiset.nsmul_cons (n : ℕ) (a : α) : n • (a ::ₘ s) = n • (↑[a]) + n • s :=
begin
  induction n with n ih,
  { simp only [add_zero, zero_nsmul] },
  { simp only [add_nsmul, one_nsmul, ih, ←multiset.singleton_add, nsmul_add] }
end
lemma multiset.nsmul_cons' (n : ℕ) (a : α) : n • (a ::ₘ s) = n • (a ::ₘ 0) +  n • s :=
multiset.nsmul_cons n a

theorem multiset.filter_cons {a : α} (s : multiset α)
  (p : α → Prop) [decidable_pred p] :
  multiset.filter p (a ::ₘ s) = (ite (p a) ↑[a] 0) + multiset.filter p s :=
begin
  split_ifs with h,
  { rw [multiset.filter_cons_of_pos _ h, multiset.singleton_add] },
  { rw [multiset.filter_cons_of_neg _ h, zero_add] },
end

lemma multiset.nsmul_filter (n : ℕ)
  (p : α → Prop) [decidable_pred p] :
  multiset.filter p (n • s) = n • multiset.filter p s :=
begin
  by_cases hn : n = 0,
  { simp only [hn, multiset.filter_zero, zero_nsmul] },
  { refine s.induction_on _ _,
    { simp only [multiset.filter_zero, nsmul_zero] },
    { intros a ha ih,
      rw [multiset.nsmul_cons, multiset.filter_add, ih, multiset.filter_cons, nsmul_add],
      congr,
      split_ifs with hp;
      { simp only [multiset.filter_eq_self, nsmul_zero, multiset.filter_eq_nil],
        intros b hb,
        rw [multiset.mem_nsmul hn, multiset.mem_coe, list.mem_singleton] at hb,
        rwa hb } } }
end

end

section
variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}

theorem multiset.countp_cons (p : α → Prop)
  [decidable_pred p] (b : α) (s : multiset α) :
  multiset.countp p (b ::ₘ s) = multiset.countp p s + (if p b then 1 else 0) :=
begin
  split_ifs with h;
  simp only [h, multiset.countp_cons_of_pos, add_zero, multiset.countp_cons_of_neg, not_false_iff],
end

lemma multiset.count_map (b : β)
  [decidable_eq β]
  (f : α → β) :
  multiset.count b (s.map f) = multiset.countp (λ x, b = f x) s :=
begin
  refine s.induction_on _ _,
  { simp only [multiset.countp_zero, multiset.count_zero, multiset.map_zero] },
  { intros a ha ih,
    rw [multiset.map_cons, multiset.count_cons, multiset.countp_cons, ih] },
end

-- TODO: should be countp_congr?
lemma multiset.countp_eq (p1 p2 : α → Prop)
  [decidable_pred p1] [decidable_pred p2]
  (h : ∀ x ∈ s, p1 x ↔ p2 x) :
  multiset.countp p1 s = multiset.countp p2 s :=
begin
  revert h,
  refine s.induction_on _ _,
  { rintro -, simp only [multiset.countp_zero] },
  { intros a t ih h,
    specialize ih (λ x hx, h _ (multiset.mem_cons_of_mem hx)),
    rw [multiset.countp_cons, multiset.countp_cons, ih],
    obtain ⟨h1, h2⟩|⟨h1, h2⟩ := iff_iff_and_or_not_and_not.mp (h a (multiset.mem_cons_self a t));
    simp only [h1, h2, if_congr, if_true, if_false, add_left_inj, eq_self_iff_true] }
end

end

lemma multiset.induction_on_repeat
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (P : multiset α → Prop)
  (h0 : P 0)
  (hnext : ∀ t {a}, a ∈ s → P t → P (t + multiset.repeat a (s.count a))) :
  P s :=
begin
  revert hnext,
  refine s.strong_induction_on _,
  clear s,
  intros s ih hnext,
  by_cases hs : s = 0,
  { simp only [hs, h0] },
  { obtain ⟨b, hb⟩ := multiset.exists_mem_of_ne_zero hs,
    rw ←multiset.filter_add_not (ne b) s,
    simp only [ne.def, not_not, multiset.filter_eq],
    convert hnext (multiset.filter (ne b) s) hb _,
    apply ih,
    { apply lt_of_le_of_ne (multiset.filter_le _ _),
      intro H,
      rw multiset.filter_eq_self at H,
      exact H b hb rfl },
    { intros t a h1 h2,
      rw multiset.count_filter_of_pos (multiset.of_mem_filter h1),
      exact hnext _ (multiset.mem_of_mem_filter h1) h2 } }
end

lemma multiset.exists_nsmul_of_dvd
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (k : ℕ)
  (h : ∀ x ∈ s, k ∣ multiset.count x s) :
  ∃ t : multiset α, s = k • t :=
begin
  obtain (rfl|hk) := nat.eq_zero_or_pos k,
  { use 0,
    simp only [nsmul_zero],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    have := h x hx,
    rw zero_dvd_iff at this,
    rw [←multiset.count_pos, this] at hx,
    exact lt_irrefl 0 hx },
  { refine s.induction_on_repeat _ _ _,
    { use 0, rw [nsmul_zero] },
    { rintros t a ha ⟨u, hu⟩,
      obtain ⟨n, hn⟩ := h a ha,
      use u + multiset.repeat a n,
      rw [nsmul_add, multiset.nsmul_repeat, hu, hn] } }
end
