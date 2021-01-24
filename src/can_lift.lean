import tactic

instance {α : Type*} {P : α → Prop} : can_lift α ({ x : α // P x}) :=
⟨coe, P, λx hx, ⟨⟨x, hx⟩, subtype.coe_mk x hx⟩⟩

instance pnat.can_lift_from_ℕ : can_lift ℕ ℕ+ :=
⟨coe, λ n, 0 < n, λx hx, ⟨⟨x, hx⟩, subtype.coe_mk x hx⟩⟩

instance pnat.can_lift_from_ℤ : can_lift ℤ ℕ+ :=
⟨coe, λ n, 0 < n, begin
  intros x hx,
  lift x to ℕ using hx.le,
  simp only [int.coe_nat_pos] at hx,
  lift x to ℕ+ using hx,
  use x,
  simp only [coe_coe],
end⟩