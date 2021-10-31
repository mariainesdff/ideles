import algebra.order.with_zero

noncomputable theory
open_locale classical

lemma with_zero.le_total {α : Type*} [linear_ordered_comm_group α] (x y : with_zero α) :
  x ≤ y ∨ y ≤ x :=
begin
  by_cases hx : x = 0,
  { exact eq.subst hx or.inl (with_zero.zero_le y)},
  { by_cases hy : y = 0,
    { exact eq.subst hy or.inr (with_zero.zero_le x) },
    { obtain ⟨ux, hux⟩ := with_zero.ne_zero_iff_exists.mp hx,
      obtain ⟨uy, huy⟩ := with_zero.ne_zero_iff_exists.mp hy,
      rw [← hux, ← huy, with_zero.coe_le_coe, with_zero.coe_le_coe],
      exact le_total _ _ }}
end

lemma with_zero.mul_le_mul_left' {α : Type*} [linear_ordered_comm_group α] (x y : with_zero α)
  (hxy : x ≤ y) (z : with_zero α) : z * x ≤ z * y := 
begin
  by_cases hz : z = 0,
  { rw [hz, group_with_zero.zero_mul, group_with_zero.zero_mul], exact le_refl 0 },
  { by_cases hx : x = 0,
    { rw [hx, group_with_zero.mul_zero], exact with_zero.zero_le _},
    { have hy : y ≠ 0,
      { intro hy,
        exact hx (le_antisymm (eq.subst hy hxy) (with_zero.zero_le x)) },
      obtain ⟨ux, hux⟩ := with_zero.ne_zero_iff_exists.mp hx,
      obtain ⟨uy, huy⟩ := with_zero.ne_zero_iff_exists.mp hy,
      obtain ⟨uz, huz⟩ := with_zero.ne_zero_iff_exists.mp hz,
      rw [← hux, ← huy, with_zero.coe_le_coe] at hxy, 
      rw [← hux, ← huy, ← huz, ← with_zero.coe_mul, ← with_zero.coe_mul, with_zero.coe_le_coe],
      exact mul_le_mul_left' hxy uz }},
  end

instance {α : Type*} [linear_ordered_comm_group α] : 
  linear_ordered_comm_group_with_zero (with_zero α) := 
{ le_total        := with_zero.le_total,
  decidable_le    := classical.dec_rel _,
  mul_le_mul_left := with_zero.mul_le_mul_left',
  zero_le_one     := with_zero.zero_le _,
  ..with_zero.partial_order,
  ..with_zero.comm_group_with_zero }
