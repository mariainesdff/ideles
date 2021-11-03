import algebra.order.with_zero

noncomputable theory
open_locale classical

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
{ mul_le_mul_left := with_zero.mul_le_mul_left',
  zero_le_one     := with_zero.zero_le _,
  ..with_zero.linear_order,
  ..with_zero.comm_group_with_zero }


lemma with_zero.div_le_div_right {α : Type*} [linear_ordered_comm_group α] (x y z : with_zero α)
  (hz : 0 < z) : x/z ≤ y/z ↔ x ≤ y := 
begin
  { by_cases hx : x = 0,
    { rw [hx, zero_div], simp only [zero_le'], },
    { by_cases hy : y = 0,
      { rw [hy, zero_div, le_zero_iff, le_zero_iff, div_eq_zero_iff,or_iff_left_iff_imp],
        intro h, 
        exact absurd h (ne_of_gt hz) },
      { rw [← ne.def, with_zero.ne_zero_iff_exists] at hx,
        obtain ⟨a, hax⟩ := hx,
        obtain ⟨b, hby⟩ := with_zero.ne_zero_iff_exists.mp hy,
        obtain ⟨c, hcz⟩ := with_zero.ne_zero_iff_exists.mp (ne_of_gt hz),
        rw [← hax, ← hby, ← hcz, with_zero.div_coe _ _, with_zero.div_coe _ _, with_zero.coe_mul,
          with_zero.coe_mul, mul_comm ↑a, mul_comm ↑b],
        split; intro hab,
        { have habc : ↑c * (↑c⁻¹ * ↑a) ≤ ↑c * (↑c⁻¹ * ↑b) := with_zero.mul_le_mul_left _ _ hab _,
          rw [← mul_assoc, ← mul_assoc, with_zero.coe_inv, mul_inv_cancel, one_mul, one_mul] 
            at habc,
          exact habc,
          exact with_zero.coe_ne_zero, },
        exact with_zero.mul_le_mul_left _ _ hab _, }}},
  end