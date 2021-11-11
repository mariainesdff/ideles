import algebra.order.with_zero

noncomputable theory
open_locale classical

lemma with_zero.div_le_div_right {α : Type*} [linear_ordered_comm_group_with_zero α] 
{x y z :  α}
  (hz : z ≠ 0) : x/z ≤ y/z ↔ x ≤ y := 
begin
  rw [div_eq_mul_inv _ _, div_eq_mul_inv _ _],
  split; intro hxy,
  { rw [← mul_one x, ← mul_one y, ← inv_mul_cancel hz, ← mul_assoc, ← mul_assoc],
    exact mul_le_mul_right' hxy _, },
  { exact mul_le_mul_right' hxy _, }
end

lemma with_zero.div_le_iff {α : Type*} [linear_ordered_comm_group_with_zero α] {x y z : α}
  (hy : y ≠ 0) : x/y ≤ z ↔ x ≤ z*y := 
begin
  conv_lhs {rw ← mul_one z, rw ← div_self hy, rw ← mul_div_assoc},
  exact with_zero.div_le_div_right hy,
end

lemma with_zero.mul_le_one {α : Type*} [linear_ordered_comm_group_with_zero α] {x y : α} 
  (hx : x ≤ 1) (hy : y ≤ 1) : x*y ≤ 1 :=
by { rw ← mul_one (1 : α), exact mul_le_mul' hx hy }