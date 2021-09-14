import ring_theory.tensor_product
import ring_theory.localization

variables {R : Type*} [comm_ring R] {S : submonoid R} (A : Type*) [comm_ring A] [algebra R A] (B : Type*) [comm_ring B] [algebra R B] [is_localization S B]

open_locale tensor_product

/- def image_submonoid : submonoid A :=
{ carrier  := (algebra_map R A)'' S,
  one_mem' := by {rw set.mem_image, use [1, S.one_mem'], simp},
  mul_mem' := 
  begin
    intros a b ha hb,
    rw set.mem_image at ha hb ⊢,
    rcases ha with ⟨r, hr, hr1⟩ ,
    rcases hb with ⟨s, hs, hs1⟩,
    use [r*s, S.mul_mem' hr hs],
    rw ← hr1,
    rw ← hs1,
    exact (algebra_map R A).map_mul r s,
  end } -/

instance : algebra A (B ⊗[R] A)  := { smul := begin
  intros a x,
  rw top,
  exact x,
  end,
  to_fun := λ a, tensor_product.tmul R 1 a,
  map_one' :=  algebra.tensor_product.one_def,
  map_mul' := sorry,
  map_zero' := tensor_product.tmul_zero A (1 : B),
  map_add' := sorry,
  commutes' := sorry,
  smul_def' := sorry } 


/- lemma tensor_product_with_localization (B : Type*) [comm_ring B] [algebra R B] [is_localization S B] : is_localization S (B ⊗[R] A) := 
{ map_units := 
  begin
    intro y,
    simp,
    rw is_unit_iff_exists_inv,
    have : ∃ z : B, ((algebra_map R B) y)*z = 1,
    { have : is_localization S B := infer_instance,
      rcases this with ⟨hmap_units, -, -⟩,
      exact is_unit_iff_exists_inv.mp (hmap_units y)},
    cases this with z hz,
    use tensor_product.tmul R z (1 : A),
    rw [algebra.tensor_product.tmul_mul_tmul, hz, mul_one, algebra.tensor_product.one_def],
  end,
  surj := sorry,
  eq_iff_exists := sorry }  -/