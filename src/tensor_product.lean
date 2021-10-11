import ring_theory.tensor_product
import ring_theory.localization

variables {R : Type*} [comm_ring R] {S : submonoid R} (A : Type*) [comm_ring A] [algebra R A] 
(B : Type*) [comm_ring B] [algebra R B] [is_localization S B]

/- open_locale tensor_product

instance : algebra A (B ⊗[R] A)  := { smul := begin
  intros a x,
  --have hx : x ∈ submodule.span R { t : B ⊗[R] A | ∃ m n, m ⊗ₜ n = t }:= sorry,
  sorry,
  end,
  to_fun := λ a, tensor_product.tmul R 1 a,
  map_one' :=  algebra.tensor_product.one_def,
  map_mul' := λ x y, by {rw [algebra.tensor_product.tmul_mul_tmul, one_mul]},
  map_zero' := tensor_product.tmul_zero A (1 : B),
  map_add' := λ x y, by {rw tensor_product.tmul_add},
  commutes' := λ a x, by {rw mul_comm},
  smul_def' := sorry } 

/- lemma tensor_product_with_localization (B : Type*) [comm_ring B] [algebra R B] [is_localization S B] : is_localization (algebra.algebra_map_submonoid A S) (B ⊗[R] A) -/

lemma tensor_product_with_localization (B : Type*) [comm_ring B] [algebra R B] 
  [is_localization S B] : is_localization (submonoid.map (algebra_map R A : R →* A) S) (B ⊗[R] A) := 
{ map_units := 
  begin
    rintro ⟨y', hy'⟩,
    rw submonoid.mem_map at hy',
    rcases hy' with ⟨y, hy, hy1⟩,
    rw is_unit_iff_exists_inv,
    have : ∃ z : B, ((algebra_map R B) y)*z = 1,
    { have : is_localization S B := infer_instance,
      rcases this with ⟨hmap_units, -, -⟩,
      exact is_unit_iff_exists_inv.mp (hmap_units ⟨y, hy⟩)},
    cases this with z hz,
    use tensor_product.tmul R z (1 : A),
    simp [← hy1],
    change (1 : B) ⊗ₜ[R] ((algebra_map R A) y : A) * z ⊗ₜ[R] 1 = 1,
    simp,
    --rw [algebra.tensor_product.tmul_mul_tmul, hz, mul_one, algebra.tensor_product.one_def],
    --rw submodule.span_induction
    sorry,
  end,
  surj := sorry,
  eq_iff_exists := {}
  /- begin
    intros x y, split; intro hxy,
    { sorry },
    { cases hxy with c hc,
      --simp, 
      sorry,}
  end -/ } -/