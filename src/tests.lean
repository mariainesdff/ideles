import algebra.pointwise
import order.filter.bases
import adeles

noncomputable theory
open nat 
--universe u

lemma padic.val_mul' {p : primes} ( q r : ℚ_[p]) (hq : q ≠ 0) (hr : r ≠ 0) : 
  (q * r).valuation = q.valuation + r.valuation := 
begin
  have h : ∥q * r∥ = ∥q∥ * ∥r∥ := padic_norm_e.mul q r,
  rw [padic.norm_eq_pow_val hq, padic.norm_eq_pow_val hr,
    padic.norm_eq_pow_val (mul_ne_zero hq hr)] at h,
  have hp :  (0 : ℝ) < ↑(p : ℕ),
  { rw [← cast_zero, cast_lt], exact prime.pos p.property },
  have h0 : ↑(p : ℕ) ≠ (0 : ℝ) := ne_of_gt hp,
  have h1 : ↑(p : ℕ) ≠ (1 : ℝ),
  { rw ← cast_one,
    intro h2,
    exact (nat.prime.ne_one p.property) (nat.cast_inj.mp h2) },
  rw [← fpow_add h0 (-q.valuation) (-r.valuation), fpow_inj hp h1, ← neg_add _ _] at h,
  exact neg_inj.mp h,
end

section ring_filter_basis

-- From the perfectoid space project:
local attribute [instance] set.has_mul set.has_add
class add_group_filter_basis (α : Type*) [add_group α] extends filter_basis α :=
(zero : ∀ {U}, U ∈ sets → (0 : α) ∈ U)
(add : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U)
(neg : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, -x) ⁻¹' U)
(conj : ∀ x₀, ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x₀+x-x₀) ⁻¹' U)

class ring_filter_basis (α : Type*) [ring α] extends add_group_filter_basis α :=
(mul : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(mul_left : ∀ (x₀ : α) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x) ⁻¹' U)
(mul_right : ∀ (x₀ : α) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x*x₀) ⁻¹' U)
--

variables (R : Type*) [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S] [algebra R S]
  [is_localization M S] (B : ring_filter_basis R)

private def localization.sets : set (set S) := 
  {(is_localization.to_localization_map M S).to_map '' U | U ∈ B.sets}

private lemma localization.sets.nonempty : set.nonempty (localization.sets R M S B) := 
begin
    cases (B.nonempty) with U hU,
    use [(is_localization.to_localization_map M S).to_map '' U, U, hU],
end

private lemma mul_left (h : ∀  (m ∈ M) (U : set R), (U ∈ B.sets) → ({m}*U) ∈ B.sets) :
  ∀ (x₀ : S) {U : set S}, U ∈ (localization.sets R M S B) → (∃ (V : set S) 
  (H : V ∈ (localization.sets R M S B)), V ⊆ (λ (x : S), x₀ * x) ⁻¹' U) := 
begin
    intros x U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    rcases (is_localization.mk'_surjective M x) with ⟨r, s, hx⟩,
    rcases ring_filter_basis.mul_left r (h s.1 s.2 V hVsets) with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros y hy,
    rcases hy with ⟨yr, hyrW, hyr_loc⟩,
    have h1 := hVW hyrW,
    rw [set.mem_preimage, set.singleton_mul, set.mem_image, subtype.val_eq_coe] at h1,
    rcases h1 with ⟨r1, hr1V, hxy⟩,
    rw [set.mem_preimage, ← hUV, set.mem_image, ← hx, ← hyr_loc],
    use [r1, hr1V],
    rw [is_localization.to_localization_map_to_map, ring_hom.coe_monoid_hom, is_localization.mk'_eq_mul_mk'_one _ _, ← one_mul (algebra_map R S r1), ← is_localization.mk'_self S s.2, is_localization.mk'_eq_mul_mk'_one _ _],
    simp only [subtype.val_eq_coe],
    rw [set_like.eta, mul_comm (algebra_map R S s), mul_assoc, mul_comm (algebra_map R S r), mul_assoc, algebra_map, ← ring_hom.map_mul, ← ring_hom.map_mul, hxy],
  end

instance localization.ring_filter_basis  (h : ∀  (m ∈ M) (U : set R), (U ∈ B.sets) → ({m}*U) ∈ B.sets) : ring_filter_basis S := { sets := {(is_localization.to_localization_map M S).to_map '' U | U ∈ B.sets},
  nonempty := 
  begin
    cases (B.nonempty) with U hU,
    use [(is_localization.to_localization_map M S).to_map '' U, U, hU],
  end,
  inter_sets := 
  begin
    intros U1 U2 h1 h2,
    rcases h1 with ⟨V1, hV1sets, hUV1⟩,
    rcases h2 with ⟨V2, hV2sets, hUV2⟩,
    rcases (B.inter_sets hV1sets hV2sets) with ⟨W, hWsets, hW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros x hx,
    rw set.mem_image at hx,
    rcases hx with ⟨r, hrW, hr⟩,
    apply set.mem_inter,
    rw [← hr, ← hUV1], 
    use [r, set.mem_of_mem_of_subset (hW hrW) (set.inter_subset_left V1 V2)], 
    rw [← hr, ← hUV2], 
    use [r, set.mem_of_mem_of_subset (hW hrW) (set.inter_subset_right V1 V2)],
  end,
  zero := 
  begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    have hVzero : (0 : R) ∈ V := add_group_filter_basis.zero hVsets,
    rw [← hUV, set.mem_image],
    use [(0 : R), hVzero],
    rw [is_localization.to_localization_map_to_map, ring_hom.coe_monoid_hom, ring_hom.map_zero],
  end,
  add := 
  begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    rcases add_group_filter_basis.add hVsets with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros x hx,
    rw set.mem_add at hx,
    rcases hx with ⟨x1, x2, ⟨r1, hr1W, hr1⟩, ⟨r2, hr2W, hr2⟩, hadd⟩,
    rw [← hUV, set.mem_image],
    use (r1 + r2),
    split,
    { apply hVW,
    use [r1, r2, hr1W, hr2W]},
    rw [is_localization.to_localization_map_to_map, algebra_map, ring_hom.coe_monoid_hom] at hr1 hr2 ⊢,
    rwa [ring_hom.map_add, hr1, hr2],
  end,
  neg := begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    rcases add_group_filter_basis.neg hVsets with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros x hx,
    rcases hx with ⟨r, hrW, hr⟩,
    rw [set.mem_preimage, ← hUV, set.mem_image],
    use [-r, hVW hrW],
    rw [is_localization.to_localization_map_to_map,algebra_map, ring_hom.coe_monoid_hom] at hr ⊢,
    rw [ring_hom.map_neg, hr],
  end,
  conj := begin
    intros x U hU,
    use [U, hU],
    simp only [add_sub_cancel', set.preimage_id'],
  end,
  mul := 
  begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    rcases ring_filter_basis.mul hVsets with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros x hx,
    rw set.mem_mul at hx,
    rcases hx with ⟨x1, x2, ⟨r1, hr1W, hr1⟩, ⟨r2, hr2W, hr2⟩, hmul⟩,
    rw [← hUV, set.mem_image],
    use (r1 * r2),
    split,
    { apply hVW,
    use [r1, r2, hr1W, hr2W]},
    rw [is_localization.to_localization_map_to_map, algebra_map, ring_hom.coe_monoid_hom] at hr1 hr2 ⊢,
    rwa [ring_hom.map_mul, hr1, hr2],
  end,
  mul_left := mul_left R M S B h,
  mul_right := 
  begin
    intros x U hU,
    have h1 : (λ y, y*x) = (λ y, x*y) := by {ext y, rw mul_comm},
    rw h1,
    exact mul_left R M S B h x hU,
  end }

  end ring_filter_basis

/-   section topological_ring

  variables (R : Type*) [ring R] (S : Type*) [ring S] (f : ring_hom R S)

/-   structure filter_basis_at_zero (α : Type*) [add_group α] extends filter_basis α :=
  (zero : ∀ {U}, U ∈ sets → (0 : α) ∈ U)

  lemma topological_ring.to_filter_basis_at_zero [t : topological_space R] [topological_ring R] : filter_basis_at_zero R := 
  { sets := { U : set R | is_open U ∧ (0 : R) ∈ U },
    nonempty :=  ⟨set.univ, t.is_open_univ, set.mem_univ (0 : R)⟩,
    inter_sets := λ U V ⟨hU_open, hU_zero⟩ ⟨hV_open, hV_zero⟩,
      by use [U ∩ V, t.is_open_inter U V hU_open hV_open, set.mem_inter hU_zero hV_zero],
    zero := λ U ⟨hU_open, hU_zero⟩ , hU_zero } -/

  end topological_ring -/

--#print R
--#print M

instance m_p {p : primes} : metric_space ℤ_[p] := infer_instance

instance t_p {p : primes} : topological_space ℤ_[p] := infer_instance

--def B_Z_p (p : primes) := {U : set ℤ_[p] | t_p.is_open U ∧ ((0 : ℤ_[p]) ∈ U)}

def B_Z_p (p : primes) := { U : set ℤ_[p] | ∃ n : ℕ,  U = metric.ball (0 : ℤ_[p]) (p^(-(n : ℤ)))}
  
lemma open_mul_Z_p {p : primes} (U : set ℤ_[p]) (hU : U ∈ B_Z_p p) (z : ℤ) (hne_zero : z ≠ 0) : 
(λ (x : ℤ_[p]), ↑z*x) '' U ∈ B_Z_p p := 
begin
  cases hU with n hball,
  lift (padic_int.valuation z) to ℕ using (padic_int.valuation_nonneg (z : ℤ_[p])) with m hm,
  have hp_ne_zero : (p : ℝ) ≠ 0,
  { rw [coe_coe, nat.cast_ne_zero],
    exact nat.prime.ne_zero p.2},
  have hne_zero' : (z : ℤ_[p]) ≠ 0 := int.cast_ne_zero.mpr (hne_zero),
  have hpos : 0 < (p : ℝ)^-(m : ℤ),
  { rw lt_iff_le_and_ne,
  split,
  { apply fpow_nonneg,  
    rw [coe_coe, ← cast_zero, nat.cast_le],
    exact le_of_lt (nat.prime.pos p.2)},
  { exact ne.symm (fpow_ne_zero _ hp_ne_zero)}},

  have hz_pos : 0 < ∥(z : ℚ_[p])∥,
  { rw [← padic_int.coe_coe_int, padic_int.padic_norm_e_of_padic_int,lt_iff_le_and_ne],
    split,
    { exact norm_nonneg (z : ℤ_[p])},
    { intro h,
      exact hne_zero' (norm_eq_zero_iff'.mp (eq.symm h))},
  },

  use (m + n),
  rw hball,
  ext x,
  split; rw set.mem_image,
  { rintro ⟨y, hyball, hxy⟩,
    rw [metric.mem_ball, dist_eq_norm, sub_zero] at hyball ⊢,
    rw [← hxy, padic_int.norm_mul, padic_int.norm_eq_pow_val hne_zero', ← hm, ← coe_coe, 
      int.coe_nat_add, neg_add (m : ℤ) n, fpow_add hp_ne_zero],
    exact mul_lt_mul'(le_of_eq (refl _)) hyball (norm_nonneg y) hpos },
    { intro hx,
      rw [metric.mem_ball, dist_eq_norm, sub_zero] at hx,
      set y := (x/z : ℚ_[p]) with hy,
      have hy_int : ∥y∥ ≤ 1,
      { rw [hy, normed_field.norm_div],
        by_cases hx_zero : (x : ℚ_[p]) = 0,
        { rw [hx_zero, norm_zero, zero_div], exact zero_le_one },
        
        rw [div_le_iff hz_pos, one_mul],
        apply le_trans (le_of_lt hx),
        rw [← padic_int.coe_coe_int, padic_int.padic_norm_e_of_padic_int, 
          padic_int.norm_eq_pow_val hne_zero', ← coe_coe, fpow_le_iff_le],
        { rw [← hm, int.coe_nat_add, neg_add, add_neg_le_iff_le_add', le_add_neg_iff_add_le, 
            add_left_neg],
          exact int.coe_nat_nonneg n },
        { rw [coe_coe, one_lt_cast], 
          exact prime.one_lt p.2 }},
      use ⟨y, hy_int⟩,
      split,
      { rw [metric.mem_ball, dist_eq_norm, sub_zero, padic_int.norm_eq_padic_norm, hy, 
          normed_field.norm_div, padic_int.padic_norm_e_of_padic_int, ← padic_int.coe_coe_int, 
          div_lt_iff,padic_int.padic_norm_e_of_padic_int],
        { rw [padic_int.norm_eq_pow_val hne_zero', ← hm, ← coe_coe, ← fpow_add hp_ne_zero, 
            ← neg_add, add_comm, ← int.coe_nat_add m n],
          exact hx },
        rw padic_int.coe_coe_int,
        exact hz_pos },
      have : (z : ℚ_[p]) ≠ 0 := int.cast_ne_zero.mpr (hne_zero),
      rw [← padic_int.cast_inj, padic_int.coe_mul,padic_int.coe_coe_int, subtype.coe_mk _ _,
      hy, ← mul_div_assoc, mul_comm, mul_div_assoc, div_self this, mul_one] },
end

/- def B := {U : set R | R.topological_space.is_open U ∧ ((0 : R) ∈ U)}

lemma open_mul (U : set R) (hU : U ∈ B) (z : M) : (λ (x : R), ↑z*x) '' U ∈ B := 
begin
  cases hU with hUopen hUzero,
  split,
  { sorry,
    },
  use [(0 : R), hUzero, mul_zero _],
end
 -/