import algebra.pointwise
import topology.algebra.ring
import topology.continuous_function.basic

open_locale classical topological_space filter

variables {R : Type*} [ring R] [t : topological_space R] [tr : topological_ring R]
include t tr

local attribute [instance] set.has_mul set.has_add

structure is_topological_basis_at_zero (s : set (set R)) : Prop :=
(h_open : ∀ U ∈ s, is_open U)
(h_zero : ∀ U ∈ s, (0 : R) ∈ U)
(h_nhds : ∀ (U : set R), (0 : R) ∈ U → is_open U → ∃ V ∈ s, V ⊆ U)

lemma is_open_add_constant (a : R) (U : set R) (hU : is_open U) : is_open ({a} + U) := 
begin
  rw [set.singleton_add, set.image_add_left],
  apply is_open.preimage _ hU,
  have h_incl : continuous (λ (b : R), (-a, b)) := continuous.prod_mk 
    (continuous_map.const (-a)).continuous_to_fun continuous_map.id.continuous_to_fun,
  have h_comp :  (λ (b : R), -a + b) = function.comp (λ ( p : R × R), p.1 + p.2)
    (λ (b : R), (-a, b)) := rfl,
  rw h_comp,
  exact continuous.comp has_continuous_add.continuous_add h_incl,
end

lemma is_topological_basis_from_basis_at_zero {B : set (set R)} 
  [hB : is_topological_basis_at_zero B] : 
  topological_space.is_topological_basis {U : set R | ∃ r : R, ∃ V ∈ B, U = {r} + V  } :=   
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { intros U hU,
    rw set.mem_set_of_eq at hU,
    rcases hU with ⟨r, V, hV, hrV⟩,
    rw hrV,
    exact is_open_add_constant r V (hB.h_open V hV)},
  { intros r U hrU hU,
    set V := ({-r} + U) with hV,
    have hV_zero : (0 : R) ∈ V,
    { rw [hV, set.singleton_add, set.image_add_left, set.mem_preimage, neg_neg, add_zero],
      exact hrU, },
    have hV_open : is_open V := is_open_add_constant (-r) U hU,
    rcases (hB.h_nhds V hV_zero hV_open) with ⟨W, hWB, hWV⟩,
    use ({r} + W),
    split,
    { rw set.mem_set_of_eq,
      use [r, W, hWB] },
    split,
    { simp only [set.image_add_left, set.mem_preimage, set.singleton_add, add_left_neg],
      exact hB.h_zero W hWB },
    { have : U = {r} + V,
      { rw [hV, set.singleton_add, set.singleton_add, set.image_add_left, set.image_add_left, 
          neg_neg],
        ext,
        rw [set.mem_preimage, set.mem_preimage, ← add_assoc,add_right_neg, zero_add] },
        rw this,
        intro x,
        repeat { rw [set.singleton_add, set.image_add_left, set.mem_preimage] },
        apply hWV }},
end

--set_option trace.class_instances true
--set_option pp.implicit true
lemma eq_of_eq_basis_at_zero {t₁ t₂ : topological_space R} {tr₁ : @topological_ring R t₁ _}
  {tr₂ : @topological_ring R t₂ _} (B : set (set R)) 
  (hB₁ : @is_topological_basis_at_zero R _ t₁ tr₁ B) 
  (hB₂ : @is_topological_basis_at_zero R _ t₂ tr₂ B) : t₁ = t₂ :=
begin
  let basis := {U : set R | ∃ (r : R) (V : set R) (H : V ∈ B), U = {r} + V},
  rw [@topological_space.is_topological_basis.eq_generate_from R t₁ basis 
    (@is_topological_basis_from_basis_at_zero R _ t₁ tr₁ B hB₁),
    @topological_space.is_topological_basis.eq_generate_from R t₂ basis 
    (@is_topological_basis_from_basis_at_zero R _ t₂ tr₂ B hB₂)],
end

lemma image_topological_basis_at_zero (R₁ : Type*) [ring R₁] [t₁ : topological_space R₁] [topological_ring R₁] (R₂ : Type*) [ring R₂] [t₂ : topological_space R₂] [topological_ring R₂] (f : ring_hom R₁ R₂)
(h_cont : continuous f) (h_open : is_open_map f) :
  is_topological_basis_at_zero { U : set R₂ | ∃ (V : set R₁), is_open V ∧ (0 : R₁) ∈ V  ∧ f '' V = U} := 
begin
  split,
  { intros U hU,
    rw set.mem_set_of_eq at hU,
    rcases hU with ⟨V, hV, -, hUV⟩,
    rw ← hUV,
    apply h_open,
    exact hV,
  },
  { intros U hU,
    rw set.mem_set_of_eq at hU,
    rcases hU with ⟨V, -, hV, hUV⟩,
    rw [← hUV, set.mem_image],
    use [0, hV],
    rw ring_hom.map_zero },
    { intros U hU_zero hU_open,
      use f '' (f⁻¹' U), 
      rw set.mem_set_of_eq,
      use [f⁻¹' U, continuous.is_open_preimage h_cont U hU_open],
      split,
      { rw [set.mem_preimage, ring_hom.map_zero],
        exact hU_zero },
      { refl },
      { intros x hx,
        rw set.mem_image at hx,
        rcases hx with ⟨y, hy, hyx⟩,
        rwa ← hyx }}
end



/- structure filter_basis_at_zero (α : Type*) [add_group α] [topological_space α]
extends filter_basis α :=
  (zero : ∀ {U}, U ∈ sets → (0 : α) ∈ U)
  (is_open : ∀ {U}, U ∈ sets → is_open U)

lemma topological_ring.to_filter_basis_at_zero [t : topological_space R] : filter_basis_at_zero R := 
{ sets := { U : set R | is_open U ∧ (0 : R) ∈ U },
  nonempty :=  ⟨set.univ, t.is_open_univ, set.mem_univ (0 : R)⟩,
  inter_sets := λ U V ⟨hU_open, hU_zero⟩ ⟨hV_open, hV_zero⟩,
    by use [U ∩ V, t.is_open_inter U V hU_open hV_open, set.mem_inter hU_zero hV_zero],
    zero := λ U ⟨hU_open, hU_zero⟩ , hU_zero,
    is_open := λ U ⟨hU_open, hU_zero⟩, hU_open }

lemma is_open_add_constant [t : topological_space R] [tr : topological_ring R] (a : R) (U : set R) (hU : is_open U) : is_open ({a} + U) := sorry -/

/- lemma is_topological_basis_from_filter_basis_at_zero [t : topological_space R] [tr : topological_ring R] : 
  topological_space.is_topological_basis {U : set R | ∃ r : R, ∃ V ∈ (topological_ring.to_filter_basis_at_zero R).sets, U = {r} + V  } :=  -/
/- lemma is_topological_basis_from__basis_at_zero [t : topological_space R] [tr : topological_ring R] : 
  topological_space.is_topological_basis {U : set R | ∃ r : R, ∃ V ∈ (𝓝 (0 : R)), U = {r} + V  } := 
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { intros U hU,
    rw set.mem_set_of_eq at hU,
    rcases hU with ⟨r, V, hV, hrV⟩,
    rw hrV,
    exact is_open_add_constant R r V (B.is_open hV)},
  { intros r U hrU hU,
    use U,
    split,
    { rw set.mem_set_of_eq,
      use [r, ({-r} + U)],
      split,
      {  },
      rw [set.singleton_add, set.singleton_add, set.image_add_left, set.image_add_left, neg_neg],
      ext,
      rw [set.mem_preimage, set.mem_preimage, ← add_assoc,add_right_neg, zero_add] },
    use hrU,
    }
end -/

/- is_topological_basis_of_open_of_nhds {s : set (set α)}
  (h_open : ∀ u ∈ s, is_open u)
  (h_nhds : ∀(a:α) (u : set α), a ∈ u → is_open u → ∃v ∈ s, a ∈ v ∧ v ⊆ u) :
  is_topological_basis s -/