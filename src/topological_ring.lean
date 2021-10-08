import algebra.pointwise
import order.filter.bases
import topology.algebra.filter_basis
import topology.algebra.localization
import topology.algebra.ring
import topology.continuous_function.basic

noncomputable theory
open nat 

open_locale classical topological_space filter

section topological_ring

variables {R : Type*} [ring R] [t : topological_space R] [tr : topological_ring R]
include t tr

attribute [instance] set.has_mul set.has_add

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

lemma image_topological_basis_at_zero {S : Type*} [ring S] [t₂ : topological_space S]
  [topological_ring S] (f : ring_hom R S) (h_cont : continuous f) (h_open : is_open_map f) :
  is_topological_basis_at_zero 
    { U : set S | ∃ (V : set R), is_open V ∧ (0 : R) ∈ V  ∧ f '' V = U} := 
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

end topological_ring

section ring_filter_basis
attribute [instance] set.has_mul set.has_add

variables (R : Type*) [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S] [algebra R S]
  [is_localization M S] (B : ring_filter_basis R)

private def localization.sets : set (set S) := 
  {(is_localization.to_localization_map M S).to_map '' U | U ∈ B.sets}

private lemma localization.sets.nonempty : set.nonempty (localization.sets R M S B) := 
begin
    cases (B.nonempty) with U hU,
    use [(is_localization.to_localization_map M S).to_map '' U, U, hU],
end

private lemma mul_left' (h : ∀  (m ∈ M) (U : set R), (U ∈ B.sets) → ({m}*U) ∈ B.sets) :
  ∀ (x₀ : S) {U : set S}, U ∈ (localization.sets R M S B) → (∃ (V : set S) 
  (H : V ∈ (localization.sets R M S B)), V ⊆ (λ (x : S), x₀ * x) ⁻¹' U) := 
begin
    rintros x U ⟨V, hVsets, hUV⟩,
    rcases (is_localization.mk'_surjective M x) with ⟨r, s, hx⟩,
    rcases B.mul_left r (h s.1 s.2 V hVsets) with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros y hy,
    rcases hy with ⟨yr, hyrW, hyr_loc⟩,
    have h1 := hVW hyrW,
    rw [set.mem_preimage, set.singleton_mul, set.mem_image, subtype.val_eq_coe] at h1,
    rcases h1 with ⟨r1, hr1V, hxy⟩,
    rw [set.mem_preimage, ← hUV, set.mem_image, ← hx, ← hyr_loc],
    use [r1, hr1V],
    rw [is_localization.to_localization_map_to_map, ring_hom.coe_monoid_hom,
      is_localization.mk'_eq_mul_mk'_one _ _, ← one_mul (algebra_map R S r1),
      ← is_localization.mk'_self S s.2, is_localization.mk'_eq_mul_mk'_one _ _],
    simp only [subtype.val_eq_coe],
    rw [set_like.eta, mul_comm (algebra_map R S s), mul_assoc, mul_comm (algebra_map R S r),
      mul_assoc, algebra_map, ← ring_hom.map_mul, ← ring_hom.map_mul, hxy],
  end

instance localization.ring_filter_basis 
  (h : ∀  (m ∈ M) (U : set R), (U ∈ B.sets) → ({m}*U) ∈ B.sets) : ring_filter_basis S := 
{ sets := {(is_localization.to_localization_map M S).to_map '' U | U ∈ B.sets},
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
  zero' := 
  begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    have hVzero : (0 : R) ∈ V := add_group_filter_basis.zero hVsets,
    rw [← hUV, set.mem_image],
    use [(0 : R), hVzero],
    rw [is_localization.to_localization_map_to_map, ring_hom.coe_monoid_hom, ring_hom.map_zero],
  end,
  add' := 
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
    rw [is_localization.to_localization_map_to_map, algebra_map, ring_hom.coe_monoid_hom]
      at hr1 hr2 ⊢,
    rwa [ring_hom.map_add, hr1, hr2],
  end,
  neg' := begin
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
  conj' := begin
    intros x U hU,
    use [U, hU],
    simp_rw [← sub_eq_add_neg, add_sub_cancel' x _, set.preimage_id'],
  end,
  mul' := 
  begin
    intros U hU,
    rcases hU with ⟨V, hVsets, hUV⟩,
    rcases B.mul hVsets with ⟨W, hWsets, hVW⟩,
    use [(is_localization.to_localization_map M S).to_map '' W, W, hWsets],
    intros x hx,
    rw set.mem_mul at hx,
    rcases hx with ⟨x1, x2, ⟨r1, hr1W, hr1⟩, ⟨r2, hr2W, hr2⟩, hmul⟩,
    rw [← hUV, set.mem_image],
    use (r1 * r2),
    split,
    { apply hVW,
    use [r1, r2, hr1W, hr2W]},
    rw [is_localization.to_localization_map_to_map, algebra_map, ring_hom.coe_monoid_hom]
      at hr1 hr2 ⊢,
    rwa [ring_hom.map_mul, hr1, hr2],
  end,
  mul_left' := mul_left' R M S B h,
  mul_right' := 
  begin
    intros x U hU,
    have h1 : (λ y, y*x) = (λ y, x*y) := by {ext y, rw mul_comm},
    rw h1,
    exact mul_left' R M S B h x hU,
  end }

private def pi.ring_filter_basis.sets {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) :
  set (set (Π i, X i)) :=
{S : set (Π i, X i) | ∃ (U : Π i, set (X i)) (F : finset ι),
  (∀ i, i ∈ F → (U i) ∈ (T i).sets) ∧ S = (F : set ι).pi U }


private lemma pi.ring_filter_basis.nonempty {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) :
  (pi.ring_filter_basis.sets T).nonempty := 
begin
  set S :=  λ i : ι, classical.some (T i).nonempty with hS_def,
  use ((∅ : set ι).pi S),
  rw [pi.ring_filter_basis.sets, set.mem_set_of_eq],
  use [S, (∅ : finset ι)],
  split,
  { intros i hi,
    exfalso,
    exact finset.not_mem_empty i hi },
  rw finset.coe_empty,
end

private lemma pi.ring_filter_basis.inter_sets {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ {U V : set (Π (i : ι), X i)}, U ∈ pi.ring_filter_basis.sets T →
  V ∈ pi.ring_filter_basis.sets T →
  (∃ (W : set (Π (i : ι), X i)) (H : W ∈ pi.ring_filter_basis.sets T), W ⊆ U ∩ V) := 
begin
  rintros U V ⟨SU, FU, h_restrU, hSFU⟩ ⟨SV, FV, h_restrV, hSFV⟩,
  set W := λ (i : ι), if hiF : i ∈ (FU ∩ FV) then
    classical.some (filter_basis.inter_sets (T i).to_add_group_filter_basis.to_filter_basis
      (h_restrU i (finset.mem_of_subset (finset.inter_subset_left FU FV) hiF))
      (h_restrV i (finset.mem_of_subset (finset.inter_subset_right FU FV) hiF))) 
    else if hiFU : i ∈ FU then SU i else if hiFV : i ∈ FV then SV i else set.univ with hW,
  have hW_sets : ∀ (i : ι), (i ∈ FU ∪ FV) → (W i) ∈ add_group_filter_basis.to_filter_basis.sets,
  { intros i hiF,
    rw hW, dsimp only,
    rw [finset.union_eq_sdiff_union_sdiff_union_inter, finset.mem_union, finset.mem_union] at hiF,
    cases hiF with hi_diff hi_inter,
    cases hi_diff with hiFU hiFV,
    { rw finset.mem_sdiff at hiFU,
      have hnot_inter : i ∉ FU ∩ FV, 
      { rw [finset.mem_inter, not_and],
        intro h, exact hiFU.right }, 
      rw [dif_neg hnot_inter, dif_pos hiFU.left],
      exact h_restrU i hiFU.left },
    { rw finset.mem_sdiff at hiFV,
      have hnot_inter : i ∉ FU ∩ FV, 
      { rw [finset.mem_inter, not_and'],
            intro h, exact hiFV.right }, 
          rw [dif_neg hnot_inter, dif_neg hiFV.right,
           dif_pos hiFV.left],
          exact h_restrV i hiFV.left },
    { rw dif_pos hi_inter,
      cases (classical.indefinite_description (λ (V : set (X i)),
        ∃ (H : V ∈ add_group_filter_basis.to_filter_basis.sets), V  ⊆ SU i ∩ SV i) _).property
        with hW_sets hW_inter,
      exact hW_sets, }},
  have hW_subset_U_i : ∀ (i : ι), (i ∈ FU) → (W i) ⊆ (SU i),
  { intros i hiFU,
    rw hW, dsimp only,
    by_cases hiFV : i ∈ FV,
    { rw dif_pos (finset.mem_inter_of_mem hiFU hiFV),
      cases (classical.indefinite_description (λ (V : set (X i)),
        ∃ (H : V ∈ add_group_filter_basis.to_filter_basis.sets), V  ⊆ SU i ∩ SV i) _).property
        with hW_sets hW_inter,
      exact set.subset.trans hW_inter (set.inter_subset_left (SU i) (SV i)) },
    { have hnot_inter : i ∉ FU ∩ FV, 
      { rw [finset.mem_inter, not_and],
        intro h, exact hiFV }, 
      rw [dif_neg hnot_inter, dif_pos hiFU] }},
  have hW_subset_V_i : ∀ (i : ι), (i ∈ FV) → (W i) ⊆ (SV i),
  { intros i hiFV,
    rw hW, dsimp only,
    by_cases hiFU : i ∈ FU,
    { rw dif_pos (finset.mem_inter_of_mem hiFU hiFV),
      cases (classical.indefinite_description (λ (V : set (X i)),
        ∃ (H : V ∈ add_group_filter_basis.to_filter_basis.sets), V  ⊆ SU i ∩ SV i) _).property
        with hW_sets hW_inter,
      exact set.subset.trans hW_inter (set.inter_subset_right (SU i) (SV i)) },
  { have hnot_inter : i ∉ FU ∩ FV, 
    { rw [finset.mem_inter, not_and'],
      intro h, exact hiFU }, 
    rw [dif_neg hnot_inter, dif_neg hiFU, dif_pos hiFV] }},
    use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ FU ∪ FV → (p i) ∈ (W i) }, W, FU ∪ FV],
  split,
  { exact hW_sets },
  { refl },
  { rw [hSFU, hSFV],
    intros x hx,
    apply set.mem_inter,
    { rw set.mem_pi, intros i hiF,
      apply hW_subset_U_i i hiF,
      exact hx i (finset.mem_union_left FV (finset.mem_coe.mp hiF))},
    { rw set.mem_pi, intros i hiF,
      apply hW_subset_V_i i hiF,
      exact hx i (finset.mem_union_right FU (finset.mem_coe.mp hiF))}},
end

private lemma pi.ring_filter_basis.zero {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) :
  ∀ {U : set (Π (i : ι), X i)}, U ∈ pi.ring_filter_basis.sets T → (0 : Π (i : ι), X i) ∈ U := 
 begin
  intros U hU,
  rw [pi.ring_filter_basis.sets, set.mem_set_of_eq] at hU,
  rcases hU with ⟨S, F, h_restr, hSF⟩,
  rw hSF,
  simp only [set.mem_pi, pi.zero_apply, finset.mem_coe],
  intros i hi,
  exact add_group_filter_basis.zero (h_restr i hi),
end

private lemma pi.ring_filter_basis.add {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ {U : set (Π (i : ι), X i)},
    U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i))
       (H : V ∈ pi.ring_filter_basis.sets T),
       V + V ⊆ U) := 
begin
  rintros U ⟨S, F, h_restr, hSF⟩,
  set V := λ (i : ι), if hiF: i ∈ F then classical.some (add_group_filter_basis.add (h_restr i hiF))
    else set.univ with hV,
  have hV_property : ∀ (i ∈ F), (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) + (V i) ⊆ (S i),
  { intros i hiF,
    rw hV, 
    dsimp only,
    rw dif_pos hiF,
    obtain ⟨hV_sets, hV_add⟩  :=  classical.some_spec (add_group_filter_basis.add (h_restr i hiF)),
    exact ⟨hV_sets, hV_add⟩,},
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
  λ i hiF, (hV_property i hiF).left,
  have hV_add : ∀ (i : ι), (i ∈ F) → (V i) + (V i) ⊆ (S i) := λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    rintros x ⟨y, z, hy, hz, hadd⟩,
    rw set.mem_set_of_eq at hy hz,
    rw [set.mem_pi, ← hadd],
    intros i hiF,
    rw pi.add_apply,
    apply hV_add i hiF,
    use [y i, z i, hy i hiF, hz i hiF] }
end

private lemma pi.ring_filter_basis.neg {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ {U : set (Π (i : ι), X i)}, U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i)) (H : V ∈ pi.ring_filter_basis.sets T), V ⊆ (λ x, -x)⁻¹' U) := 
begin
  rintros U ⟨S, F, h_restr, hSF⟩,
  set V : (Π i, set (X i)) := λ (i : ι), if hiF : i ∈ F then
    classical.some (add_group_filter_basis.neg (h_restr i hiF)) else set.univ with hV,
  have hV_property : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) ⊆ (λ (x : X i), -x) ⁻¹' S i,
  { intros i hiF,
    rw hV,
    dsimp only,
    rw dif_pos hiF,
    obtain ⟨hV_sets, hV_neg⟩ := classical.some_spec (add_group_filter_basis.neg (h_restr i hiF)),
    exact ⟨hV_sets, hV_neg⟩ },
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
  λ i hiF, (hV_property i hiF).left,
  have hV_neg : ∀ (i : ι), i ∈ F → (V i) ⊆ (λ (x : X i), -x) ⁻¹' (S i) :=
  λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    rintros x hx,
    rw [set.mem_preimage, set.mem_pi],
    intros i hiF,
    rw [pi.neg_apply, ← set.mem_neg],
    apply hV_neg i hiF,
    exact hx i hiF }
end

private lemma pi.ring_filter_basis.conj {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ (x₀ : Π (i : ι), X i) (U : set (Π (i : ι), X i)), U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i)) (H : V ∈ pi.ring_filter_basis.sets T),
       V ⊆ (λ (x : Π (i : ι), X i), x₀ + x + - x₀) ⁻¹' U) :=
begin
  rintros x U ⟨S, F, h_restr, hSF⟩,
  set V := λ (i : ι), if hiF : i ∈ F then
    classical.some(add_group_filter_basis.conj' (x i) (h_restr i hiF)) else set.univ with hV,
  have hV_property : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) ⊆ (λ (y : X i), x i + y + - x i) ⁻¹' (S i),
  { intros i hiF,
    rw hV, 
    dsimp only,
    rw [dif_pos hiF],
    obtain ⟨hV_sets, hV_conj⟩ :=
    classical.some_spec (add_group_filter_basis.conj' (x i)(h_restr i hiF)),
    exact ⟨hV_sets, hV_conj⟩, },
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
  λ i hiF, (hV_property i hiF).left,
  have hV_conj : ∀ (i : ι), (i ∈ F) → (V i) ⊆ (λ (x_1 : X i), x i + x_1 + - x i) ⁻¹' (S i) :=
  λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    intros x hx,
    rw set.mem_set_of_eq at hx,
    rw [set.mem_preimage, set.mem_pi],
    intros i hiF,
    apply hV_conj i hiF,
    exact hx i hiF }
end

private lemma pi.ring_filter_basis.mul {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ {U : set (Π (i : ι), X i)},
    U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i))
       (H : V ∈ pi.ring_filter_basis.sets T),
       V * V ⊆ U) := 
begin
  rintros U ⟨S, F, h_restr, hSF⟩,
  set V := λ (i : ι), if hiF : i ∈ F then classical.some((T i).mul (h_restr i hiF))
    else set.univ with hV,
  have hV_property : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) * (V i) ⊆ (S i),
  { intros i hiF,
    rw hV, 
    dsimp only,
    rw dif_pos hiF,
    obtain ⟨hV_sets, hV_mul⟩ := classical.some_spec ((T i).mul (h_restr i hiF)),
    exact ⟨hV_sets, hV_mul⟩ },
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
  λ i hiF, (hV_property i hiF).left,
  have hV_mul : ∀ (i : ι), (i ∈ F) → (V i) * (V i) ⊆ (S i) := λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    rintros x ⟨y, z, hy, hz, hadd⟩,
    rw set.mem_set_of_eq at hy hz,
    rw [set.mem_pi, ← hadd],
    intros i hiF,
    rw pi.mul_apply,
    apply hV_mul i hiF,
    use [y i, z i, hy i hiF, hz i hiF] }
end

private lemma pi.ring_filter_basis.mul_left {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ (x₀ : Π (i : ι), X i) (U : set (Π (i : ι), X i)), U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i)) (H : V ∈ pi.ring_filter_basis.sets T),
       V ⊆ (λ (x : Π (i : ι), X i), x₀ * x) ⁻¹' U) := 
begin
  rintros x U ⟨S, F, h_restr, hSF⟩,
  set V : Π i : ι, set (X i) := λ (i : ι), if hiF : i ∈ F then
    classical.some((T i).mul_left (x i) (h_restr i hiF)) else set.univ with hV,
  have hV_property : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) ⊆ (λ (y : X i), x i * y) ⁻¹' (S i),
  { intros i hiF,
    rw hV, 
    dsimp only,
    rw dif_pos hiF,
    obtain ⟨hV_sets, hV_mul_left⟩ :=
    classical.some_spec((T i).mul_left (x i) (h_restr i hiF)),
    exact ⟨hV_sets, hV_mul_left⟩, },
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
  λ i hiF, (hV_property i hiF).left,
  have hV_mul_left : ∀ (i : ι), (i ∈ F) → (V i) ⊆ (λ (x_1 : X i), x i * x_1) ⁻¹' (S i) :=
  λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    intros x hx,
    rw set.mem_set_of_eq at hx,
    rw [set.mem_preimage, set.mem_pi],
    intros i hiF,
    apply hV_mul_left i hiF,
    exact hx i hiF }
end

private lemma pi.ring_filter_basis.mul_right {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
  ∀ (x₀ : Π (i : ι), X i) (U : set (Π (i : ι), X i)), U ∈ pi.ring_filter_basis.sets T →
    (∃ (V : set (Π (i : ι), X i)) (H : V ∈ pi.ring_filter_basis.sets T),
       V ⊆ (λ (x : Π (i : ι), X i), x * x₀) ⁻¹' U) := 
begin
  rintros x U ⟨S, F, h_restr, hSF⟩,
  set V : Π i : ι, set (X i) := λ (i : ι), if hiF : i ∈ F then
    classical.some((T i).mul_right (x i) (h_restr i hiF)) else set.univ with hV,
  have hV_property : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets ∧
    (V i) ⊆ (λ (y : X i), y * x i) ⁻¹' (S i),
  { intros i hiF,
    rw hV, 
    dsimp only,
    rw dif_pos hiF,
    obtain ⟨hV_sets, hV_mul_right⟩ :=
      classical.some_spec((T i).mul_right (x i) (h_restr i hiF)),
    exact ⟨hV_sets, hV_mul_right⟩, },
  have hV_sets : ∀ (i : ι), (i ∈ F) → (V i) ∈ add_group_filter_basis.to_filter_basis.sets :=
    λ i hiF, (hV_property i hiF).left,
  have hV_mul_right : ∀ (i : ι), (i ∈ F) → (V i) ⊆ (λ (x_1 : X i), x_1 * x i) ⁻¹' (S i) :=
    λ i hiF, (hV_property i hiF).right,
  clear hV_property,
  use [{ p : (Π i : ι, X i) | ∀ (i : ι), i ∈ F → (p i) ∈ (V i) }, V, F],
  { split,
    { intros i hiF,
      exact hV_sets i hiF },
    { refl }},
  { rw hSF,
    intros x hx,
    rw set.mem_set_of_eq at hx,
    rw [set.mem_preimage, set.mem_pi],
    intros i hiF,
    apply hV_mul_right i hiF,
    exact hx i hiF }
end

instance pi.ring_filter_basis {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (T : Π i, ring_filter_basis (X i)) :
  ring_filter_basis (Π i, X i) := 
{ sets       := pi.ring_filter_basis.sets T,
  nonempty   := pi.ring_filter_basis.nonempty T,
  inter_sets := λ U V hU hV, pi.ring_filter_basis.inter_sets T hU hV,
  zero'      := λ U hU, pi.ring_filter_basis.zero T hU,
  add'       := λ U hU, pi.ring_filter_basis.add T hU,
  neg'       := λ U hU, pi.ring_filter_basis.neg T hU,
  conj'      := λ x U hU, pi.ring_filter_basis.conj T x U hU,
  mul'       := λ U hU, pi.ring_filter_basis.mul T hU,
  mul_left'  := λ x U hU, pi.ring_filter_basis.mul_left T x U hU,
  mul_right' := λ x U hU, pi.ring_filter_basis.mul_right T x U hU, }

  /- The product topology on Π i, X i equals the topology associated to pi.ring_filter_basis -/

lemma pi_eq_ring_filter_basis_topology {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  [∀ i, topological_space (X i)] [∀ i, topological_ring (X i)] (B : 
  ring_filter_basis (Π i, X i)) : Pi.topological_space = B.topology
:= 
begin
  apply le_antisymm,
  { intros U hU,
  sorry,
  },
  { have hB : B.topology = topological_space.mk_of_nhds _ := rfl,
    intros U hU,
    rw hB,
    simp only,
    intros a ha,
    sorry }
end

  end ring_filter_basis
