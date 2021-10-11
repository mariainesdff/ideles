import topology.algebra.filter_basis
import topology.algebra.ring

noncomputable theory
open nat set

open_locale classical topological_space filter

attribute [instance] set.has_mul set.has_add

lemma nhds_nonempty {α : Type*} [topological_space α] (a : α) : set.nonempty (nhds a).sets :=
begin
  use set.univ,
  rw [filter.mem_sets, mem_nhds_iff],
  use [set.univ, rfl.subset, is_open_univ],
end

instance nhds_zero_add_group_filter_basis {X : Type*} [add_group X] [topological_space X] [tg: topological_add_group X] : add_group_filter_basis X := 
{ sets := (nhds (0 : X)).sets,
  nonempty := nhds_nonempty (0 : X),
  inter_sets := λ S T hS hT, ⟨S ∩ T, (nhds (0 : X)).inter_sets hS hT, rfl.subset⟩,
  zero' := λ S hS, mem_of_mem_nhds (filter.mem_sets.mp hS),
  add' := λ S hS,
  begin
    --use [S, hS],
    rw [filter.mem_sets, mem_nhds_iff] at hS,
    rcases hS with ⟨T, hST, hT_open, hT_zero⟩,
    sorry
  end,
  neg' := λ S hS,
  begin
    use (λ (x : X), -x) ⁻¹' S,
    split,
    { rw [filter.mem_sets, mem_nhds_iff] at hS ⊢,
      rcases hS with ⟨T, hST, hT_open, hT_zero⟩,
      use (λ (x : X), -x) ⁻¹' T,
      split,
      { rw [neg_preimage, neg_preimage, neg_subset_neg],
        exact hST },
      { split,
        { exact (continuous_def.mp tg.continuous_neg) T hT_open, },
        { rw [mem_preimage, neg_zero], exact hT_zero, }}},
    { refl },
  end,
  conj' := λ x S hS,
  begin
    sorry,
  end, }


instance nhds_zero_ring_filter_basis {X : Type*} [ring X] [topological_space X] : ring_filter_basis X := 
{ --sets := (nhds (0 : X)).sets,
  mul' := sorry,
  mul_left' := sorry,
  mul_right' := sorry,
  .. nhds_zero_add_group_filter_basis }



private def pi.ring_filter_basis.sets {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)]
  (T : Π i, ring_filter_basis (X i)) :
  set (set (Π i, X i)) :=
{S : set (Π i, X i) | ∃ (U : Π i, set (X i)) (F : finset ι),
  (∀ i, i ∈ F → (U i) ∈ (T i).sets) ∧ S = (F : set ι).pi U }


private lemma pi.ring_filter_basis.nonempty {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) :
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

private lemma pi.ring_filter_basis.inter_sets {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.zero {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) :
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

private lemma pi.ring_filter_basis.add {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.neg {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.conj {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.mul {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.mul_left {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

private lemma pi.ring_filter_basis.mul_right {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) : 
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

instance pi.ring_filter_basis {ι : Type*} {X : ι → Type*} [∀ i, ring (X i)] (T : Π i, ring_filter_basis (X i)) :
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
