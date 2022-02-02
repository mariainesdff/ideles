/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
import field_theory.galois
import topology.algebra.filter_basis

open_locale classical

/-!
# Krull topology 

We define the Krull topology on `L ≃ₐ[K] L` for an arbitrary field extension `L/K`. In order to do this,
we first define a `group_filter_basis` on `L ≃ₐ[K] L`, whose sets are `E.fixing_subgroup` for all 
intermediate fields `E` with `E/K` finite dimensional. 

## Main Definitions 

- `finite_exts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixed_by_finite K L`. Given a field extension `L/K`, `fixed_by_finite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `gal_basis K L`. Given a field extension `L/K`, this is the filter basis on `L ≃ₐ[K] L` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite. 

- `gal_group_basis K L`. This is the same as `gal_basis K L`, but with the added structure 
  that it is a group filter basis on `L ≃ₐ[K] L`, rather than just a filter basis. 

- `krull_topology K L`. Given a field extension `L/K`, this is the topology on `L ≃ₐ[K] L`, induced by 
  the group filter basis `gal_group_basis K L`. 

## Notations 

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field `E`. 
  That is, `Gal(L/E)` is the subgroup of `L ≃ₐ[K] L` consisting of automorphisms that fix every 
  element of `E`. In particular, we distinguish between `L ≃ₐ[E] L` and `Gal(L/E)`, since the 
  former is defined to be a subgroup of `L ≃ₐ[K] L`, while the latter is a group in its own right. 

## Implementation Notes 

- `krull_topology K L` is defined as an instance for type class inference. 
-/


/-- Mapping intermediate fields along algebra equivalences preserves the partial order -/
lemma intermediate_field.map_mono {K L M : Type*} [field K] [field L] [field M]
  [algebra K L] [algebra K M] {E1 E2 : intermediate_field K L}
  (e : L ≃ₐ[K] M) (h12 : E1 ≤ E2) : 
E1.map e.to_alg_hom ≤ E2.map e.to_alg_hom :=
set.image_subset e h12 

/-- Mapping intermediate fields along the identity does not change them -/
lemma intermediate_field.map_id {K L : Type*} [field K] [field L] [algebra K L] 
{E : intermediate_field K L} : 
E.map (alg_hom.id K L) = E :=
set_like.coe_injective $ set.image_id _

-- this and the next few lemmas would make some nice PR's
@[simps] def ring_equiv.subsemiring_map {R S : Type*} [non_assoc_semiring R] [non_assoc_semiring S] 
 (e : R ≃+* S) (s : subsemiring R) :
  s ≃+* s.map e.to_ring_hom :=
{ ..e.to_add_equiv.add_submonoid_map s.to_add_submonoid,
  ..e.to_mul_equiv.submonoid_map s.to_submonoid }

@[simps] def ring_equiv.subring_map {R S : Type*} [ring R] [ring S] (e : R ≃+* S) (s : subring R) :
  s ≃+* s.map e.to_ring_hom :=
e.subsemiring_map s.to_subsemiring

@[simps] def alg_equiv.subalgebra_map {R A B : Type*} [comm_semiring R] [semiring A]
  [semiring B] [algebra R A] [algebra R B] (e : A ≃ₐ[R] B) (S : subalgebra R A) :
  S ≃ₐ[R] (S.map e.to_alg_hom) :=
{ commutes' := λ r, by { ext, simp },
  ..e.to_ring_equiv.subsemiring_map S.to_subsemiring }

@[simps] def alg_equiv.intermediate_field_map {K L M : Type*} [field K] [field L] [field M]
  [algebra K L] [algebra K M] (e : L ≃ₐ[K] M) (E : intermediate_field K L) :
  E ≃ₐ[K] (E.map e.to_alg_hom) :=
e.subalgebra_map E.to_subalgebra


/-- Mapping a finite dimensional intermediate field along an algebra equivalence gives 
  a finite-dimensional intermediate field. -/
lemma im_finite_dimensional {K L : Type*} [field K] [field L] [algebra K L]
{E : intermediate_field K L} (σ : L ≃ₐ[K] L) (h_findim : finite_dimensional K E): 
finite_dimensional K (E.map σ.to_alg_hom) :=
linear_equiv.finite_dimensional (alg_equiv.intermediate_field_map σ E).to_linear_equiv

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts (K : Type*) [field K] (L : Type*) [field L] [algebra K L] : 
set (intermediate_field K L) :=
{E | finite_dimensional K E}

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `L ≃ₐ[K] L`, where `E/K` is finite -/
def fixed_by_finite (K L : Type*) [field K] [field L] [algebra K L]: set (subgroup (L ≃ₐ[K] L)) :=
intermediate_field.fixing_subgroup '' (finite_exts K L)

/-- For an field extension `L/K`, the intermediate field `K` is finite-dimensional over `K` -/
lemma intermediate_field.finite_dimensional_bot (K L : Type*) [field K] 
  [field L] [algebra K L] : finite_dimensional K (⊥ : intermediate_field K L) :=
finite_dimensional_of_dim_eq_one intermediate_field.dim_bot 

/-- This lemma says that `Gal(L/K) = L ≃ₐ[K] L` -/
lemma intermediate_field.fixing_subgroup.bot {K L : Type*} [field K] 
  [field L] [algebra K L] : 
  intermediate_field.fixing_subgroup (⊥ : intermediate_field K L) = ⊤ :=
begin
  ext f,
  refine ⟨λ _, subgroup.mem_top _, λ _, _⟩,
  rintro ⟨x, hx⟩,
  rw intermediate_field.mem_bot at hx,
  rcases hx with ⟨y, rfl⟩,
  exact f.commutes y,
end

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixed_by_finite K L` -/
lemma top_fixed_by_finite {K L : Type*} [field K] [field L] [algebra K L] : 
  ⊤ ∈ fixed_by_finite K L :=
⟨⊥, intermediate_field.finite_dimensional_bot K L, intermediate_field.fixing_subgroup.bot⟩

/-- If `E1` and `E2` are finite-dimensional intermediate fields, then so is their compositum. 
  This rephrases a result already in mathlib so that it is compatible with our type classes -/
lemma finite_dimensional_sup {K L: Type*} [field K] [field L] [algebra K L] 
  (E1 E2 : intermediate_field K L) (h1 : finite_dimensional K E1)
  (h2 : finite_dimensional K E2) : finite_dimensional K ↥(E1 ⊔ E2) :=
by exactI intermediate_field.finite_dimensional_sup E1 E2

/-- An element of `L ≃ₐ[K] L` is in `Gal(L/E)` if and only if it fixes every element of `E`-/
lemma mem_fixing_subgroup_iff {K L : Type*} [field K] [field L] [algebra K L] 
(E : intermediate_field K L) (σ : (L ≃ₐ[K] L)): σ ∈ E.fixing_subgroup ↔  
∀ (x : L), x ∈ E → σ x = x :=
⟨λ hσ x hx, hσ ⟨x, hx⟩, λ h ⟨x, hx⟩, h x hx⟩

/-- The map `E ↦ Gal(L/E)` is inclusion-reversing -/
lemma intermediate_field.fixing_subgroup.antimono {K L : Type*} [field K] [field L] [algebra K L] 
{E1 E2 : intermediate_field K L} (h12 : E1 ≤ E2) : E2.fixing_subgroup ≤ E1.fixing_subgroup :=
begin
  rintro σ hσ ⟨x, hx⟩,
  exact hσ ⟨x, h12 hx⟩,
end

/-- Given a field extension `L/K`, `gal_basis K L` is the filter basis on `L ≃ₐ[K] L` whose sets are 
  `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional -/
def gal_basis (K L : Type*) [field K] [field L] [algebra K L] : filter_basis (L ≃ₐ[K] L) :=
{ sets := subgroup.carrier '' (fixed_by_finite K L),
  nonempty := ⟨⊤, ⊤, top_fixed_by_finite, rfl⟩,
  inter_sets :=
  begin
    rintros X Y ⟨H1, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨H2, ⟨E2, h_E2, rfl⟩, rfl⟩,
    use (intermediate_field.fixing_subgroup (E1 ⊔ E2)).carrier,
    refine ⟨⟨_, ⟨_, finite_dimensional_sup E1 E2 h_E1 h_E2, rfl⟩, rfl⟩, _⟩,
    rw set.subset_inter_iff,
    exact ⟨intermediate_field.fixing_subgroup.antimono le_sup_left,
      intermediate_field.fixing_subgroup.antimono le_sup_right⟩,
  end
}

/-- A subset of `L ≃ₐ[K] L` is a member of `gal_basis K L` if and only if it is the underlying set
  of `Gal(L/E)` for some finite subextension `E/K`-/
lemma mem_gal_basis_iff (K L : Type*) [field K] [field L] [algebra K L] 
(U : set (L ≃ₐ[K] L)) : U ∈ gal_basis K L ↔ U ∈ subgroup.carrier '' (fixed_by_finite K L) :=
iff.rfl

/-- For a field extension `L/K`, `gal_group_basis K L` is the group filter basis on `L ≃ₐ[K] L` whose 
  sets are `Gal(L/E)` for finite subextensions `E/K` -/
def gal_group_basis (K L : Type*) [field K] [field L] [algebra K L] : 
group_filter_basis (L ≃ₐ[K] L) :=
{ to_filter_basis := gal_basis K L,
  one' := λ U ⟨H, hH, h2⟩, h2 ▸ H.one_mem,
  mul' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    rintros x ⟨a, b, haH, hbH, rfl⟩,
    exact H.mul_mem haH hbH,
  end⟩,
  inv' := λ U hU, ⟨U, hU, begin
    rcases hU with ⟨H, hH, rfl⟩,
    exact H.inv_mem',
  end⟩,
  conj' := 
  begin
    rintros σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩,
    let F : intermediate_field K L := E.map (σ.symm.to_alg_hom),
    refine ⟨F.fixing_subgroup.carrier, ⟨⟨F.fixing_subgroup, ⟨F, 
      im_finite_dimensional σ.symm hE, rfl⟩, rfl⟩, λ g hg, _⟩⟩,
    change σ * g * σ⁻¹ ∈ E.fixing_subgroup,
    rw mem_fixing_subgroup_iff,
    intros x hx,
    change σ(g(σ⁻¹ x)) = x,
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by {dsimp, rw ← alg_equiv.inv_fun_eq_symm, refl }⟩,
    have h_g_fix : g (σ⁻¹ x) = (σ⁻¹ x),
    { rw [subgroup.mem_carrier, mem_fixing_subgroup_iff F g] at hg,
      exact hg (σ⁻¹ x) h_in_F,
    },
    rw h_g_fix,
    change σ(σ⁻¹ x) = x,
    exact alg_equiv.apply_symm_apply σ x,
  end
}

/-- For a field extension `L/K`, `krull_topology K L` is the topological space structure on 
  `L ≃ₐ[K] L` induced by the group filter basis `gal_group_basis K L` -/
@[instance]
def krull_topology (K L : Type*) [field K] [field L] [algebra K L] :
topological_space (L ≃ₐ[K] L) :=
group_filter_basis.topology (gal_group_basis K L)

/-- For a field extension `L/K`, `krull_topological_group K L` is the topological group consisting of
  `L ≃ₐ[K] L`, together with the Krull topology `krull_topology K L` -/
def krull_topological_group (K L : Type*) [field K] [field L] [algebra K L] :
topological_group (L ≃ₐ[K] L) :=
group_filter_basis.is_topological_group (gal_group_basis K L)


