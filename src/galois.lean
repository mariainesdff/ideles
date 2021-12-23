import field_theory.galois
import field_theory.is_alg_closed.algebraic_closure
import topology.algebra.group
import number_theory.number_field
import group_theory.abelianization

variables (K: Type*) [field K] [number_field K] (L : Type*) [field L] [algebra K L]

/-- Given a field extension `L/K`, `finite_exts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite -/
def finite_exts : set (intermediate_field K L) := λ E, finite_dimensional K E

/-- Given a field extension `L/K`, `fixed_by_finite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite -/
def fixed_by_finite : set (set (L ≃ₐ[K] L)) :=
subgroup.carrier '' (intermediate_field.fixing_subgroup '' (finite_exts K L))

/-- Given a field extension `L/K`, `top_on_gg K L` is the coarsest
topology on `Gal(L/K)` such that the subgroups `Gal(L/E)` are
open subsets -/
def group_top_on_gg : group_topology (L ≃ₐ[K] L) :=
Sup (λ (a : group_topology (L ≃ₐ[K] L)), ∀ (U ∈ (fixed_by_finite K L)), 
  topological_space.is_open a.to_topological_space U)

def G_K := ((algebraic_closure K) ≃ₐ[K] (algebraic_closure K))
noncomputable instance : group (G_K K) := alg_equiv.aut
noncomputable instance : topological_space (G_K K) :=
(group_top_on_gg K (algebraic_closure K)).to_topological_space
instance : topological_group (G_K K) :=
(group_top_on_gg K (algebraic_closure K)).to_topological_group

lemma topological_group.continuous_conj {G : Type*} [topological_space G] [group G]
  [topological_group G] (g : G) : continuous  (λ (h : G), g*h*g⁻¹) := 
begin
  have h_comp : (λ (h : G), g*h*g⁻¹) = (λ (h : G), g*h) ∘ (λ (h : G), h*g⁻¹),
  { ext h,
    rw [function.comp_app, mul_assoc]},
  rw h_comp,
  apply continuous.comp ( continuous_mul_left g) (continuous_mul_right g⁻¹),
end

def subgroup.is_normal_topological_closure {G : Type*} [topological_space G] [group G]
  [topological_group G] (N : subgroup G) [N.normal] :
  (subgroup.topological_closure N).normal := 
{ conj_mem := 
  begin
    intros n hn g,
    apply mem_closure_of_continuous (topological_group.continuous_conj g) hn,
    intros m hm,    
    apply subset_closure,
    exact subgroup.normal.conj_mem infer_instance m hm g,
  end }

def subgroup.connected_component_of_identity {G : Type*} [topological_space G] [group G]
  [topological_group G] (s : subgroup G) : subgroup G := 
{ carrier  := connected_component (1 : G),
  one_mem' := mem_connected_component,
  mul_mem' := λ g h hg hh,
  begin
    rw connected_component_eq hg,
    have : g ∈ connected_component (g*h),
    { apply continuous.image_connected_component_subset (continuous_mul_left g),
      rw ← connected_component_eq hh,
      use [(1 : G), mem_connected_component],
      simp only [mul_one], },
    rw ← connected_component_eq this,
    exact mem_connected_component,
  end,
  inv_mem' := λ g hg,
  begin
    rw ← one_inv,
    apply continuous.image_connected_component_subset continuous_inv,
    rw set.mem_image,
    use [g, hg],
    apply_instance,
  end }

/-! Topological abelianization -/

instance G_K.is_normal_commutator_closure : (commutator (G_K K)).topological_closure.normal := 
subgroup.is_normal_topological_closure (commutator (G_K K))

def G_K_ab := (G_K K) ⧸ (subgroup.topological_closure (commutator (G_K K)))
noncomputable instance : group (G_K_ab K) :=
quotient_group.quotient.group (commutator (G_K K)).topological_closure
noncomputable instance : topological_space (G_K_ab K) :=
quotient_group.quotient.topological_space (subgroup.topological_closure (commutator (G_K K)))
instance : topological_group (G_K_ab K) :=
topological_group_quotient (commutator (G_K K)).topological_closure
