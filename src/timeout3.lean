import valuation

variables {R : Type} {K : Type} [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : maximal_spectrum R)

noncomputable def v_valued_K (v : maximal_spectrum R) : valued K :=
{ Γ₀  := with_zero (multiplicative ℤ),
  grp := infer_instance,
  -- necessary
  v   := adic_valuation v }

noncomputable def ts' : topological_space K := @valued.topological_space K _ (v_valued_K v)
lemma tdr' : @topological_division_ring K _ (ts' v) := @valued.topological_division_ring K _ (v_valued_K v)
noncomputable def us' : uniform_space K := @topological_add_group.to_uniform_space K _ (ts' v) _
lemma ug' : @uniform_add_group K (us' v) _ := @topological_add_group_is_uniform K _ (ts' v) _

variables (K)
def K_v := @uniform_space.completion K (us' v)

noncomputable instance : field (K_v K v) := @field_completion K _ (us' v) (tdr' v) _ (ug' v) _

variables (R)

def K_hat := (Π (v : maximal_spectrum R), K_v K v)

def foo := { x : (K_hat R K) // ∃ (v : maximal_spectrum R), (x v)⁻¹ = 37 }

def bar : foo R K → K_hat R K := λ x, x.1
