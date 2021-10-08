import tests

noncomputable theory
open nat

/- The localization map is continuous for the localization topology and for the ring_filter_basis
topology on A_Q_f -/
lemma localization_continuous : @continuous pi_Z_p A_Q_f
  pi_Z_p.topological_space A_Q_f.topological_space (localization.monoid_of M).to_fun := 
ring_topology.coinduced_continuous _

lemma ring_filter_basis_continuous : @continuous pi_Z_p A_Q_f
  pi_Z_p.topological_space (A_Q_f.ring_filter_basis.topology) (localization.monoid_of M).to_fun :=
begin
  sorry,
end

/- The localization map is open for the localization topology and for the ring_filter_basis
topology on A_Q_f -/
lemma localization_open_map : @is_open_map pi_Z_p A_Q_f
  pi_Z_p.topological_space A_Q_f.topological_space (localization.monoid_of M).to_fun :=
begin
  sorry,
end

lemma ring_filter_basis_open_map : @is_open_map pi_Z_p A_Q_f
  pi_Z_p.topological_space (A_Q_f.ring_filter_basis.topology) (localization.monoid_of M).to_fun :=
begin
  sorry,
end

/- The localization topology on A_Q_f agrees with the restricted product topology -/
lemma usual_topology : A_Q_f.topological_space = (A_Q_f.ring_filter_basis).topology :=
eq_of_eq_basis_at_zero _
  (@image_topological_basis_at_zero pi_Z_p _ _
    pi_Z_p.topological_ring (localization M) _ A_Q_f.topological_space A_Q_f.topological_ring
    (algebra_map pi_Z_p A_Q_f) localization_continuous localization_open_map)
  (@image_topological_basis_at_zero pi_Z_p _ _
    pi_Z_p.topological_ring (localization M) _ A_Q_f.ring_filter_basis.topology
    A_Q_f.ring_filter_basis.is_topological_ring (algebra_map pi_Z_p A_Q_f)
    ring_filter_basis_continuous ring_filter_basis_open_map)
