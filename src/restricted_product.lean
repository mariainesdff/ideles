import topology.algebra.group
import drestprod

open_locale big_operators

universes u v 

variables (ι : Type u) [dec_ι : decidable_eq ι]
variables (β : ι → Type v) [Π (i : ι), topological_space (β i)] [Π (i : ι), group (β i)][∀ (i : ι), topological_group (β i)]
variables (α : ι → Type v) [Π (i : ι), topological_space (α i)] [Π (i : ι), group (α i)][∀ (i : ι), topological_group (α i)]
variables [Π i, has_lift_t (α i) (β i)]

@[derive [inhabited]]
def restricted_product : Type* := drestprod β α

notation `Π'` binders `, ` r:(scoped f, drestprod f) := r
infix ` →ₚ `:25 := drestprod
