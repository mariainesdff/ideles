# Adèles and idèles of global fields

We formalize the finite adèle ring and finite idèle group of a Dedekind domain. Building on this, we formalize the (finite) adèle ring and (finite) idèle group of any number field or function field.

In the number field case, we moreover define the idèle class group and provide two applications: the statement of the main theorem of global class field theory, and a proof that the ideal class group is isomorphic to an explicit quotient of the idèle class group.

As a prerequisite, we formalize adic valuations on Dedekind domains and the associated completions.

This formalization is described in the paper "Formalizing the ring of adèles of a global field", [to be presented at ITP 2022](https://itpconference.github.io/ITP22/cfp.html). The version of the source code referred to in the paper is at the tag [journal-submission](https://github.com/mariainesdff/ideles/tree/journal-submission), and the corresponding documentation can be found in [this link](https://mariainesdff.github.io/ideles/journal-submission).

## Guide through the code

This project is currently in the process of being integrated into `mathlib`. Please see below where to find the main contributions (this list will be updated when new features are added to `mathlib`). Other small contributions developing background results are scattered through the library.
- `height_one_spectrum` : [src/ring_theory/dedekind_domain/ideal.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/ideal.html#height-one-spectrum-of-a-dedekind-domain)
- `height_one_spectrum.int_valuation` : [src/ring_theory/dedekind_domain/adic_valuation.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/adic_valuation.html#is_dedekind_domain.height_one_spectrum.int_valuation)
- `height_one_spectrum.valuation` : [src/ring_theory/dedekind_domain/adic_valuation.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/adic_valuation.html#is_dedekind_domain.height_one_spectrum.valuation)
- `height_one_spectrum.adic_completion` : [src/ring_theory/dedekind_domain/adic_valuation.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/adic_valuation.html#is_dedekind_domain.height_one_spectrum.adic_completion)
- `function_field.infty_valuation` : [src/number_theory/function_field.lean](https://leanprover-community.github.io/mathlib_docs/number_theory/function_field.html#function_field.infty_valuation_def)
- `function_field.valued_Fqt_infty` : [src/number_theory/function_field.lean](https://leanprover-community.github.io/mathlib_docs/number_theory/function_field.html#function_field.valued_Fqt_infty)
- `ideal.finite_factors` : [src/ring_theory/dedekind_domain/factorization.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/factorization.html#ideal.finite_factors)
- `ideal.finprod_height_one_spectrum_factorization` : [src/ring_theory/dedekind_domain/factorization.lean](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain/factorization.html#ideal.finprod_height_one_spectrum_factorization)

## Installation instructions
The formalization has been developed over Lean 3 and its matemathical library mathlib. For detailed instructions to install Lean, mathlib, and supporting tools, visit the [Lean Community website](https://leanprover-community.github.io/get_started.html).

After installation, run the command `leanproject get mariainesdff/ideles` to obtain a copy of the project's source files and dependencies. To open the project in VS Code, either run `path/to/ideles` on the command line, or use the "Open Folder" menu option to open the project's root directory.

## Documentation

The documentation automatically generated from the source files of the project is available on [this link](https://mariainesdff.github.io/ideles). Note that it includes documentation for the version of mathlib used by the project.

See also [Lean's general documentation](https://leanprover.github.io/documentation/) and the [current mathlib docs](https://leanprover-community.github.io/mathlib_docs).

Copyright (C) 2022, María Inés de Frutos-Fernández
