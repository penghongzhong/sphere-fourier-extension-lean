# arXiv manuscript and Lean correspondence

Theorem 1.1 gives the full spherical Fourier extension range specified in the
[official JSP-001040 problem](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#jsp-001040).
It uses the polar surface measure and the kernel \(e^{2\pi iX\cdot\omega}\).
Theorem 1.2 states strong type on the finite Knapp boundary. Both
`MemLp` membership and the norm inequality are included in the Lean output.
In the finite equality case, the Lean proof of Theorem 1.1 applies Theorem 1.2.

The table gives principal proof nodes with the arXiv manuscript numbering.
Each listed declaration is checked by `ManuscriptCorrespondence.lean`, and the
two manuscript statements are printed in full in `ManuscriptStatement.audit.log`.

The critical local estimate and the strict mixed range use the pinned OpenAI
local-smoothing formalization. The proof uses the arbitrary-small-power-loss
form of the critical local estimate. The comparison with the fixed paraboloid
in Section 3 and the classical bilinear exponent comparison in Section 4
explain the literature context. The verified proof retains the auxiliary
spherical phase comparisons, the sharp-cutoff sparse argument, and the
sphere-specific transverse estimate.

The introductory cap-scaling display (1.2) previews the necessary-condition
argument mapped under `nec:knapp` below.

| Manuscript location | Mathematical content | Lean declarations |
| --- | --- | --- |
| Theorem 1.1, p. 1 (`thm:main`) | Full strong range, the exact prize statement | `JSP001040Manuscript.fullRange`, `RestrictionWork.jsp001040_catalog_statement`, `RestrictionWork.fullSphereRestrictionConjecture` |
| Theorem 1.2, p. 2 (`thm:boundary`) | Strong type on the finite Knapp boundary | `JSP001040Manuscript.finiteKnappBoundary`, `RestrictionWork.finiteKnappBoundarySufficiency`, `RestrictionWork.finiteKnappBoundary_of_quarter_graph` |
| Lemma 2.1, p. 4 (`nec:constant-asymptotic`) | Nonzero radial asymptotic | `OAI.Analysis.Fourier.Radial.bessel_normalized_asymptotic`, `OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic` |
| Proposition 2.2, p. 5 (`nec:necessary`) | Necessity including radial equality | `RestrictionWork.sphere_constant_nonintegrability`, `RestrictionWork.original_radial_necessary`, `RestrictionWork.original_sphere_necessity` |
| Equation (2.12), p. 6 (`nec:knapp`) | Cap coherence and Knapp necessity | `RestrictionWork.cap_coherent_pointwise`, `RestrictionWork.original_cap_norm_transfer`, `RestrictionWork.cap_knapp_necessity`, `RestrictionWork.original_knapp_necessary` |
| Equation (2.13), p. 6 (`nec:infty`) | Infinite output | `RestrictionWork.extension_top_bound` |
| Equation (3.1), p. 7 (`eq:critical-local-sphere`) | Critical local sphere estimate with arbitrary small power loss | `CriticalReplay.twoPi_critical_local_extension`, `RestrictionWork.original_critical_local_input` |
| Theorem 3.1, p. 7 (`input:strict`) | Strict mixed range | `CriticalReplay.global_mixed_extension`, `RestrictionWork.original_global_strict_input`, `RestrictionWork.strict_admissible_sufficiency` |
| Lemma 3.3, p. 8 (`lem:uniform-local-graphs`) | Uniform local estimates for caps and rebases | `RestrictionWork.uniform_shifted_spherical_subcap_bound`, `RestrictionWork.shifted_spherical_local_bound` |
| Equation (3.18), p. 10 (`eq:graph-mass-decay`) | Graph measure and Fourier decay | `RestrictionWork.shifted_spherical_kernel_decay` |
| Lemma 3.4, p. 11 (`lem:graph-sparse`) | Sparse family estimate | `RestrictionWork.shifted_spherical_sparse_integral_kernel_bound`, `RestrictionWork.shifted_graph_sparse_restriction_indexed`, `RestrictionWork.shifted_graph_sparse_measure_fourier_bound` |
| Theorem 3.2, p. 8 (`input:diagonal`) | Uniform removal of the local loss and global diagonal estimate | `RestrictionWork.measure_sparse_bound_implies_restriction`, `RestrictionWork.shifted_graph_global_restriction`, `RestrictionWork.shifted_graph_global_extension`, `RestrictionWork.shifted_graph_global_diagonal_product` |
| Lemma 4.1, p. 14 (`trans:slab`) | Radon strip estimates | `RestrictionWork.filtered_radon_two_norm_sq_le`, `RestrictionWork.filtered_radon_uniform_frequency_bound`, `RestrictionWork.radon_strip_restricted_bound` |
| Equation (4.10), p. 16 (`trans:factor`) | Spherical collision factorization | `RestrictionWork.shifted_cap_chord_bounds`, `RestrictionWork.sphere_stereo_distance`, `RestrictionWork.sphere_stereo_norm_sq`, `RestrictionWork.sphere_stereo_incidence`, `RestrictionWork.shifted_collision_radon_factor` |
| Lemma 4.2, p. 16 (`trans:row`) | Gaussian collision row bounds | `RestrictionWork.shifted_stereo_chart_measure_bounds`, `RestrictionWork.shifted_collision_double_strip_bound`, `RestrictionWork.shifted_collision_gaussian_row_bound` |
| Lemma 4.3, p. 17 (`trans:energy`) | Gaussian energy and transverse product | `RestrictionWork.graph_extension_product_plancherel`, `RestrictionWork.graph_extension_gaussian_product_energy_le`, `RestrictionWork.shifted_graph_transverse_restricted_two` |
| Proposition 4.4, p. 18 (`trans:restricted`) | Interpolation to strict gain across the Knapp line | `RestrictionWork.shifted_graph_transverse_knapp_gain`, `RestrictionWork.shifted_graph_restricted_knapp_gain` |
| Proposition 4.5, p. 19 (`trans:rescaled`) | Whitney pair rescaling | `RestrictionWork.graph_rebase_product_norm_transfer`, `RestrictionWork.shifted_graph_whitney_pair_bound` |
| Equation (5.1), p. 20 (`kn:pair-geometry`) | Whitney geometry | `RestrictionWork.dyadic_whitney_pair_distance_ge`, `RestrictionWork.dyadic_whitney_pair_localize` |
| Equation (5.2), p. 21 (`kn:whitney-expansion`) | Whitney expansion | `RestrictionWork.graph_extension_whitney_hasSum` |
| Lemma 5.1, p. 21 (`kn:layer`) | Frequency overlap and one-layer summation | `RestrictionWork.card_dyadic_whitney_frequency_overlap`, `RestrictionWork.graph_whitney_layer_eLpNorm` |
| Equation (5.7), p. 22 (`kn:mass-bounds`) | Cell mass and row incidence bounds | `RestrictionWork.dyadic_whitney_mass_le`, `RestrictionWork.dyadic_whitney_mass_sum_le` |
| Equation (5.10), p. 23 (`kn:two-scale`) | Coarse and fine scales at the exact mass power | `RestrictionWork.dyadic_whitney_mass_tsum_le` |
| Proposition 5.2, p. 22 (`kn:restricted`) | Restricted estimate on the exact boundary | `RestrictionWork.spherical_graph_restricted_knapp_at_le_two`, `RestrictionWork.spherical_graph_restricted_knapp_below_half`, `RestrictionWork.spherical_graph_restricted_knapp_linear` |
| Theorem 5.3, p. 23 (`kn:strong`) | Strong-type upgrade by dyadic pairing | `RestrictionWork.spherical_graph_knapp_atom_pairing_le`, `RestrictionWork.dyadic_exponential_kernel_sum_le`, `RestrictionWork.weighted_matrix_rpow_sum_le_of_normalized`, `RestrictionWork.spherical_graph_knapp_unit_pairing`, `RestrictionWork.graph_extension_le_of_unit_pairing`, `RestrictionWork.spherical_graph_knapp_strong` |
| Equation (6.1), p. 25 (`cap:density`) | Canonical cap surface measure | `RestrictionWork.cap_area_identity` |
| Equation (6.5), p. 26 (`cap:identity`) | Exact affine phase and physical Jacobian | `RestrictionWork.original_cap_rescaling`, `RestrictionWork.original_cap_physical_measure` |
| Proposition 6.1, p. 25 (`cap:transfer`) | Reverse norm transfer, rotations and finite cover | `RestrictionWork.original_cap_reverse`, `RestrictionWork.original_small_cap_bound_of_graph`, `RestrictionWork.original_small_cap_contains_ball`, `RestrictionWork.sphere_isometry_measurePreserving`, `RestrictionWork.extension_comp_sphereIsometry`, `RestrictionWork.boundedSphereExtension_of_ball_bound`, `RestrictionWork.boundedSphereExtension_of_quarter_graph` |
| Section 6, p. 25 (`cap:section`) | Finite Knapp reparametrization and full-sphere deduction | `RestrictionWork.admissible_finite_knapp_reparam`, `RestrictionWork.fullSphereRestriction_of_graph_strong` |

The arXiv editorial revision adds four historical references and moves the verification statement to the acknowledgements. The 17 statement labels and all Lean declarations match the archived manuscript. Only the presentation of several existing formulas changes from inline to display. The two external principal analytic inputs are the critical local estimate and the strict mixed estimate. Zero additional analytic axioms occur in the archived audit. This editorial revision uses the archived Lean audit, without a new Lean execution.


## Formula presentation revision

All 17 theorem, lemma and proposition statements have been rewritten to display their hypotheses and conclusions explicitly. The abstract uses impersonal wording. In that formula-only revision, the statement labels and the 20 then-numbered equations matched the preceding arXiv edition. The proof expansions below expose calculations already contained in the preceding argument.

| Expanded calculation | Existing formal correspondence |
| --- | --- |
| Radial symmetry, energy bounds and tail integrals | OAI.Analysis.Fourier.Radial.bessel_normalized_asymptotic |
| Knapp phase lower bound and scale inequality | RestrictionWork.cap_coherent_pointwise, RestrictionWork.cap_knapp_necessity |
| Critical cap/rebase Jacobians and auxiliary phase bounds | RestrictionWork.uniform_shifted_spherical_subcap_bound, RestrictionWork.shifted_spherical_local_bound |
| Sparse operator endpoint interpolation and coefficient summation | RestrictionWork.shifted_graph_sparse_restriction_indexed, RestrictionWork.measure_sparse_bound_implies_restriction |
| Slab interpolation, Gaussian rows and product energy | RestrictionWork.radon_strip_restricted_bound, RestrictionWork.shifted_collision_gaussian_row_bound, RestrictionWork.graph_extension_gaussian_product_energy_le |
| Product exponent interpolation and affine rescaling | RestrictionWork.shifted_graph_restricted_knapp_gain, RestrictionWork.graph_rebase_product_norm_transfer |
| Layer operator bounds and two geometric scale sums | RestrictionWork.graph_whitney_layer_eLpNorm, RestrictionWork.dyadic_whitney_mass_tsum_le |
| Dyadic pairing exponents and norm recovery | RestrictionWork.spherical_graph_knapp_atom_pairing_le, RestrictionWork.graph_extension_le_of_unit_pairing |
| Cap norm transfer, rotations and finite cover | RestrictionWork.original_cap_reverse, RestrictionWork.boundedSphereExtension_of_ball_bound |

The Lean source files and the archived audit logs are byte-identical to the preceding edition. This is an equivalent reformulation and expansion of the manuscript presentation. The prior strict Lean audit is retained. No new Lean execution is reported for this revision.


## Reference and definition revision

The current manuscript has 97 numbered equations and 17 numbered theorem, lemma and proposition statements. Every such number has a subsequent explicit reference in the manuscript body. The label audit reports zero duplicate labels, zero undefined references, zero unused numbered equations and zero unused theorem numbers. Equation numbering is consecutive within each section.

The mathematical conventions now define the norm notation, indicators, derivative notation, orthogonal groups, distance and comparison notation before the proofs. The Gaussian energy region and the collision phase domain convention are specified before their use. Proof steps cite the exact phase identities, Jacobians, endpoint estimates, interpolation bounds and summation formulas they use. No equation numbers appear as annotations above mathematical symbols, and the manuscript contains no Longrightarrow command.

The additional equation labels identify existing mathematical steps. Their formal ownership is the audited statement or proof listed below. This is a correspondence of proof content, not a claim that each editorial anchor is a separately compiled Lean declaration. The Lean source files and archived audit logs are byte-identical to the preceding revision. No new Lean execution is reported.

| Audited mathematical environment | New equation anchors | Existing Lean correspondence |
| --- | --- | --- |
| input:strict (3.1) | eq:strict-diagonal, eq:strict-mixed-intermediate | RestrictionWork.strict_admissible_sufficiency |
| input:diagonal (3.2) | eq:spherical-graph-phase, eq:rebased-graph-phase, eq:sparse-cover-layers, eq:sparse-cover-cost, eq:dyadic-coefficient-mass, eq:lattice-fourier-tiling | RestrictionWork.shifted_graph_global_diagonal_product |
| lem:uniform-local-graphs (3.3) | eq:cap-extension-identity, eq:critical-scaling-cancellation, eq:quadratic-cap-approximation, eq:auxiliary-cap-comparison, eq:uniform-cap-local, eq:rebased-extension-identity, eq:rebased-local-with-loss, eq:rebased-quadratic-remainder, eq:auxiliary-rebased-comparison | RestrictionWork.shifted_spherical_local_bound |
| lem:graph-sparse (3.4) | eq:graph-mass, eq:sparse-data-norm, eq:sparse-kernel-mass, eq:sparse-gram-off-diagonal, eq:sparse-operator-endpoints, eq:sparse-operator-b | RestrictionWork.shifted_graph_sparse_measure_fourier_bound |
| cap:transfer (6.1) | cap:graph-hypothesis, cap:input-norm, cap:physical-map, cap:local-bound, cap:boundary-cancellation, cap:rotation, cap:global-bound | RestrictionWork.boundedSphereExtension_of_quarter_graph |
| trans:slab (4.1) | trans:slab-fourier, trans:slab-infty, trans:slab-two | RestrictionWork.radon_strip_restricted_bound |
| trans:row (4.2) | trans:chord-bounds, trans:stereo-chart, trans:stereo-distance, trans:stereo-radius, trans:stereo-measure, trans:phase-defect, trans:collision-slab, trans:collision-strip, trans:gaussian-kernel, trans:collision-gaussian | RestrictionWork.shifted_collision_gaussian_row_bound |
| trans:energy (4.3) | trans:time-gaussian, trans:gaussian-energy | RestrictionWork.shifted_graph_transverse_restricted_two |
| trans:restricted (4.4) | trans:two-product, trans:two-gap, trans:diagonal-product | RestrictionWork.shifted_graph_restricted_knapp_gain |
| trans:rescaled (4.5) | trans:physical-dilation, trans:rebase-identity | RestrictionWork.shifted_graph_whitney_pair_bound |
| kn:layer (5.1) | kn:multiplier-l1, kn:multiplier-l2, kn:layer-distribution | RestrictionWork.graph_whitney_layer_eLpNorm |
| kn:restricted (5.2) | kn:pair-bound, kn:layer-mass, kn:mass-powers, kn:scale-series, kn:square-restricted | RestrictionWork.spherical_graph_restricted_knapp_linear |
| kn:strong (5.3) | kn:normalized-masses, kn:atom-pairing, kn:pair-exponents, kn:decaying-pairing, kn:exponential-sum, kn:matrix-pairing, kn:dual-pairing, kn:dual-test | RestrictionWork.spherical_graph_knapp_strong |
| nec:constant-asymptotic (2.1) | nec:radial-ode, nec:conjugated-ode, nec:energy-differential, nec:energy-bounds, nec:coefficient-derivatives, nec:coefficient-tail | OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic |
| nec:necessary (2.2) | nec:radial-integrability, nec:cap-input, nec:cap-phase, nec:cap-coherence, nec:cap-volume | RestrictionWork.original_sphere_necessity |
