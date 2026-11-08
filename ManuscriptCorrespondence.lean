import ManuscriptStatement

set_option autoImplicit false

-- Theorem 1·1. Full strong range, the exact prize statement.
#check JSP001040Manuscript.fullRange
#print axioms JSP001040Manuscript.fullRange
#check RestrictionWork.jsp001040_catalog_statement
#print axioms RestrictionWork.jsp001040_catalog_statement
#check RestrictionWork.fullSphereRestrictionConjecture
#print axioms RestrictionWork.fullSphereRestrictionConjecture

-- Theorem 1·2. Strong type on the finite Knapp boundary.
#check JSP001040Manuscript.finiteKnappBoundary
#print axioms JSP001040Manuscript.finiteKnappBoundary
#check RestrictionWork.finiteKnappBoundarySufficiency
#print axioms RestrictionWork.finiteKnappBoundarySufficiency
#check RestrictionWork.finiteKnappBoundary_of_quarter_graph
#print axioms RestrictionWork.finiteKnappBoundary_of_quarter_graph

-- Lemma 2·1. Nonzero radial asymptotic.
#check OAI.Analysis.Fourier.Radial.bessel_normalized_asymptotic
#print axioms OAI.Analysis.Fourier.Radial.bessel_normalized_asymptotic
#check OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic
#print axioms OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic

-- Proposition 2·2. Necessity including radial equality.
#check RestrictionWork.sphere_constant_nonintegrability
#print axioms RestrictionWork.sphere_constant_nonintegrability
#check RestrictionWork.original_radial_necessary
#print axioms RestrictionWork.original_radial_necessary
#check RestrictionWork.original_sphere_necessity
#print axioms RestrictionWork.original_sphere_necessity

-- Equation (2·1). Cap coherence and Knapp necessity.
#check RestrictionWork.cap_coherent_pointwise
#print axioms RestrictionWork.cap_coherent_pointwise
#check RestrictionWork.original_cap_norm_transfer
#print axioms RestrictionWork.original_cap_norm_transfer
#check RestrictionWork.cap_knapp_necessity
#print axioms RestrictionWork.cap_knapp_necessity
#check RestrictionWork.original_knapp_necessary
#print axioms RestrictionWork.original_knapp_necessary

-- Equation (2·2). Infinite output.
#check RestrictionWork.extension_top_bound
#print axioms RestrictionWork.extension_top_bound

-- Equation (3·1). Critical local sphere estimate with arbitrary small power loss.
#check CriticalReplay.twoPi_critical_local_extension
#print axioms CriticalReplay.twoPi_critical_local_extension
#check RestrictionWork.original_critical_local_input
#print axioms RestrictionWork.original_critical_local_input

-- Theorem 3·1. Strict mixed range.
#check CriticalReplay.global_mixed_extension
#print axioms CriticalReplay.global_mixed_extension
#check RestrictionWork.original_global_strict_input
#print axioms RestrictionWork.original_global_strict_input
#check RestrictionWork.strict_admissible_sufficiency
#print axioms RestrictionWork.strict_admissible_sufficiency

-- Lemma 3·3. Uniform local estimates for caps and rebases.
#check RestrictionWork.uniform_shifted_spherical_subcap_bound
#print axioms RestrictionWork.uniform_shifted_spherical_subcap_bound
#check RestrictionWork.shifted_spherical_local_bound
#print axioms RestrictionWork.shifted_spherical_local_bound

-- Equation (3·4). Graph measure and Fourier decay.
#check RestrictionWork.shifted_spherical_kernel_decay
#print axioms RestrictionWork.shifted_spherical_kernel_decay

-- Lemma 3·4. Sparse family estimate.
#check RestrictionWork.shifted_spherical_sparse_integral_kernel_bound
#print axioms RestrictionWork.shifted_spherical_sparse_integral_kernel_bound
#check RestrictionWork.shifted_graph_sparse_restriction_indexed
#print axioms RestrictionWork.shifted_graph_sparse_restriction_indexed
#check RestrictionWork.shifted_graph_sparse_measure_fourier_bound
#print axioms RestrictionWork.shifted_graph_sparse_measure_fourier_bound

-- Theorem 3·2. Uniform removal of the local loss and global diagonal estimate.
#check RestrictionWork.measure_sparse_bound_implies_restriction
#print axioms RestrictionWork.measure_sparse_bound_implies_restriction
#check RestrictionWork.shifted_graph_global_restriction
#print axioms RestrictionWork.shifted_graph_global_restriction
#check RestrictionWork.shifted_graph_global_extension
#print axioms RestrictionWork.shifted_graph_global_extension
#check RestrictionWork.shifted_graph_global_diagonal_product
#print axioms RestrictionWork.shifted_graph_global_diagonal_product

-- Lemma 4·1. Radon strip estimates.
#check RestrictionWork.filtered_radon_two_norm_sq_le
#print axioms RestrictionWork.filtered_radon_two_norm_sq_le
#check RestrictionWork.filtered_radon_uniform_frequency_bound
#print axioms RestrictionWork.filtered_radon_uniform_frequency_bound
#check RestrictionWork.radon_strip_restricted_bound
#print axioms RestrictionWork.radon_strip_restricted_bound

-- Equation (4·1). Spherical collision factorization.
#check RestrictionWork.shifted_cap_chord_bounds
#print axioms RestrictionWork.shifted_cap_chord_bounds
#check RestrictionWork.sphere_stereo_distance
#print axioms RestrictionWork.sphere_stereo_distance
#check RestrictionWork.sphere_stereo_norm_sq
#print axioms RestrictionWork.sphere_stereo_norm_sq
#check RestrictionWork.sphere_stereo_incidence
#print axioms RestrictionWork.sphere_stereo_incidence
#check RestrictionWork.shifted_collision_radon_factor
#print axioms RestrictionWork.shifted_collision_radon_factor

-- Lemma 4·2. Gaussian collision row bounds.
#check RestrictionWork.shifted_stereo_chart_measure_bounds
#print axioms RestrictionWork.shifted_stereo_chart_measure_bounds
#check RestrictionWork.shifted_collision_double_strip_bound
#print axioms RestrictionWork.shifted_collision_double_strip_bound
#check RestrictionWork.shifted_collision_gaussian_row_bound
#print axioms RestrictionWork.shifted_collision_gaussian_row_bound

-- Lemma 4·3. Gaussian energy and transverse product.
#check RestrictionWork.graph_extension_product_plancherel
#print axioms RestrictionWork.graph_extension_product_plancherel
#check RestrictionWork.graph_extension_gaussian_product_energy_le
#print axioms RestrictionWork.graph_extension_gaussian_product_energy_le
#check RestrictionWork.shifted_graph_transverse_restricted_two
#print axioms RestrictionWork.shifted_graph_transverse_restricted_two

-- Proposition 4·4. Interpolation to strict gain across the Knapp line.
#check RestrictionWork.shifted_graph_transverse_knapp_gain
#print axioms RestrictionWork.shifted_graph_transverse_knapp_gain
#check RestrictionWork.shifted_graph_restricted_knapp_gain
#print axioms RestrictionWork.shifted_graph_restricted_knapp_gain

-- Proposition 4·5. Whitney pair rescaling.
#check RestrictionWork.graph_rebase_product_norm_transfer
#print axioms RestrictionWork.graph_rebase_product_norm_transfer
#check RestrictionWork.shifted_graph_whitney_pair_bound
#print axioms RestrictionWork.shifted_graph_whitney_pair_bound

-- Equation (5·1). Whitney geometry.
#check RestrictionWork.dyadic_whitney_pair_distance_ge
#print axioms RestrictionWork.dyadic_whitney_pair_distance_ge
#check RestrictionWork.dyadic_whitney_pair_localize
#print axioms RestrictionWork.dyadic_whitney_pair_localize

-- Equation (5·2). Whitney expansion.
#check RestrictionWork.graph_extension_whitney_hasSum
#print axioms RestrictionWork.graph_extension_whitney_hasSum

-- Lemma 5·1. Frequency overlap and one-layer summation.
#check RestrictionWork.card_dyadic_whitney_frequency_overlap
#print axioms RestrictionWork.card_dyadic_whitney_frequency_overlap
#check RestrictionWork.graph_whitney_layer_eLpNorm
#print axioms RestrictionWork.graph_whitney_layer_eLpNorm

-- Equation (5·3). Cell mass and row incidence bounds.
#check RestrictionWork.dyadic_whitney_mass_le
#print axioms RestrictionWork.dyadic_whitney_mass_le
#check RestrictionWork.dyadic_whitney_mass_sum_le
#print axioms RestrictionWork.dyadic_whitney_mass_sum_le

-- Equation (5·4). Coarse and fine scales at the exact mass power.
#check RestrictionWork.dyadic_whitney_mass_tsum_le
#print axioms RestrictionWork.dyadic_whitney_mass_tsum_le

-- Proposition 5·2. Restricted estimate on the exact boundary.
#check RestrictionWork.spherical_graph_restricted_knapp_at_le_two
#print axioms RestrictionWork.spherical_graph_restricted_knapp_at_le_two
#check RestrictionWork.spherical_graph_restricted_knapp_below_half
#print axioms RestrictionWork.spherical_graph_restricted_knapp_below_half
#check RestrictionWork.spherical_graph_restricted_knapp_linear
#print axioms RestrictionWork.spherical_graph_restricted_knapp_linear

-- Theorem 5·3. Strong-type upgrade by dyadic pairing.
#check RestrictionWork.spherical_graph_knapp_atom_pairing_le
#print axioms RestrictionWork.spherical_graph_knapp_atom_pairing_le
#check RestrictionWork.dyadic_exponential_kernel_sum_le
#print axioms RestrictionWork.dyadic_exponential_kernel_sum_le
#check RestrictionWork.weighted_matrix_rpow_sum_le_of_normalized
#print axioms RestrictionWork.weighted_matrix_rpow_sum_le_of_normalized
#check RestrictionWork.spherical_graph_knapp_unit_pairing
#print axioms RestrictionWork.spherical_graph_knapp_unit_pairing
#check RestrictionWork.graph_extension_le_of_unit_pairing
#print axioms RestrictionWork.graph_extension_le_of_unit_pairing
#check RestrictionWork.spherical_graph_knapp_strong
#print axioms RestrictionWork.spherical_graph_knapp_strong

-- Equation (6·1). Canonical cap surface measure.
#check RestrictionWork.cap_area_identity
#print axioms RestrictionWork.cap_area_identity

-- Equation (6·2). Exact affine phase and physical Jacobian.
#check RestrictionWork.original_cap_rescaling
#print axioms RestrictionWork.original_cap_rescaling
#check RestrictionWork.original_cap_physical_measure
#print axioms RestrictionWork.original_cap_physical_measure

-- Proposition 6·1. Reverse norm transfer, rotations and finite cover.
#check RestrictionWork.original_cap_reverse
#print axioms RestrictionWork.original_cap_reverse
#check RestrictionWork.original_small_cap_bound_of_graph
#print axioms RestrictionWork.original_small_cap_bound_of_graph
#check RestrictionWork.original_small_cap_contains_ball
#print axioms RestrictionWork.original_small_cap_contains_ball
#check RestrictionWork.sphere_isometry_measurePreserving
#print axioms RestrictionWork.sphere_isometry_measurePreserving
#check RestrictionWork.extension_comp_sphereIsometry
#print axioms RestrictionWork.extension_comp_sphereIsometry
#check RestrictionWork.boundedSphereExtension_of_ball_bound
#print axioms RestrictionWork.boundedSphereExtension_of_ball_bound
#check RestrictionWork.boundedSphereExtension_of_quarter_graph
#print axioms RestrictionWork.boundedSphereExtension_of_quarter_graph

-- Section 6. Finite Knapp reparametrization and full-sphere deduction.
#check RestrictionWork.admissible_finite_knapp_reparam
#print axioms RestrictionWork.admissible_finite_knapp_reparam
#check RestrictionWork.fullSphereRestriction_of_graph_strong
#print axioms RestrictionWork.fullSphereRestriction_of_graph_strong

