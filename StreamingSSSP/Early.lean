module

public import StreamingSSSP.Early.Recurrence
public import StreamingSSSP.Early.BallShrink
public import StreamingSSSP.Early.Stars

/-!
# Faithful early-level local analysis

`ShortPath` records an actual finite-cost walk. Balls use the finite integer
shortest distances of `Graph`, with arbitrary real radii.

* `grouped_type1_cover`, `grouped_type1_count_at`,
  `core_piece_contained`, `core_piece_classes_distinct`, and
  `grouped_fringe_contained` give the no-bridge contiguous partition. The
  disjointness lemmas are `Cells.overlap_eq`, `Cover.fringe_disjoint`, and
  `Cover.core_fringe_disjoint`. Each pivot owns at most one fringe interval.
* `keeps_pair_window`, `pair_owner_count`, and `keeps_probability_pair`
  prove noisy knockout, including the single bad group per fixed shift.
* `Sampling.expected_survivors_le` and `Fractional.exp_sum_le` prove the
  `8/p` one-direction bound without a rare-event or pivot-count assumption.
* `earlyRadius` is the minimum-shell rule on `4*k` candidates, with uniform
  independent group and finite-grid shift. `expected_early_shell` bounds
  its expected full fringe size by `b/(k*M)`.
* `expected_early_pieces` gives `1 + 2*p*Y` for the fixed eligible set.
  `expected_actual_early_related` bounds the actual induced-graph related
  tally by `17/p`, assuming positive scale, `M ≥ 2`, `N > 0`, `0 < p ≤ 1`,
  directional search balls of size at most `b`, and
  `2*b*b*p^2 ≤ k*M`. Its search radius is `(2*lambda+2)*D`, and the next
  search radius is overestimated by `(lambda-1)*D`, with `lambda=4*k*M`.
* `nested_advance_star_of_infix` proves actual ancestor-star containment
  and detour `3*eta*Dnew` for a nested child bridge, using only distance
  monotonicity, `eta ≥ 2`, and `Dnew ≤ Dold/2`.
  `global_advance_star_from_initial_scale` gives radius `8*Delta` from
  `eta*D0 ≤ 5*Delta`. `StarArrays.arrays_advance_star` and
  `StarArrays.arrays_global_star` realize these edges from verified exact
  (possibly radius-capped) query arrays; `StarArrays.queriedEdges_eq_star` instantiates
  the interface with the existing executable Bellman--Ford arrays.
* `core_child_inball_subset` and `core_child_outball_subset` derive actual
  ball containment in comparison-tournament survivors for any
  distance-monotone restriction of a surviving core class.
  `core_child_inball_shrink` and `core_child_outball_shrink` turn comparison
  hits into ball cardinality bounds at `t ≤ (lambda-1)*D`.
  `early_fringe_card_le` proves the deterministic `b/k` fringe-size bound
  for each selected group and shift, with directional parent balls `≤ b`.

The local law samples only the supplied eligible set `E`. Connecting that
law to deferred first-success ranks is the controller's responsibility.
Nothing deletes earlier pivots from graphs or from another pivot's fringe.
The tally is before type-2 splitting; global level summation and hopset
composition are separate.
-/
