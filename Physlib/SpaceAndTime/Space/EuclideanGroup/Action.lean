/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Physlib.SpaceAndTime.Space.Origin
public import Physlib.SpaceAndTime.Space.EuclideanGroup.AffineGroup

/-!
# The action of the Euclidean group on `Space`

The Euclidean group `EuclideanGroup d = ℝᵈ ⋊ O(d)` (`Space/EuclideanGroup/Basic.lean`) is the group
of rigid motions of `d`-dimensional space. This file makes that geometric meaning literal: it
endows the affine space of points `Space d` (`Space/Basic.lean`) with a `MulAction` of
`EuclideanGroup d` **by isometries**, and specialises it to the rotations.

## Main results

* `EuclideanGroup.smul_vsub_smul` — displacements transform by the linear part alone.
* `EuclideanGroup.dist_smul` — the action preserves distance.
* `EuclideanGroup.rotation_smul_origin` / `rotation_smul_vsub_origin` — rotations fix the origin
  and act about it by their orthogonal part.
* `EuclideanGroup.chartEuclidean_smul` — agreement with the affine-isometry model
  (`AffineGroup.lean`); the rest of the file does not depend on it.

## Implementation notes

`Space d` is an affine space (`NormedAddTorsor`) with no canonical origin, so the action is
defined relative to the coordinate basepoint `Space.origin d`:

`g • p = (g.linear • (p -ᵥ Space.origin d) + g.translation) +ᵥ Space.origin d`.

The basepoint `Space.origin` and the chart `Space.chartEuclidean` are defined in
`Space/Origin.lean`.
-/

@[expose] public section

variable {d : ℕ}

namespace EuclideanGroup

/-! ## Part 1: the action of the Euclidean group on `Space`

The motion `g = ⟨t, Q⟩` acts by `g • p = (Q • (p -ᵥ origin) + t) +ᵥ origin`. The `MulAction` laws
reduce to the semidirect-product group law of `EuclideanGroup`. -/

/-- The action of the Euclidean group on the affine space of points `Space d`: `g = ⟨t, Q⟩` rotates
`p` about the coordinate origin by the orthogonal part `Q` and then translates by `t`. -/
noncomputable instance : MulAction (EuclideanGroup d) (Space d) where
  smul g p := (g.linear • (p -ᵥ Space.origin d) + g.translation) +ᵥ Space.origin d
  one_smul p := by
    show ((1 : Matrix.orthogonalGroup (Fin d) ℝ) • (p -ᵥ Space.origin d) + 0) +ᵥ Space.origin d = p
    simp
  mul_smul g h p := by
      show (((g * h).linear • (p -ᵥ Space.origin d) + (g * h).translation) +ᵥ Space.origin d)
        = (((g.linear • (((h.linear • (p -ᵥ Space.origin d) + h.translation) +ᵥ Space.origin d)
              -ᵥ Space.origin d))
            + g.translation) +ᵥ Space.origin d)
      simp [vadd_vsub, add_comm, add_assoc, mul_smul]

/-- Coordinate formula for the action: `(g • p) i = (Q • (p -ᵥ origin)) i + t i`. -/
@[simp] lemma smul_apply (g : EuclideanGroup d) (p : Space d) (i : Fin d) :
    (g • p) i = (g.linear • (p -ᵥ Space.origin d)) i + g.translation i := by
  show ((g.linear • (p -ᵥ Space.origin d) + g.translation) +ᵥ Space.origin d) i
    = (g.linear • (p -ᵥ Space.origin d)) i + g.translation i
  simp [Space.vadd_apply]

/-- The displacement between two points transforms by the **orthogonal part alone**: the
translation cancels. This is the key lemma behind `dist_smul`. -/
@[simp] lemma smul_vsub_smul (g : EuclideanGroup d) (p q : Space d) :
    (g • p) -ᵥ (g • q) = g.linear • (p -ᵥ q) := by
  show ((g.linear • (p -ᵥ Space.origin d) + g.translation) +ᵥ Space.origin d)
      -ᵥ ((g.linear • (q -ᵥ Space.origin d) + g.translation) +ᵥ Space.origin d)
    = g.linear • (p -ᵥ q)
  rw [vadd_vsub_vadd_cancel_right, add_sub_add_right_eq_sub, ← smul_sub,
    vsub_sub_vsub_cancel_right]

/-- The Euclidean group acts on `Space d` **by isometries**: every rigid motion preserves distance.
-/
lemma dist_smul (g : EuclideanGroup d) (p q : Space d) :
    dist (g • p) (g • q) = dist p q := by
  rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin d)) (g • p) (g • q),
    dist_eq_norm_vsub (EuclideanSpace ℝ (Fin d)) p q, smul_vsub_smul]
  exact (orthogonalToLinearIsometryEquiv g.linear).norm_map _

/-! ## Part 2: specialisation to rotations

The `RotationGroup d` action is the restriction of the Euclidean action along
`RotationGroup d ≤ EuclideanGroup d` (`RotationGroup` elements have zero translation). The lemmas
below record that rotations fix the origin, act by their orthogonal part about the origin, and
preserve distance. -/

/-- The rotation-group action is the restriction of the Euclidean action: `r • p = ↑r • p`
(definitional). -/
@[simp] lemma rotation_smul_eq (r : RotationGroup d) (p : Space d) :
    r • p = (r : EuclideanGroup d) • p := rfl

/-- A rotation fixes the coordinate origin: its translation part vanishes
(`RotationGroup ≤ OriginStabilizer`), so `↑r • origin = origin`. Stated in the `↑r` form (the simp
normal form of `r • _`, via `rotation_smul_eq`) so it is a well-formed `simp` lemma. -/
@[simp] lemma rotation_smul_origin (r : RotationGroup d) :
    (r : EuclideanGroup d) • Space.origin d = Space.origin d := by
  have h_trans : (r : EuclideanGroup d).translation = 0 := by
    apply r.property.right
  have h_rot : (r : EuclideanGroup d) • (Space.origin d) =
      ((r : EuclideanGroup d).linear • (0 : EuclideanSpace ℝ (Fin d)) + 0) +ᵥ (Space.origin d) := by
    show ((r : EuclideanGroup d).linear • (Space.origin d -ᵥ Space.origin d)
        + (r : EuclideanGroup d).translation) +ᵥ Space.origin d = _
    rw [vsub_self, h_trans]
  simp [h_rot]

/-- A rotation acts on the displacement from the origin by its orthogonal part, for every `p`:
`(r • p) -ᵥ origin = Q • (p -ᵥ origin)`. -/
lemma rotation_smul_vsub_origin (r : RotationGroup d) (p : Space d) :
    (r • p) -ᵥ Space.origin d = (r : EuclideanGroup d).linear • (p -ᵥ Space.origin d) := by
  rw [rotation_smul_eq]
  nth_rewrite 1 [← rotation_smul_origin r]
  rw [smul_vsub_smul]

/-- The rotation group acts on `Space d` **by isometries** (inherited from `dist_smul`). -/
lemma rotation_dist_smul (r : RotationGroup d) (p q : Space d) :
    dist (r • p) (r • q) = dist p q :=
  dist_smul (r : EuclideanGroup d) p q

/-! ## Part 3: relation to the affine isometry action (optional bridge)

`chartEuclidean_smul` records that, under the chart `Space.chartEuclidean` (`Space/Origin.lean`),
`p ↦ p -ᵥ origin`, the Part 1 action is the transport of `toAffineIsometryMulEquiv`
(`AffineGroup.lean`) from `EuclideanSpace` to `Space`. Nothing in Parts 1–2 depends on it. -/

/-- **The unification bridge.** Under the standard chart, the Euclidean action on `Space d` is the
transport of `toAffineIsometryMulEquiv` acting on `EuclideanSpace`:
`chart (g • p) = (toAffineIsometryMulEquiv g) (chart p)`. -/
lemma chartEuclidean_smul (g : EuclideanGroup d) (p : Space d) :
    Space.chartEuclidean d (g • p) = toAffineIsometryMulEquiv g (Space.chartEuclidean d p) := by
  rw [Space.chartEuclidean_apply]
  rw [toAffineIsometryMulEquiv_apply, toAffineIsometryHom_apply]
  have h_left : g • p -ᵥ Space.origin d = g.linear • (p -ᵥ Space.origin d) + g.translation := by
    exact
      (eq_vadd_iff_vsub_eq (g • p) (g.linear • (p -ᵥ Space.origin d) + g.translation)
            (Space.origin d)).mp
        rfl
  simp [h_left]
  exact add_comm' (g.linear • (p -ᵥ Space.origin d)) g.translation
end EuclideanGroup
