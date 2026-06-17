/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# The origin of `Space` and the Euclidean chart

This file isolates two basepoint-dependent pieces of the `Space` API so they can be shared without
importing the full vector-space structure (`Space/Module.lean`) or the Euclidean action
(`Space/EuclideanGroup/Action.lean`).

* `Space.origin` — the coordinate origin (the point all of whose coordinates vanish). It is
  definitionally the zero of the vector-space structure on `Space d` (`Space.origin_eq_zero`,
  `Space/Module.lean`), but is provided here as a plain definition so this file need not import
  that structure.
* `Space.chartEuclidean` — the standard affine isometry `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`,
  `p ↦ p -ᵥ origin`, identifying a point with its coordinate vector relative to the origin.
-/

@[expose] public section

namespace Space

/-- The coordinate origin of `Space d`, the point all of whose coordinates vanish; the basepoint
for the Euclidean action. Definitionally `(0 : Space d)` (see `Space.origin_eq_zero`). -/
def origin (d : ℕ) : Space d := ⟨0⟩

@[simp] lemma origin_apply (d : ℕ) (i : Fin d) : (origin d) i = 0 := rfl

/-- The standard chart `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`, `p ↦ p -ᵥ origin`, identifying a
point with its coordinate vector relative to the origin. -/
noncomputable def chartEuclidean (d : ℕ) :
    Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (AffineIsometryEquiv.vaddConst ℝ (origin d)).symm

@[simp] lemma chartEuclidean_apply (d : ℕ) (p : Space d) :
    chartEuclidean d p = p -ᵥ origin d := rfl

end Space
