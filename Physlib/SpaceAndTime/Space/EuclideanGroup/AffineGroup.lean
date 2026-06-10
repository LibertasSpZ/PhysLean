/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Physlib.SpaceAndTime.Space.EuclideanGroup.Basic

/-!
# The inclusion of the Euclidean group into the affine isometry group

We include the abstract Euclidean group `EuclideanGroup n = ℝⁿ ⋊ O(n)` into Mathlib's affine
automorphism group, as the composite of two monoid homomorphisms

`EuclideanGroup n →* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _ →* AffineEquiv ℝ _ _`.

This composite, `Euclidean.toAffineEquiv`, is the result intended for use elsewhere. The final
section additionally upgrades the first homomorphism to a group isomorphism, exhibiting
`EuclideanGroup n` as the full group of affine isometries of Euclidean space; that strengthening is
self-contained and is not used by the inclusion.

## Main definitions

The inclusion:

* `OrthogonalToLinearIsometryEquiv` : an orthogonal matrix as a linear isometry equivalence of
  `EuclideanSpace ℝ (Fin n)`.
* `Euclidean.toAffineIsometryHom` : `⟨t, Q⟩ ↦ (x ↦ Q x + t)`, as a monoid homomorphism into the
  affine isometry group (first leg).
* `AffineIsometryEquiv.toAffineEquivHom` : `AffineIsometryEquiv.toAffineEquiv` as a monoid
  homomorphism (second leg).
* `Euclidean.toAffineEquiv` : the inclusion into the affine automorphism group, the composite of
  the two legs.

The optional strengthening (section `EuclideanIsometryEquiv`, not used by the inclusion):

* `LinearIsometryEquivToOrthogonal` : the inverse bridge, a linear isometry equivalence read back as
  an orthogonal matrix.
* `Euclidean.toAffineIsometryEquiv` : `Euclidean.toAffineIsometryHom` upgraded to a group
  isomorphism `EuclideanGroup n ≃* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`.
-/

@[expose] public section

variable {n : ℕ}

open scoped Matrix in
/-- An orthogonal matrix viewed as a linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def OrthogonalToLinearIsometryEquiv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin n)) Q).isometryOfInner fun x y => by
    simp only [DistribMulAction.toLinearEquiv_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    show (Q.val *ᵥ y.ofLp) ⬝ᵥ (Q.val *ᵥ x.ofLp) = y.ofLp ⬝ᵥ x.ofLp
    have hQ : (Q.val)ᵀ * Q.val = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hQ, Matrix.vecMul_one]

@[simp] lemma OrthogonalToLinearIsometryEquiv_apply
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    OrthogonalToLinearIsometryEquiv Q x = Q • x := rfl

/-! ### `One`/`Mul` projection lemmas for `EuclideanGroup`

These expose the semidirect-product formulas behind the `Group` instance so that `simp` can
reduce the translation/linear components of `1` and `A * B`. -/

@[simp] lemma EuclideanGroup.one_translation : (1 : EuclideanGroup n).translation = 0 := rfl
@[simp] lemma EuclideanGroup.one_linear : (1 : EuclideanGroup n).linear = 1 := rfl
@[simp] lemma EuclideanGroup.mul_translation (A B : EuclideanGroup n) :
    (A * B).translation = A.translation + A.linear • B.translation := rfl
@[simp] lemma EuclideanGroup.mul_linear (A B : EuclideanGroup n) :
    (A * B).linear = A.linear * B.linear := rfl

/-- The forward functor `⟨t, Q⟩ ↦ (x ↦ Q x + t)`, bundled as a monoid homomorphism from the
Euclidean group into the affine isometry group of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def Euclidean.toAffineIsometryHom :
    EuclideanGroup n →*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun A := AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
    (OrthogonalToLinearIsometryEquiv A.linear).toAffineIsometryEquiv
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x; simp
  map_mul' A B := by
    apply AffineIsometryEquiv.ext
    intro x
    simp [mul_smul, add_assoc]

/-- Unfolds `Euclidean.toAffineIsometryHom` into its translation and linear factors. -/
@[simp] lemma Euclidean.toAffineIsometryHom_apply (A : EuclideanGroup n) :
    Euclidean.toAffineIsometryHom A =
      AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
        (OrthogonalToLinearIsometryEquiv A.linear).toAffineIsometryEquiv := rfl

/-- `AffineIsometryEquiv.toAffineEquiv` bundled as a monoid homomorphism into the affine
automorphism group. -/
noncomputable def AffineIsometryEquiv.toAffineEquivHom :
    AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) →*
      AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun e := e.toAffineEquiv
  map_one' := by
    apply AffineEquiv.ext; intro x; trivial
  map_mul' e e' := by
    apply AffineEquiv.ext; intro x; simp

/-- The inclusion of the Euclidean group into Mathlib's affine automorphism group, as the
composite `EuclideanGroup →* AffineIsometryEquiv →* AffineEquiv`. -/
noncomputable def Euclidean.toAffineEquiv :
    EuclideanGroup n →* AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  AffineIsometryEquiv.toAffineEquivHom.comp Euclidean.toAffineIsometryHom

/-! ### Strengthening to an isomorphism

The first leg `Euclidean.toAffineIsometryHom` is in fact a group isomorphism: every affine isometry
of `EuclideanSpace ℝ (Fin n)` is `x ↦ Q x + t` for a unique orthogonal `Q` and translation `t`. We
record this as a `MulEquiv`, reusing the forward functor above and adding the inverse together with
the two round-trip identities. Nothing above this section depends on it. -/
section EuclideanIsometryEquiv

/-- A linear isometry equivalence read back as an orthogonal matrix, inverse to
`OrthogonalToLinearIsometryEquiv` (see the round-trip `@[simp]` lemmas below). -/
noncomputable def LinearIsometryEquivToOrthogonal
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
   let b := EuclideanSpace.basisFun (Fin n) ℝ
   ⟨LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv, by
    have hb : LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv
        = b.toBasis.toMatrix (b.map L) := by
      ext i j
      simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.map_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [hb]
    exact b.toMatrix_orthonormalBasis_mem_orthogonal (b.map L)⟩

/-- `LinearIsometryEquivToOrthogonal` is a right inverse of `OrthogonalToLinearIsometryEquiv`. -/
@[simp] lemma OrthogonalToLinearIsometryEquiv_right_inv
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    OrthogonalToLinearIsometryEquiv (LinearIsometryEquivToOrthogonal L) = L := by
    apply LinearIsometryEquiv.ext; intro x
    rw [OrthogonalToLinearIsometryEquiv_apply]
    show Matrix.toEuclideanLin (LinearIsometryEquivToOrthogonal L).val x = L x
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    show Matrix.toLin _ _
        (LinearMap.toMatrix _ _
          (L.toLinearEquiv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) x = L x
    rw [Matrix.toLin_toMatrix]
    rfl

/-- `LinearIsometryEquivToOrthogonal` is a left inverse of `OrthogonalToLinearIsometryEquiv`. -/
@[simp] lemma OrthogonalToLinearIsometryEquiv_left_inv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    LinearIsometryEquivToOrthogonal (OrthogonalToLinearIsometryEquiv Q) = Q := by
  apply Subtype.ext
  have hlin :
      ((OrthogonalToLinearIsometryEquiv Q).toLinearEquiv :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
        = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Q.val := by
    ext x; rfl
  show LinearMap.toMatrix _ _
      ((OrthogonalToLinearIsometryEquiv Q).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = Q.val
  rw [hlin, LinearMap.toMatrix_toLin]

/-- The affine map `x ↦ t +ᵥ L x`, projected to its linear isometry component, is `L`. -/
@[simp] lemma linearIsometryEquiv_constVAdd_mul
    (t : EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
        L.toAffineIsometryEquiv).linearIsometryEquiv) = L := by
  apply LinearIsometryEquiv.ext; intro x
  have h := (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
      L.toAffineIsometryEquiv).map_vsub x 0
  rw [vsub_eq_sub, sub_zero] at h
  rw [h]
  simp

/-- `EuclideanGroup n ≃* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`: the Euclidean group
is the group of affine isometries of Euclidean space. -/
noncomputable def Euclidean.toAffineIsometryEquiv :
    EuclideanGroup n ≃*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun := Euclidean.toAffineIsometryHom
  invFun e := ⟨e 0, LinearIsometryEquivToOrthogonal e.linearIsometryEquiv⟩
  left_inv A := by
    refine EuclideanGroup.ext ?_ ?_
    · simp
    · simp [linearIsometryEquiv_constVAdd_mul, OrthogonalToLinearIsometryEquiv_left_inv]
  right_inv e := by
    apply AffineIsometryEquiv.ext; intro x
    simp only [Euclidean.toAffineIsometryHom_apply,
      OrthogonalToLinearIsometryEquiv_right_inv,
      AffineIsometryEquiv.coe_mul, Function.comp_apply,
      LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      AffineIsometryEquiv.coe_constVAdd, vadd_eq_add]
    have h := e.map_vadd 0 x
    simp [vadd_eq_add, add_zero] at h
    rw [h, add_comm]
  map_mul' := Euclidean.toAffineIsometryHom.map_mul'

/-- `Euclidean.toAffineIsometryEquiv` agrees with `Euclidean.toAffineIsometryHom`. -/
@[simp] lemma Euclidean.toAffineIsometryEquiv_apply (A : EuclideanGroup n) :
    Euclidean.toAffineIsometryEquiv A = Euclidean.toAffineIsometryHom A := rfl

end EuclideanIsometryEquiv
