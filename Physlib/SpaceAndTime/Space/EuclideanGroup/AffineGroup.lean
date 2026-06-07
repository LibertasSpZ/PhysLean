/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu
-/
module

public import Physlib.SpaceAndTime.Space.EuclideanGroup.Basic

/-!
# The affine group and the inclusion of the Euclidean group

This file defines the `n`-dimensional affine group `AffineGroup n` as the semidirect product of
translations of `EuclideanSpace ℝ (Fin n)` with the general linear group `GL(n, ℝ)`, equips it with
a group structure, and constructs the inclusion of the Euclidean group `EuclideanGroup n` into it.

It then connects this concrete affine group to Mathlib's affine automorphism group
`AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`: the group isomorphism `AffineGroup.toAffineEquiv`
identifies the two, and composing it with `Euclidean.incl` realizes the Euclidean group inside
Mathlib's affine group as `Euclidean.toAffineEquiv`.

## Main definitions

* `AffineGroup n` : the affine group `ℝⁿ ⋊ GL(n, ℝ)`.
* `Euclidean.incl` : the inclusion `EuclideanGroup n →* AffineGroup n`.
* `AffineGroup.toAffineEquiv` : the group isomorphism between `AffineGroup n` and Mathlib's
  `AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`.
* `Euclidean.toAffineEquiv` : the inclusion of the Euclidean group into Mathlib's affine group.

The isomorphism `AffineGroup.toAffineEquiv` uses `GLToLinEquiv` and `LinEquivToGL` to move
between matrix linear parts and linear automorphisms of Euclidean space.
-/

@[expose] public section

variable {n : ℕ}

/-- The group of invertible affine transformations of `EuclideanSpace ℝ (Fin n)`. -/
@[ext]
structure AffineGroup (n : ℕ) where
  /-- The translation part of an affine transformation. -/
  translation : EuclideanSpace ℝ (Fin n)
  /-- The linear part of an affine transformation, as an invertible matrix. -/
  linear : Matrix.GeneralLinearGroup (Fin n) ℝ

/-- Group structure on `Aff(n) = ℝ^n ⋊ GL(n)`, with the usual semidirect-product
multiplication. -/
noncomputable instance : Group (AffineGroup n) where
  mul A B := ⟨A.translation + A.linear • B.translation, A.linear * B.linear⟩
  mul_assoc A B C := by
    refine AffineGroup.ext ?_ ?_
    · show A.translation + A.linear • B.translation + (A.linear * B.linear) • C.translation
        = A.translation + A.linear • (B.translation + B.linear • C.translation)
      rw [mul_smul, smul_add, add_assoc]
    · exact mul_assoc A.linear B.linear C.linear
  one := ⟨0, 1⟩
  one_mul A := by
    refine AffineGroup.ext ?_ ?_
    · show 0 + (1 : Matrix.GeneralLinearGroup (Fin n) ℝ) • A.translation = A.translation
      rw [zero_add, one_smul]
    · exact one_mul A.linear
  mul_one A := by
    refine AffineGroup.ext ?_ ?_
    · show A.translation + A.linear • 0 = A.translation
      rw [smul_zero, add_zero]
    · exact mul_one A.linear
  inv A := ⟨A.linear⁻¹ • (-A.translation), A.linear⁻¹⟩
  inv_mul_cancel A := by
    refine AffineGroup.ext ?_ ?_
    · show A.linear⁻¹ • (-A.translation) + A.linear⁻¹ • A.translation = 0
      rw [← smul_add, neg_add_cancel, smul_zero]
    · exact inv_mul_cancel A.linear

/-- Inclusion of the Euclidean group into the Affine group. -/
noncomputable def Euclidean.incl :
    EuclideanGroup n →* AffineGroup n where
  toFun A := ⟨A.translation, Matrix.GeneralLinearGroup.mkOfDetNeZero A.linear.val
    (Matrix.isUnit_det_of_left_inverse A.linear.property.left).ne_zero⟩
  map_one' := by
    refine AffineGroup.ext ?_ ?_
    · rfl
    · apply Units.ext
      show (1 : Matrix.orthogonalGroup (Fin n) ℝ).val = (1 : Matrix (Fin n) (Fin n) ℝ)
      rw [OneMemClass.coe_one]
  map_mul' x y := by
    refine AffineGroup.ext ?_ ?_
    · rfl
    · apply Units.ext
      show ((x.linear * y.linear).val : Matrix (Fin n) (Fin n) ℝ)
          = (x.linear.val * y.linear.val : Matrix (Fin n) (Fin n) ℝ)
      rw [Submonoid.coe_mul]

/-- The inclusion of the Euclidean group into the affine group is injective. -/
lemma Euclidean.incl_injective : Function.Injective (Euclidean.incl (n := n)) := by
  intros x y hxy
  unfold incl at hxy
  simp at hxy
  refine EuclideanGroup.ext ?_ ?_
  · exact hxy.left
  · apply Subtype.ext
    exact congrArg Units.val hxy.right

/-- The inclusion into the affine group preserves the rotation-translation decomposition; this is
the `map_mul` transport of `ofRotationTranslation.decompose`. -/
lemma Euclidean.incl_decompose (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    Euclidean.incl (EuclideanGroup.ofRotationTranslation Q t) =
      Euclidean.incl (translationVector.incl n (Multiplicative.ofAdd t)) *
      Euclidean.incl (EuclideanGroup.ofRotation Q) := by
  rw [ofRotationTranslation.decompose, map_mul]

/-!
## Connection to Mathlib's affine group

The declarations below identify the concrete `AffineGroup n` with Mathlib's affine automorphism
group `AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`, and transport the Euclidean inclusion across
that identification.
-/

/-- A general linear matrix viewed as a linear automorphism of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def GLToLinEquiv (Q : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  DistribMulAction.toLinearEquiv ℝ _ Q

/-- A linear automorphism of `EuclideanSpace ℝ (Fin n)`, read as a general linear matrix in the
standard basis. -/
noncomputable def LinEquivToGL
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.GeneralLinearGroup (Fin n) ℝ :=
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  Matrix.GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix b b e)
    (e.isUnit_det b b).ne_zero

/-! ### Round-trip lemmas between `GLToLinEquiv` and `LinEquivToGL`

These lemmas show that the two coordinate bridges are mutually inverse and that `GLToLinEquiv`
is multiplicative. -/

/-- Reading a linear automorphism as a matrix and back recovers the original automorphism. -/
lemma GLToLinEquiv_linEquivToGL
    (e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    GLToLinEquiv (LinEquivToGL e) = e := by
  apply LinearEquiv.ext
  intro x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change Matrix.toLin b b
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix b b e) _ :
        Matrix (Fin n) (Fin n) ℝ) x = e x
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.toLin_toMatrix]
  rfl

/-- Viewing a general linear matrix as a linear automorphism and back recovers the original
matrix. -/
lemma linEquivToGL_GLToLinEquiv (Q : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    LinEquivToGL (GLToLinEquiv Q) = Q := by
  apply Units.ext
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let e := Matrix.toLin b b Q
  change (Matrix.GeneralLinearGroup.mkOfDetNeZero (LinearMap.toMatrix b b e) _ :
      Matrix (Fin n) (Fin n) ℝ) = Q
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, LinearMap.toMatrix_toLin]

/-- `GLToLinEquiv` sends products of matrices to compositions of linear automorphisms. -/
lemma GLToLinEquiv_mul (Q Q' : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    GLToLinEquiv (Q * Q') = GLToLinEquiv Q * GLToLinEquiv Q' := by
  ext v; simp [GLToLinEquiv, mul_smul]

/-- The group isomorphism between `AffineGroup n = ℝⁿ ⋊ GL(n, ℝ)` and Mathlib's affine
automorphism group. It sends `⟨t, Q⟩` to the affine equivalence `x ↦ Q x + t`. -/
noncomputable def AffineGroup.toAffineEquiv :
    AffineGroup n ≃* AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun A := AffineEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
    (GLToLinEquiv A.linear).toAffineEquiv
  invFun e := ⟨e 0, LinEquivToGL e.linear⟩
  left_inv := by
    intro A
    refine AffineGroup.ext ?_ ?_
    · simp only [AffineEquiv.coe_mul, Function.comp_apply,
        LinearEquiv.coe_toAffineEquiv, AffineEquiv.constVAdd_apply,
        map_zero]
      rw [vadd_eq_add, add_zero]
    · simp only
      rw [← AffineEquiv.linearHom_apply, map_mul]
      simp only [AffineEquiv.linearHom_apply]
      change LinEquivToGL (1 * GLToLinEquiv A.linear) = A.linear
      rw [one_mul]
      exact linEquivToGL_GLToLinEquiv A.linear
  right_inv := by
    intro e
    simp only [GLToLinEquiv_linEquivToGL]
    apply AffineEquiv.ext; intro x
    simp only [AffineEquiv.coe_mul, Function.comp_apply,
        LinearEquiv.coe_toAffineEquiv, AffineEquiv.constVAdd_apply, vadd_eq_add]
    rw [add_comm, ← vadd_eq_add, ← e.map_vadd 0 x, vadd_eq_add, add_zero]
  map_mul' x y := by
    apply AffineEquiv.ext; intro p
    simp only [AffineEquiv.coe_mul, Function.comp_apply,
      AffineEquiv.constVAdd_apply, LinearEquiv.coe_toAffineEquiv, vadd_eq_add,
      GLToLinEquiv, DistribMulAction.toLinearEquiv_apply]
    show x.translation + x.linear • y.translation + (x.linear * y.linear) • p =
      x.translation + x.linear • (y.translation + y.linear • p)
    simp [add_assoc, mul_smul]

/-- The inclusion of the Euclidean group into Mathlib's affine automorphism group. -/
noncomputable def Euclidean.toAffineEquiv :
    EuclideanGroup n →* AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  (AffineGroup.toAffineEquiv (n := n)).toMonoidHom.comp Euclidean.incl
