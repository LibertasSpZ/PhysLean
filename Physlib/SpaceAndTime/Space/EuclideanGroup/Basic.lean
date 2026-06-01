/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Euclidean group

This file defines the Euclidean group as translations composed with orthogonal maps, together
with the special Euclidean group, translation subgroup, rotation subgroups, and the inclusion of the
Euclidean group into the affine group.
-/

/-- An n-dimensional `Euclidean group` is a group of
rotations, reflections, and translations.
-/
@[ext]
structure EuclideanGroup (n : ℕ) where
  translation : EuclideanSpace ℝ (Fin n)
  linear : Matrix.orthogonalGroup (Fin n) ℝ

/-- Action of an orthogonal-group element on a Euclidean vector,
bridged through `WithLp`. -/
private def act {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Q.val.mulVec v.ofLp)

private lemma act_mul {n : ℕ} (Q Q' : Matrix.orthogonalGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : act (Q * Q') v = act Q (act Q' v) := by
  ext i
  simp [act, ← Matrix.mulVec_mulVec]

private lemma act_add {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) : act Q (u + v) = act Q u + act Q v := by
  ext i
  simp [act, Matrix.mulVec_add]

private lemma act_one {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : act 1 v = v := by
  ext i
  simp [act]

private lemma act_zero {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    act Q 0 = 0 := by
  ext i
  simp [act]

private lemma act_neg {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : act Q (-v) = -act Q v := by
  ext i
  simp [act, Matrix.mulVec_neg]

/-- Group structure on E(n) is determined by Translations ⋊ Orthogonal. -/
noncomputable instance : Group (EuclideanGroup n) where
  mul A B := ⟨A.translation + act A.linear B.translation, A.linear * B.linear⟩
  mul_assoc A B C := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + act A.linear B.translation + act (A.linear * B.linear) C.translation
        = A.translation + act A.linear (B.translation + act B.linear C.translation)
      rw [act_mul, act_add, add_assoc]
    · exact mul_assoc A.linear B.linear C.linear
  one := ⟨0, 1⟩
  one_mul A := by
    refine EuclideanGroup.ext ?_ ?_
    · show 0 + act 1 A.translation = A.translation
      rw [zero_add, act_one]
    · exact one_mul A.linear
  mul_one A := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + act A.linear 0 = A.translation
      rw [act_zero, add_zero]
    · exact mul_one A.linear
  inv A := ⟨act A.linear⁻¹ (-A.translation), A.linear⁻¹⟩
  inv_mul_cancel A := by
    refine EuclideanGroup.ext ?_ ?_
    · show act A.linear⁻¹ (-A.translation) + act A.linear⁻¹ A.translation = 0
      rw [act_neg, neg_add_cancel]
    · exact inv_mul_cancel A.linear

private lemma det_coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val.det = (Q.val.det)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← Matrix.det_mul, ← Submonoid.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, Matrix.det_one]

private lemma coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val = (Q.val)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]

/-- Special Euclidean Group is the subgroup with det(Q) = 1 where Q ∈ O(n) -/
def specialEuclideanGroup (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.linear.val.det = 1}
  mul_mem' {a b} ha hb := by
    show (a.linear * b.linear).val.det = 1
    rw [Submonoid.coe_mul, Matrix.det_mul, ha, hb, one_mul]
  one_mem' := by
    show (1 : ↥(Matrix.orthogonalGroup (Fin n) ℝ)).val.det = 1
    rw [OneMemClass.coe_one, Matrix.det_one]
  inv_mem' {a} ha := by
    show (a.linear⁻¹).val.det = 1
    rw [det_coe_inv, ha, inv_one]

/-- The inclusion of the special Euclidean group into the Euclidean group. -/
noncomputable def specialEuclideanGroup.incl (n : ℕ) :
    specialEuclideanGroup n →* EuclideanGroup n := (specialEuclideanGroup n).subtype

/-- Translation is the subgroup with Q = 1. -/
def translationGroup (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.linear.val = 1}
  mul_mem' {a b} ha hb := by
    show (a.linear * b.linear).val = 1
    rw [Submonoid.coe_mul, ha, hb, one_mul]
  one_mem' := by
    show (1 : ↥(Matrix.orthogonalGroup (Fin n) ℝ)).val = 1
    rw [OneMemClass.coe_one]
  inv_mem' {a} ha := by
    show (a.linear⁻¹).val = 1
    rw [coe_inv, ha, inv_one]

/-- The inclusion of the translation subgroup into the Euclidean group. -/
noncomputable def translationGroup.incl (n : ℕ) :
    translationGroup n →* EuclideanGroup n := (translationGroup n).subtype

/-- MonoidHom including a translation vector into the Euclidean Group. -/
def translationVector.incl (n : ℕ) :
    Multiplicative (EuclideanSpace ℝ (Fin n)) →* EuclideanGroup n where
  toFun v := ⟨v.toAdd, 1⟩
  map_one' := by rfl
  map_mul' x y := by
    refine EuclideanGroup.ext ?_ ?_
    · show Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + act 1 (Multiplicative.toAdd y)
      simp [act_one]
    · show 1 = 1 * 1
      simp [mul_one]

/-- An API feature: the translation vector inclusion image is the translationGroup carrier. -/
lemma translationVector.incl_range :
    Set.range (@translationVector.incl n) = (translationGroup n : Set (EuclideanGroup n)) := by
  ext g
  constructor
  · rintro ⟨v, hv⟩
    show g.linear.val = 1
    rw [← hv]
    rfl
  · intro h
    rw [Set.mem_range]
    refine ⟨g.translation, ?_⟩
    show (⟨g.translation, 1⟩ : EuclideanGroup n) = g
    refine EuclideanGroup.ext rfl ?_
    apply Subtype.ext
    simp [h.symm]

/-- The translation by the zero vector is the identity of the Euclidean group. -/
lemma translation_zero : translationVector.incl n
    (Multiplicative.ofAdd (0 : EuclideanSpace ℝ (Fin n))) = 1 := by
  simp

/-- The subgroup of `EuclideanGroup n` whose elements fix the origin
(translation = 0). This is the copy of `O(n)` sitting inside `E(n)`. -/
def originStabilizer (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.translation = 0}
  mul_mem' {a b} ha hb := by
    show a.translation + act a.linear b.translation = 0
    rw [ha, hb, act_zero, zero_add]
  one_mem' := rfl
  inv_mem' {a} ha := by
    show act a.linear⁻¹ (-a.translation) = 0
    rw [ha, neg_zero, act_zero]

/-- Rotation Group is the subgroup of E(n) consisting of rotations about the origin:
elements with `det = 1` (orientation-preserving) and `translation = 0` (origin-fixing). -/
noncomputable def RotationGroup (n : ℕ) : Subgroup (EuclideanGroup n) :=
  specialEuclideanGroup n ⊓ originStabilizer n

/-- The inclusion of the rotation subgroup into the Euclidean group. -/
noncomputable def RotationGroup.incl (n : ℕ) :
    RotationGroup n →* EuclideanGroup n := (RotationGroup n).subtype

variable {n} (p : EuclideanSpace ℝ (Fin n))
/-- The subgroup of rotation about a spatial point `p : EuclideanSpace ℝ (Fin n)` consists of
elements of the form T(p) * r * T(-p) with T(·): translationVector.incl n (Multiplicative.ofAdd ·)
and r : RotationGroup where r is viewed as a rotation about the origin. Note T(-p) = T(p)⁻¹.
-/
noncomputable def rotationsAbout : Subgroup (EuclideanGroup n) where
  carrier := {g | ∃ r : RotationGroup n, g = translationVector.incl n (Multiplicative.ofAdd p)
    * (r : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p))}
  mul_mem' {a b} ha hb := by
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    use r1 * r2
    rw [hr1, hr2]
    simp only [ofAdd_neg, map_inv, conj_mul, Subgroup.coe_mul]
  one_mem' := by
    simp; use 1
    constructor
    · simp
    · simp
  inv_mem' {a} ha := by
    obtain ⟨ra, hra⟩ := ha
    use ra⁻¹
    rw [hra]
    simp [mul_inv_rev, mul_assoc]

/-- The inclusion of rotations about `p` into the Euclidean group. -/
noncomputable def rotationsAbout.incl : rotationsAbout p →* EuclideanGroup n :=
  (rotationsAbout p).subtype

/-- Conjugate a rotation about `p` back to a rotation about the origin. -/
noncomputable def rotationsAbout.toOrigin :
    rotationsAbout p →* RotationGroup n where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd (-p))
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd p), by
      obtain ⟨g, hg⟩ := g
      obtain ⟨r, hr⟩ := hg
      simp; rw [hr]; simp [mul_assoc]
      ⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hr1, hr2]
    simp [mul_assoc]

/-- Conjugate a rotation about the origin to a rotation about `p`. -/
noncomputable def rotationsAbout.fromOrigin :
    RotationGroup n →* rotationsAbout p where
  toFun g := ⟨translationVector.incl n (Multiplicative.ofAdd p)
    * (g : EuclideanGroup n) * translationVector.incl n (Multiplicative.ofAdd (-p)), by use g
      ⟩
  map_one' := by simp
  map_mul' := by
    intro x y
    obtain ⟨a, ha⟩ := x
    obtain ⟨b, hb⟩ := y
    obtain ⟨r1, hr1⟩ := ha
    obtain ⟨r2, hr2⟩ := hb
    simp

private lemma rotationsAbout_forward_identity :
    (rotationsAbout.fromOrigin p).comp (rotationsAbout.toOrigin p) =
      MonoidHom.id (rotationsAbout p) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold rotationsAbout.toOrigin
  unfold rotationsAbout.fromOrigin
  simp [mul_assoc]

private lemma rotationsAbout_backward_identity :
    (rotationsAbout.toOrigin p).comp (rotationsAbout.fromOrigin p) =
      MonoidHom.id (RotationGroup n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply, SetLike.coe_eq_coe]
  unfold rotationsAbout.toOrigin
  unfold rotationsAbout.fromOrigin
  simp [mul_assoc]

/-- API feature: conjugation by the translation `T(p)` exhibits the rotations about `p` as
isomorphic to the rotations about the origin `RotationGroup n`. -/
noncomputable def rotationsAboutEquiv : rotationsAbout p ≃* RotationGroup n :=
  MonoidHom.toMulEquiv (rotationsAbout.toOrigin p) (rotationsAbout.fromOrigin p)
    (rotationsAbout_forward_identity p) (rotationsAbout_backward_identity p)

/-- API feature: the degenerate identity that `rotationsAbout 0 = RotationGroup n` -/
lemma rotationsAbout_zero : rotationsAbout (0 : EuclideanSpace ℝ (Fin n)) = RotationGroup n := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨g1, hg1⟩ := hg
    simp at hg1
    rw [hg1]
    simp
  · intro hg
    use ⟨g, hg⟩
    simp
/-- Rotations are members of special orthogonal groups and can be viewed as members of
orthogonal groups. -/
def specialOrthogonal.incl (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* Matrix.orthogonalGroup (Fin n) ℝ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

/-- The Euclidean group element given by a rotation about the origin (zero translation). -/
def EuclideanGroup.ofRotation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    EuclideanGroup n := ⟨0, specialOrthogonal.incl n Q⟩

/-- Specialization to a group element from a rotation and a translation. -/
def EuclideanGroup.ofRotationTranslation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) : EuclideanGroup n :=
  ⟨t, specialOrthogonal.incl n Q⟩

/-- The specialization projects back to the translation component. -/
@[simp]
lemma ofRotationTranslation.toTranslation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (EuclideanGroup.ofRotationTranslation Q t).translation = t := rfl

/-- The specialization projects back to the rotation component. -/
@[simp]
lemma ofRotationTranslation.toRotation (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (EuclideanGroup.ofRotationTranslation Q t).linear = specialOrthogonal.incl n Q := rfl

/-- API feature: the inclusion image decomposes as group product. -/
@[simp]
lemma ofRotationTranslation.decompose (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    (EuclideanGroup.ofRotationTranslation Q t) =
    (translationVector.incl n (Multiplicative.ofAdd t)) * (EuclideanGroup.ofRotation (Q)) := by
  refine EuclideanGroup.ext ?_ ?_
  · show t = t + act 1 0
    rw [act_zero, add_zero]
  · show specialOrthogonal.incl n Q = 1 * specialOrthogonal.incl n Q
    rw [one_mul]

/-- The isomorphism's forward map: a special orthogonal matrix as a rotation about the origin. -/
noncomputable def specialOrthogonal.toRotation (n : ℕ):
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* RotationGroup n where
  toFun g := ⟨EuclideanGroup.ofRotation g, by
      refine ⟨?_, ?_⟩
      · show (EuclideanGroup.ofRotation g).linear.val.det = 1
        exact (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).right
      · show (EuclideanGroup.ofRotation g).translation = 0
        rfl
      ⟩
  map_one' := rfl
  map_mul' x y := by
    apply Subtype.ext
    refine EuclideanGroup.ext ?_ ?_
    · show (0 : EuclideanSpace ℝ (Fin n)) = 0 + act (specialOrthogonal.incl n x) 0
      rw [act_zero, add_zero]
    · show specialOrthogonal.incl n (x * y)
          = specialOrthogonal.incl n x * specialOrthogonal.incl n y
      rw [map_mul]

/-- The isomorphism's inverse map: the linear part of a rotation about the origin, as a special
orthogonal matrix. -/
noncomputable def specialOrthogonal.fromRotation (n : ℕ):
    RotationGroup n →* Matrix.specialOrthogonalGroup (Fin n) ℝ where
  toFun g := ⟨g.val.linear, ⟨g.val.linear.property,(g.property).left⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma specialOrthogonal_forward_identity :
    (specialOrthogonal.fromRotation n).comp (specialOrthogonal.toRotation n) =
      MonoidHom.id (Matrix.specialOrthogonalGroup (Fin n) ℝ) := by
  apply MonoidHom.ext
  intro x
  rfl

private lemma specialOrthogonal_backward_identity :
     (specialOrthogonal.toRotation n).comp (specialOrthogonal.fromRotation n) =
      MonoidHom.id (RotationGroup n) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  refine EuclideanGroup.ext ?_ ?_
  · show (0 : EuclideanSpace ℝ (Fin n)) = x.val.translation
    have h : x.val.translation = 0 := x.property.right
    rw [h]
  · rfl

/-- API feature: SO(n) ≃* RotationGroup n -/
noncomputable def specialOrthogonalEquiv :
    Matrix.specialOrthogonalGroup (Fin n) ℝ ≃* RotationGroup n :=
    MonoidHom.toMulEquiv (specialOrthogonal.toRotation n) (specialOrthogonal.fromRotation n)
    (specialOrthogonal_forward_identity) (specialOrthogonal_backward_identity)

/-- An n-dimensional `Affine group` is the group of invertible affine transformations:
translations composed with general linear maps. -/
@[ext]
structure AffineGroup (n : ℕ) where
  translation : EuclideanSpace ℝ (Fin n)
  linear : Matrix.GeneralLinearGroup (Fin n) ℝ

/-- Action of a general-linear-group element on a Euclidean vector,
bridged through `WithLp`. -/
private def act_affine {n : ℕ} (Q : Matrix.GeneralLinearGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Q.val.mulVec v.ofLp)

private lemma act_affine_mul {n : ℕ} (Q Q' : Matrix.GeneralLinearGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : act_affine (Q * Q') v = act_affine Q (act_affine Q' v) := by
  ext i
  simp [act_affine, ← Matrix.mulVec_mulVec]

private lemma act_affine_add {n : ℕ} (Q : Matrix.GeneralLinearGroup (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    act_affine Q (u + v) = act_affine Q u + act_affine Q v := by
  ext i
  simp [act_affine, Matrix.mulVec_add]

private lemma act_affine_one {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : act_affine 1 v = v := by
  ext i
  simp [act_affine]

private lemma act_affine_zero {n : ℕ} (Q : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    act_affine Q 0 = 0 := by
  ext i
  simp [act_affine]

private lemma act_affine_neg {n : ℕ} (Q : Matrix.GeneralLinearGroup (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) : act_affine Q (-v) = -act_affine Q v := by
  ext i
  simp [act_affine, Matrix.mulVec_neg]

/-- Group structure on Aff(n) is determined by Translations ⋊ GeneralLinear. -/
noncomputable instance : Group (AffineGroup n) where
  mul A B := ⟨A.translation + act_affine A.linear B.translation, A.linear * B.linear⟩
  mul_assoc A B C := by
    refine AffineGroup.ext ?_ ?_
    · show A.translation + act_affine A.linear B.translation
          + act_affine (A.linear * B.linear) C.translation
        = A.translation + act_affine A.linear (B.translation + act_affine B.linear C.translation)
      rw [act_affine_mul, act_affine_add, add_assoc]
    · exact mul_assoc A.linear B.linear C.linear
  one := ⟨0, 1⟩
  one_mul A := by
    refine AffineGroup.ext ?_ ?_
    · show 0 + act_affine 1 A.translation = A.translation
      rw [zero_add, act_affine_one]
    · exact one_mul A.linear
  mul_one A := by
    refine AffineGroup.ext ?_ ?_
    · show A.translation + act_affine A.linear 0 = A.translation
      rw [act_affine_zero, add_zero]
    · exact mul_one A.linear
  inv A := ⟨act_affine A.linear⁻¹ (-A.translation), A.linear⁻¹⟩
  inv_mul_cancel A := by
    refine AffineGroup.ext ?_ ?_
    · show act_affine A.linear⁻¹ (-A.translation) + act_affine A.linear⁻¹ A.translation = 0
      rw [act_affine_neg, neg_add_cancel]
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

/-- The inclusion of the Euclidean group into the affine group is injective, so it realizes
`E(n)` as a subgroup of `Aff(n)` (issue #940, requirement 5). -/
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
