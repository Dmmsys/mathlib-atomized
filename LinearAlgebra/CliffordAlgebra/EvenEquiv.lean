/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

This file provides some notable isomorphisms regarding the even subalgebra, `CliffordAlgebra.even`.

## Main definitions

* `CliffordAlgebra.equivEven`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `CliffordAlgebra.EquivEven.Q'`: The quadratic form used by this "one-up" algebra.
  * `CliffordAlgebra.toEven`: The simp-normal form of the forward direction of this isomorphism.
  * `CliffordAlgebra.ofEven`: The simp-normal form of the reverse direction of this isomorphism.

* `CliffordAlgebra.evenEquivEvenNeg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `CliffordAlgebra.evenToNeg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `CliffordAlgebra.coe_toEven_reverse_involute`: the behavior of `CliffordAlgebra.toEven` on the
  "Clifford conjugate", that is `CliffordAlgebra.reverse` composed with
  `CliffordAlgebra.involute`.
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `CliffordAlgebra.equivEven` -/


namespace EquivEven

/--
Definition of `Q'` / `Q'` 的定义

English:
abbreviation Q'
  signature: : QuadraticForm R (M × R)
  body: Q.prod -QuadraticMap.sq (R := R)

中文:
缩写 Q'
  签名: : QuadraticForm R (M × R)
  定义体: Q.prod -QuadraticMap.sq (R := R)

Depends on / 依赖: Q.prod, QuadraticMap, QuadraticMap.sq
-/
abbrev Q' : QuadraticForm R (M × R) :=
Q.prod -QuadraticMap.sq (R := R)

/--
theorem `Q'_apply` / 定理 `Q'_apply`

English:
theorem Q'_apply
  given: (m : M × R)
  statement: Q' Q m = Q m.1 - m.2 * m.2
  proof: (sub_eq_add_neg _ _).symm

中文:
定理 Q'_apply
  条件: (m : M × R)
  结论: Q' Q m = Q m.1 - m.2 * m.2
  证明: (sub_eq_add_neg _ _).symm
-/
theorem Q'_apply (m : M × R) : Q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm

/--
Definition of `e0` / `e0` 的定义

English:
definition e0
  signature: : CliffordAlgebra (Q' Q)
  body: ι (Q' Q) (0, 1)

中文:
定义 e0
  签名: : CliffordAlgebra (Q' Q)
  定义体: ι (Q' Q) (0, 1)
-/
def e0 : CliffordAlgebra (Q' Q) :=
  ι (Q' Q) (0, 1)

/--
Definition of `v` / `v` 的定义

English:
definition v
  signature: : M ->ₗ[R] CliffordAlgebra (Q' Q)
  body: ι (Q' Q) ∘ₗ LinearMap.inl _ _ _

中文:
定义 v
  签名: : M ->ₗ[R] CliffordAlgebra (Q' Q)
  定义体: ι (Q' Q) ∘ₗ LinearMap.inl _ _ _

Depends on / 依赖: LinearMap, LinearMap.inl
-/
def v : M ->ₗ[R] CliffordAlgebra (Q' Q) :=
  ι (Q' Q) ∘ₗ LinearMap.inl _ _ _

/--
theorem `ι_eq_v_add_smul_e0` / 定理 `ι_eq_v_add_smul_e0`

English:
theorem ι_eq_v_add_smul_e0
  given: (m : M) (r : R)
  statement: ι (Q' Q) (m, r) = v Q m + r • e0 Q
  proof: by
  rw [e0]; rw [v]; rw [LinearMap.comp_apply]; rw [LinearMap.inl_apply]; rw [← map_smul]; rw [Prod.smul_mk]; rw [smul_zero]; rw [smul_eq_mul]; rw [mul_one]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]

中文:
定理 ι_eq_v_add_smul_e0
  条件: (m : M) (r : R)
  结论: ι (Q' Q) (m, r) = v Q m + r • e0 Q
  证明: by
  rw [e0]; rw [v]; rw [LinearMap.comp_apply]; rw [LinearMap.inl_apply]; rw [← map_smul]; rw [Prod.smul_mk]; rw [smul_zero]; rw [smul_eq_mul]; rw [mul_one]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.inl_apply, Prod.mk_add_mk, Prod.smul_mk, add_zero, comp_apply, inl_apply, map_add, map_smul, mk_add_mk, mul_one, smul_eq_mul, smul_mk, smul_zero, zero_add
-/
theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (Q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0]; rw [v]; rw [LinearMap.comp_apply]; rw [LinearMap.inl_apply]; rw [← map_smul]; rw [Prod.smul_mk]; rw [smul_zero]; rw [smul_eq_mul]; rw [mul_one]; rw [← map_add]; rw [Prod.mk_add_mk]; rw [zero_add]; rw [add_zero]

/--
theorem `e0_mul_e0` / 定理 `e0_mul_e0`

English:
theorem e0_mul_e0
  statement: e0 Q * e0 Q = -1
  proof: (ι_sq_scalar _ _).trans by simp

中文:
定理 e0_mul_e0
  结论: e0 Q * e0 Q = -1
  证明: (ι_sq_scalar _ _).trans by simp
-/
theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
(ι_sq_scalar _ _).trans by simp

/--
theorem `v_sq_scalar` / 定理 `v_sq_scalar`

English:
theorem v_sq_scalar
  given: (m : M)
  statement: v Q m * v Q m = algebraMap _ _ (Q m)
  proof: (ι_sq_scalar _ _).trans by simp

中文:
定理 v_sq_scalar
  条件: (m : M)
  结论: v Q m * v Q m = algebraMap _ _ (Q m)
  证明: (ι_sq_scalar _ _).trans by simp
-/
theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
(ι_sq_scalar _ _).trans by simp

set_option backward.defeqAttrib.useBackward true in
/--
theorem `neg_e0_mul_v` / 定理 `neg_e0_mul_v`

English:
theorem neg_e0_mul_v
  given: (m : M)
  statement: -(e0 Q * v Q m) = v Q m * e0 Q
  proof: by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  simp [QuadraticMap.polar]

中文:
定理 neg_e0_mul_v
  条件: (m : M)
  结论: -(e0 Q * v Q m) = v Q m * e0 Q
  证明: by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  simp [QuadraticMap.polar]

Depends on / 依赖: QuadraticMap, QuadraticMap.polar, neg_eq_of_add_eq_zero_right
-/
theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans ?_)
  simp [QuadraticMap.polar]

/--
theorem `neg_v_mul_e0` / 定理 `neg_v_mul_e0`

English:
theorem neg_v_mul_e0
  given: (m : M)
  statement: -(v Q m * e0 Q) = e0 Q * v Q m
  proof: by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm

@[simp]

中文:
定理 neg_v_mul_e0
  条件: (m : M)
  结论: -(v Q m * e0 Q) = e0 Q * v Q m
  证明: by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm

@[simp]

Depends on / 依赖: neg_e0_mul_v, neg_eq_iff_eq_neg
-/
theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_eq_neg]
  exact (neg_e0_mul_v _ m).symm

@[simp]
/--
theorem `e0_mul_v_mul_e0` / 定理 `e0_mul_v_mul_e0`

English:
theorem e0_mul_v_mul_e0
  given: (m : M)
  statement: e0 Q * v Q m * e0 Q = v Q m
  proof: by
  rw [← neg_v_mul_e0]; rw [← neg_mul]; rw [mul_assoc]; rw [e0_mul_e0]; rw [mul_neg_one]; rw [neg_neg]

@[simp]

中文:
定理 e0_mul_v_mul_e0
  条件: (m : M)
  结论: e0 Q * v Q m * e0 Q = v Q m
  证明: by
  rw [← neg_v_mul_e0]; rw [← neg_mul]; rw [mul_assoc]; rw [e0_mul_e0]; rw [mul_neg_one]; rw [neg_neg]

@[simp]

Depends on / 依赖: e0_mul_e0, mul_assoc, mul_neg_one, neg_mul, neg_neg, neg_v_mul_e0
-/
theorem e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m := by
  rw [← neg_v_mul_e0]; rw [← neg_mul]; rw [mul_assoc]; rw [e0_mul_e0]; rw [mul_neg_one]; rw [neg_neg]

@[simp]
/--
theorem `reverse_v` / 定理 `reverse_v`

English:
theorem reverse_v
  given: (m : M)
  statement: reverse (Q := Q' Q) (v Q m) = v Q m
  proof: reverse_ι _

@[simp]

中文:
定理 reverse_v
  条件: (m : M)
  结论: reverse (Q := Q' Q) (v Q m) = v Q m
  证明: reverse_ι _

@[simp]
-/
theorem reverse_v (m : M) : reverse (Q := Q' Q) (v Q m) = v Q m :=
  reverse_ι _

@[simp]
/--
theorem `involute_v` / 定理 `involute_v`

English:
theorem involute_v
  given: (m : M)
  statement: involute (v Q m) = -v Q m
  proof: involute_ι _

@[simp]

中文:
定理 involute_v
  条件: (m : M)
  结论: involute (v Q m) = -v Q m
  证明: involute_ι _

@[simp]
-/
theorem involute_v (m : M) : involute (v Q m) = -v Q m :=
  involute_ι _

@[simp]
/--
theorem `reverse_e0` / 定理 `reverse_e0`

English:
theorem reverse_e0
  statement: reverse (Q := Q' Q) (e0 Q) = e0 Q
  proof: reverse_ι _

@[simp]

中文:
定理 reverse_e0
  结论: reverse (Q := Q' Q) (e0 Q) = e0 Q
  证明: reverse_ι _

@[simp]
-/
theorem reverse_e0 : reverse (Q := Q' Q) (e0 Q) = e0 Q :=
  reverse_ι _

@[simp]
/--
theorem `involute_e0` / 定理 `involute_e0`

English:
theorem involute_e0
  statement: involute (e0 Q) = -e0 Q
  proof: involute_ι _

中文:
定理 involute_e0
  结论: involute (e0 Q) = -e0 Q
  证明: involute_ι _
-/
theorem involute_e0 : involute (e0 Q) = -e0 Q :=
  involute_ι _

end EquivEven

open EquivEven

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `toEven` / `toEven` 的定义

English:
definition toEven
  signature: : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra.even (Q' Q)
  body: by
  refine CliffordAlgebra.lift Q ⟨?_, fun m => ?_⟩
  · refine LinearMap.codRestrict _ ?_ fun m => Submodule.mem_iSup_of_mem ⟨2, rfl⟩ ?_
    · exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk]; rw [pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearM

中文:
定义 toEven
  签名: : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra.even (Q' Q)
  定义体: by
  refine CliffordAlgebra.lift Q ⟨?_, fun m => ?_⟩
  · refine LinearMap.codRestrict _ ?_ fun m => Submodule.mem_iSup_of_mem ⟨2, rfl⟩ ?_
    · exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk]; rw [pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearM

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, LinearMap, LinearMap.codRestrict, LinearMap.codRestrict_apply, LinearMap.mem_range_self, LinearMap.mulLeft, Subalgebra, Subalgebra.coe_mul, Submodule, Submodule.mem_iSup_of_mem, Submodule.mul_mem_mul, Subtype, Subtype.coe_mk, codRestrict, codRestrict_apply, coe_mk, coe_mul, even_toSubmodule, mem_iSup_of_mem
-/
def toEven : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra.even (Q' Q) := by
  refine CliffordAlgebra.lift Q ⟨?_, fun m => ?_⟩
  · refine LinearMap.codRestrict _ ?_ fun m => Submodule.mem_iSup_of_mem ⟨2, rfl⟩ ?_
    · exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk]; rw [pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
  · ext1
    simp only [Subalgebra.coe_mul, ← even_toSubmodule]
    rw [LinearMap.codRestrict_apply]
    simp [← mul_assoc, v_sq_scalar]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `toEven_ι` / 定理 `toEven_ι`

English:
theorem toEven_ι
  given: (m : M)
  statement: (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m
  proof: by
  simp only [toEven, CliffordAlgebra.lift_ι_apply, ← even_toSubmodule]
  rw [LinearMap.codRestrict_apply]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.mulLeft_apply]

中文:
定理 toEven_ι
  条件: (m : M)
  结论: (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m
  证明: by
  simp only [toEven, CliffordAlgebra.lift_ι_apply, ← even_toSubmodule]
  rw [LinearMap.codRestrict_apply]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.mulLeft_apply]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift_, Function, Function.comp_apply, LinearMap, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearMap.mulLeft_apply, codRestrict_apply, coe_comp, comp_apply, even_toSubmodule, mulLeft_apply, toEven
-/
theorem toEven_ι (m : M) : (toEven Q (ι Q m) : CliffordAlgebra (Q' Q)) = e0 Q * v Q m := by
  simp only [toEven, CliffordAlgebra.lift_ι_apply, ← even_toSubmodule]
  rw [LinearMap.codRestrict_apply]; rw [LinearMap.coe_comp]; rw [Function.comp_apply]; rw [LinearMap.mulLeft_apply]

/--
Definition of `ofEven` / `ofEven` 的定义

English:
definition ofEven
  signature: : CliffordAlgebra.even (Q' Q) ->ₐ[R] CliffordAlgebra Q
  body: by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R ->ₗ[R] M × R ->ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).com

中文:
定义 ofEven
  签名: : CliffordAlgebra.even (Q' Q) ->ₐ[R] CliffordAlgebra Q
  定义体: by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R ->ₗ[R] M × R ->ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).com
-/
def ofEven : CliffordAlgebra.even (Q' Q) ->ₐ[R] CliffordAlgebra Q := by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R ->ₗ[R] M × R ->ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).comp (LinearMap.fst _ _ _) +
            (Algebra.linearMap R _).comp (LinearMap.snd _ _ _)).compl₂
      ((ι Q).comp (LinearMap.fst _ _ _) - (Algebra.linearMap R _).comp (LinearMap.snd _ _ _))
  haveI f_apply : forall x y, f x y = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
    fun x y => by rfl
  haveI hc : forall (r : R) (x : CliffordAlgebra Q), Commute (algebraMap _ _ r) x := Algebra.commutes
  haveI hm :
    forall m : M × R,
      ι Q m.1 * ι Q m.1 - algebraMap R _ m.2 * algebraMap R _ m.2 = algebraMap R _ (Q' Q m) := by
    intro m
    rw [ι_sq_scalar]; rw [← map_mul]; rw [← map_sub]; rw [sub_eq_add_neg]; rw [Q'_apply]; rw [sub_eq_add_neg]
  refine even.lift (Q' Q) ⟨f, ?_, ?_⟩ <;> simp_rw [f_apply]
  · intro m
    rw [← (hc _ _).symm.mul_self_sub_mul_self_eq]; rw [hm]
  · intro m₁ m₂ m₃
    rw [← mul_smul_comm]; rw [← mul_assoc]; rw [mul_assoc (_ + _)]; rw [← (hc _ _).symm.mul_self_sub_mul_self_eq']; rw [Algebra.smul_def]; rw [← mul_assoc]; rw [hm]

/--
theorem `ofEven_ι` / 定理 `ofEven_ι`

English:
theorem ofEven_ι
  given: (x y : M × R)
  proof: even.lift_ι (Q' Q) _ x y

中文:
定理 ofEven_ι
  条件: (x y : M × R)
  证明: even.lift_ι (Q' Q) _ x y

Depends on / 依赖: even.lift_
-/
theorem ofEven_ι (x y : M × R) :
    ofEven Q ((even.ι (Q' Q)).bilin x y) =
      (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
  even.lift_ι (Q' Q) _ x y

/--
theorem `toEven_comp_ofEven` / 定理 `toEven_comp_ofEven`

English:
theorem toEven_comp_ofEven
  statement: (toEven Q).comp (ofEven Q) = AlgHom.id R _
  proof: even.algHom_ext (Q' Q)
EvenHom.ext
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
Subtype.ext
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m

中文:
定理 toEven_comp_ofEven
  结论: (toEven Q).comp (ofEven Q) = AlgHom.id R _
  证明: even.algHom_ext (Q' Q)
EvenHom.ext
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
Subtype.ext
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m

Depends on / 依赖: AlgHom, AlgHom.commutes, EvenHom, EvenHom.ext, LinearMap, LinearMap.ext, Subalgebra, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_sub, Subtype, Subtype.ext, algHom_ext, algebraMap, coe_add, coe_mul, coe_sub, commutes, even.algHom_ext, map_add
-/
theorem toEven_comp_ofEven : (toEven Q).comp (ofEven Q) = AlgHom.id R _ :=
even.algHom_ext (Q' Q)
EvenHom.ext
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
Subtype.ext
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (Q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m₁ + algebraMap R _ r₁) * (e0 Q * v Q m₂ - algebraMap R _ r₂) := by
                rw [ofEven_ι]; rw [map_mul]; rw [map_add]; rw [map_sub]; rw [AlgHom.commutes]; rw [AlgHom.commutes]; rw [Subalgebra.coe_mul]; rw [Subalgebra.coe_add]; rw [Subalgebra.coe_sub]; rw [toEven_ι]; rw [toEven_ι]; rw [Subalgebra.coe_algebraMap]; rw [Subalgebra.coe_algebraMap]
              _ =
                  e0 Q * v Q m₁ * (e0 Q * v Q m₂) + r₁ • e0 Q * v Q m₂ - r₂ • e0 Q * v Q m₁ -
                    algebraMap R _ (r₁ * r₂) := by
                rw [mul_sub]; rw [add_mul]; rw [add_mul]; rw [← Algebra.commutes]; rw [← Algebra.smul_def]; rw [← map_mul]; rw [←
                  Algebra.smul_def]; rw [sub_add_eq_sub_sub]; rw [smul_mul_assoc]; rw [smul_mul_assoc]
              _ =
                  v Q m₁ * v Q m₂ + r₁ • e0 Q * v Q m₂ + v Q m₁ * r₂ • e0 Q +
                    r₁ • e0 Q * r₂ • e0 Q := by
                have h1 : e0 Q * v Q m₁ * (e0 Q * v Q m₂) = v Q m₁ * v Q m₂ := by
                  rw [← mul_assoc]; rw [e0_mul_v_mul_e0]
                have h2 : -(r₂ • e0 Q * v Q m₁) = v Q m₁ * r₂ • e0 Q := by
                  rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [← smul_neg]; rw [neg_e0_mul_v]
                have h3 : -algebraMap R _ (r₁ * r₂) = r₁ • e0 Q * r₂ • e0 Q := by
                  rw [Algebra.algebraMap_eq_smul_one]; rw [smul_mul_smul_comm]; rw [e0_mul_e0]; rw [smul_neg]
                rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [h1]; rw [h2]; rw [h3]
              _ = ι (Q' Q) (m₁, r₁) * ι (Q' Q) (m₂, r₂) := by
                rw [ι_eq_v_add_smul_e0]; rw [ι_eq_v_add_smul_e0]; rw [mul_add]; rw [add_mul]; rw [add_mul]; rw [add_assoc]

/--
theorem `ofEven_comp_toEven` / 定理 `ofEven_comp_toEven`

English:
theorem ofEven_comp_toEven
  statement: (ofEven Q).comp (toEven Q) = AlgHom.id R _
  proof: CliffordAlgebra.hom_ext
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [toEven_ι]
          exact ofEven

中文:
定理 ofEven_comp_toEven
  结论: (ofEven Q).comp (toEven Q) = AlgHom.id R _
  证明: CliffordAlgebra.hom_ext
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [toEven_ι]
          exact ofEven

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.hom_ext, LinearMap, LinearMap.ext, Subtype, Subtype.coe_eta, algebraMap, coe_eta, hom_ext, map_one, map_zero, ofEven, one_mul, simp_rw, sub_zero, toEven, zero_add
-/
theorem ofEven_comp_toEven : (ofEven Q).comp (toEven Q) = AlgHom.id R _ :=
CliffordAlgebra.hom_ext
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [toEven_ι]
          exact ofEven_ι Q _ _
        _ = ι Q m := by rw [map_one, map_zero, map_zero, sub_zero, zero_add, one_mul]

/--
Definition of `equivEven` / `equivEven` 的定义

English:
definition equivEven
  signature: : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q)
  body: AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)

中文:
定义 equivEven
  签名: : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q)
  定义体: AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, ofAlgHom, ofEven, ofEven_comp_toEven, toEven, toEven_comp_ofEven
-/
def equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (Q' Q) :=
  AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (toEven_comp_ofEven Q) (ofEven_comp_toEven Q)

/--
theorem `coe_toEven_reverse_involute` / 定理 `coe_toEven_reverse_involute`

English:
theorem coe_toEven_reverse_involute
  given: (x : CliffordAlgebra Q)
  proof: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | m

中文:
定理 coe_toEven_reverse_involute
  条件: (x : CliffordAlgebra Q)
  证明: by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | m

Depends on / 依赖: AlgHom, AlgHom.commutes, CliffordAlgebra, CliffordAlgebra.induction, Subalgebra, Subalgebra.coe_add, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, Subalgebra.coe_neg, algebraMap, coe_add, coe_algebraMap, coe_mul, coe_neg, commutes, map_add, map_mul, map_neg, neg_e0_mul_v, reverse
-/
theorem coe_toEven_reverse_involute (x : CliffordAlgebra Q) :
    ↑(toEven Q (reverse (involute x))) =
      reverse (Q := Q' Q) (toEven Q x : CliffordAlgebra (Q' Q)) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, Subalgebra.coe_algebraMap, reverse.commutes]
  | ι m =>
    simp only [involute_ι, Subalgebra.coe_neg, toEven_ι, reverse.map_mul, reverse_v, reverse_e0,
      reverse_ι, neg_e0_mul_v, map_neg]
  | mul x y hx hy => simp only [map_mul, Subalgebra.coe_mul, reverse.map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]

/-! ### Constructions needed for `CliffordAlgebra.evenEquivEvenNeg` -/

/--
Definition of `evenToNeg` / `evenToNeg` 的定义

English:
definition evenToNeg
  signature: (Q' : QuadraticForm R M) (h : Q' = -Q)
  body: even.lift Q
    { bilin := -(even.ι Q' :).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, neg_apply, map_neg, neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h, neg_apply, smul_n

中文:
定义 evenToNeg
  签名: (Q' : QuadraticForm R M) (h : Q' = -Q)
  定义体: even.lift Q
    { bilin := -(even.ι Q' :).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, neg_apply, map_neg, neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h, neg_apply, smul_n

Depends on / 依赖: EvenHom, EvenHom.contract, EvenHom.contract_mid, LinearMap, LinearMap.neg_apply, contract, contract_mid, even.lift, map_neg, neg_apply, neg_mul_neg, neg_neg, neg_smul, simp_rw, smul_neg
-/
def evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) :
    CliffordAlgebra.even Q ->ₐ[R] CliffordAlgebra.even Q' :=
even.lift Q
    { bilin := -(even.ι Q' :).bilin
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, EvenHom.contract, h, neg_apply, map_neg, neg_neg]
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, EvenHom.contract_mid, h, neg_apply, smul_neg,
          neg_smul] }

@[simp]
/--
theorem `evenToNeg_ι` / 定理 `evenToNeg_ι`

English:
theorem evenToNeg_ι
  given: (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M)
  proof: even.lift_ι _ _ m₁ m₂

中文:
定理 evenToNeg_ι
  条件: (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M)
  证明: even.lift_ι _ _ m₁ m₂

Depends on / 依赖: even.lift_
-/
theorem evenToNeg_ι (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M) :
    evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
  even.lift_ι _ _ m₁ m₂

/--
theorem `evenToNeg_comp_evenToNeg` / 定理 `evenToNeg_comp_evenToNeg`

English:
theorem evenToNeg_comp_evenToNeg
  given: (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q')
  proof: by
  ext m₁ m₂ : 4
  simp [evenToNeg_ι]

中文:
定理 evenToNeg_comp_evenToNeg
  条件: (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q')
  证明: by
  ext m₁ m₂ : 4
  simp [evenToNeg_ι]
-/
theorem evenToNeg_comp_evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q') :
    (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _ := by
  ext m₁ m₂ : 4
  simp [evenToNeg_ι]

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps!]
/--
Definition of `evenEquivEvenNeg` / `evenEquivEvenNeg` 的定义

English:
definition evenEquivEvenNeg
  signature: : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q)
  body: AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)

中文:
定义 evenEquivEvenNeg
  签名: : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q)
  定义体: AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, evenToNeg, evenToNeg_comp_evenToNeg, neg_neg, ofAlgHom
-/
def evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q) :=
  AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_neg _).symm)
    (evenToNeg_comp_evenToNeg _ _ _ _) (evenToNeg_comp_evenToNeg _ _ _ _)

end CliffordAlgebra
