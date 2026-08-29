/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Star

/-!
# The star operation, bundled as a continuous star-linear equiv
-/

@[expose] public section



@[inherit_doc]
notation:25 M " ->L⋆[" R "] " M₂ => ContinuousLinearMap (starRingEnd R) M M₂

@[inherit_doc]
notation:50 M " ≃L⋆[" R "] " M₂ => ContinuousLinearEquiv (starRingEnd R) M M₂

section starL

variable (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] [TopologicalSpace A] [ContinuousStar A]

set_option backward.defeqAttrib.useBackward true in
/-- If `A` is a topological module over a commutative `R` with compatible actions,
then `star` is a continuous semilinear equivalence. -/
@[simps! apply]
/--
Definition of `starL` / `starL` 的定义

English:
definition starL
  signature: : A ≃L⋆[R] A where
  body: starLinearEquiv R

@[simp]

中文:
定义 starL
  签名: : A ≃L⋆[R] A where
  定义体: starLinearEquiv R

@[simp]

Depends on / 依赖: starLinearEquiv
-/
def starL : A ≃L⋆[R] A where
  toLinearEquiv := starLinearEquiv R

@[simp]
/--
theorem `toLinearEquiv_starL` / 定理 `toLinearEquiv_starL`

English:
theorem toLinearEquiv_starL
  statement: (starL R : A ≃L⋆[R] A).toLinearEquiv = starLinearEquiv R
  proof: rfl

@[simp]

中文:
定理 toLinearEquiv_starL
  结论: (starL R : A ≃L⋆[R] A).toLinearEquiv = starLinearEquiv R
  证明: rfl

@[simp]
-/
theorem toLinearEquiv_starL : (starL R : A ≃L⋆[R] A).toLinearEquiv = starLinearEquiv R :=
  rfl

@[simp]
/--
theorem `symm_starL` / 定理 `symm_starL`

English:
theorem symm_starL
  statement: (starL R : A ≃L⋆[R] A).symm = starL R
  proof: rfl

@[deprecated "Use `symm_starL` and `starL_apply` instead" (since := "2026-06-03")]

中文:
定理 symm_starL
  结论: (starL R : A ≃L⋆[R] A).symm = starL R
  证明: rfl

@[deprecated "Use `symm_starL` and `starL_apply` instead" (since := "2026-06-03")]
-/
theorem symm_starL : (starL R : A ≃L⋆[R] A).symm = starL R :=
  rfl

@[deprecated "Use `symm_starL` and `starL_apply` instead" (since := "2026-06-03")]
/--
theorem `starL_symm_apply` / 定理 `starL_symm_apply`

English:
theorem starL_symm_apply
  given: (x : A)
  statement: (starL R).symm x = starAddEquiv.symm x
  proof: by
  simp

中文:
定理 starL_symm_apply
  条件: (x : A)
  结论: (starL R).symm x = starAddEquiv.symm x
  证明: by
  simp
-/
theorem starL_symm_apply (x : A) : (starL R).symm x = starAddEquiv.symm x := by
  simp

variable [TrivialStar R]

-- TODO: this could be replaced with something like `(starL R).restrict_scalarsₛₗ h` if we
-- implemented the idea in
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Star-semilinear.20maps.20are.20semilinear.20when.20star.20is.20trivial/near/359557835
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `A` is a topological module over a commutative `R` with trivial star and compatible actions,
then `star` is a continuous linear equivalence. -/
@[simps! apply]
/--
Definition of `starL'` / `starL'` 的定义

English:
definition starL'
  signature: : A ≃L[R] A
  body: (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)

@[simp]

中文:
定义 starL'
  签名: : A ≃L[R] A
  定义体: (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.refl, continuous_id, continuous_invFun, continuous_toFun, map_smul
-/
def starL' : A ≃L[R] A :=
  (starL R : A ≃L⋆[R] A).trans
    ({ AddEquiv.refl A with
        map_smul' := fun r a => by simp
        continuous_toFun := continuous_id
        continuous_invFun := continuous_id } :
      A ≃L⋆[R] A)

@[simp]
/--
theorem `symm_starL'` / 定理 `symm_starL'`

English:
theorem symm_starL'
  statement: (starL' R : A ≃L[R] A).symm = starL' R
  proof: rfl

中文:
定理 symm_starL'
  结论: (starL' R : A ≃L[R] A).symm = starL' R
  证明: rfl
-/
theorem symm_starL' : (starL' R : A ≃L[R] A).symm = starL' R :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated "Use `symm_starL'` and `starL'_apply` instead" (since := "2026-06-03")]
/--
theorem `starL'_symm_apply` / 定理 `starL'_symm_apply`

English:
theorem starL'_symm_apply
  given: (x : A)
  statement: (starL' R).symm x = starAddEquiv.symm x
  proof: by
  simp

中文:
定理 starL'_symm_apply
  条件: (x : A)
  结论: (starL' R).symm x = starAddEquiv.symm x
  证明: by
  simp
-/
theorem starL'_symm_apply (x : A) : (starL' R).symm x = starAddEquiv.symm x := by
  simp

end starL

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A] [Invertible (2 : R)] [TopologicalSpace A]

@[fun_prop]
/--
theorem `continuous_selfAdjointPart` / 定理 `continuous_selfAdjointPart`

English:
theorem continuous_selfAdjointPart
  given: [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A]
  proof: ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _

@[fun_prop]

中文:
定理 continuous_selfAdjointPart
  条件: [连续加法 A] [余ntinuousStar A] [连续常数标量乘法 R A]
  证明: ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _

@[fun_prop]
-/
theorem continuous_selfAdjointPart [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (selfAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.add continuous_star).subtype_mk _

@[fun_prop]
/--
theorem `continuous_skewAdjointPart` / 定理 `continuous_skewAdjointPart`

English:
theorem continuous_skewAdjointPart
  given: [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A]
  proof: ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _

@[fun_prop]

中文:
定理 continuous_skewAdjointPart
  条件: [余ntinuousSub A] [余ntinuousStar A] [连续常数标量乘法 R A]
  证明: ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _

@[fun_prop]
-/
theorem continuous_skewAdjointPart [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    Continuous (skewAdjointPart R (A := A)) :=
  ((continuous_const_smul _).comp <| continuous_id.sub continuous_star).subtype_mk _

@[fun_prop]
/--
theorem `continuous_decomposeProdAdjoint` / 定理 `continuous_decomposeProdAdjoint`

English:
theorem continuous_decomposeProdAdjoint
  statement: [IsTopologicalAddGroup A] [ContinuousStar A]
  proof: (continuous_selfAdjointPart R A).prodMk (continuous_skewAdjointPart R A)

@[fun_prop]

中文:
定理 continuous_decomposeProdAdjoint
  结论: [是拓扑加群 A] [余ntinuousStar A]
  证明: (continuous_selfAdjointPart R A).prodMk (continuous_skewAdjointPart R A)

@[fun_prop]

Depends on / 依赖: continuous_selfAdjointPart, continuous_skewAdjointPart, prodMk
-/
theorem continuous_decomposeProdAdjoint [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : Continuous (StarModule.decomposeProdAdjoint R A) :=
  (continuous_selfAdjointPart R A).prodMk (continuous_skewAdjointPart R A)

@[fun_prop]
/--
theorem `continuous_decomposeProdAdjoint_symm` / 定理 `continuous_decomposeProdAdjoint_symm`

English:
theorem continuous_decomposeProdAdjoint_symm
  given: [ContinuousAdd A]
  proof: (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

中文:
定理 continuous_decomposeProdAdjoint_symm
  条件: [连续加法 A]
  证明: (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

Depends on / 依赖: continuous_fst, continuous_snd, continuous_subtype_val, continuous_subtype_val.comp
-/
theorem continuous_decomposeProdAdjoint_symm [ContinuousAdd A] :
    Continuous (StarModule.decomposeProdAdjoint R A).symm :=
  (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

/-- The self-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps! -isSimp]
/--
Definition of `selfAdjointPartL` / `selfAdjointPartL` 的定义

English:
definition selfAdjointPartL
  signature: [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A]
  body: selfAdjointPart R

中文:
定义 selfAdjointPartL
  签名: [连续加法 A] [余ntinuousStar A] [连续常数标量乘法 R A]
  定义体: selfAdjointPart R

Depends on / 依赖: selfAdjointPart
-/
def selfAdjointPartL [ContinuousAdd A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A ->L[R] selfAdjoint A where
  toLinearMap := selfAdjointPart R

/-- The skew-adjoint part of an element of a star module, as a continuous linear map. -/
@[simps!]
/--
Definition of `skewAdjointPartL` / `skewAdjointPartL` 的定义

English:
definition skewAdjointPartL
  signature: [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A]
  body: skewAdjointPart R

#adaptation_note

中文:
定义 skewAdjointPartL
  签名: [余ntinuousSub A] [余ntinuousStar A] [连续常数标量乘法 R A]
  定义体: skewAdjointPart R

#adaptation_note

Depends on / 依赖: skewAdjointPart
-/
def skewAdjointPartL [ContinuousSub A] [ContinuousStar A] [ContinuousConstSMul R A] :
    A ->L[R] skewAdjoint A where
  toLinearMap := skewAdjointPart R

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a continuous linear equivalence. -/
@[simps!]
/--
Definition of `StarModule.decomposeProdAdjointL` / `StarModule.decomposeProdAdjointL` 的定义

English:
definition StarModule.decomposeProdAdjointL
  signature: [IsTopologicalAddGroup A] [ContinuousStar A]
  body: StarModule.decomposeProdAdjoint R A

中文:
定义 对合模.decomposeProdAdjointL
  签名: [是拓扑加群 A] [余ntinuousStar A]
  定义体: StarModule.decomposeProdAdjoint R A

Depends on / 依赖: StarModule, StarModule.decomposeProdAdjoint, decomposeProdAdjoint
-/
def StarModule.decomposeProdAdjointL [IsTopologicalAddGroup A] [ContinuousStar A]
    [ContinuousConstSMul R A] : A ≃L[R] selfAdjoint A × skewAdjoint A where
  toLinearEquiv := StarModule.decomposeProdAdjoint R A
