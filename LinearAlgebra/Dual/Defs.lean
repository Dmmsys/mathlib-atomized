/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `Module.Dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `Module.Dual.eval R M : M →ₗ[R] Dual R (Dual R)` is the canonical map to the double dual.
  * `Module.Dual.transpose` is the linear map from `M →ₗ[R] M'` to `Dual R M' →ₗ[R] Dual R M`.
  * `LinearMap.dualMap` is `Module.Dual.transpose` of a given linear map, for dot notation.
  * `LinearEquiv.dualMap` is for the dual of an equivalence.
* Submodules:
  * `Submodule.dualRestrict W` is the transpose `Dual R M →ₗ[R] Dual R W` of the inclusion map.
  * `Submodule.dualAnnihilator W` is the kernel of `W.dualRestrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `Submodule.dualPairing W` is the canonical pairing between `Dual R M ⧸ W.dualAnnihilator`
    and `W`. It is nondegenerate for vector spaces (`Subspace.dualPairing_nondegenerate`).

## Main results

* Annihilators:
  * `Module.dualAnnihilator_gc R M` is the antitone Galois correspondence between
    `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator`.
* Finite-dimensional vector spaces:
  * `Module.evalEquiv` is the equivalence `V ≃ₗ[K] Dual K (Dual K V)`
  * `Module.mapEvalEquiv` is the order isomorphism between subspaces of `V` and
    subspaces of `Dual K (Dual K V)`.

## Notes

* The identity map `id` on `Module.Dual R M` can be interpreted as a bilinear pairing when read as
  `Module.Dual R V →ₗ[R] M →ₗ[R] R`. It is the flipped pairing to `Module.Dual.eval`.

-/

@[expose] public section

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The left dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[wikidata Q752487]
/--
Definition of `Dual` / `Dual` 的定义

English:
abbreviation Dual
  signature: (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
  body: M ->ₗ[R] R

中文:
缩写 对偶
  签名: (R M : 类型) [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: M ->ₗ[R] R
-/
abbrev Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M ->ₗ[R] R

/-- The canonical pairing of a vector space and its algebraic dual. -/
@[deprecated LinearMap.id (since := "2026-04-02")]
/--
Definition of `dualPairing` / `dualPairing` 的定义

English:
definition dualPairing
  signature: (R M) [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: LinearMap.id

@[deprecated "`Module.dualPairing` has been deprecated" (since := "2026-04-02")]

中文:
定义 dualPairing
  签名: (R M) [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: LinearMap.id

@[deprecated "`Module.dualPairing` has been deprecated" (since := "2026-04-02")]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M ->ₗ[R] M ->ₗ[R] R :=
  LinearMap.id

@[deprecated "`Module.dualPairing` has been deprecated" (since := "2026-04-02")]
/--
theorem `dualPairing_apply` / 定理 `dualPairing_apply`

English:
theorem dualPairing_apply
  given: (v x)
  statement: dualPairing R M v x = v x
  proof: rfl

中文:
定理 dualPairing_apply
  条件: (v x)
  结论: dualPairing R M v x = v x
  证明: rfl

Depends on / 依赖: _le_eLpNorm, _mul_eLpNorm, eLpNorm, hp0_lt, nnnorm_smul_le, of_forall
-/
theorem dualPairing_apply (v x) : dualPairing R M v x = v x := rfl

namespace Dual

instance (R : Type*) [Semiring R] [Module R M] : Inhabited (Dual R M) := ⟨0⟩

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: : M ->ₗ[R] Dual R (Dual R M)
  body: LinearMap.flip LinearMap.id

@[simp]

中文:
定义 eval
  签名: : M ->ₗ[R] 对偶 R (对偶 R M)
  定义体: LinearMap.flip LinearMap.id

@[simp]

Depends on / 依赖: LinearMap, LinearMap.flip, LinearMap.id
-/
def eval : M ->ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
/--
theorem `eval_apply` / 定理 `eval_apply`

English:
theorem eval_apply
  given: (v : M) (a : Dual R M)
  statement: eval R M v a = a v
  proof: rfl

中文:
定理 eval_apply
  条件: (v : M) (a : 对偶 R M)
  结论: eval R M v a = a v
  证明: rfl
-/
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  rfl

variable {R M} {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: : (M ->ₗ[R] M') ->ₗ[R] Dual R M' ->ₗ[R] Dual R M
  body: (LinearMap.llcomp R M M' R).flip

中文:
定义 transpose
  签名: : (M ->ₗ[R] M') ->ₗ[R] 对偶 R M' ->ₗ[R] 对偶 R M
  定义体: (LinearMap.llcomp R M M' R).flip

Depends on / 依赖: LinearMap, LinearMap.llcomp, llcomp
-/
def transpose : (M ->ₗ[R] M') ->ₗ[R] Dual R M' ->ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip

/--
theorem `transpose_apply` / 定理 `transpose_apply`

English:
theorem transpose_apply
  given: (u : M ->ₗ[R] M') (l : Dual R M')
  statement: transpose u l = l.comp u
  proof: rfl

中文:
定理 transpose_apply
  条件: (u : M ->ₗ[R] M') (l : 对偶 R M')
  结论: transpose u l = l.comp u
  证明: rfl
-/
theorem transpose_apply (u : M ->ₗ[R] M') (l : Dual R M') : transpose u l = l.comp u :=
  rfl

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']

/--
theorem `transpose_comp` / 定理 `transpose_comp`

English:
theorem transpose_comp
  given: (u : M' ->ₗ[R] M'') (v : M ->ₗ[R] M')
  proof: rfl

中文:
定理 transpose_comp
  条件: (u : M' ->ₗ[R] M'') (v : M ->ₗ[R] M')
  证明: rfl
-/
theorem transpose_comp (u : M' ->ₗ[R] M'') (v : M ->ₗ[R] M') :
    transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl

end Dual

end Module

section DualMap

open Module

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/--
Definition of `LinearMap.dualMap` / `LinearMap.dualMap` 的定义

English:
definition LinearMap.dualMap
  signature: (f : M₁ ->ₗ[R] M₂)
  body: Module.Dual.transpose f

中文:
定义 线性映射.dualMap
  签名: (f : M₁ ->ₗ[R] M₂)
  定义体: Module.Dual.transpose f

Depends on / 依赖: Module, Module.Dual.transpose, transpose
-/
def LinearMap.dualMap (f : M₁ ->ₗ[R] M₂) : Dual R M₂ ->ₗ[R] Dual R M₁ :=
  Module.Dual.transpose f

/--
lemma `LinearMap.dualMap_eq_lcomp` / 引理 `LinearMap.dualMap_eq_lcomp`

English:
lemma LinearMap.dualMap_eq_lcomp
  given: (f : M₁ ->ₗ[R] M₂)
  statement: f.dualMap = f.lcomp R R
  proof: rfl

中文:
引理 线性映射.dualMap_eq_lcomp
  条件: (f : M₁ ->ₗ[R] M₂)
  结论: f.dualMap = f.lcomp R R
  证明: rfl
-/
lemma LinearMap.dualMap_eq_lcomp (f : M₁ ->ₗ[R] M₂) : f.dualMap = f.lcomp R R := rfl

/--
theorem `LinearMap.dualMap_def` / 定理 `LinearMap.dualMap_def`

English:
theorem LinearMap.dualMap_def
  given: (f : M₁ ->ₗ[R] M₂)
  statement: f.dualMap = Module.Dual.transpose f
  proof: rfl

中文:
定理 线性映射.dualMap_def
  条件: (f : M₁ ->ₗ[R] M₂)
  结论: f.dualMap = 模.对偶.transpose f
  证明: rfl
-/
theorem LinearMap.dualMap_def (f : M₁ ->ₗ[R] M₂) : f.dualMap = Module.Dual.transpose f :=
  rfl

/--
theorem `LinearMap.dualMap_apply'` / 定理 `LinearMap.dualMap_apply'`

English:
theorem LinearMap.dualMap_apply'
  given: (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂)
  statement: f.dualMap g = g.comp f
  proof: rfl

@[simp]

中文:
定理 线性映射.dualMap_apply'
  条件: (f : M₁ ->ₗ[R] M₂) (g : 对偶 R M₂)
  结论: f.dualMap g = g.comp f
  证明: rfl

@[simp]
-/
theorem LinearMap.dualMap_apply' (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g = g.comp f :=
  rfl

@[simp]
/--
theorem `LinearMap.dualMap_apply` / 定理 `LinearMap.dualMap_apply`

English:
theorem LinearMap.dualMap_apply
  given: (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂) (x : M₁)
  proof: rfl

@[simp]

中文:
定理 线性映射.dualMap_apply
  条件: (f : M₁ ->ₗ[R] M₂) (g : 对偶 R M₂) (x : M₁)
  证明: rfl

@[simp]
-/
theorem LinearMap.dualMap_apply (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
/--
theorem `LinearMap.dualMap_id` / 定理 `LinearMap.dualMap_id`

English:
theorem LinearMap.dualMap_id
  statement: (LinearMap.id : M₁ ->ₗ[R] M₁).dualMap = LinearMap.id
  proof: by
  ext
  rfl

中文:
定理 线性映射.dualMap_id
  结论: (线性映射.id : M₁ ->ₗ[R] M₁).dualMap = 线性映射.id
  证明: by
  ext
  rfl
-/
theorem LinearMap.dualMap_id : (LinearMap.id : M₁ ->ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl

/--
theorem `LinearMap.dualMap_comp_dualMap` / 定理 `LinearMap.dualMap_comp_dualMap`

English:
theorem LinearMap.dualMap_comp_dualMap
  statement: {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
  proof: rfl

中文:
定理 线性映射.dualMap_comp_dualMap
  结论: {M₃ : 类型} [加法交换幺半群 M₃] [模 R M₃]
  证明: rfl
-/
theorem LinearMap.dualMap_comp_dualMap {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
    (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl

/--
theorem `LinearMap.dualMap_injective_of_surjective` / 定理 `LinearMap.dualMap_injective_of_surjective`

English:
theorem LinearMap.dualMap_injective_of_surjective
  given: {f : M₁ ->ₗ[R] M₂} (hf : Function.Surjective f)
  proof: by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

中文:
定理 线性映射.dualMap_injective_of_surjective
  条件: {f : M₁ ->ₗ[R] M₂} (hf : 函数.满射 f)
  证明: by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

Depends on / 依赖: Module, Module.Dual, congr_arg
-/
theorem LinearMap.dualMap_injective_of_surjective {f : M₁ ->ₗ[R] M₂} (hf : Function.Surjective f) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

/--
Definition of `LinearEquiv.dualMap` / `LinearEquiv.dualMap` 的定义

English:
definition LinearEquiv.dualMap
  signature: (f : M₁ ≃ₗ[R] M₂)
  body: f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x => congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x => congr_arg φ (f.left_inv x)

@[simp]

中文:
定义 线性等价.dualMap
  签名: (f : M₁ ≃ₗ[R] M₂)
  定义体: f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x => congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x => congr_arg φ (f.left_inv x)

@[simp]

Depends on / 依赖: dualMap, f.toLinearMap.dualMap, toLinearMap
-/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where
  __ := f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x => congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x => congr_arg φ (f.left_inv x)

@[simp]
/--
theorem `LinearEquiv.dualMap_apply` / 定理 `LinearEquiv.dualMap_apply`

English:
theorem LinearEquiv.dualMap_apply
  given: (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁)
  proof: rfl

@[simp]

中文:
定理 线性等价.dualMap_apply
  条件: (f : M₁ ≃ₗ[R] M₂) (g : 对偶 R M₂) (x : M₁)
  证明: rfl

@[simp]
-/
theorem LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
/--
theorem `LinearEquiv.dualMap_refl` / 定理 `LinearEquiv.dualMap_refl`

English:
theorem LinearEquiv.dualMap_refl
  proof: by
  ext
  rfl

@[simp]

中文:
定理 线性等价.dualMap_refl
  证明: by
  ext
  rfl

@[simp]
-/
theorem LinearEquiv.dualMap_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl

@[simp]
/--
theorem `LinearEquiv.dualMap_symm` / 定理 `LinearEquiv.dualMap_symm`

English:
theorem LinearEquiv.dualMap_symm
  given: {f : M₁ ≃ₗ[R] M₂}
  proof: rfl

中文:
定理 线性等价.dualMap_symm
  条件: {f : M₁ ≃ₗ[R] M₂}
  证明: rfl
-/
theorem LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl

/--
theorem `LinearEquiv.dualMap_trans` / 定理 `LinearEquiv.dualMap_trans`

English:
theorem LinearEquiv.dualMap_trans
  statement: {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
  proof: rfl

中文:
定理 线性等价.dualMap_trans
  结论: {M₃ : 类型} [加法交换幺半群 M₃] [模 R M₃] (f : M₁ ≃ₗ[R] M₂)
  证明: rfl
-/
theorem LinearEquiv.dualMap_trans {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl

/--
theorem `Module.Dual.eval_naturality` / 定理 `Module.Dual.eval_naturality`

English:
theorem Module.Dual.eval_naturality
  given: (f : M₁ ->ₗ[R] M₂)
  proof: by
  rfl

@[simp]

中文:
定理 模.对偶.eval_naturality
  条件: (f : M₁ ->ₗ[R] M₂)
  证明: by
  rfl

@[simp]
-/
theorem Module.Dual.eval_naturality (f : M₁ ->ₗ[R] M₂) :
    f.dualMap.dualMap ∘ₗ eval R M₁ = eval R M₂ ∘ₗ f := by
  rfl

@[simp]
/--
lemma `Dual.apply_one_mul_eq` / 引理 `Dual.apply_one_mul_eq`

English:
lemma Dual.apply_one_mul_eq
  given: (f : Dual R R) (r : R)
  proof: by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm]

@[simp]

中文:
引理 对偶.apply_one_mul_eq
  条件: (f : 对偶 R R) (r : R)
  证明: by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm]

@[simp]

Depends on / 依赖: conv_rhs, map_smul, mul_comm, mul_one, smul_eq_mul
-/
lemma Dual.apply_one_mul_eq (f : Dual R R) (r : R) :
    f 1 * r = f r := by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul]; rw [smul_eq_mul]; rw [mul_comm]

@[simp]
/--
lemma `LinearMap.range_dualMap_dual_eq_span_singleton` / 引理 `LinearMap.range_dualMap_dual_eq_span_singleton`

English:
lemma LinearMap.range_dualMap_dual_eq_span_singleton
  given: (f : Dual R M₁)
  proof: by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ => ⟨r 1, ?_⟩, fun ⟨r, hr⟩ => ⟨r • LinearMap.id, ?_⟩⟩
  · ext; simp [dualMap_apply', ← hr]
  · ext; simp [dualMap_apply', ← hr]

中文:
引理 线性映射.range_dualMap_dual_eq_span_singleton
  条件: (f : 对偶 R M₁)
  证明: by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ => ⟨r 1, ?_⟩, fun ⟨r, hr⟩ => ⟨r • LinearMap.id, ?_⟩⟩
  · ext; simp [dualMap_apply', ← hr]
  · ext; simp [dualMap_apply', ← hr]

Depends on / 依赖: LinearMap, LinearMap.id, Submodule, Submodule.mem_span_singleton, dualMap_apply, mem_span_singleton
-/
lemma LinearMap.range_dualMap_dual_eq_span_singleton (f : Dual R M₁) :
    range f.dualMap = R ∙ f := by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ => ⟨r 1, ?_⟩, fun ⟨r, hr⟩ => ⟨r • LinearMap.id, ?_⟩⟩
  · ext; simp [dualMap_apply', ← hr]
  · ext; simp [dualMap_apply', ← hr]

end DualMap

namespace Module

variable {K V : Type*}
variable [CommSemiring K] [AddCommMonoid V] [Module K V]

open Module Module.Dual Submodule LinearMap Module

section IsReflexive

open Function

variable (R M N : Type*)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/--
Definition of `IsReflexive` / `IsReflexive` 的定义

English:
class IsReflexive
  parameters: : Prop where
  axioms and operations (1):
    - bijective_dual_eval' : Bijective (Dual.eval R M)

中文:
类 是自反
  参数: : 命题 where
  公理与运算 (1 个):
    - bijective_dual_eval' : 双射 (对偶.eval R M)
-/
class IsReflexive : Prop where
  /-- A reflexive module is one for which the natural map to its double dual is a bijection. -/
  bijective_dual_eval' : Bijective (Dual.eval R M)

/--
lemma `bijective_dual_eval` / 引理 `bijective_dual_eval`

English:
lemma bijective_dual_eval
  given: [IsReflexive R M]
  statement: Bijective (Dual.eval R M)
  proof: IsReflexive.bijective_dual_eval'

中文:
引理 bijective_dual_eval
  条件: [是自反 R M]
  结论: 双射 (对偶.eval R M)
  证明: IsReflexive.bijective_dual_eval'

Depends on / 依赖: IsReflexive, IsReflexive.bijective_dual_eval, bijective_dual_eval
-/
lemma bijective_dual_eval [IsReflexive R M] : Bijective (Dual.eval R M) :=
  IsReflexive.bijective_dual_eval'

variable [IsReflexive R M]

/--
theorem `erange_coe` / 定理 `erange_coe`

English:
theorem erange_coe
  statement: LinearMap.range (eval R M) = ⊤
  proof: range_eq_top.mpr (bijective_dual_eval _ _).2

中文:
定理 erange_coe
  结论: 线性映射.range (eval R M) = ⊤
  证明: range_eq_top.mpr (bijective_dual_eval _ _).2

Depends on / 依赖: bijective_dual_eval, range_eq_top, range_eq_top.mpr
-/
theorem erange_coe : LinearMap.range (eval R M) = ⊤ :=
  range_eq_top.mpr (bijective_dual_eval _ _).2

/--
Definition of `evalEquiv` / `evalEquiv` 的定义

English:
definition evalEquiv
  signature: : M ≃ₗ[R] Dual R (Dual R M)
  body: LinearEquiv.ofBijective _ (bijective_dual_eval R M)

中文:
定义 evalEquiv
  签名: : M ≃ₗ[R] 对偶 R (对偶 R M)
  定义体: LinearEquiv.ofBijective _ (bijective_dual_eval R M)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, bijective_dual_eval, ofBijective
-/
def evalEquiv : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ (bijective_dual_eval R M)

/--
lemma `evalEquiv_toLinearMap` / 引理 `evalEquiv_toLinearMap`

English:
lemma evalEquiv_toLinearMap
  statement: evalEquiv R M = Dual.eval R M
  proof: rfl

中文:
引理 evalEquiv_toLinearMap
  结论: evalEquiv R M = 对偶.eval R M
  证明: rfl
-/
@[simp] lemma evalEquiv_toLinearMap : evalEquiv R M = Dual.eval R M := rfl

/--
lemma `evalEquiv_apply` / 引理 `evalEquiv_apply`

English:
lemma evalEquiv_apply
  given: (m : M)
  statement: evalEquiv R M m = Dual.eval R M m
  proof: rfl

中文:
引理 evalEquiv_apply
  条件: (m : M)
  结论: evalEquiv R M m = 对偶.eval R M m
  证明: rfl
-/
@[simp] lemma evalEquiv_apply (m : M) : evalEquiv R M m = Dual.eval R M m := rfl

/--
lemma `apply_evalEquiv_symm_apply` / 引理 `apply_evalEquiv_symm_apply`

English:
lemma apply_evalEquiv_symm_apply
  given: (f : Dual R M) (g : Dual R (Dual R M))
  proof: by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g]; rw [evalEquiv_apply]; rw [Dual.eval_apply]

中文:
引理 apply_evalEquiv_symm_apply
  条件: (f : 对偶 R M) (g : 对偶 R (对偶 R M))
  证明: by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g]; rw [evalEquiv_apply]; rw [Dual.eval_apply]
-/
@[simp] lemma apply_evalEquiv_symm_apply (f : Dual R M) (g : Dual R (Dual R M)) :
    f ((evalEquiv R M).symm g) = g f := by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g]; rw [evalEquiv_apply]; rw [Dual.eval_apply]

/--
lemma `symm_dualMap_evalEquiv` / 引理 `symm_dualMap_evalEquiv`

English:
lemma symm_dualMap_evalEquiv
  proof: by
  ext; simp

中文:
引理 symm_dualMap_evalEquiv
  证明: by
  ext; simp
-/
@[simp] lemma symm_dualMap_evalEquiv :
    (evalEquiv R M).symm.dualMap = Dual.eval R (Dual R M) := by
  ext; simp

/--
lemma `Dual.eval_comp_comp_evalEquiv_eq` / 引理 `Dual.eval_comp_comp_evalEquiv_eq`

English:
lemma Dual.eval_comp_comp_evalEquiv_eq
  proof: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [evalEquiv_toLinearMap]; rw [eval_naturality]

中文:
引理 对偶.eval_comp_comp_evalEquiv_eq
  证明: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [evalEquiv_toLinearMap]; rw [eval_naturality]
-/
@[simp] lemma Dual.eval_comp_comp_evalEquiv_eq
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f : M ->ₗ[R] M'} :
    Dual.eval R M' ∘ₗ f ∘ₗ (evalEquiv R M).symm = f.dualMap.dualMap := by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.comp_toLinearMap_symm_eq]; rw [evalEquiv_toLinearMap]; rw [eval_naturality]

/--
lemma `dualMap_dualMap_eq_iff_of_injective` / 引理 `dualMap_dualMap_eq_iff_of_injective`

English:
lemma dualMap_dualMap_eq_iff_of_injective
  proof: by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a => congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h)]; rw [LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg

中文:
引理 dualMap_dualMap_eq_iff_of_injective
  证明: by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a => congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h)]; rw [LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg

Depends on / 依赖: Dual.eval, Dual.eval_comp_comp_evalEquiv_eq, LinearEquiv, LinearEquiv.eq_comp_toLinearMap_iff, LinearMap, LinearMap.comp, cancel_left, eq_comp_toLinearMap_iff, evalEquiv, eval_comp_comp_evalEquiv_eq, propext, symm.toLinearMap, toLinearMap
-/
lemma dualMap_dualMap_eq_iff_of_injective
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f g : M ->ₗ[R] M'}
    (h : Injective (Dual.eval R M')) :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g := by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a => congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h)]; rw [LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg

/--
lemma `dualMap_dualMap_eq_iff` / 引理 `dualMap_dualMap_eq_iff`

English:
lemma dualMap_dualMap_eq_iff
  proof: dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective

中文:
引理 dualMap_dualMap_eq_iff
  证明: dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective
-/
@[simp] lemma dualMap_dualMap_eq_iff
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [IsReflexive R M'] {f g : M ->ₗ[R] M'} :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g :=
  dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective

/--
Instance `Dual.instIsReflecive` / 实例 `Dual.instIsReflecive`

English:
instance Dual.instIsReflecive
  signature: : IsReflexive R (Dual R M)
  body: ⟨by simpa only [← symm_dualMap_evalEquiv] using! (evalEquiv R M).dualMap.symm.bijective⟩

中文:
实例 对偶.instIsReflecive
  签名: : 是自反 R (对偶 R M)
  定义体: ⟨by simpa only [← symm_dualMap_evalEquiv] using! (evalEquiv R M).dualMap.symm.bijective⟩

Depends on / 依赖: bijective, dualMap, dualMap.symm.bijective, evalEquiv, symm_dualMap_evalEquiv
-/
instance Dual.instIsReflecive : IsReflexive R (Dual R M) :=
  ⟨by simpa only [← symm_dualMap_evalEquiv] using! (evalEquiv R M).dualMap.symm.bijective⟩

variable {R M N} in
/--
lemma `IsReflexive.of_split` / 引理 `IsReflexive.of_split`

English:
lemma IsReflexive.of_split
  given: (i : N ->ₗ[R] M) (s : M ->ₗ[R] N) (H : s ∘ₗ i = .id)
  proof: ⟨.of_comp (f := i.dualMap.dualMap)
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
.of_comp (g := s) (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

中文:
引理 是自反.of_split
  条件: (i : N ->ₗ[R] M) (s : M ->ₗ[R] N) (H : s ∘ₗ i = .id)
  证明: ⟨.of_comp (f := i.dualMap.dualMap)
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
.of_comp (g := s) (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

Depends on / 依赖: bijective_dual_eval, congr_arg, dualMap, i.dualMap.dualMap, injective_of_comp_eq_id, of_comp, s.dualMap.dualMap, surjective_of_comp_eq_id
-/
lemma IsReflexive.of_split (i : N ->ₗ[R] M) (s : M ->ₗ[R] N) (H : s ∘ₗ i = .id) :
    IsReflexive R N where
  bijective_dual_eval' :=
⟨.of_comp (f := i.dualMap.dualMap)
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
.of_comp (g := s) (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

/--
Definition of `mapEvalEquiv` / `mapEvalEquiv` 的定义

English:
definition mapEvalEquiv
  signature: : Submodule R M ≃o Submodule R (Dual R (Dual R M))
  body: Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]

中文:
定义 mapEvalEquiv
  签名: : 子模 R M ≃o 子模 R (对偶 R (对偶 R M))
  定义体: Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]

Depends on / 依赖: Submodule, Submodule.orderIsoMapComap, evalEquiv, orderIsoMapComap
-/
def mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M)) :=
  Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]
/--
theorem `mapEvalEquiv_apply` / 定理 `mapEvalEquiv_apply`

English:
theorem mapEvalEquiv_apply
  given: (W : Submodule R M)
  proof: rfl

@[simp]

中文:
定理 mapEvalEquiv_apply
  条件: (W : 子模 R M)
  证明: rfl

@[simp]
-/
theorem mapEvalEquiv_apply (W : Submodule R M) :
    mapEvalEquiv R M W = W.map (Dual.eval R M) :=
  rfl

@[simp]
/--
theorem `mapEvalEquiv_symm_apply` / 定理 `mapEvalEquiv_symm_apply`

English:
theorem mapEvalEquiv_symm_apply
  given: (W'' : Submodule R (Dual R (Dual R M)))
  proof: rfl

中文:
定理 mapEvalEquiv_symm_apply
  条件: (W'' : 子模 R (对偶 R (对偶 R M)))
  证明: rfl
-/
theorem mapEvalEquiv_symm_apply (W'' : Submodule R (Dual R (Dual R M))) :
    (mapEvalEquiv R M).symm W'' = W''.comap (Dual.eval R M) :=
  rfl

variable {R M N} in
/--
lemma `equiv` / 引理 `equiv`

English:
lemma equiv
  given: (e : M ≃ₗ[R] N)
  statement: IsReflexive R N where
  proof: by
    let ed : Dual R (Dual R N) ≃ₗ[R] Dual R (Dual R M) := e.symm.dualMap.dualMap
    have : Dual.eval R N = ed.symm.comp ((Dual.eval R M).comp e.symm.toLinearMap) := by
      ext m f
      exact DFunLike.congr_arg f (e.apply_symm_apply m).symm
    simp only [this,
      coe_comp, LinearEquiv.coe_

中文:
引理 equiv
  条件: (e : M ≃ₗ[R] N)
  结论: 是自反 R N where
  证明: by
    let ed : Dual R (Dual R N) ≃ₗ[R] Dual R (Dual R M) := e.symm.dualMap.dualMap
    have : Dual.eval R N = ed.symm.comp ((Dual.eval R M).comp e.symm.toLinearMap) := by
      ext m f
      exact DFunLike.congr_arg f (e.apply_symm_apply m).symm
    simp only [this,
      coe_comp, LinearEquiv.coe_

Depends on / 依赖: Bijective, Bijective.comp, DFunLike, DFunLike.congr_arg, Dual.eval, EquivLike, EquivLike.comp_bijective, LinearEquiv, LinearEquiv.bijective, LinearEquiv.coe_coe, apply_symm_apply, bijective, bijective_dual_eval, coe_coe, coe_comp, comp_bijective, congr_arg, dualMap, e.apply_symm_apply, e.symm.dualMap.dualMap
-/
lemma equiv (e : M ≃ₗ[R] N) : IsReflexive R N where
  bijective_dual_eval' := by
    let ed : Dual R (Dual R N) ≃ₗ[R] Dual R (Dual R M) := e.symm.dualMap.dualMap
    have : Dual.eval R N = ed.symm.comp ((Dual.eval R M).comp e.symm.toLinearMap) := by
      ext m f
      exact DFunLike.congr_arg f (e.apply_symm_apply m).symm
    simp only [this,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact Bijective.comp (bijective_dual_eval R M) (LinearEquiv.bijective _)

/--
Instance `_root_.MulOpposite.instModuleIsReflexive` / 实例 `_root_.MulOpposite.instModuleIsReflexive`

English:
instance _root_.MulOpposite.instModuleIsReflexive
  signature: : IsReflexive R (MulOpposite M)
  body: equiv MulOpposite.opLinearEquiv _

中文:
实例 _root_.MulOpposite.instModuleIsReflexive
  签名: : 是自反 R (MulOpposite M)
  定义体: equiv MulOpposite.opLinearEquiv _

Depends on / 依赖: MulOpposite, MulOpposite.opLinearEquiv, opLinearEquiv
-/
instance _root_.MulOpposite.instModuleIsReflexive : IsReflexive R (MulOpposite M) :=
equiv MulOpposite.opLinearEquiv _

-- see Note [lower instance priority]
instance (priority := 100) IsReflexive.to_isTorsionFree : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm :=
(bijective_dual_eval R M).injective by ext n; simpa [hr.1.eq_iff] using congr(n $hm)

end IsReflexive

end Module

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {W : Submodule R M}

/--
Definition of `dualRestrict` / `dualRestrict` 的定义

English:
definition dualRestrict
  signature: (W : Submodule R M)
  body: LinearMap.domRestrict' W

中文:
定义 dualRestrict
  签名: (W : 子模 R M)
  定义体: LinearMap.domRestrict' W

Depends on / 依赖: LinearMap, LinearMap.domRestrict, domRestrict
-/
def dualRestrict (W : Submodule R M) : Module.Dual R M ->ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W

/--
theorem `dualRestrict_def` / 定理 `dualRestrict_def`

English:
theorem dualRestrict_def
  given: (W : Submodule R M)
  statement: W.dualRestrict = W.subtype.dualMap
  proof: rfl

@[simp]

中文:
定理 dualRestrict_def
  条件: (W : 子模 R M)
  结论: W.dualRestrict = W.subtype.dualMap
  证明: rfl

@[simp]
-/
theorem dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl

@[simp]
/--
theorem `dualRestrict_apply` / 定理 `dualRestrict_apply`

English:
theorem dualRestrict_apply
  given: (W : Submodule R M) (φ : Module.Dual R M) (x : W)
  proof: rfl

中文:
定理 dualRestrict_apply
  条件: (W : 子模 R M) (φ : 模.对偶 R M) (x : W)
  证明: rfl
-/
theorem dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl

/--
Definition of `dualAnnihilator` / `dualAnnihilator` 的定义

English:
definition dualAnnihilator
  signature: {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  body: LinearMap.ker W.dualRestrict

@[simp]

中文:
定义 dualAnnihilator
  签名: {R M : 类型} [交换半环 R] [加法交换幺半群 M] [模 R M]
  定义体: LinearMap.ker W.dualRestrict

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ker, W.dualRestrict, dualRestrict
-/
def dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
(W : Submodule R M) : Submodule R Module.Dual R M :=
  LinearMap.ker W.dualRestrict

@[simp]
/--
theorem `mem_dualAnnihilator` / 定理 `mem_dualAnnihilator`

English:
theorem mem_dualAnnihilator
  given: (φ : Module.Dual R M)
  statement: φ in W.dualAnnihilator ↔ forall w in W, φ w = 0
  proof: by
  simp_rw [dualAnnihilator, LinearMap.mem_ker, LinearMap.ext_iff, dualRestrict_apply,
    Subtype.forall, LinearMap.zero_apply]

中文:
定理 mem_dualAnnihilator
  条件: (φ : 模.对偶 R M)
  结论: φ in W.dualAnnihilator ↔ 对任意 w in W, φ w = 0
  证明: by
  simp_rw [dualAnnihilator, LinearMap.mem_ker, LinearMap.ext_iff, dualRestrict_apply,
    Subtype.forall, LinearMap.zero_apply]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, LinearMap.mem_ker, LinearMap.zero_apply, Subtype, Subtype.forall, dualAnnihilator, dualRestrict_apply, ext_iff, mem_ker, simp_rw, zero_apply
-/
theorem mem_dualAnnihilator (φ : Module.Dual R M) : φ in W.dualAnnihilator ↔ forall w in W, φ w = 0 := by
  simp_rw [dualAnnihilator, LinearMap.mem_ker, LinearMap.ext_iff, dualRestrict_apply,
    Subtype.forall, LinearMap.zero_apply]

/--
theorem `dualRestrict_ker_eq_dualAnnihilator` / 定理 `dualRestrict_ker_eq_dualAnnihilator`

English:
theorem dualRestrict_ker_eq_dualAnnihilator
  given: (W : Submodule R M)
  proof: rfl

中文:
定理 dualRestrict_ker_eq_dualAnnihilator
  条件: (W : 子模 R M)
  证明: rfl
-/
theorem dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) :
    LinearMap.ker W.dualRestrict = W.dualAnnihilator :=
  rfl

/--
Definition of `dualCoannihilator` / `dualCoannihilator` 的定义

English:
definition dualCoannihilator
  signature: (Φ : Submodule R (Module.Dual R M))
  body: Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]

中文:
定义 dualCoannihilator
  签名: (Φ : 子模 R (模.对偶 R M))
  定义体: Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]

Depends on / 依赖: Module, Module.Dual.eval, dualAnnihilator, dualAnnihilator.comap
-/
def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]
/--
theorem `mem_dualCoannihilator` / 定理 `mem_dualCoannihilator`

English:
theorem mem_dualCoannihilator
  given: {Φ : Submodule R (Module.Dual R M)} (x : M)
  proof: by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]

中文:
定理 mem_dualCoannihilator
  条件: {Φ : 子模 R (模.对偶 R M)} (x : M)
  证明: by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]

Depends on / 依赖: Module, Module.Dual.eval_apply, dualCoannihilator, eval_apply, mem_comap, mem_dualAnnihilator, simp_rw
-/
theorem mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x in Φ.dualCoannihilator ↔ forall φ in Φ, (φ x : R) = 0 := by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]

/--
lemma `dualAnnihilator_map_dualMap_le` / 引理 `dualAnnihilator_map_dualMap_le`

English:
lemma dualAnnihilator_map_dualMap_le
  statement: {N : Type*} [AddCommMonoid N] [Module R N]
  proof: by
  intro; aesop

中文:
引理 dualAnnihilator_map_dualMap_le
  结论: {N : 类型} [加法交换幺半群 N] [模 R N]
  证明: by
  intro; aesop
-/
lemma dualAnnihilator_map_dualMap_le {N : Type*} [AddCommMonoid N] [Module R N]
    (W : Submodule R M) (f : N ->ₗ[R] M) :
    W.dualAnnihilator.map f.dualMap <= (W.comap f).dualAnnihilator := by
  intro; aesop

/--
theorem `comap_dualAnnihilator` / 定理 `comap_dualAnnihilator`

English:
theorem comap_dualAnnihilator
  given: (Φ : Submodule R (Module.Dual R M))
  proof: rfl

中文:
定理 comap_dualAnnihilator
  条件: (Φ : 子模 R (模.对偶 R M))
  证明: rfl
-/
theorem comap_dualAnnihilator (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualAnnihilator.comap (Module.Dual.eval R M) = Φ.dualCoannihilator := rfl

/--
theorem `map_dualCoannihilator_le` / 定理 `map_dualCoannihilator_le`

English:
theorem map_dualCoannihilator_le
  given: (Φ : Submodule R (Module.Dual R M))
  proof: map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

中文:
定理 map_dualCoannihilator_le
  条件: (Φ : 子模 R (模.对偶 R M))
  证明: map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

Depends on / 依赖: comap_dualAnnihilator, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem map_dualCoannihilator_le (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualCoannihilator.map (Module.Dual.eval R M) <= Φ.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

variable (R M) in
/--
theorem `dualAnnihilator_gc` / 定理 `dualAnnihilator_gc`

English:
theorem dualAnnihilator_gc
  proof: by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_dualAnnihilator, mem_dualCoannihilator]
  grind

中文:
定理 dualAnnihilator_gc
  证明: by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_dualAnnihilator, mem_dualCoannihilator]
  grind

Depends on / 依赖: Function, Function.comp_apply, OrderDual, OrderDual.ofDual_toDual, OrderDual.rec, OrderDual.toDual_le_toDual, SetLike, SetLike.le_def, comp_apply, le_def, mem_dualAnnihilator, mem_dualCoannihilator, ofDual_toDual, toDual_le_toDual
-/
theorem dualAnnihilator_gc :
    GaloisConnection
      (OrderDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M)))
      (dualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_dualAnnihilator, mem_dualCoannihilator]
  grind

/--
theorem `le_dualAnnihilator_iff_le_dualCoannihilator` / 定理 `le_dualAnnihilator_iff_le_dualCoannihilator`

English:
theorem le_dualAnnihilator_iff_le_dualCoannihilator
  statement: {U : Submodule R (Module.Dual R M)}
  proof: (dualAnnihilator_gc R M).le_iff_le

@[simp]

中文:
定理 le_dualAnnihilator_iff_le_dualCoannihilator
  结论: {U : 子模 R (模.对偶 R M)}
  证明: (dualAnnihilator_gc R M).le_iff_le

@[simp]

Depends on / 依赖: dualAnnihilator_gc, le_iff_le
-/
theorem le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)}
    {V : Submodule R M} : U <= V.dualAnnihilator ↔ V <= U.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_iff_le

@[simp]
/--
theorem `dualAnnihilator_bot` / 定理 `dualAnnihilator_bot`

English:
theorem dualAnnihilator_bot
  statement: (⊥ : Submodule R M).dualAnnihilator = ⊤
  proof: (dualAnnihilator_gc R M).l_bot

@[simp]

中文:
定理 dualAnnihilator_bot
  结论: (⊥ : 子模 R M).dualAnnihilator = ⊤
  证明: (dualAnnihilator_gc R M).l_bot

@[simp]

Depends on / 依赖: dualAnnihilator_gc, l_bot
-/
theorem dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  (dualAnnihilator_gc R M).l_bot

@[simp]
/--
theorem `dualAnnihilator_top` / 定理 `dualAnnihilator_top`

English:
theorem dualAnnihilator_top
  statement: (⊤ : Submodule R M).dualAnnihilator = ⊥
  proof: by
  simp [eq_bot_iff, SetLike.le_def, LinearMap.ext_iff]

@[simp]

中文:
定理 dualAnnihilator_top
  结论: (⊤ : 子模 R M).dualAnnihilator = ⊥
  证明: by
  simp [eq_bot_iff, SetLike.le_def, LinearMap.ext_iff]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, SetLike, SetLike.le_def, eq_bot_iff, ext_iff, le_def
-/
theorem dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ := by
  simp [eq_bot_iff, SetLike.le_def, LinearMap.ext_iff]

@[simp]
/--
theorem `dualCoannihilator_bot` / 定理 `dualCoannihilator_bot`

English:
theorem dualCoannihilator_bot
  statement: (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤
  proof: (dualAnnihilator_gc R M).u_top

@[gcongr, mono]

中文:
定理 dualCoannihilator_bot
  结论: (⊥ : 子模 R (模.对偶 R M)).dualCoannihilator = ⊤
  证明: (dualAnnihilator_gc R M).u_top

@[gcongr, mono]

Depends on / 依赖: dualAnnihilator_gc, u_top
-/
theorem dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤ :=
  (dualAnnihilator_gc R M).u_top

@[gcongr, mono]
/--
theorem `dualAnnihilator_anti` / 定理 `dualAnnihilator_anti`

English:
theorem dualAnnihilator_anti
  given: {U V : Submodule R M} (hUV : U <= V)
  proof: (dualAnnihilator_gc R M).monotone_l hUV

@[gcongr, mono]

中文:
定理 dualAnnihilator_anti
  条件: {U V : 子模 R M} (hUV : U <= V)
  证明: (dualAnnihilator_gc R M).monotone_l hUV

@[gcongr, mono]

Depends on / 依赖: dualAnnihilator_gc, monotone_l
-/
theorem dualAnnihilator_anti {U V : Submodule R M} (hUV : U <= V) :
    V.dualAnnihilator <= U.dualAnnihilator :=
  (dualAnnihilator_gc R M).monotone_l hUV

@[gcongr, mono]
/--
theorem `dualCoannihilator_anti` / 定理 `dualCoannihilator_anti`

English:
theorem dualCoannihilator_anti
  given: {U V : Submodule R (Module.Dual R M)} (hUV : U <= V)
  proof: (dualAnnihilator_gc R M).monotone_u hUV

中文:
定理 dualCoannihilator_anti
  条件: {U V : 子模 R (模.对偶 R M)} (hUV : U <= V)
  证明: (dualAnnihilator_gc R M).monotone_u hUV

Depends on / 依赖: dualAnnihilator_gc, monotone_u
-/
theorem dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U <= V) :
    V.dualCoannihilator <= U.dualCoannihilator :=
  (dualAnnihilator_gc R M).monotone_u hUV

/--
theorem `le_dualAnnihilator_dualCoannihilator` / 定理 `le_dualAnnihilator_dualCoannihilator`

English:
theorem le_dualAnnihilator_dualCoannihilator
  given: (U : Submodule R M)
  proof: (dualAnnihilator_gc R M).le_u_l U

中文:
定理 le_dualAnnihilator_dualCoannihilator
  条件: (U : 子模 R M)
  证明: (dualAnnihilator_gc R M).le_u_l U

Depends on / 依赖: dualAnnihilator_gc, le_u_l
-/
theorem le_dualAnnihilator_dualCoannihilator (U : Submodule R M) :
    U <= U.dualAnnihilator.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_u_l U

/--
theorem `le_dualCoannihilator_dualAnnihilator` / 定理 `le_dualCoannihilator_dualAnnihilator`

English:
theorem le_dualCoannihilator_dualAnnihilator
  given: (U : Submodule R (Module.Dual R M))
  proof: (dualAnnihilator_gc R M).l_u_le U

中文:
定理 le_dualCoannihilator_dualAnnihilator
  条件: (U : 子模 R (模.对偶 R M))
  证明: (dualAnnihilator_gc R M).l_u_le U

Depends on / 依赖: dualAnnihilator_gc, l_u_le
-/
theorem le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
    U <= U.dualCoannihilator.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_le U

/--
theorem `dualAnnihilator_dualCoannihilator_dualAnnihilator` / 定理 `dualAnnihilator_dualCoannihilator_dualAnnihilator`

English:
theorem dualAnnihilator_dualCoannihilator_dualAnnihilator
  given: (U : Submodule R M)
  proof: (dualAnnihilator_gc R M).l_u_l_eq_l U

中文:
定理 dualAnnihilator_dualCoannihilator_dualAnnihilator
  条件: (U : 子模 R M)
  证明: (dualAnnihilator_gc R M).l_u_l_eq_l U

Depends on / 依赖: dualAnnihilator_gc, l_u_l_eq_l
-/
theorem dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) :
    U.dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_l_eq_l U

/--
theorem `dualCoannihilator_dualAnnihilator_dualCoannihilator` / 定理 `dualCoannihilator_dualAnnihilator_dualCoannihilator`

English:
theorem dualCoannihilator_dualAnnihilator_dualCoannihilator
  given: (U : Submodule R (Module.Dual R M))
  proof: (dualAnnihilator_gc R M).u_l_u_eq_u U

中文:
定理 dualCoannihilator_dualAnnihilator_dualCoannihilator
  条件: (U : 子模 R (模.对偶 R M))
  证明: (dualAnnihilator_gc R M).u_l_u_eq_u U

Depends on / 依赖: dualAnnihilator_gc, u_l_u_eq_u
-/
theorem dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Module.Dual R M)) :
    U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_l_u_eq_u U

/--
theorem `dualAnnihilator_sup_eq` / 定理 `dualAnnihilator_sup_eq`

English:
theorem dualAnnihilator_sup_eq
  given: (U V : Submodule R M)
  proof: (dualAnnihilator_gc R M).l_sup

中文:
定理 dualAnnihilator_sup_eq
  条件: (U V : 子模 R M)
  证明: (dualAnnihilator_gc R M).l_sup

Depends on / 依赖: dualAnnihilator_gc, l_sup
-/
theorem dualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_sup

/--
theorem `dualCoannihilator_sup_eq` / 定理 `dualCoannihilator_sup_eq`

English:
theorem dualCoannihilator_sup_eq
  given: (U V : Submodule R (Module.Dual R M))
  proof: (dualAnnihilator_gc R M).u_inf

中文:
定理 dualCoannihilator_sup_eq
  条件: (U V : 子模 R (模.对偶 R M))
  证明: (dualAnnihilator_gc R M).u_inf

Depends on / 依赖: dualAnnihilator_gc, u_inf
-/
theorem dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) :
    (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_inf

/--
theorem `dualAnnihilator_iSup_eq` / 定理 `dualAnnihilator_iSup_eq`

English:
theorem dualAnnihilator_iSup_eq
  given: {ι : Sort*} (U : ι -> Submodule R M)
  proof: (dualAnnihilator_gc R M).l_iSup

中文:
定理 dualAnnihilator_iSup_eq
  条件: {ι : 类型层*} (U : ι -> 子模 R M)
  证明: (dualAnnihilator_gc R M).l_iSup

Depends on / 依赖: dualAnnihilator_gc, l_iSup
-/
theorem dualAnnihilator_iSup_eq {ι : Sort*} (U : ι -> Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator :=
  (dualAnnihilator_gc R M).l_iSup

/--
theorem `dualCoannihilator_iSup_eq` / 定理 `dualCoannihilator_iSup_eq`

English:
theorem dualCoannihilator_iSup_eq
  given: {ι : Sort*} (U : ι -> Submodule R (Module.Dual R M))
  proof: (dualAnnihilator_gc R M).u_iInf

中文:
定理 dualCoannihilator_iSup_eq
  条件: {ι : 类型层*} (U : ι -> 子模 R (模.对偶 R M))
  证明: (dualAnnihilator_gc R M).u_iInf

Depends on / 依赖: dualAnnihilator_gc, u_iInf
-/
theorem dualCoannihilator_iSup_eq {ι : Sort*} (U : ι -> Submodule R (Module.Dual R M)) :
    (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator :=
  (dualAnnihilator_gc R M).u_iInf

/--
theorem `sup_dualAnnihilator_le_inf` / 定理 `sup_dualAnnihilator_le_inf`

English:
theorem sup_dualAnnihilator_le_inf
  given: (U V : Submodule R M)
  proof: by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

中文:
定理 sup_dualAnnihilator_le_inf
  条件: (U V : 子模 R M)
  证明: by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

Depends on / 依赖: dualCoannihilator_sup_eq, inf_le_inf, le_dualAnnihilator_dualCoannihilator, le_dualAnnihilator_iff_le_dualCoannihilator
-/
theorem sup_dualAnnihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator <= (U ⊓ V).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

/--
theorem `iSup_dualAnnihilator_le_iInf` / 定理 `iSup_dualAnnihilator_le_iInf`

English:
theorem iSup_dualAnnihilator_le_iInf
  given: {ι : Sort*} (U : ι -> Submodule R M)
  proof: by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]

中文:
定理 iSup_dualAnnihilator_le_iInf
  条件: {ι : 类型层*} (U : ι -> 子模 R M)
  证明: by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]

Depends on / 依赖: dualCoannihilator_iSup_eq, iInf_mono, le_dualAnnihilator_dualCoannihilator, le_dualAnnihilator_iff_le_dualCoannihilator
-/
theorem iSup_dualAnnihilator_le_iInf {ι : Sort*} (U : ι -> Submodule R M) :
    ⨆ i : ι, (U i).dualAnnihilator <= (⨅ i : ι, U i).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator]; rw [dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]
/--
lemma `coe_dualAnnihilator_span` / 引理 `coe_dualAnnihilator_span`

English:
lemma coe_dualAnnihilator_span
  given: (s : Set M)
  proof: by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]

中文:
引理 coe_dualAnnihilator_span
  条件: (s : 集合 M)
  证明: by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, mem_coe, mem_dualAnnihilator, mem_ker, mem_ofPred_eq, span_le
-/
lemma coe_dualAnnihilator_span (s : Set M) :
    ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s subseteq LinearMap.ker f} := by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]
/--
lemma `coe_dualCoannihilator_span` / 引理 `coe_dualCoannihilator_span`

English:
lemma coe_dualCoannihilator_span
  given: (s : Set (Module.Dual R M))
  proof: by
  ext x
  have (φ : _) : x in LinearMap.ker φ ↔ φ in LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker, this]
  exact span_le

中文:
引理 coe_dualCoannihilator_span
  条件: (s : 集合 (模.对偶 R M))
  证明: by
  ext x
  have (φ : _) : x in LinearMap.ker φ ↔ φ in LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker, this]
  exact span_le

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.mem_ker, Module, Module.Dual.eval, Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, mem_coe, mem_dualCoannihilator, mem_ker, mem_ofPred_eq, span_le
-/
lemma coe_dualCoannihilator_span (s : Set (Module.Dual R M)) :
    ((span R s).dualCoannihilator : Set M) = {x | forall f in s, f x = 0} := by
  ext x
  have (φ : _) : x in LinearMap.ker φ ↔ φ in LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker, this]
  exact span_le

end Submodule

open Module

namespace LinearMap

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable (f : M₁ ->ₗ[R] M₂)

/--
theorem `ker_dualMap_eq_dualAnnihilator_range` / 定理 `ker_dualMap_eq_dualAnnihilator_range`

English:
theorem ker_dualMap_eq_dualAnnihilator_range
  proof: by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, coe_range, Set.forall_mem_range, dualMap_apply, zero_apply]

中文:
定理 ker_dualMap_eq_dualAnnihilator_range
  证明: by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, coe_range, Set.forall_mem_range, dualMap_apply, zero_apply]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, Set.forall_mem_range, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_dualAnnihilator, coe_range, dualMap_apply, ext_iff, forall_mem_range, mem_coe, mem_dualAnnihilator, mem_ker, simp_rw, zero_apply
-/
theorem ker_dualMap_eq_dualAnnihilator_range :
    LinearMap.ker f.dualMap = (range f).dualAnnihilator := by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, coe_range, Set.forall_mem_range, dualMap_apply, zero_apply]

/--
theorem `range_dualMap_le_dualAnnihilator_ker` / 定理 `range_dualMap_le_dualAnnihilator_ker`

English:
theorem range_dualMap_le_dualAnnihilator_ker
  proof: by
  rintro _ ⟨ψ, rfl⟩
  simp +contextual

中文:
定理 range_dualMap_le_dualAnnihilator_ker
  证明: by
  rintro _ ⟨ψ, rfl⟩
  simp +contextual

Depends on / 依赖: contextual
-/
theorem range_dualMap_le_dualAnnihilator_ker :
    LinearMap.range f.dualMap <= (ker f).dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp +contextual

end LinearMap

section CommSemiring

variable {R M M' : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace LinearMap

open Submodule

/--
theorem `ker_dualMap_eq_dualCoannihilator_range` / 定理 `ker_dualMap_eq_dualCoannihilator_range`

English:
theorem ker_dualMap_eq_dualCoannihilator_range
  given: (f : M ->ₗ[R] M')
  proof: by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]

中文:
定理 ker_dualMap_eq_dualCoannihilator_range
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, dualMap, ext_iff
-/
theorem ker_dualMap_eq_dualCoannihilator_range (f : M ->ₗ[R] M') :
    LinearMap.ker f.dualMap = (range (Dual.eval R M' ∘ₗ f)).dualCoannihilator := by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]
/--
lemma `dualCoannihilator_range_eq_ker_flip` / 引理 `dualCoannihilator_range_eq_ker_flip`

English:
lemma dualCoannihilator_range_eq_ker_flip
  given: (B : M ->ₗ[R] M' ->ₗ[R] R)
  proof: by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

中文:
引理 dualCoannihilator_range_eq_ker_flip
  条件: (B : M ->ₗ[R] M' ->ₗ[R] R)
  证明: by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

Depends on / 依赖: B.flip, LinearMap, LinearMap.ext_iff, ext_iff
-/
lemma dualCoannihilator_range_eq_ker_flip (B : M ->ₗ[R] M' ->ₗ[R] R) :
    (range B).dualCoannihilator = LinearMap.ker B.flip := by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

end LinearMap

end CommSemiring
