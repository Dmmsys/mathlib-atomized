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
/-
**Module.Dual** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module`。
形式化陈述：Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]
参数：R M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left dual space of an R-module M is the R-module of linear maps `M → R`.
-/
abbrev Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] R

/-- The canonical pairing of a vector space and its algebraic dual. -/
@[deprecated LinearMap.id (since := "2026-04-02")]
/-
**Module.dualPairing** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] : Module
.Dual R M ->ₗ[R] M ->ₗ[R] R
参数：R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical pairing of a vector space and its algebraic dual.
-/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id

@[deprecated "`Module.dualPairing` has been deprecated" (since := "2026-04-02")]
/-
**Module.dualPairing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：dualPairing_apply (v x) : dualPairing R M v x = v x
参数：v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem dualPairing_apply (v x) : dualPairing R M v x = v x := rfl

namespace Dual

/-
**Module.Dual.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Dual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [Semiring R] [Module R M] : Inhabited (Dual R M) := ⟨0⟩

/-- Maps a module M to the dual of the dual of M. See `Module.erange_coe` and
`Module.evalEquiv`. -/
/-
**Module.Dual.eval** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：eval : M ->ₗ[R] Dual R (Dual R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a module M to the dual of the dual of M. See `Module.erange_coe` and
`Module.evalEquiv`.
-/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
/-
**Module.Dual.eval_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：eval_apply (v : M) (a : Dual R M) : eval R M v a = a v
参数：v : M；a : Dual R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  rfl

variable {R M} {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`Dual R M' →ₗ[R] Dual R M`. -/
/-
**Module.Dual.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：transpose : (M ->ₗ[R] M') ->ₗ[R] Dual R M' ->ₗ[R] Dual R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`Dual R M' →ₗ[R] Dual R M`.
-/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip
/-
**Module.Dual.transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：transpose_apply (u : M ->ₗ[R] M') (l : Dual R M') : transpose u l = l.comp
 u
参数：u : M ->ₗ[R] M'；l : Dual R M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose u l = l.comp u :=
  rfl

variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']
/-
**Module.Dual.transpose_comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：transpose_comp (u : M' ->ₗ[R] M'') (v : M ->ₗ[R] M') : transpose (u.comp v
) = (transpose v).comp (transpose u)
参数：u : M' ->ₗ[R] M''；v : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (u.comp v) = (transpose v).comp (transpose u) :=
  rfl

end Dual

end Module

section DualMap

open Module

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dualMap` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
/-
**LinearMap.dualMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.dualMap (f : M₁ ->ₗ[R] M₂) : Dual R M₂ ->ₗ[R] Dual R M₁
参数：f : M₁ ->ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dualMap` is the linear map between the 
dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`.
-/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
  Module.Dual.transpose f
/-
**LinearMap.dualMap_eq_lcomp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_eq_lcomp (f : M₁ ->ₗ[R] M₂) : f.dualMap = f.lcomp R R
参数：f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
lemma LinearMap.dualMap_eq_lcomp (f : M₁ →ₗ[R] M₂) : f.dualMap = f.lcomp R R := rfl
/-
**LinearMap.dualMap_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_def (f : M₁ ->ₗ[R] M₂) : f.dualMap = Module.Dual.transpo
se f
参数：f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearMap.dualMap_def (f : M₁ →ₗ[R] M₂) : f.dualMap = Module.Dual.transpose f :=
  rfl
/-
**LinearMap.dualMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_apply' (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g 
= g.comp f
参数：f : M₁ ->ₗ[R] M₂；g : Dual R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearMap.dualMap_apply' (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g = g.comp f :=
  rfl

@[simp]
/-
**LinearMap.dualMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_apply (f : M₁ ->ₗ[R] M₂) (g : Dual R M₂) (x : M₁) : f.du
alMap g x = g (f x)
参数：f : M₁ ->ₗ[R] M₂；g : Dual R M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearMap.dualMap_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
/-
**LinearMap.dualMap_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_id : (LinearMap.id : M₁ ->ₗ[R] M₁).dualMap = LinearMap.i
d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearMap.dualMap_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl
/-
**LinearMap.dualMap_comp_dualMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_comp_dualMap {M₃ : Type*} [AddCommMonoid M₃] [Module R M
₃] (f : M₁ ->ₗ[R] M₂) (g : M₂ ->ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f)
.dualMap
参数：f : M₁ ->ₗ[R] M₂；g : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearMap.dualMap_comp_dualMap {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl

/-- If a linear map is surjective, then its dual is injective. -/
/-
**LinearMap.dualMap_injective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.dualMap_injective_of_surjective {f : M₁ ->ₗ[R] M₂} (hf : Functio
n.Surjective f) : Function.Injective f.dualMap
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If a linear map is surjective, then its dual is injective.
-/
theorem LinearMap.dualMap_injective_of_surjective {f : M₁ →ₗ[R] M₂} (hf : Function.Surjective f) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

/-- The `LinearEquiv` version of `LinearMap.dualMap`. -/
/-
**LinearEquiv.dualMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where __
参数：f : M₁ ≃ₗ[R] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearEquiv` version of `LinearMap.dualMap`.
-/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where
  __ := f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.left_inv x)

@[simp]
/-
**LinearEquiv.dualMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) : f.d
ualMap g x = g (f x)
参数：f : M₁ ≃ₗ[R] M₂；g : Dual R M₂；x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
/-
**LinearEquiv.dualMap_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.dualMap_refl : (LinearEquiv.refl R M₁).dualMap = LinearEquiv.r
efl R (Dual R M₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem LinearEquiv.dualMap_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl

@[simp]
/-
**LinearEquiv.dualMap_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} : (LinearEquiv.dualMap f).symm 
= LinearEquiv.dualMap f.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl
/-
**LinearEquiv.dualMap_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.dualMap_trans {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f
 : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dual
Map
参数：f : M₁ ≃ₗ[R] M₂；g : M₂ ≃ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem LinearEquiv.dualMap_trans {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl
/-
**Module.Dual.eval_naturality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Dual.eval_naturality (f : M₁ ->ₗ[R] M₂) : f.dualMap.dualMap ∘ₗ eval
 R M₁ = eval R M₂ ∘ₗ f
参数：f : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem Module.Dual.eval_naturality (f : M₁ →ₗ[R] M₂) :
    f.dualMap.dualMap ∘ₗ eval R M₁ = eval R M₂ ∘ₗ f := by
  rfl

@[simp]
/-
**Dual.apply_one_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Dual.apply_one_mul_eq (f : Dual R R) (r : R) : f 1 * r = f r
参数：f : Dual R R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma Dual.apply_one_mul_eq (f : Dual R R) (r : R) :
    f 1 * r = f r := by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul, smul_eq_mul, mul_comm]

@[simp]
/-
**LinearMap.range_dualMap_dual_eq_span_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.range_dualMap_dual_eq_span_singleton (f : Dual R M₁) : range f.d
ualMap = R ∙ f
参数：f : Dual R M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Dual.apply_one_mul_eq`：Dual.apply_one_mul_eq (f : Dual R R) (r : R) : f 
1 * r = f r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
lemma LinearMap.range_dualMap_dual_eq_span_singleton (f : Dual R M₁) :
    range f.dualMap = R ∙ f := by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r 1, ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r • LinearMap.id, ?_⟩⟩
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

/-- A reflexive module is one for which the natural map to its double dual is a bijection.

Any finitely-generated projective module (and thus any finite-dimensional vector space)
is reflexive. See `Module.instIsReflexiveOfFiniteOfProjective`. -/
/-
**Module.IsReflexive** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u_3) → (M : Type u_4) → [inst : CommSemiring R] → [inst_1 : AddC
ommMonoid M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reflexive module is one for which the natural map to its double dual is a bije
ction.

Any finitely-generated projective module (and thus any finite-dimensional vector
 space)
is reflexive. See `Module.instIsReflexiveOfFiniteOfProjective`.
-/
class IsReflexive : Prop where
  /-- A reflexive module is one for which the natural map to its double dual is a bijection. -/
  bijective_dual_eval' : Bijective (Dual.eval R M)
/-
**Module.bijective_dual_eval** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：bijective_dual_eval [IsReflexive R M] : Bijective (Dual.eval R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.bijective_dual_eval'`：∀ {R : Type u_3} {M : Type u_4}
 {inst : CommSemiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}
   [self : Module.IsReflexive…
-/
lemma bijective_dual_eval [IsReflexive R M] : Bijective (Dual.eval R M) :=
  IsReflexive.bijective_dual_eval'

variable [IsReflexive R M]
/-
**Module.erange_coe** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：erange_coe : LinearMap.range (eval R M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)
-/
theorem erange_coe : LinearMap.range (eval R M) = ⊤ :=
  range_eq_top.mpr (bijective_dual_eval _ _).2

/-- The bijection between a reflexive module and its double dual, bundled as a `LinearEquiv`. -/
/-
**Module.evalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：evalEquiv : M ≃ₗ[R] Dual R (Dual R M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)

--- 原说明 ---
The bijection between a reflexive module and its double dual, bundled as a `Line
arEquiv`.
-/
def evalEquiv : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ (bijective_dual_eval R M)
/-
**Module.evalEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.IsReflexive R M], ↑(Mod
ule.evalEquiv R M) = Module.Dual.eval R M
参数：R : Type u_3；M : Type u_4；Module.evalEquiv R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
@[simp] lemma evalEquiv_toLinearMap : evalEquiv R M = Dual.eval R M := rfl
/-
**Module.evalEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.IsReflexive R M] (m : M
), (Module.evalEquiv R M) m = (Module.Dual.eval R M) m
参数：R : Type u_3；M : Type u_4；m : M；Module.evalEquiv R M；Module.Dual.eval R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
@[simp] lemma evalEquiv_apply (m : M) : evalEquiv R M m = Dual.eval R M m := rfl
/-
**Module.apply_evalEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.IsReflexive R M] (f : M
odule.Dual R M) (g : Module.Dual R (Module.Dual R M)),   f ((Module.evalEquiv R 
M).symm g) = g f
参数：R : Type u_3；M : Type u_4；f : Module.Dual R M；g : Module.Dual R (Module.Dual 
R M)；(Module.evalEquiv R M).symm g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.evalEquiv_apply`：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : Modu
le.IsReflexi…
· 使用定理 `Module.Dual.eval_apply`：eval_apply (v : M) (a : Dual R M) : eval R M v a
 = a v
-/
@[simp] lemma apply_evalEquiv_symm_apply (f : Dual R M) (g : Dual R (Dual R M)) :
    f ((evalEquiv R M).symm g) = g f := by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g, evalEquiv_apply, Dual.eval_apply]
/-
**Module.symm_dualMap_evalEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.IsReflexive R M], ↑(Mod
ule.evalEquiv R M).symm.dualMap = Module.Dual.eval R (Module.Dual R M)
参数：R : Type u_3；M : Type u_4；Module.evalEquiv R M；Module.Dual R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.apply_evalEquiv_symm_apply`：∀ (R : Type u_3) (M : Type u_4) [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [in
st_3 : Module.IsReflexi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma symm_dualMap_evalEquiv :
    (evalEquiv R M).symm.dualMap = Dual.eval R (Dual R M) := by
  ext; simp
/-
**Module.Dual.eval_comp_comp_evalEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual
`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Module.IsReflexive R M] {M' : 
Type u_6} [inst_4 : AddCommMonoid M'] [inst_5 : _root_.Module R M']   {f : M →ₗ[
R] M'}, Module.Dual.eval R M' ∘ₗ f ∘ₗ ↑(Module.evalEquiv R M).symm = f.dualMap.d
ualMap
参数：R : Type u_3；M : Type u_4；Module.evalEquiv R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
· 使用定理 `Module.evalEquiv_toLinearMap`：∀ (R : Type u_3) (M : Type u_4) [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 
: Module.IsReflexi…
· 使用定理 `Module.Dual.eval_naturality`：Module.Dual.eval_naturality (f : M₁ ->ₗ[R] 
M₂) : f.dualMap.dualMap ∘ₗ eval R M₁ = eval R M₂ ∘ₗ f
-/
@[simp] lemma Dual.eval_comp_comp_evalEquiv_eq
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f : M →ₗ[R] M'} :
    Dual.eval R M' ∘ₗ f ∘ₗ (evalEquiv R M).symm = f.dualMap.dualMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq,
    evalEquiv_toLinearMap, eval_naturality]
/-
**Module.dualMap_dualMap_eq_iff_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：dualMap_dualMap_eq_iff_of_injective {M' : Type*} [AddCommMonoid M'] [Modul
e R M'] {f g : M ->ₗ[R] M'} (h : Injective (Dual.eval R M')) : f.dualMap.dualMap
 = g.dualMap.dualMap ↔ f = g
参数：h : Injective (Dual.eval R M')。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_iff`：eq_comp_toLinearMap_iff (f g : M₂ -
>ₛₗ[σ₂₃] M₃) : f.comp e₁₂.toLinearMap = g.comp e₁₂.toLinearMap ↔ f = g
· 使用定理 `LinearMap.cancel_left`：cancel_left (hf : Injective f) : f.comp g = f.com
p g' ↔ g = g'
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma dualMap_dualMap_eq_iff_of_injective
    {M' : Type*} [AddCommMonoid M'] [Module R M'] {f g : M →ₗ[R] M'}
    (h : Injective (Dual.eval R M')) :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g := by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a ↦ congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h), LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg
/-
**Module.dualMap_dualMap_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [Module.IsReflexive R M] {M' : Type u_6}
 [inst_4 : AddCommMonoid M'] [inst_5 : _root_.Module R M']   [Module.IsReflexive
 R M'] {f g : M →ₗ[R] M'}, f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g
参数：R : Type u_3；M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.dualMap_dualMap_eq_iff_of_injective`：dualMap_dualMap_eq_iff_of_in
jective {M' : Type*} [AddCommMonoid M'] [Module R M'] {f g : M ->ₗ[R] M'} (h : I
njective (Dual.eval R M')) : f.d…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)
-/
@[simp] lemma dualMap_dualMap_eq_iff
    {M' : Type*} [AddCommMonoid M'] [Module R M'] [IsReflexive R M'] {f g : M →ₗ[R] M'} :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g :=
  dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective

/-- The dual of a reflexive module is reflexive. -/
/-
**Module.Dual.instIsReflecive** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：∀ (R : Type u_3) (M : Type u_4) [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [Module.IsReflexive R M], Module.IsRefle
xive R (Module.Dual R M)
参数：R : Type u_3；M : Type u_4；Module.Dual R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
The dual of a reflexive module is reflexive.
-/
instance Dual.instIsReflecive : IsReflexive R (Dual R M) :=
  ⟨by simpa only [← symm_dualMap_evalEquiv] using! (evalEquiv R M).dualMap.symm.bijective⟩

variable {R M N} in
/-- A direct summand of a reflexive module is reflexive. -/
/-
**Module.IsReflexive.of_split** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsReflexive`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] [Module.IsReflexive R M]   (i : N →ₗ[R] M) (s : M
 →ₗ[R] N), s ∘ₗ i = LinearMap.id → Module.IsReflexive R N
参数：i : N →ₗ[R] M；s : M →ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)
· 使用定理 `LinearMap.injective_of_comp_eq_id`：injective_of_comp_eq_id : Injective f
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearMap.surjective_of_comp_eq_id`：surjective_of_comp_eq_id : Surjectiv
e g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A direct summand of a reflexive module is reflexive.
-/
lemma IsReflexive.of_split (i : N →ₗ[R] M) (s : M →ₗ[R] N) (H : s ∘ₗ i = .id) :
    IsReflexive R N where
  bijective_dual_eval' :=
    ⟨.of_comp (f := i.dualMap.dualMap) <|
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
    .of_comp (g := s) <| (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

/-- The isomorphism `Module.evalEquiv` induces an order isomorphism on subspaces. -/
/-
**Module.mapEvalEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `Module.evalEquiv` induces an order isomorphism on subspaces.
-/
def mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M)) :=
  Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]
/-
**Module.mapEvalEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：mapEvalEquiv_apply (W : Submodule R M) : mapEvalEquiv R M W = W.map (Dual.
eval R M)
参数：W : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem mapEvalEquiv_apply (W : Submodule R M) :
    mapEvalEquiv R M W = W.map (Dual.eval R M) :=
  rfl

@[simp]
/-
**Module.mapEvalEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：mapEvalEquiv_symm_apply (W'' : Submodule R (Dual R (Dual R M))) : (mapEval
Equiv R M).symm W'' = W''.comap (Dual.eval R M)
参数：W'' : Submodule R (Dual R (Dual R M))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem mapEvalEquiv_symm_apply (W'' : Submodule R (Dual R (Dual R M))) :
    (mapEvalEquiv R M).symm W'' = W''.comap (Dual.eval R M) :=
  rfl

variable {R M N} in
/-
**Module.equiv** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：equiv (e : M ≃ₗ[R] N) : IsReflexive R N where bijective_dual_eval'
参数：e : M ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
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
/-
**Module._root_.MulOpposite.instModuleIsReflexive** 是 Mathlib 中的一个实例，位于命名空间 `Mod
ule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.MulOpposite.instModuleIsReflexive : IsReflexive R (MulOpposite M) :=
  equiv <| MulOpposite.opLinearEquiv _

-- see Note [lower instance priority]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsReflexive.to_isTorsionFree : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm :=
    (bijective_dual_eval R M).injective <| by ext n; simpa [hr.1.eq_iff] using congr(n $hm)

end IsReflexive

end Module

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {W : Submodule R M}

/-- The `dualRestrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
/-
**Submodule.dualRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualRestrict (W : Submodule R M) : Module.Dual R M ->ₗ[R] Module.Dual R W
参数：W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `dualRestrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`.
-/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W
/-
**Submodule.dualRestrict_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap
参数：W : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl

@[simp]
/-
**Submodule.dualRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) : W.d
ualRestrict φ x = φ (x : M)
参数：W : Submodule R M；φ : Module.Dual R M；x : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl

/-- The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
/-
**Submodule.dualAnnihilator** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R
 M] (W : Submodule R M) : Submodule R Module.Dual R M
参数：W : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`.
-/
def dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
  LinearMap.ker W.dualRestrict

@[simp]
/-
**Submodule.mem_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_dualAnnihilator (φ : Module.Dual R M) : φ in W.dualAnnihilator ↔ foral
l w in W, φ w = 0
参数：φ : Module.Dual R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dualAnnihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0 := by
  simp_rw [dualAnnihilator, LinearMap.mem_ker, LinearMap.ext_iff, dualRestrict_apply,
    Subtype.forall, LinearMap.zero_apply]

/-- That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$. -/
/-
**Submodule.dualRestrict_ker_eq_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) : LinearMap.ker W.
dualRestrict = W.dualAnnihilator
参数：W : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M

--- 原说明 ---
That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$.
-/
theorem dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) :
    LinearMap.ker W.dualRestrict = W.dualAnnihilator :=
  rfl

/-- The `dualAnnihilator` of a submodule of the dual space pulled back along the evaluation map
`Module.Dual.eval`. -/
/-
**Submodule.dualCoannihilator** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M
参数：Φ : Submodule R (Module.Dual R M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `dualAnnihilator` of a submodule of the dual space pulled back along the eva
luation map
`Module.Dual.eval`.
-/
def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]
/-
**Submodule.mem_dualCoannihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) : x in Φ
.dualCoannihilator ↔ forall φ in Φ, (φ x : R) = 0
参数：Module.Dual R M；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualCoannihilator ↔ ∀ φ ∈ Φ, (φ x : R) = 0 := by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]
/-
**Submodule.dualAnnihilator_map_dualMap_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：dualAnnihilator_map_dualMap_le {N : Type*} [AddCommMonoid N] [Module R N] 
(W : Submodule R M) (f : N ->ₗ[R] M) : W.dualAnnihilator.map f.dualMap <= (W.com
ap f).dualAnnihilator
参数：W : Submodule R M；f : N ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dualAnnihilator_map_dualMap_le {N : Type*} [AddCommMonoid N] [Module R N]
    (W : Submodule R M) (f : N →ₗ[R] M) :
    W.dualAnnihilator.map f.dualMap ≤ (W.comap f).dualAnnihilator := by
  intro; aesop
/-
**Submodule.comap_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_dualAnnihilator (Φ : Submodule R (Module.Dual R M)) : Φ.dualAnnihila
tor.comap (Module.Dual.eval R M) = Φ.dualCoannihilator
参数：Φ : Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
-/
theorem comap_dualAnnihilator (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualAnnihilator.comap (Module.Dual.eval R M) = Φ.dualCoannihilator := rfl
/-
**Submodule.map_dualCoannihilator_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_dualCoannihilator_le (Φ : Submodule R (Module.Dual R M)) : Φ.dualCoann
ihilator.map (Module.Dual.eval R M) <= Φ.dualAnnihilator
参数：Φ : Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Submodule.comap_dualAnnihilator`：comap_dualAnnihilator (Φ : Submodule R 
(Module.Dual R M)) : Φ.dualAnnihilator.comap (Module.Dual.eval R M) = Φ.dualCoan
nihilator
-/
theorem map_dualCoannihilator_le (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualCoannihilator.map (Module.Dual.eval R M) ≤ Φ.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

variable (R M) in
/-
**Submodule.dualAnnihilator_gc** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_gc : GaloisConnection (OrderDual.toDual ∘ (dualAnnihilator
 : Submodule R M -> Submodule R (Module.Dual R M))) (dualCoannihilator ∘ OrderDu
al.ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem dualAnnihilator_gc :
    GaloisConnection
      (OrderDual.toDual ∘ (dualAnnihilator : Submodule R M → Submodule R (Module.Dual R M)))
      (dualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual,
    SetLike.le_def, mem_dualAnnihilator, mem_dualCoannihilator]
  grind
/-
**Submodule.le_dualAnnihilator_iff_le_dualCoannihilator** 是 Mathlib 中的一个定理，位于命名空
间 `Submodule`。
形式化陈述：le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual 
R M)} {V : Submodule R M} : U <= V.dualAnnihilator ↔ V <= U.dualCoannihilator
参数：Module.Dual R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)}
    {V : Submodule R M} : U ≤ V.dualAnnihilator ↔ V ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_iff_le

@[simp]
/-
**Submodule.dualAnnihilator_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  (dualAnnihilator_gc R M).l_bot

@[simp]
/-
**Submodule.dualAnnihilator_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ := by
  simp [eq_bot_iff, SetLike.le_def, LinearMap.ext_iff]

@[simp]
/-
**Submodule.dualCoannihilator_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihila
tor = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_top`：u_top [OrderTop β] {l : α -> β} {u : β -> α} (gc
 : GaloisConnection l u) : u ⊤ = ⊤
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤ :=
  (dualAnnihilator_gc R M).u_top

@[gcongr, mono]
/-
**Submodule.dualAnnihilator_anti** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_anti {U V : Submodule R M} (hUV : U <= V) : V.dualAnnihila
tor <= U.dualAnnihilator
参数：hUV : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualAnnihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.dualAnnihilator ≤ U.dualAnnihilator :=
  (dualAnnihilator_gc R M).monotone_l hUV

@[gcongr, mono]
/-
**Submodule.dualCoannihilator_anti** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U <= V
) : V.dualCoannihilator <= U.dualCoannihilator
参数：Module.Dual R M；hUV : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U ≤ V) :
    V.dualCoannihilator ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).monotone_u hUV
/-
**Submodule.le_dualAnnihilator_dualCoannihilator** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：le_dualAnnihilator_dualCoannihilator (U : Submodule R M) : U <= U.dualAnni
hilator.dualCoannihilator
参数：U : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem le_dualAnnihilator_dualCoannihilator (U : Submodule R M) :
    U ≤ U.dualAnnihilator.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_u_l U
/-
**Submodule.le_dualCoannihilator_dualAnnihilator** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
 U <= U.dualCoannihilator.dualAnnihilator
参数：U : Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
    U ≤ U.dualCoannihilator.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_le U
/-
**Submodule.dualAnnihilator_dualCoannihilator_dualAnnihilator** 是 Mathlib 中的一个定理
，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) : U.
dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator
参数：U : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) :
    U.dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_l_eq_l U
/-
**Submodule.dualCoannihilator_dualAnnihilator_dualCoannihilator** 是 Mathlib 中的一个
定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Modu
le.Dual R M)) : U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCo
annihilator
参数：U : Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.u_l_u_eq_u`：u_l_u_eq_u (b : β) : u (l (u b)) = u b
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Module.Dual R M)) :
    U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_l_u_eq_u U
/-
**Submodule.dualAnnihilator_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_sup_eq (U V : Submodule R M) : (U ⊔ V).dualAnnihilator = U
.dualAnnihilator ⊓ V.dualAnnihilator
参数：U V : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_sup
/-
**Submodule.dualCoannihilator_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) : (U ⊔ V).d
ualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator
参数：U V : Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.u_inf`：∀ {β : Type u} {α : Type v} {b₁ b₂ : β} [inst : 
SemilatticeInf β] [inst_1 : SemilatticeInf α] {u : β → α} {l : α → β},   GaloisC
onnection l …
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) :
    (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_inf
/-
**Submodule.dualAnnihilator_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualAnnihilator_iSup_eq {ι : Sort*} (U : ι -> Submodule R M) : (⨆ i : ι, U
 i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator
参数：U : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualAnnihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator :=
  (dualAnnihilator_gc R M).l_iSup
/-
**Submodule.dualCoannihilator_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：dualCoannihilator_iSup_eq {ι : Sort*} (U : ι -> Submodule R (Module.Dual R
 M)) : (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator
参数：U : ι -> Submodule R (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `GaloisConnection.u_iInf`：∀ {α : Type u} {β : Type v} {ι : Sort x} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] {u : α → β}   {l : β → α}, Gal
oisConnection…
· 使用定理 `Submodule.dualAnnihilator_gc`：dualAnnihilator_gc : GaloisConnection (Ord
erDual.toDual ∘ (dualAnnihilator : Submodule R M -> Submodule R (Module.Dual R M
))) (dualCoannihil…
-/
theorem dualCoannihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R (Module.Dual R M)) :
    (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator :=
  (dualAnnihilator_gc R M).u_iInf

/-- See also `Subspace.dualAnnihilator_inf_eq` for vector subspaces. -/
/-
**Submodule.sup_dualAnnihilator_le_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sup_dualAnnihilator_le_inf (U V : Submodule R M) : U.dualAnnihilator ⊔ V.d
ualAnnihilator <= (U ⊓ V).dualAnnihilator
参数：U V : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.le_dualAnnihilator_iff_le_dualCoannihilator`：le_dualAnnihilato
r_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)} {V : Submodule R 
M} : U <= V.dualAnnihilator ↔ V <= U.dualCo…
· 使用定理 `Submodule.dualCoannihilator_sup_eq`：dualCoannihilator_sup_eq (U V : Subm
odule R (Module.Dual R M)) : (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V
.dualCoannihilator
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Submodule.le_dualAnnihilator_dualCoannihilator`：le_dualAnnihilator_dualC
oannihilator (U : Submodule R M) : U <= U.dualAnnihilator.dualCoannihilator

--- 原说明 ---
See also `Subspace.dualAnnihilator_inf_eq` for vector subspaces.
-/
theorem sup_dualAnnihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator ≤ (U ⊓ V).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

/-- See also `Subspace.dualAnnihilator_iInf_eq` for vector subspaces when `ι` is finite. -/
/-
**Submodule.iSup_dualAnnihilator_le_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_dualAnnihilator_le_iInf {ι : Sort*} (U : ι -> Submodule R M) : ⨆ i : 
ι, (U i).dualAnnihilator <= (⨅ i : ι, U i).dualAnnihilator
参数：U : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.le_dualAnnihilator_iff_le_dualCoannihilator`：le_dualAnnihilato
r_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)} {V : Submodule R 
M} : U <= V.dualAnnihilator ↔ V <= U.dualCo…
· 使用定理 `Submodule.dualCoannihilator_iSup_eq`：dualCoannihilator_iSup_eq {ι : Sort
*} (U : ι -> Submodule R (Module.Dual R M)) : (⨆ i : ι, U i).dualCoannihilator =
 ⨅ i : ι, (U i).dualCoann…
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `Submodule.le_dualAnnihilator_dualCoannihilator`：le_dualAnnihilator_dualC
oannihilator (U : Submodule R M) : U <= U.dualAnnihilator.dualCoannihilator

--- 原说明 ---
See also `Subspace.dualAnnihilator_iInf_eq` for vector subspaces when `ι` is fin
ite.
-/
theorem iSup_dualAnnihilator_le_iInf {ι : Sort*} (U : ι → Submodule R M) :
    ⨆ i : ι, (U i).dualAnnihilator ≤ (⨅ i : ι, U i).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]
/-
**Submodule.coe_dualAnnihilator_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：coe_dualAnnihilator_span (s : Set M) : ((span R s).dualAnnihilator : Set (
Module.Dual R M)) = {f | s subseteq LinearMap.ker f}
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
-/
lemma coe_dualAnnihilator_span (s : Set M) :
    ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s ⊆ LinearMap.ker f} := by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]
/-
**Submodule.coe_dualCoannihilator_span** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：coe_dualCoannihilator_span (s : Set (Module.Dual R M)) : ((span R s).dualC
oannihilator : Set M) = {x | forall f in s, f x = 0}
参数：s : Set (Module.Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
-/
lemma coe_dualCoannihilator_span (s : Set (Module.Dual R M)) :
    ((span R s).dualCoannihilator : Set M) = {x | ∀ f ∈ s, f x = 0} := by
  ext x
  have (φ : _) : x ∈ LinearMap.ker φ ↔ φ ∈ LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_ofPred_eq, ← LinearMap.mem_ker, this]
  exact span_le

end Submodule

open Module

namespace LinearMap

variable {R M₁ M₂ : Type*} [CommSemiring R]
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable (f : M₁ →ₗ[R] M₂)

/-
**LinearMap.ker_dualMap_eq_dualAnnihilator_range** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：ker_dualMap_eq_dualAnnihilator_range : LinearMap.ker f.dualMap = (range f)
.dualAnnihilator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_dualMap_eq_dualAnnihilator_range :
    LinearMap.ker f.dualMap = (range f).dualAnnihilator := by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, coe_range, Set.forall_mem_range, dualMap_apply, zero_apply]
/-
**LinearMap.range_dualMap_le_dualAnnihilator_ker** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：range_dualMap_le_dualAnnihilator_ker : LinearMap.range f.dualMap <= (ker f
).dualAnnihilator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem range_dualMap_le_dualAnnihilator_ker :
    LinearMap.range f.dualMap ≤ (ker f).dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp +contextual

end LinearMap

section CommSemiring

variable {R M M' : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace LinearMap

open Submodule

/-
**LinearMap.ker_dualMap_eq_dualCoannihilator_range** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：ker_dualMap_eq_dualCoannihilator_range (f : M ->ₗ[R] M') : LinearMap.ker f
.dualMap = (range (Dual.eval R M' ∘ₗ f)).dualCoannihilator
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_dualMap_eq_dualCoannihilator_range (f : M →ₗ[R] M') :
    LinearMap.ker f.dualMap = (range (Dual.eval R M' ∘ₗ f)).dualCoannihilator := by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]
/-
**LinearMap.dualCoannihilator_range_eq_ker_flip** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rMap`。
形式化陈述：dualCoannihilator_range_eq_ker_flip (B : M ->ₗ[R] M' ->ₗ[R] R) : (range B)
.dualCoannihilator = LinearMap.ker B.flip
参数：B : M ->ₗ[R] M' ->ₗ[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dualCoannihilator_range_eq_ker_flip (B : M →ₗ[R] M' →ₗ[R] R) :
    (range B).dualCoannihilator = LinearMap.ker B.flip := by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

end LinearMap

end CommSemiring

