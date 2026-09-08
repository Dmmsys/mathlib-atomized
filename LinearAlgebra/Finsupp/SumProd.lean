/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Finsupp.SMul

/-!
# `Finsupp`s and sum/product types

This file contains results about modules involving `Finsupp` and sum/product/sigma types.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

section Sum

variable (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sumFinsuppEquivProdFinsupp`. -/
@[simps apply symm_apply]
/-
**Finsupp.sumFinsuppLEquivProdFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sumFinsuppLEquivProdFinsupp {α β : Type*} : (α oplus β ->₀ M) ≃ₗ[R] (α ->₀
 M) × (β ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sumFinsuppEquivProdFinsupp`.
-/
def sumFinsuppLEquivProdFinsupp {α β : Type*} : (α ⊕ β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        simp only [AddEquiv.toFun_eq_coe, Prod.smul_fst, Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }
/-
**Finsupp.fst_sumFinsuppLEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：fst_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (x : α
) : (sumFinsuppLEquivProdFinsupp R f).1 x = f (Sum.inl x)
参数：f : α oplus β ->₀ M；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (x : α) :
    (sumFinsuppLEquivProdFinsupp R f).1 x = f (Sum.inl x) :=
  rfl
/-
**Finsupp.snd_sumFinsuppLEquivProdFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：snd_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α oplus β ->₀ M) (y : β
) : (sumFinsuppLEquivProdFinsupp R f).2 y = f (Sum.inr y)
参数：f : α oplus β ->₀ M；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : α ⊕ β →₀ M) (y : β) :
    (sumFinsuppLEquivProdFinsupp R f).2 y = f (Sum.inr y) :=
  rfl
/-
**Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p`。
形式化陈述：sumFinsuppLEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α ->₀ M) × (β ->
₀ M)) (x : α) : ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inl x) = fg.1 x
参数：fg : (α ->₀ M) × (β ->₀ M)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumFinsuppLEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inl x) = fg.1 x :=
  rfl
/-
**Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p`。
形式化陈述：sumFinsuppLEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α ->₀ M) × (β ->
₀ M)) (y : β) : ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inr y) = fg.2 y
参数：fg : (α ->₀ M) × (β ->₀ M)；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumFinsuppLEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section Sigma

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]
variable (R)

/-- On a `Fintype η`, `Finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `(j : η) → (ιs j →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sigmaFinsuppAddEquivPiFinsupp`. -/
/-
**Finsupp.sigmaFinsuppLEquivPiFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η -> Type*} [AddCommMonoid M
] [Module R M] : ((Σ j, ιs j) ->₀ M) ≃ₗ[R] (j : _) -> (ιs j ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a `Fintype η`, `Finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `(j : η) → (ιs j →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sigmaFinsuppAddEquivPiFinsupp`.
-/
noncomputable def sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] : ((Σ j, ιs j) →₀ M) ≃ₗ[R] (j : _) → (ιs j →₀ M) :=
  { sigmaFinsuppAddEquivPiFinsupp with
    map_smul' := fun c f => by
      ext
      simp }

@[simp]
/-
**Finsupp.sigmaFinsuppLEquivPiFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sigmaFinsuppLEquivPiFinsupp_apply {M : Type*} {ιs : η -> Type*} [AddCommMo
noid M] [Module R M] (f : (Σ j, ιs j) ->₀ M) (j i) : sigmaFinsuppLEquivPiFinsupp
 R f j i = f ⟨j, i⟩
参数：f : (Σ j, ιs j) ->₀ M；j i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFinsuppLEquivPiFinsupp_apply {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] (f : (Σ j, ιs j) →₀ M) (j i) : sigmaFinsuppLEquivPiFinsupp R f j i = f ⟨j, i⟩ :=
  rfl

@[simp]
/-
**Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Fins
upp`。
形式化陈述：sigmaFinsuppLEquivPiFinsupp_symm_apply {M : Type*} {ιs : η -> Type*} [AddC
ommMonoid M] [Module R M] (f : (j : _) -> (ιs j ->₀ M)) (ji) : (Finsupp.sigmaFin
suppLEquivPiFinsupp R).symm f ji = f ji.1 ji.2
参数：f : (j : _) -> (ιs j ->₀ M)；ji。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFinsuppLEquivPiFinsupp_symm_apply {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] (f : (j : _) → (ιs j →₀ M)) (ji) :
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm f ji = f ji.1 ji.2 :=
  rfl

end Sigma

end Finsupp

