/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.Supported

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Module structure on monoid algebras

## Main results

* `MonoidAlgebra.module`, `AddMonoidAlgebra.module`: lift a module structure to monoid algebras

## Implementation notes

We do not state the equivalent of `DistribMulAction M (MonoidAlgebra S M)` for `AddMonoidAlgebra`
because mathlib does not have the notion of distributive actions of additive groups.
-/

@[expose] public section

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single
open Module

variable {R S M N O G : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

section SMul

section DistribMulAction
variable [Monoid S] [Semiring R] [DistribMulAction S R]

@[to_additive (dont_translate := S) distribMulAction]
/-
**MonoidAlgebra.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：distribMulAction : DistribMulAction S R[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction : DistribMulAction S R[M] := fast_instance% coeffEquiv.distribMulAction _

@[to_additive (dont_translate := S) (attr := simp)]
/-
**MonoidAlgebra.mapDomain_smul** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomain_smul (f : M -> N) (s : S) (x : R[M]) : mapDomain f (s • x) = s •
 mapDomain f x
参数：f : M -> N；s : S；x : R[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.coeff_mapDomain`：∀ {R : Type u_3} {M : Type u_6} {N : Type
 u_7} [inst : Semiring R] (f : M → N) (x : MonoidAlgebra R M),   (MonoidAlgebra.
mapDomain f x).coef…
· 使用定理 `Finsupp.mapDomain_smul`：mapDomain_smul [AddCommMonoid M] [DistribSMul R 
M] {f : α -> β} (b : R) (v : α ->₀ M) : mapDomain f (b • v) = b • mapDomain f v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomain_smul (f : M → N) (s : S) (x : R[M]) : mapDomain f (s • x) = s • mapDomain f x := by
  ext; simp [Finsupp.mapDomain_smul]

end DistribMulAction

section Module
variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R S[M] := fast_instance% coeffEquiv.module _

@[to_additive]
/-
**MonoidAlgebra.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：instIsTorsionFree [IsTorsionFree R S] : IsTorsionFree R S[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.moduleIsTorsionFree`：∀ (R : Type u_1) {α : Type u_2} {β : Type u_3
} [inst : Semiring R] (e : α ≃ β) [inst_1 : AddCommMonoid β]   [inst_2 : _root_.
Module R β] [Mo…
-/
instance instIsTorsionFree [IsTorsionFree R S] : IsTorsionFree R S[M] :=
  coeffEquiv.moduleIsTorsionFree _

variable (R) in
/-- `MonoidAlgebra.coeff` as a linear equiv. -/
@[to_additive (attr := simps! apply symm_apply)
/-- `MonoidAlgebra.coeff` as a linear equiv. -/]
/-
**MonoidAlgebra.coeffLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：coeffLinearEquiv : S[M] ≃ₗ[R] M ->₀ S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeffLinearEquiv : S[M] ≃ₗ[R] M →₀ S := coeffEquiv.linearEquiv _

variable (R S) in
/-- `MonoidAlgebra.mapDomain` as a linear map. -/
@[to_additive /-- `AddMonoidAlgebra.mapDomain` as a linear map. -/]
/-
**MonoidAlgebra.mapDomainLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainLinearMap (f : M -> N) : S[M] ->ₗ[R] S[N]
参数：f : M -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidAlgebra.mapDomain` as a linear map.
-/
def mapDomainLinearMap (f : M → N) : S[M] →ₗ[R] S[N] :=
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Finsupp.lmapDomain _ _ f ∘ₗ
    (coeffLinearEquiv _).toLinearMap

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapDomainLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：coeff_mapDomainLinearMap (f : M -> N) (x : S[M]) : (mapDomainLinearMap R S
 f x).coeff = x.coeff.mapDomain f
参数：f : M -> N；x : S[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_mapDomainLinearMap (f : M → N) (x : S[M]) :
    (mapDomainLinearMap R S f x).coeff = x.coeff.mapDomain f := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainLinearMap_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：mapDomainLinearMap_single (f : M -> N) (s : S) (m : M) : mapDomainLinearMa
p R S f (single m s) = single (f m) s
参数：f : M -> N；s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainLinearMap_single (f : M → N) (s : S) (m : M) :
    mapDomainLinearMap R S f (single m s) = single (f m) s := by simp [mapDomainLinearMap]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainLinearMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：mapDomainLinearMap_comp (f : M -> N) (g : N -> O) : mapDomainLinearMap R S
 (g ∘ f) = mapDomainLinearMap R S g ∘ₗ mapDomainLinearMap R S f
参数：f : M -> N；g : N -> O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainLinearMap_comp (f : M → N) (g : N → O) :
    mapDomainLinearMap R S (g ∘ f) = mapDomainLinearMap R S g ∘ₗ mapDomainLinearMap R S f := by
  ext; simp [Finsupp.mapDomain_comp]

variable (R S) in
/-- `MonoidAlgebra.mapDomain` as a linear equiv. -/
@[to_additive /-- `AddMonoidAlgebra.mapDomain` as a linear equiv. -/]
/-
**MonoidAlgebra.mapDomainLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：mapDomainLinearEquiv (e : M ≃ N) : S[M] ≃ₗ[R] S[N]
参数：e : M ≃ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonoidAlgebra.mapDomain` as a linear equiv.
-/
def mapDomainLinearEquiv (e : M ≃ N) : S[M] ≃ₗ[R] S[N] :=
  (coeffLinearEquiv _).trans <| (Finsupp.domLCongr e).trans <| (coeffLinearEquiv _).symm

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.coeff_mapDomainLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：coeff_mapDomainLinearEquiv (e : M ≃ N) (x : S[M]) : (mapDomainLinearEquiv 
R S e x).coeff = equivMapDomain e x.coeff
参数：e : M ≃ N；x : S[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_mapDomainLinearEquiv (e : M ≃ N) (x : S[M]) :
    (mapDomainLinearEquiv R S e x).coeff = equivMapDomain e x.coeff := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainLinearEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlg
ebra`。
形式化陈述：mapDomainLinearEquiv_single (e : M ≃ N) (s : S) (m : M) : mapDomainLinearE
quiv R S e (single m s) = single (e m) s
参数：e : M ≃ N；s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainLinearEquiv_single (e : M ≃ N) (s : S) (m : M) :
    mapDomainLinearEquiv R S e (single m s) = single (e m) s := by simp [mapDomainLinearEquiv]

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.symm_mapDomainLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：symm_mapDomainLinearEquiv (e : M ≃ N) : (mapDomainLinearEquiv R S e).symm 
= mapDomainLinearEquiv R S e.symm
参数：e : M ≃ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mapDomainLinearEquiv (e : M ≃ N) :
    (mapDomainLinearEquiv R S e).symm = mapDomainLinearEquiv R S e.symm := rfl

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.mapDomainLinearEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlge
bra`。
形式化陈述：mapDomainLinearEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) : mapDomainLinearEqui
v R S (e₁.trans e₂) = (mapDomainLinearEquiv R S e₁).trans (mapDomainLinearEquiv 
R S e₂)
参数：e₁ : M ≃ N；e₂ : N ≃ O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapDomainLinearEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    mapDomainLinearEquiv R S (e₁.trans e₂) =
      (mapDomainLinearEquiv R S e₁).trans (mapDomainLinearEquiv R S e₂) := by ext; simp

variable (R M) in
/-- The trivial monoid algebra is the base ring. -/
@[to_additive (dont_translate := R)
/-- The trivial monoid algebra is the base ring. -/]
/-
**MonoidAlgebra.uniqueLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：uniqueLinearEquiv [One M] [Subsingleton M] : S[M] ≃ₗ[R] S where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def uniqueLinearEquiv [One M] [Subsingleton M] : S[M] ≃ₗ[R] S where
  toAddEquiv := coeffAddEquiv.trans <| Finsupp.uniqueAddEquiv 1
  map_smul' r x := by simp

variable (R) in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.uniqueLinearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：uniqueLinearEquiv_apply [One M] [Subsingleton M] (x : S[M]) : uniqueLinear
Equiv R M x = x.coeff 1
参数：x : S[M]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniqueLinearEquiv_apply [One M] [Subsingleton M] (x : S[M]) :
    uniqueLinearEquiv R M x = x.coeff 1 := rfl

variable (R M) in
@[to_additive (attr := simp)]
/-
**MonoidAlgebra.uniqueLinearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAl
gebra`。
形式化陈述：uniqueLinearEquiv_symm_apply [One M] [Subsingleton M] (s : S) : (uniqueLin
earEquiv R M).symm s = .single 1 s
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uniqueLinearEquiv_symm_apply [One M] [Subsingleton M] (s : S) :
    (uniqueLinearEquiv R M).symm s = .single 1 s := rfl

variable (R S s) in
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/
@[to_additive
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/]
/-
**MonoidAlgebra.supported** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：supported : Submodule R S[M]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def supported : Submodule R S[M] := (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap
/-
**MonoidAlgebra.mem_supported** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : _root_.Module R S]   {s : Set M} {x : MonoidAlgebra S M
}, x ∈ MonoidAlgebra.supported R S s ↔ ↑x.coeff.support ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma mem_supported : x ∈ supported R S s ↔ ↑x.coeff.support ⊆ s := .rfl

@[to_additive]
/-
**MonoidAlgebra.mem_supported'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：mem_supported' : x in supported R S s ↔ forall m ∉ s, x.coeff m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_supported' : x ∈ supported R S s ↔ ∀ m ∉ s, x.coeff m = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

variable (R S s) in
@[to_additive]
/-
**MonoidAlgebra.supported_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：supported_eq_map : supported R S s = (Finsupp.supported S R s).map (coeffL
inearEquiv R).symm.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
-/
lemma supported_eq_map :
    supported R S s = (Finsupp.supported S R s).map (coeffLinearEquiv R).symm.toLinearMap :=
  Submodule.comap_equiv_eq_map_symm ..

set_option backward.isDefEq.respectTransparency false in
variable (R S s) in
@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.supported_eq_span_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：supported_eq_span_single : supported R R s = .span R ((fun m => single m 1
) '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.supported_eq_map`：supported_eq_map : supported R S s = (Fi
nsupp.supported S R s).map (coeffLinearEquiv R).symm.toLinearMap
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Finsupp.supported_eq_span_single`：supported_eq_span_single (s : Set α) :
 supported R R s = span R ((fun i => single i 1) '' s)
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_symm_apply`：∀ (R : Type u_1) {S : Type u_
2} {M : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Mod
ule R S]   (a : M →₀ S), (Monoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma supported_eq_span_single : supported R R s = .span R ((fun m ↦ single m 1) '' s) := by
  simp [supported_eq_map, Finsupp.supported_eq_span_single R s, Submodule.map_span,
    ← Set.image_comp]

@[to_additive (attr := gcongr)]
/-
**MonoidAlgebra.supported_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：supported_mono (hst : s subseteq t) : supported R S s <= supported R S t
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma supported_mono (hst : s ⊆ t) : supported R S s ≤ supported R S t := fun _ h ↦ h.trans hst

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
@[to_additive (dont_translate := R) (attr := simps!)
/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/]
/-
**MonoidAlgebra.supportedEquivFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：supportedEquivFinsupp (s : Set M) : supported R S s ≃ₗ[R] s ->₀ S
参数：s : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def supportedEquivFinsupp (s : Set M) : supported R S s ≃ₗ[R] s →₀ S :=
  { toFun x := ⟨x.1.coeff, x.2⟩
    invFun x := ⟨.ofCoeff x.1, x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
   ≪≫ₗ Finsupp.supportedEquivFinsupp s

end Module

@[to_additive (dont_translate := R) faithfulSMul]
/-
**MonoidAlgebra.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：faithfulSMul [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty
 M] : FaithfulSMul R S[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.faithfulSMul`：∀ (M : Type u_1) {α : Type u_4} {β : Type u_5} [inst
 : SMul M β] (e : α ≃ β) [FaithfulSMul M β], FaithfulSMul M α
-/
instance faithfulSMul [Semiring S] [SMulZeroClass R S] [FaithfulSMul R S] [Nonempty M] :
    FaithfulSMul R S[M] := coeffEquiv.faithfulSMul _

/-- The standard basis for a monoid algebra. -/
@[to_additive /-- The standard basis for an additive monoid algebra. -/]
/-
**MonoidAlgebra.basis** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：basis (R k) [Semiring k] : Module.Basis R k (MonoidAlgebra k R) where repr
参数：R k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard basis for a monoid algebra.
-/
def basis (R k) [Semiring k] : Module.Basis R k (MonoidAlgebra k R) where
  repr := coeffLinearEquiv _

@[to_additive (dont_translate := k) (attr := simp)]
/-
**MonoidAlgebra.basis_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：basis_apply (k) [Semiring k] (r : R) : MonoidAlgebra.basis R k r = MonoidA
lgebra.single r 1
参数：k；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma basis_apply (k) [Semiring k] (r : R) :
    MonoidAlgebra.basis R k r = MonoidAlgebra.single r 1 :=
  rfl

/-- This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` when `M = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ S[M]` and then it can be an instance.
TODO: Generalise to a group acting on another, instead of just the left multiplication action.
-/
@[implicit_reducible]
/-
**MonoidAlgebra.comapDistribMulActionSelf** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：comapDistribMulActionSelf [Group G] [Semiring S] : DistribMulAction G S[G]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance as it conflicts with `MonoidAlgebra.distribMulAction` wh
en `M = kˣ`.

TODO: Change the type to `DistribMulAction Gᵈᵐᵃ S[M]` and then it can be an inst
ance.
TODO: Generalise to a group acting on another, instead of just the left multipli
cation action.
-/
def comapDistribMulActionSelf [Group G] [Semiring S] : DistribMulAction G S[G] :=
  have := Finsupp.comapDistribMulAction (G := G) (α := G) (M := S)
  fast_instance% coeffEquiv.distribMulAction _

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.single_mem_span_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`
。
形式化陈述：single_mem_span_single [Semiring R] [Nontrivial R] {m : M} {s : Set M} : s
ingle m 1 in Submodule.span R ((single · (1 : R)) '' s) ↔ m in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `MonoidAlgebra.coeffLinearEquiv_apply`：∀ (R : Type u_1) {S : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : _root_.Module R
 S]   (a : MonoidAlgebra S…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma single_mem_span_single [Semiring R] [Nontrivial R] {m : M} {s : Set M} :
    single m 1 ∈ Submodule.span R ((single · (1 : R)) '' s) ↔ m ∈ s := by
  refine (Set.mem_image_equiv (f := (coeffLinearEquiv R).toEquiv)).symm.trans ?_
  change _ ∈ (Submodule.span R _).map (coeffLinearEquiv R).toLinearMap ↔ _
  simp [Submodule.map_span, ← Set.image_comp, Finsupp.single_mem_span_single]

end SMul

/-! #### Copies of `ext` lemmas and bundled `single`s from `Finsupp` -/

section ExtLemmas
variable [Semiring S]

/-- `MonoidAlgebra.single` as a `DistribMulActionHom`. -/
@[to_additive (dont_translate := R) singleDistribMulActionHom
/-- `AddMonoidAlgebra.single` as a `DistribMulActionHom`. -/]
/-
**MonoidAlgebra.singleDistribMulActionHom** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgeb
ra`。
形式化陈述：singleDistribMulActionHom [Monoid R] [DistribMulAction R S] (a : M) : S ->
+[R] S[M] where __
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def singleDistribMulActionHom [Monoid R] [DistribMulAction R S] (a : M) : S →+[R] S[M] where
  __ := singleAddHom a
  map_smul' S m := by simp

/-- A copy of `Finsupp.distribMulActionHom_ext'` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) (attr := ext) distribMulActionHom_ext'
/-- A copy of `Finsupp.distribMulActionHom_ext'` for `AddMonoidAlgebra`. -/]
/-
**MonoidAlgebra.distribMulActionHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebr
a`。
形式化陈述：distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulA
ction R N] [DistribMulAction R S] {f g : S[M] ->+[R] N} (h : forall a, f.comp (s
ingleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) : f = g
参数：h : forall a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMul
ActionHom a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.toAddMonoidHom_injective`：∀ {M : Type u_1} [inst : M
onoid M] {N : Type u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 
: AddMonoid A]   [inst_3 : Distrib…
· 使用引理 `MonoidAlgebra.addMonoidHom_ext`：addMonoidHom_ext [AddZeroClass N] ⦃f g :
 R[M] ->+ N⦄ (h : forall m r, f (single m r) = g (single m r)) : f = g
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `DistribMulActionHom.instAddDistribAddActionSemiHomClassCoeAddMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : AddMonoid A]   [inst_3 : Distrib…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R S] {f g : S[M] →+[R] N}
    (h : ∀ a, f.comp (singleDistribMulActionHom a) = g.comp (singleDistribMulActionHom a)) :
    f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(h a) x)

/-- A copy of `Finsupp.lsingle` for `MonoidAlgebra`. -/
@[to_additive (dont_translate := R) /-- A copy of `Finsupp.lsingle` for `AddMonoidAlgebra`. -/]
/-
**MonoidAlgebra.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：lsingle [Semiring R] [Module R S] (a : M) : S ->ₗ[R] S[M]
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of `Finsupp.lsingle` for `MonoidAlgebra`.
-/
def lsingle [Semiring R] [Module R S] (a : M) : S →ₗ[R] S[M] :=
  (coeffLinearEquiv _).symm.toLinearMap.comp <| Finsupp.lsingle a

@[to_additive (attr := simp)]
/-
**MonoidAlgebra.lsingle_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lsingle_apply [Semiring R] [Module R S] (a : M) (b : S) : lsingle (R
参数：a : M；b : S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lsingle_apply [Semiring R] [Module R S] (a : M) (b : S) :
    lsingle (R := R) a b = single a b :=
  rfl

/-- A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`. -/
@[to_additive (attr := ext high)]
/-
**MonoidAlgebra.lhom_ext'** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module 
R S] ⦃f g : S[M] ->ₗ[R] N⦄ (H : forall (x : M), LinearMap.comp f (lsingle x) = L
inearMap.comp g (lsingle x)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用引理 `MonoidAlgebra.addMonoidHom_ext`：addMonoidHom_ext [AddZeroClass N] ⦃f g :
 R[M] ->+ N⦄ (h : forall m r, f (single m r) = g (single m r)) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A copy of `Finsupp.lhom_ext'` for `MonoidAlgebra`.
-/
lemma lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R S]
    ⦃f g : S[M] →ₗ[R] N⦄
    (H : ∀ (x : M), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addMonoidHom_ext fun a x ↦ congr($(H a) x)

end ExtLemmas

section MiscTheorems
variable [Semiring R] [Semiring S] [MulOneClass M] {s : Set M} {m : M}

/-
**MonoidAlgebra.smul_of** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：smul_of (m : M) (r : R) : r • of R M m = single m r
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_of (m : M) (r : R) : r • of R M m = single m r := by simp

/-- The image of an element `m : M` in `R[M]` belongs to the submodule generated by
`s : Set M` if and only if `m ∈ s`. -/
/-
**MonoidAlgebra.of_mem_span_of_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：of_mem_span_of_iff [Nontrivial R] : of R M m in Submodule.span R (of R M '
' s) ↔ m in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.single_mem_span_single`：single_mem_span_single [Semiring R
] [Nontrivial R] {m : M} {s : Set M} : single m 1 in Submodule.span R ((single ·
 (1 : R)) '' s) ↔ m in s

--- 原说明 ---
The image of an element `m : M` in `R[M]` belongs to the submodule generated by
`s : Set M` if and only if `m ∈ s`.
-/
lemma of_mem_span_of_iff [Nontrivial R] : of R M m ∈ Submodule.span R (of R M '' s) ↔ m ∈ s :=
  single_mem_span_single

/-- If the image of an element `m : M` in `R[M]` belongs to the submodule generated by the
closure of some `s : Set M` then `m ∈ closure s`. -/
/-
**MonoidAlgebra.mem_closure_of_mem_span_closure** 是 Mathlib 中的一个引理，位于命名空间 `Monoi
dAlgebra`。
形式化陈述：mem_closure_of_mem_span_closure [Nontrivial R] (h : of R M m in Submodule.
span R (Submonoid.closure <| of R M '' s)) : m in Submonoid.closure s
参数：h : of R M m in Submodule.span R (Submonoid.closure <| of R M '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MonoidAlgebra.of_mem_span_of_iff`：of_mem_span_of_iff [Nontrivial R] : of
 R M m in Submodule.span R (of R M '' s) ↔ m in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)

--- 原说明 ---
If the image of an element `m : M` in `R[M]` belongs to the submodule generated 
by the
closure of some `s : Set M` then `m ∈ closure s`.
-/
lemma mem_closure_of_mem_span_closure [Nontrivial R]
    (h : of R M m ∈ Submodule.span R (Submonoid.closure <| of R M '' s)) :
    m ∈ Submonoid.closure s := by
  rw [← MonoidHom.map_mclosure] at h; simpa using of_mem_span_of_iff.1 h
/-
**MonoidAlgebra.liftNC_smul** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：liftNC_smul (f : S ->+* R) (g : M ->* R) (c : S) (φ : S[M]) : liftNC (f : 
S ->+ R) g (c • φ) = f c * liftNC (f : S ->+ R) g φ
参数：f : S ->+* R；g : M ->* R；c : S；φ : S[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `MonoidAlgebra.addHom_ext'`：addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g
 : R[M] ->+ N⦄ (hfg : forall m, f.comp (singleAddHom m) = g.comp (singleAddHom m
)) : f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [inst 
: Semiring R] (m : M) (r : R),   (MonoidAlgebra.singleAddHom m) r = MonoidAlgebr
a.single m r
· 使用引理 `MonoidAlgebra.smul_single`：smul_single (a : A) (m : M) (r : R) : a • sin
gle m r = single m (a • r)
· 使用定理 `MonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : G -> R) (a
 : G) (b : k) : liftNC f g (single a b) = f b * g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem liftNC_smul (f : S →+* R) (g : M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC (↑f) g) from
    DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

end MiscTheorems

/-! #### Non-unital, non-associative algebra structure -/
section NonUnitalNonAssocAlgebra

variable (S) [Semiring S] [DistribSMul R S] [Mul M]

@[to_additive (dont_translate := R S) isScalarTower_self]
/-
**MonoidAlgebra.isScalarTower_self** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
 smul_assoc t a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq M] (x y : R[M]) (m : M) 
: (x * y).coeff m = x.coeff.sum fun m₁ r₁ => y.coeff.sum fun m₂ r₂ => if m₁ * m₂
 = m then r₁ …
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
instance isScalarTower_self [IsScalarTower R S S] : IsScalarTower R S[M] S[M] where
  smul_assoc t a b := by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, smul_mul_assoc]

/-- Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so we can take
`R = S` in the below. In other words, if the coefficients are commutative amongst themselves, they
also commute with the algebra multiplication. -/
@[to_additive (dont_translate := R S) smulCommClass_self]
/-
**MonoidAlgebra.smulCommClass_self** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
形式化陈述：smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
 smul_comm t a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq M] (x y : R[M]) (m : M) 
: (x * y).coeff m = x.coeff.sum fun m₁ r₁ => y.coeff.sum fun m₂ r₂ => if m₁ * m₂
 = m then r₁ …
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)

--- 原说明 ---
Note that if `S` is a `CommSemiring` then we have `SMulCommClass S S S` and so w
e can take
`R = S` in the below. In other words, if the coefficients are commutative amongs
t themselves, they
also commute with the algebra multiplication.
-/
instance smulCommClass_self [SMulCommClass R S S] : SMulCommClass R S[M] S[M] where
  smul_comm t a b := by
    classical ext; simp [coeff_mul, sum_smul_index', Finsupp.smul_sum, mul_smul_comm]

@[to_additive (dont_translate := R S) smulCommClass_symm_self]
/-
**MonoidAlgebra.smulCommClass_symm_self** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra
`。
形式化陈述：smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance smulCommClass_symm_self [SMulCommClass S R S] : SMulCommClass S[M] R S[M] :=
  have := SMulCommClass.symm S R S; .symm ..

end NonUnitalNonAssocAlgebra

section Submodule

variable [CommSemiring S] [Monoid M]
variable {V : Type*} [AddCommMonoid V]
variable [Module S V] [Module S[M] V] [IsScalarTower S S[M] V]

/-- A submodule over `S` which is stable under scalar multiplication by elements of `M` is a
submodule over `S[M]` -/
/-
**MonoidAlgebra.submoduleOfSMulMem** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：submoduleOfSMulMem (W : Submodule S V) (h : forall (g : M) (v : V), v in W
 -> of S M g • v in W) : Submodule S[M] V where carrier
参数：W : Submodule S V；h : forall (g : M) (v : V), v in W -> of S M g • v in W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule over `S` which is stable under scalar multiplication by elements of 
`M` is a
submodule over `S[M]`
-/
def submoduleOfSMulMem (W : Submodule S V) (h : ∀ (g : M) (v : V), v ∈ W → of S M g • v ∈ W) :
    Submodule S[M] V where
  carrier := W
  zero_mem' := W.zero_mem'
  add_mem' := W.add_mem'
  smul_mem' f v hv := by
    rw [← f.sum_coeff_single, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end MonoidAlgebra

/-! ### Additive monoids -/

namespace AddMonoidAlgebra
section Semiring
variable [Semiring R] [Semiring S]

/-- The image of an element `m : M` in `R[M]` belongs the submodule generated by
`s : Set M` if and only if `m ∈ s`. -/
/-
**AddMonoidAlgebra.of'_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [Nontrivial R] {m : M}
 {s : Set M},   AddMonoidAlgebra.of' R M m ∈ Submodule.span R (AddMonoidAlgebra.
of' R M '' s) ↔ m ∈ s
参数：AddMonoidAlgebra.of' R M '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_mem_span_single`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Semiring R] [Nontrivial R] {m : M} {s : Set M},   AddMonoidAlgebra.sing
le m 1 ∈ Submodule.span R ((f…

--- 原说明 ---
The image of an element `m : M` in `R[M]` belongs the submodule generated by
`s : Set M` if and only if `m ∈ s`.
-/
lemma of'_mem_span [Nontrivial R] {m : M} {s : Set M} :
    of' R M m ∈ Submodule.span R (of' R M '' s) ↔ m ∈ s := single_mem_span_single

set_option backward.isDefEq.respectTransparency false in
/-- If the image of an element `m : M` in `R[M]` belongs the submodule generated by
the closure of some `s : Set M` then `m ∈ closure s`. -/
/-
**AddMonoidAlgebra.mem_closure_of_mem_span_closure** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dMonoidAlgebra`。
形式化陈述：mem_closure_of_mem_span_closure [AddMonoid M] [Nontrivial R] {m : M} {s : 
Set M} (h : of' R M m in Submodule.span R (Submonoid.closure <| of' R M '' s)) :
 m in AddSubmonoid.closure s
参数：h : of' R M m in Submodule.span R (Submonoid.closure <| of' R M '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidAlgebra.of'_mem_span`：∀ {R : Type u_1} {M : Type u_3} [inst : S
emiring R] [Nontrivial R] {m : M} {s : Set M},   AddMonoidAlgebra.of' R M m ∈ Su
bmodule.span R (Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr'`：image_congr' {f g : α -> β} {s : Set α} (h : forall x 
: α, f x = g x) : f '' s = g '' s
· 使用定理 `AddMonoidAlgebra.of'_eq_of`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] [inst_1 : AddZeroClass M] (a : M),   AddMonoidAlgebra.of' R M a = (AddMo
noidAlgebra.of R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If the image of an element `m : M` in `R[M]` belongs the submodule generated by
the closure of some `s : Set M` then `m ∈ closure s`.
-/
lemma mem_closure_of_mem_span_closure [AddMonoid M] [Nontrivial R] {m : M} {s : Set M}
    (h : of' R M m ∈ Submodule.span R (Submonoid.closure <| of' R M '' s)) :
    m ∈ AddSubmonoid.closure s := by
  suffices Multiplicative.ofAdd m ∈ Submonoid.closure (Multiplicative.toAdd ⁻¹' s) by
    simpa [← AddSubmonoid.toSubmonoid_closure]
  let s' := @Submonoid.closure (Multiplicative M) Multiplicative.mulOneClass s
  have h' : Submonoid.map (of R M) s' = Submonoid.closure (of R M '' s) :=
    MonoidHom.map_mclosure _ _
  rw [Set.image_congr' (show ∀ x, of' R M x = of R M x from fun x => of'_eq_of x), ← h'] at h
  simpa using! of'_mem_span.1 h
/-
**AddMonoidAlgebra.liftNC_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：liftNC_smul [AddZeroClass M] (f : S ->+* R) (g : Multiplicative M ->* R) (
c : S) (φ : S[M]) : liftNC (f : S ->+ R) g (c • φ) = f c * liftNC (f : S ->+ R) 
g φ
参数：f : S ->+* R；g : Multiplicative M ->* R；c : S；φ : S[M]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddMonoidAlgebra.addHom_ext'`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {N : Type u_8} [inst_1 : AddZeroClass N]   ⦃f g : AddMonoidAlgebra R M
 →+ N⦄,   (∀ (m : …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `AddMonoidAlgebra.smul_single`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] {A : Type u_8} [inst_1 : SMulZeroClass A R] (a : A) (m : M) (r : R),  
 a • AddMonoidAlge…
· 使用定理 `AddMonoidAlgebra.liftNC_single`：liftNC_single (f : k ->+ R) (g : Multipl
icative G -> R) (a : G) (b : k) : liftNC f g (single a b) = f b * g (Multiplicat
ive.ofAdd a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma liftNC_smul [AddZeroClass M] (f : S →+* R) (g : Multiplicative M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp [mul_assoc]

end Semiring
end AddMonoidAlgebra

