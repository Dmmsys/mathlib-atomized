/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Vertex operators

In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.

## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.

## Main results
* Ext

## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.

## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

@[expose] public section

assert_not_exists Cardinal

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
/-
**HVertexOperator** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R] (V :
 Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
参数：Γ : Type*；R : Type*；V : Type*；W : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear 
map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`.
-/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

@[ext]
/-
**HVertexOperator.ext** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`。
形式化陈述：ext (A B : HVertexOperator Γ R V W) (h : forall v : V, A v = B v) : A = B
参数：A B : HVertexOperator Γ R V W；h : forall v : V, A v = B v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

set_option backward.isDefEq.respectTransparency false in
/-- The coefficients of a heterogeneous vertex operator, viewed as a linear map to formal power
series with coefficients in linear maps. -/
@[simps]
/-
**HVertexOperator.coeff** 是 Mathlib 中的一个定义，位于命名空间 `HVertexOperator`。
形式化陈述：coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -> V ->ₗ[R] W where toFun A n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The coefficients of a heterogeneous vertex operator, viewed as a linear map to f
ormal power
series with coefficients in linear maps.
-/
def coeff : HVertexOperator Γ R V W →ₗ[R] Γ → V →ₗ[R] W where
  toFun A n := {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
/-
**HVertexOperator.coeff_isPWOsupport** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`
。
形式化陈述：coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) : ((of R).symm (A
 v)).coeff.support.IsPWO
参数：A : HVertexOperator Γ R V W；v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[ext]
/-
**HVertexOperator.coeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`。
形式化陈述：coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W ->ₗ[R] Γ -
> (V ->ₗ[R] W))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HVertexOperator.ext`：ext (A B : HVertexOperator Γ R V W) (h : forall v :
 V, A v = B v) : A = B
· 使用定理 `HahnModule.ext`：ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff 
= ((of R).symm y).coeff) : x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W →ₗ[R] Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

set_option backward.isDefEq.respectTransparency false in
/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
/-
**HVertexOperator.of_coeff** 是 Mathlib 中的一个定义，位于命名空间 `HVertexOperator`。
形式化陈述：of_coeff (f : Γ -> V ->ₗ[R] W) (hf : forall (x : V), (Function.support (f 
· x)).IsPWO) : HVertexOperator Γ R V W where toFun x
参数：f : Γ -> V ->ₗ[R] W；hf : forall (x : V), (Function.support (f · x)).IsPWO。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a coefficient function valued in linear maps satisfying a partially well-o
rdered support
condition, we produce a heterogeneous vertex operator.
-/
def of_coeff (f : Γ → V →ₗ[R] W) (hf : ∀ (x : V), (Function.support (f · x)).IsPWO) :
    HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/-
**HVertexOperator.coeff_of_coeff** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`。
形式化陈述：coeff_of_coeff (f : Γ -> V ->ₗ[R] W) (hf : forall (x : V), (Function.suppo
rt (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f
参数：f : Γ -> V ->ₗ[R] W；hf : forall (x : V), (Function.support (fun g => f g x)).
IsPWO。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ (x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

@[simp]
/-
**HVertexOperator.of_coeff_coeff** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`。
形式化陈述：of_coeff_coeff (A : HVertexOperator Γ R V W) : of_coeff A.coeff A.coeff_is
PWOsupport = A
参数：A : HVertexOperator Γ R V W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HVertexOperator.coeff_isPWOsupport`：coeff_isPWOsupport (A : HVertexOpera
tor Γ R V W) (v : V) : ((of R).symm (A v)).coeff.support.IsPWO
-/
theorem of_coeff_coeff (A : HVertexOperator Γ R V W) : of_coeff A.coeff A.coeff_isPWOsupport = A :=
  rfl

end Coeff

section Products

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
@[simps]
/-
**HVertexOperator.compHahnSeries** 是 Mathlib 中的一个定义，位于命名空间 `HVertexOperator`。
形式化陈述：compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where coeff g'
参数：u : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composite of two heterogeneous vertex operators acting on a vector, as an it
erated Hahn
series.
-/
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HVertexOperator.compHahnSeries_add** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`
。
形式化陈述：compHahnSeries_add (u v : U) : compHahnSeries A B (u + v) = compHahnSeries
 A B u + compHahnSeries A B v
参数：u v : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HVertexOperator.compHahnSeries_coeff`：∀ {Γ : Type u_5} {Γ' : Type u_6} [
inst : PartialOrder Γ] [inst_1 : PartialOrder Γ'] {R : Type u_7} [inst_2 : CommR
ing R]   {U : Type u_8} {V…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `HVertexOperator.coeff_apply_apply`：∀ {Γ : Type u_1} [inst : PartialOrder
 Γ] {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst_1 : CommRing R]   [inst_2
 : AddCommGroup V] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_add`：coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a =
 x.coeff a + y.coeff a
-/
theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**HVertexOperator.compHahnSeries_smul** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator
`。
形式化陈述：compHahnSeries_smul (r : R) (u : U) : compHahnSeries A B (r • u) = r • com
pHahnSeries A B u
参数：r : R；u : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HVertexOperator.compHahnSeries_coeff`：∀ {Γ : Type u_5} {Γ' : Type u_6} [
inst : PartialOrder Γ] [inst_1 : PartialOrder Γ'] {R : Type u_7} [inst_2 : CommR
ing R]   {U : Type u_8} {V…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `HVertexOperator.coeff_apply_apply`：∀ {Γ : Type u_1} [inst : PartialOrder
 Γ] {R : Type u_2} {V : Type u_3} {W : Type u_4} [inst_1 : CommRing R]   [inst_2
 : AddCommGroup V] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_smul`：coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).c
oeff a = r • x.coeff a
-/
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

set_option backward.isDefEq.respectTransparency false in
/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
/-
**HVertexOperator.comp** 是 Mathlib 中的一个定义，位于命名空间 `HVertexOperator`。
形式化陈述：comp : HVertexOperator (Γ' ×ₗ Γ) R U W where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composite of two heterogeneous vertex operators, as a heterogeneous vertex o
perator.
-/
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

@[simp]
/-
**HVertexOperator.coeff_comp** 是 Mathlib 中的一个定理，位于命名空间 `HVertexOperator`。
形式化陈述：coeff_comp (g : Γ' ×ₗ Γ) : (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.c
oeff (ofLex g).1
参数：g : Γ' ×ₗ Γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

end Products

end HVertexOperator

