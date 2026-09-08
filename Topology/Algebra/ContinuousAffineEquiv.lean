/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Continuous affine equivalences

In this file, we define continuous affine equivalences, affine equivalences
which are continuous with continuous inverse.

## Main definitions
* `ContinuousAffineEquiv.refl k P`: the identity map as a `ContinuousAffineEquiv`;
* `e.symm`: the inverse map of a `ContinuousAffineEquiv` as a `ContinuousAffineEquiv`;
* `e.trans e'`: composition of two `ContinuousAffineEquiv`s; note that the order
  follows `mathlib`'s `CategoryTheory` convention (apply `e`, then `e'`),
  not the convention used in function composition and compositions of bundled morphisms.

* `e.toHomeomorph`: the continuous affine equivalence `e` as a homeomorphism
* `e.toContinuousAffineMap`: the continuous affine equivalence `e` as a continuous affine map
* `ContinuousLinearEquiv.toContinuousAffineEquiv`: a continuous linear equivalence as a continuous
  affine equivalence
* `ContinuousAffineEquiv.constVAdd`: `AffineEquiv.constVAdd` as a continuous affine equivalence

## TODO
- equip `ContinuousAffineEquiv k P P` with a `Group` structure,
  with multiplication corresponding to composition in `AffineEquiv.group`.

-/

@[expose] public section

open Function

/-- A continuous affine equivalence, denoted `P₁ ≃ᴬ[k] P₂`, between two affine topological spaces
is an affine equivalence such that forward and inverse maps are continuous. -/
/-
**ContinuousAffineEquiv** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommG
roup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁] [AddCommGroup V₂]
 [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂] extends P₁ ≃ᵃ[k] P₂ where
 continuous_toFun : Continuous toFun
参数：k P₁ P₂ : Type*。
继承自：P₁ ≃ᵃ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous affine equivalence, denoted `P₁ ≃ᴬ[k] P₂`, between two affine topol
ogical spaces
is an affine equivalence such that forward and inverse maps are continuous.
-/
structure ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
    [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
    [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
    extends P₁ ≃ᵃ[k] P₂ where
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop

@[inherit_doc]
notation:25 P₁ " ≃ᴬ[" k:25 "] " P₂:0 => ContinuousAffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

namespace ContinuousAffineEquiv

-- Basic set-up: standard fields, coercions and ext lemmas
section Basic

/-- A continuous affine equivalence is a homeomorphism. -/
/-
**ContinuousAffineEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffine
Equiv`。
形式化陈述：toHomeomorph (e : P₁ ≃ᴬ[k] P₂) : P₁ ≃ₜ P₂ where __
参数：e : P₁ ≃ᴬ[k] P₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.continuous_toFun`：∀ {k : Type u_1} {P₁ : Type u_2}
 {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Add
CommGroup V₁] [inst_2 : _roo…
· 使用定理 `ContinuousAffineEquiv.continuous_invFun`：∀ {k : Type u_1} {P₁ : Type u_2
} {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Ad
dCommGroup V₁] [inst_2 : _roo…

--- 原说明 ---
A continuous affine equivalence is a homeomorphism.
-/
def toHomeomorph (e : P₁ ≃ᴬ[k] P₂) : P₁ ≃ₜ P₂ where
  __ := e
/-
**ContinuousAffineEquiv.toAffineEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：toAffineEquiv_injective : Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) -> P₁ ≃
ᵃ[k] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) → P₁ ≃ᵃ[k] P₂) := by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr
/-
**ContinuousAffineEquiv.instEquivLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：instEquivLike : EquivLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEquivLike : EquivLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)
/-
**ContinuousAffineEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomeomorphClass (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

attribute [coe] ContinuousAffineEquiv.toAffineEquiv

/-- Coerce continuous affine equivalences to affine equivalences. -/
/-
**ContinuousAffineEquiv.coe** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce continuous affine equivalences to affine equivalences.
-/
instance coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂) := ⟨toAffineEquiv⟩
/-
**ContinuousAffineEquiv.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineE
quiv`。
形式化陈述：instFunLike : FunLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toAffineEquiv
  coe_injective _ _ h := toAffineEquiv_injective (DFunLike.coe_injective h)

@[simp, norm_cast]
/-
**ContinuousAffineEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEquiv
`。
形式化陈述：coe_coe (e : P₁ ≃ᴬ[k] P₂) : ⇑(e : P₁ ≃ᵃ[k] P₂) = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (e : P₁ ≃ᴬ[k] P₂) : ⇑(e : P₁ ≃ᵃ[k] P₂) = e :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineE
quiv`。
形式化陈述：coe_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv = e :=
  rfl

@[ext]
/-
**ContinuousAffineEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {e e' : P₁ ≃ᴬ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

@[continuity]
/-
**ContinuousAffineEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂), Continuous ⇑e
参数：e : P₁ ≃ᴬ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.continuous_toFun`：∀ {k : Type u_1} {P₁ : Type u_2}
 {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Add
CommGroup V₁] [inst_2 : _roo…
-/
protected theorem continuous (e : P₁ ≃ᴬ[k] P₂) : Continuous e :=
  e.2

/-- A continuous affine equivalence is a continuous affine map. -/
/-
**ContinuousAffineEquiv.toContinuousAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousAffineEquiv`。
形式化陈述：toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : P₁ ->ᴬ[k] P₂ where __
参数：e : P₁ ≃ᴬ[k] P₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.continuous_toFun`：∀ {k : Type u_1} {P₁ : Type u_2}
 {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Add
CommGroup V₁] [inst_2 : _roo…

--- 原说明 ---
A continuous affine equivalence is a continuous affine map.
-/
def toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : P₁ →ᴬ[k] P₂ where
  __ := e
  cont := e.continuous_toFun

/-- Coerce continuous linear equivs to continuous linear maps. -/
/-
**ContinuousAffineEquiv.ContinuousAffineMap.coe** 是 Mathlib 中的一个定义，位于命名空间 `Conti
nuousAffineEquiv.ContinuousAffineMap`。
形式化陈述：{k : Type u_1} →   {P₁ : Type u_2} →     {P₂ : Type u_3} →       {V₁ : Typ
e u_6} →         {V₂ : Type u_7} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : _root_.Module k V₁] →           
      [inst_3 : AddTorsor V₁ P₁] →                   [inst_4 : TopologicalSpace 
P₁] →                     [inst_5 : AddCommGroup V₂] →                       [in
st_6 : _root_.Module k V₂] →                         [inst_7 : AddTorsor V₂ P₂] 
→ [inst_8 : TopologicalSpace P₂] → Coe (P₁ ≃ᴬ[k] P₂) (P₁ →ᴬ[k] P₂)
参数：P₁ ≃ᴬ[k] P₂；P₁ →ᴬ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce continuous linear equivs to continuous linear maps.
-/
instance ContinuousAffineMap.coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ →ᴬ[k] P₂) :=
  ⟨toContinuousAffineMap⟩

@[simp]
/-
**ContinuousAffineEquiv.coe_toContinuousAffineMap** 是 Mathlib 中的一个引理，位于命名空间 `Con
tinuousAffineEquiv`。
形式化陈述：coe_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toContinuousAffineMap = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toContinuousAffineMap = e :=
  rfl
/-
**ContinuousAffineEquiv.toContinuousAffineMap_injective** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousAffineEquiv`。
形式化陈述：toContinuousAffineMap_injective : Function.Injective (toContinuousAffineMa
p : (P₁ ≃ᴬ[k] P₂) -> (P₁ ->ᴬ[k] P₂))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toContinuousAffineMap_injective :
    Function.Injective (toContinuousAffineMap : (P₁ ≃ᴬ[k] P₂) → (P₁ →ᴬ[k] P₂)) := by
  intro e e' h
  ext p
  simp_rw [← coe_toContinuousAffineMap, h]
/-
**ContinuousAffineEquiv.toContinuousAffineMap_toAffineMap** 是 Mathlib 中的一个引理，位于命
名空间 `ContinuousAffineEquiv`。
形式化陈述：toContinuousAffineMap_toAffineMap (e : P₁ ≃ᴬ[k] P₂) : e.toContinuousAffine
Map.toAffineMap = e.toAffineEquiv.toAffineMap
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousAffineMap_toAffineMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap :=
  rfl
/-
**ContinuousAffineEquiv.toContinuousAffineMap_toContinuousMap** 是 Mathlib 中的一个引理
，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：toContinuousAffineMap_toContinuousMap (e : P₁ ≃ᴬ[k] P₂) : e.toContinuousAf
fineMap.toContinuousMap = toContinuousMap e.toHomeomorph
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousAffineMap_toContinuousMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toContinuousMap = toContinuousMap e.toHomeomorph :=
  rfl

end Basic

section ReflSymmTrans

variable (k P₁) in
/-- Identity map as a `ContinuousAffineEquiv`. -/
/-
**ContinuousAffineEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：refl : P₁ ≃ᴬ[k] P₁ where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Identity map as a `ContinuousAffineEquiv`.
-/
def refl : P₁ ≃ᴬ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]
/-
**ContinuousAffineEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqui
v`。
形式化陈述：coe_refl : ⇑(refl k P₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：refl_apply (x : P₁) : refl k P₁ x = x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.toAffineEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AffineEquiv`。
形式化陈述：toAffineEquiv_refl : (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_refl : (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁ :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.toEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Equiv`。
形式化陈述：toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

/-- Inverse of a continuous affine equivalence as a continuous affine equivalence. -/
@[symm]
/-
**ContinuousAffineEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：symm (e : P₁ ≃ᴬ[k] P₂) : P₂ ≃ᴬ[k] P₁ where toAffineEquiv
参数：e : P₁ ≃ᴬ[k] P₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.continuous_invFun`：∀ {k : Type u_1} {P₁ : Type u_2
} {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Ad
dCommGroup V₁] [inst_2 : _roo…
· 使用定理 `ContinuousAffineEquiv.continuous_toFun`：∀ {k : Type u_1} {P₁ : Type u_2}
 {P₂ : Type u_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : Add
CommGroup V₁] [inst_2 : _roo…

--- 原说明 ---
Inverse of a continuous affine equivalence as a continuous affine equivalence.
-/
def symm (e : P₁ ≃ᴬ[k] P₂) : P₂ ≃ᴬ[k] P₁ where
  toAffineEquiv := e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

/-- See Note [custom simps projection].
  We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**ContinuousAffineEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineE
quiv.Simps`。
形式化陈述：{k : Type u_1} →   {P₁ : Type u_2} →     {P₂ : Type u_3} →       {V₁ : Typ
e u_6} →         {V₂ : Type u_7} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : _root_.Module k V₁] →           
      [inst_3 : AddTorsor V₁ P₁] →                   [inst_4 : TopologicalSpace 
P₁] →                     [inst_5 : AddCommGroup V₂] →                       [in
st_6 : _root_.Module k V₂] →                         [inst_7 : AddTorsor V₂ P₂] 
→ [inst_8 : TopologicalSpace P₂] → (P₁ ≃ᴬ[k] P₂) → P₁ → P₂
参数：P₁ ≃ᴬ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
  We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (e : P₁ ≃ᴬ[k] P₂) : P₁ → P₂ :=
  e

/-- See Note [custom simps projection]. -/
/-
**ContinuousAffineEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAf
fineEquiv.Simps`。
形式化陈述：{k : Type u_1} →   {P₁ : Type u_2} →     {P₂ : Type u_3} →       {V₁ : Typ
e u_6} →         {V₂ : Type u_7} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : _root_.Module k V₁] →           
      [inst_3 : AddTorsor V₁ P₁] →                   [inst_4 : TopologicalSpace 
P₁] →                     [inst_5 : AddCommGroup V₂] →                       [in
st_6 : _root_.Module k V₂] →                         [inst_7 : AddTorsor V₂ P₂] 
→ [inst_8 : TopologicalSpace P₂] → (P₁ ≃ᴬ[k] P₂) → P₂ → P₁
参数：P₁ ≃ᴬ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.symm_apply (e : P₁ ≃ᴬ[k] P₂) : P₂ → P₁ :=
  e.symm

initialize_simps_projections ContinuousAffineEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**ContinuousAffineEquiv.toAffineEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
AffineEquiv`。
形式化陈述：toAffineEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toAffineEquiv = e.toAffineEq
uiv.symm
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toAffineEquiv = e.toAffineEquiv.symm :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.coe_symm_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAffineEquiv`。
形式化陈述：coe_symm_toAffineEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toAffineEquiv.symm = e.symm
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toAffineEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toAffineEquiv.symm = e.symm := rfl

@[simp]
/-
**ContinuousAffineEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffine
Equiv`。
形式化陈述：toEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
/-
**ContinuousAffineEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineEquiv`。
形式化陈述：coe_symm_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv.symm = e.symm
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
/-
**ContinuousAffineEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineEquiv`。
形式化陈述：apply_symm_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₂) : e (e.symm p) = p
参数：e : P₁ ≃ᴬ[k] P₂；p : P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
/-
**ContinuousAffineEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineEquiv`。
形式化陈述：symm_apply_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₁) : e.symm (e p) = p
参数：e : P₁ ≃ᴬ[k] P₂；p : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p
/-
**ContinuousAffineEquiv.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：apply_eq_iff_eq (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
-/
theorem apply_eq_iff_eq (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq

@[simp]
/-
**ContinuousAffineEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.symm = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.symm = e := rfl
/-
**ContinuousAffineEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (P₁ ≃ᴬ[k] P₂) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousAffineEquiv.symm_symm`：symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.sy
mm = e
-/
theorem symm_bijective : Function.Bijective (symm : (P₁ ≃ᴬ[k] P₂) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**ContinuousAffineEquiv.symm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：symm_symm_apply (e : P₁ ≃ᴬ[k] P₂) (x : P₁) : e.symm.symm x = e x
参数：e : P₁ ≃ᴬ[k] P₂；x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm_apply (e : P₁ ≃ᴬ[k] P₂) (x : P₁) : e.symm.symm x = e x :=
  rfl
/-
**ContinuousAffineEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：symm_apply_eq (e : P₁ ≃ᴬ[k] P₂) {x y} : e.symm x = y ↔ x = e y
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.symm_apply_eq`：symm_apply_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e.s
ymm p₁ = p₂ ↔ p₁ = e p₂
-/
theorem symm_apply_eq (e : P₁ ≃ᴬ[k] P₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq
/-
**ContinuousAffineEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {x y} : y = e.symm x ↔ e y = x
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.eq_symm_apply`：eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ 
= e.symm p₁ ↔ e p₂ = p₁
-/
theorem eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**ContinuousAffineEquiv.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAffineEquiv`。
形式化陈述：apply_eq_iff_eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.
symm p₂
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ContinuousAffineEquiv.eq_symm_apply`：eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {x 
y} : y = e.symm x ↔ e y = x
-/
theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.eq_symm_apply.symm

@[simp]
/-
**ContinuousAffineEquiv.image_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：image_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s
参数：f : P₁ ≃ᴬ[k] P₂；s : Set P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage_symm _

@[simp]
/-
**ContinuousAffineEquiv.preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：preimage_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s
参数：f : P₁ ≃ᴬ[k] P₂；s : Set P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAffineEquiv.image_symm`：image_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set 
P₂) : f.symm '' s = f ⁻¹' s
-/
theorem preimage_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm
/-
**ContinuousAffineEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂), Function.Bijective ⇑e
参数：e : P₁ ≃ᴬ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : P₁ ≃ᴬ[k] P₂) : Bijective e :=
  e.toEquiv.bijective
/-
**ContinuousAffineEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂), Function.Surjective ⇑e
参数：e : P₁ ≃ᴬ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : P₁ ≃ᴬ[k] P₂) : Surjective e :=
  e.toEquiv.surjective
/-
**ContinuousAffineEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂), Function.Injective ⇑e
参数：e : P₁ ≃ᴬ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : P₁ ≃ᴬ[k] P₂) : Injective e :=
  e.toEquiv.injective
/-
**ContinuousAffineEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAffineEquiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁), ⇑e '' s = ⇑e.symm ⁻¹' s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
protected theorem image_eq_preimage_symm (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s
/-
**ContinuousAffineEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousAffineEquiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : _root_.Module k V₁
] [inst_3 : AddTorsor V₁ P₁] [inst_4 : TopologicalSpace P₁]   [inst_5 : AddCommG
roup V₂] [inst_6 : _root_.Module k V₂] [inst_7 : AddTorsor V₂ P₂] [inst_8 : Topo
logicalSpace P₂]   (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂), ⇑e.symm '' s = ⇑e ⁻¹' s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineEquiv.image_eq_preimage_symm`：∀ {k : Type u_1} {P₁ : Typ
e u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1
 : AddCommGroup V₁] [inst_2 : _roo…
· 使用定理 `ContinuousAffineEquiv.symm_symm`：symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.sy
mm = e
-/
protected theorem image_symm_eq_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) :
    e.symm '' s = e ⁻¹' s := by
  rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
/-
**ContinuousAffineEquiv.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neEquiv`。
形式化陈述：image_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e ⁻¹' s = s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `ContinuousAffineEquiv.surjective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ :
 Type u_3} {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGr
oup V₁] [inst_2 : _roo…
-/
theorem image_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e ⁻¹' s = s :=
  e.surjective.image_preimage s

@[simp]
/-
**ContinuousAffineEquiv.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neEquiv`。
形式化陈述：preimage_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e ⁻¹' e '' s = s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.preimage_image`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), f ⁻¹' f '' s = s
· 使用定理 `ContinuousAffineEquiv.injective`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : 
Type u_3} {V₁ : Type u_6} {V₂ : Type u_7} [inst : Ring k]   [inst_1 : AddCommGro
up V₁] [inst_2 : _roo…
-/
theorem preimage_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e ⁻¹' e '' s = s :=
  e.injective.preimage_image s
/-
**ContinuousAffineEquiv.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineEquiv`。
形式化陈述：symm_image_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e.symm '' e '' s = s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem symm_image_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e.symm '' e '' s = s :=
  e.toEquiv.symm_image_image s
/-
**ContinuousAffineEquiv.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineEquiv`。
形式化陈述：image_symm_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e.symm '' s = s
参数：e : P₁ ≃ᴬ[k] P₂；s : Set P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.symm_image_image`：symm_image_image (e : P₁ ≃ᴬ[k] P
₂) (s : Set P₁) : e.symm '' e '' s = s
-/
theorem image_symm_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp]
/-
**ContinuousAffineEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：refl_symm : (refl k P₁).symm = refl k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (refl k P₁).symm = refl k P₁ :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：symm_refl : (refl k P₁).symm = refl k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

/-- Composition of two `ContinuousAffineEquiv`alences, applied left to right. -/
@[trans]
/-
**ContinuousAffineEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEquiv`。
形式化陈述：trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : P₁ ≃ᴬ[k] P₃ where toAffineEqu
iv
参数：e : P₁ ≃ᴬ[k] P₂；e' : P₂ ≃ᴬ[k] P₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two `ContinuousAffineEquiv`alences, applied left to right.
-/
def trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : P₁ ≃ᴬ[k] P₃ where
  toAffineEquiv := e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := e'.continuous_toFun.comp (e.continuous_toFun)
  continuous_invFun := e.continuous_invFun.comp (e'.continuous_invFun)

@[simp]
/-
**ContinuousAffineEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：coe_trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : ⇑(e.trans e') = e' ∘ e
参数：e : P₁ ≃ᴬ[k] P₂；e' : P₂ ≃ᴬ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineE
quiv`。
形式化陈述：trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁) : e.trans e' p =
 e' (e p)
参数：e : P₁ ≃ᴬ[k] P₂；e' : P₂ ≃ᴬ[k] P₃；p : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl
/-
**ContinuousAffineEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineE
quiv`。
形式化陈述：trans_assoc (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄) : (e₁
.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃)
参数：e₁ : P₁ ≃ᴬ[k] P₂；e₂ : P₂ ≃ᴬ[k] P₃；e₃ : P₃ ≃ᴬ[k] P₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
-/
theorem trans_assoc (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ ↦ rfl

@[simp]
/-
**ContinuousAffineEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：trans_refl (e : P₁ ≃ᴬ[k] P₂) : e.trans (refl k P₂) = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
-/
theorem trans_refl (e : P₁ ≃ᴬ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ ↦ rfl

@[simp]
/-
**ContinuousAffineEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEq
uiv`。
形式化陈述：refl_trans (e : P₁ ≃ᴬ[k] P₂) : (refl k P₁).trans e = e
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
-/
theorem refl_trans (e : P₁ ≃ᴬ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ ↦ rfl

@[simp]
/-
**ContinuousAffineEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：self_trans_symm (e : P₁ ≃ᴬ[k] P₂) : e.trans e.symm = refl k P₁
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
· 使用定理 `ContinuousAffineEquiv.symm_apply_apply`：symm_apply_apply (e : P₁ ≃ᴬ[k] P
₂) (p : P₁) : e.symm (e p) = p
-/
theorem self_trans_symm (e : P₁ ≃ᴬ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
/-
**ContinuousAffineEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：symm_trans_self (e : P₁ ≃ᴬ[k] P₂) : e.symm.trans e = refl k P₂
参数：e : P₁ ≃ᴬ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.ext`：ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x =
 e' x) : e = e'
· 使用定理 `ContinuousAffineEquiv.apply_symm_apply`：apply_symm_apply (e : P₁ ≃ᴬ[k] P
₂) (p : P₂) : e (e.symm p) = p
-/
theorem symm_trans_self (e : P₁ ≃ᴬ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply
/-
**ContinuousAffineEquiv.trans_toContinuousAffineMap** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousAffineEquiv`。
形式化陈述：trans_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : (e.tran
s e').toContinuousAffineMap = e'.toContinuousAffineMap.comp e.toContinuousAffine
Map
参数：e : P₁ ≃ᴬ[k] P₂；e' : P₂ ≃ᴬ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) :
    (e.trans e').toContinuousAffineMap = e'.toContinuousAffineMap.comp e.toContinuousAffineMap :=
  rfl

end ReflSymmTrans

section

variable (k)
variable [TopologicalSpace V₁] [IsTopologicalAddTorsor P₁]

/-- The affine homeomorphism `V ≃ᴬ[k] P` given by `v ↦ v +ᵥ p`. This is `Equiv.vaddConst`
as a `ContinuousAffineEquiv`. -/
@[simps! apply symm_apply]
/-
**ContinuousAffineEquiv.vaddConst** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：vaddConst (p : P₁) : V₁ ≃ᴬ[k] P₁ where __
参数：p : P₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun

--- 原说明 ---
The affine homeomorphism `V ≃ᴬ[k] P` given by `v ↦ v +ᵥ p`. This is `Equiv.vaddC
onst`
as a `ContinuousAffineEquiv`.
-/
def vaddConst (p : P₁) : V₁ ≃ᴬ[k] P₁ where
  __ := AffineEquiv.vaddConst k p
  __ := Homeomorph.vaddConst p

@[simp]
/-
**ContinuousAffineEquiv.toAffineEquiv_vaddConst** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：toAffineEquiv_vaddConst {p : P₁} : vaddConst k p = AffineEquiv.vaddConst k
 p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAffineEquiv_vaddConst {p : P₁} : vaddConst k p = AffineEquiv.vaddConst k p := rfl

/-- The affine homeomorphism given by `p' ↦ p -ᵥ p'`. This is `Equiv.constVSub` as a
`ContinuousAffineEquiv`. -/
@[simps! apply symm_apply]
/-
**ContinuousAffineEquiv.constVSub** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：constVSub (p : P₁) : P₁ ≃ᴬ[k] V₁ where __
参数：p : P₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun

--- 原说明 ---
The affine homeomorphism given by `p' ↦ p -ᵥ p'`. This is `Equiv.constVSub` as a
`ContinuousAffineEquiv`.
-/
def constVSub (p : P₁) : P₁ ≃ᴬ[k] V₁ where
  __ := AffineEquiv.constVSub k p
  __ := Homeomorph.constVSub p

@[simp]
/-
**ContinuousAffineEquiv.toAffineEquiv_constVSub** 是 Mathlib 中的一个引理，位于命名空间 `Conti
nuousAffineEquiv`。
形式化陈述：toAffineEquiv_constVSub {p : P₁} : constVSub k p = AffineEquiv.constVSub k
 p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAffineEquiv_constVSub {p : P₁} : constVSub k p = AffineEquiv.constVSub k p := rfl

/-- The affine homeomorphism given by reflection about the point `x`.
This is `Equiv.pointReflection` as a `ContinuousAffineEquiv`. -/
/-
**ContinuousAffineEquiv.pointReflection** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：pointReflection (x : P₁) : P₁ ≃ᴬ[k] P₁
参数：x : P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine homeomorphism given by reflection about the point `x`.
This is `Equiv.pointReflection` as a `ContinuousAffineEquiv`.
-/
def pointReflection (x : P₁) : P₁ ≃ᴬ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)

@[simp]
/-
**ContinuousAffineEquiv.coe_pointReflection** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sAffineEquiv`。
形式化陈述：coe_pointReflection (x : P₁) : (pointReflection k x : P₁ -> P₁) = Equiv.po
intReflection x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_pointReflection (x : P₁) :
    (pointReflection k x : P₁ → P₁) = Equiv.pointReflection x := rfl
/-
**ContinuousAffineEquiv.pointReflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousAffineEquiv`。
形式化陈述：pointReflection_apply (x y : P₁) : pointReflection k x y = (x -ᵥ y) +ᵥ x
参数：x y : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointReflection_apply (x y : P₁) : pointReflection k x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.pointReflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAffineEquiv`。
形式化陈述：pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflecti
on k x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineEquiv.toAffineEquiv_injective`：toAffineEquiv_injective :
 Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) -> P₁ ≃ᵃ[k] P₂)
· 使用定理 `AffineEquiv.pointReflection_symm`：pointReflection_symm (x : P₁) : (point
Reflection k x).symm = pointReflection k x
-/
theorem pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
  toAffineEquiv_injective <| AffineEquiv.pointReflection_symm k x

@[simp]
/-
**ContinuousAffineEquiv.toAffineEquiv_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousAffineEquiv`。
形式化陈述：toAffineEquiv_pointReflection (x : P₁) : (pointReflection k x).toAffineEqu
iv = AffineEquiv.pointReflection k x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineEquiv_pointReflection (x : P₁) :
    (pointReflection k x).toAffineEquiv = AffineEquiv.pointReflection k x :=
  rfl
/-
**ContinuousAffineEquiv.pointReflection_self** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usAffineEquiv`。
形式化陈述：pointReflection_self (x : P₁) : pointReflection k x x = x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem pointReflection_self (x : P₁) : pointReflection k x x = x :=
  vsub_vadd _ _
/-
**ContinuousAffineEquiv.pointReflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAffineEquiv`。
形式化陈述：pointReflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁
 -> P₁)
参数：x : P₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.pointReflection_involutive`：pointReflection_involutive (x : P) : I
nvolutive (pointReflection x : P -> P)
-/
theorem pointReflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁ → P₁) :=
  Equiv.pointReflection_involutive x

end

section

variable {E F : Type*} [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [AddCommGroup F] [Module k F] [TopologicalSpace F]

/-- Reinterpret a continuous linear equivalence between modules
as a continuous affine equivalence. -/
/-
**ContinuousAffineEquiv._root_.ContinuousLinearEquiv.toContinuousAffineEquiv** 是
 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a continuous linear equivalence between modules
as a continuous affine equivalence.
-/
def _root_.ContinuousLinearEquiv.toContinuousAffineEquiv (L : E ≃L[k] F) : E ≃ᴬ[k] F where
  toAffineEquiv := L.toAffineEquiv
  continuous_toFun := L.continuous_toFun
  continuous_invFun := L.continuous_invFun

@[simp]
/-
**ContinuousAffineEquiv._root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv
** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv (e : E ≃L[k] F) :
    ⇑e.toContinuousAffineEquiv = e :=
  rfl
/-
**ContinuousAffineEquiv._root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toC
ontinuousAffineMap** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap (L : E ≃L[k] F) :
    L.toContinuousAffineEquiv.toContinuousAffineMap =
      L.toContinuousLinearMap.toContinuousAffineMap :=
  rfl

variable (k P₁) in
/-- The map `p ↦ v +ᵥ p` as a continuous affine automorphism of an affine space
  on which addition is continuous. -/
/-
**ContinuousAffineEquiv.constVAdd** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：constVAdd [ContinuousConstVAdd V₁ P₁] (v : V₁) : P₁ ≃ᴬ[k] P₁ where toAffin
eEquiv
参数：v : V₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `p ↦ v +ᵥ p` as a continuous affine automorphism of an affine space
  on which addition is continuous.
-/
def constVAdd [ContinuousConstVAdd V₁ P₁] (v : V₁) : P₁ ≃ᴬ[k] P₁ where
  toAffineEquiv := AffineEquiv.constVAdd k P₁ v
  continuous_toFun := continuous_const_vadd v
  continuous_invFun := continuous_const_vadd (-v)
/-
**ContinuousAffineEquiv.constVAdd_coe** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：constVAdd_coe [ContinuousConstVAdd V₁ P₁] (v : V₁) : (constVAdd k P₁ v).to
AffineEquiv = .constVAdd k P₁ v
参数：v : V₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma constVAdd_coe [ContinuousConstVAdd V₁ P₁] (v : V₁) :
    (constVAdd k P₁ v).toAffineEquiv = .constVAdd k P₁ v := rfl

end

section

variable (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₃ ≃ᴬ[k] P₄)

/-- Product of two continuous affine equivalences. The map comes from `Equiv.prodCongr` -/
@[simps toAffineEquiv]
/-
**ContinuousAffineEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：prodCongr : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two continuous affine equivalences. The map comes from `Equiv.prodCon
gr`
-/
def prodCongr : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where
  __ := AffineEquiv.prodCongr e₁ e₂
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

@[simp]
/-
**ContinuousAffineEquiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffi
neEquiv`。
形式化陈述：prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.prodCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAff
ineEquiv`。
形式化陈述：prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
参数：p : P₁ × P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp]
/-
**ContinuousAffineEquiv.prodCongr_toContinuousAffineMap** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAffineEquiv`。
形式化陈述：prodCongr_toContinuousAffineMap : (e₁.prodCongr e₂).toContinuousAffineMap 
= e₁.toContinuousAffineMap.prodMap e₂.toContinuousAffineMap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_toContinuousAffineMap : (e₁.prodCongr e₂).toContinuousAffineMap =
    e₁.toContinuousAffineMap.prodMap e₂.toContinuousAffineMap :=
  rfl

end

section

variable (k P₁ P₂ P₃)

/-- Product of affine spaces is commutative up to continuous affine isomorphism. -/
@[simps! apply toAffineEquiv]
/-
**ContinuousAffineEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqui
v`。
形式化陈述：prodComm : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)

--- 原说明 ---
Product of affine spaces is commutative up to continuous affine isomorphism.
-/
def prodComm : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where
  __ := AffineEquiv.prodComm k P₁ P₂
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

@[simp]
/-
**ContinuousAffineEquiv.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffin
eEquiv`。
形式化陈述：prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Product of affine spaces is associative up to continuous affine isomorphism. -/
@[simps! apply toAffineEquiv]
/-
**ContinuousAffineEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAffineEqu
iv`。
形式化陈述：prodAssoc : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of affine spaces is associative up to continuous affine isomorphism.
-/
def prodAssoc : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where
  __ := AffineEquiv.prodAssoc k P₁ P₂ P₃
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

end

end ContinuousAffineEquiv

