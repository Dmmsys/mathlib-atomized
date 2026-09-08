/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Affine equivalences

In this file we define `AffineEquiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂`, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `AffineEquiv.refl k P`: the identity map as an `AffineEquiv`;

* `e.symm`: the inverse map of an `AffineEquiv` as an `AffineEquiv`;

* `e.trans e'`: composition of two `AffineEquiv`s; note that the order follows `mathlib`'s
  `CategoryTheory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

We equip `AffineEquiv k P P` with a `Group` structure with multiplication corresponding to
composition in `AffineEquiv.group`.

## Tags

affine space, affine equivalence
-/

@[expose] public section

open Function Set

open Affine

/-- An affine equivalence, denoted `P₁ ≃ᵃ[k] P₂`, is an equivalence between affine spaces
such that both forward and inverse maps are affine.

We define it using an `Equiv` for the map and a `LinearEquiv` for the linear part in order
to allow affine equivalences with good definitional equalities. -/
/-
**AffineEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) →   (P₁ : Type u_2) →     (P₂ : Type u_3) →       {V₁ : Typ
e u_4} →         {V₂ : Type u_5} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : AddCommGroup V₂] →              
   [_root_.Module k V₁] →                   [_root_.Module k V₂] → [AddTorsor V₁
 P₁] → [AddTorsor V₂ P₂] → Type (max (max (max u_2 u_3) u_4) u_5)
参数：max (max u_2 u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine equivalence, denoted `P₁ ≃ᵃ[k] P₂`, is an equivalence between affine s
paces
such that both forward and inverse maps are affine.

We define it using an `Equiv` for the map and a `LinearEquiv` for the linear par
t in order
to allow affine equivalences with good definitional equalities.
-/
structure AffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  /-- The underlying linear equiv of modules. -/
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : ∀ (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p

@[inherit_doc]
notation:25 P₁ " ≃ᵃ[" k:25 "] " P₂:0 => AffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

namespace AffineEquiv

/-- Reinterpret an `AffineEquiv` as an `AffineMap`. -/
@[coe]
/-
**AffineEquiv.toAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ ->ᵃ[k] P₂
参数：e : P₁ ≃ᵃ[k] P₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.map_vadd'`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…

--- 原说明 ---
Reinterpret an `AffineEquiv` as an `AffineMap`.
-/
def toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ →ᵃ[k] P₂ :=
  { e with }

@[simp]
/-
**AffineEquiv.toAffineMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) : toAffineMap (mk f f'
 h) = ⟨f, f', h⟩
参数：f : P₁ ≃ P₂；f' : V₁ ≃ₗ[k] V₂；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
    toAffineMap (mk f f' h) = ⟨f, f', h⟩ :=
  rfl

@[simp]
/-
**AffineEquiv.linear_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：linear_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : e.toAffineMap.linear = e.linear
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : e.toAffineMap.linear = e.linear :=
  rfl
/-
**AffineEquiv.toAffineMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toAffineMap_injective : Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) -> P₁ ->ᵃ[k
] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.mk.injEq`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2
 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst_
2 : _roo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineEquiv.mk.congr_simp`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u
_3} {V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V₁]
 [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toAffineMap_injective : Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) → P₁ →ᵃ[k] P₂) := by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp_all

@[simp]
/-
**AffineEquiv.toAffineMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e 
= e'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineEquiv.toAffineMap_injective`：toAffineMap_injective : Injective (to
AffineMap : (P₁ ≃ᵃ[k] P₂) -> P₁ ->ᵃ[k] P₂)
-/
theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  toAffineMap_injective.eq_iff
/-
**AffineEquiv.equivLike** 是 Mathlib 中的一个实例，位于命名空间 `AffineEquiv`。
形式化陈述：equivLike : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equivLike : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineMap_injective (DFunLike.coe_injective h)
/-
**AffineEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂) :=
  ⟨AffineEquiv.toEquiv⟩

@[simp]
/-
**AffineEquiv.map_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ 
e p
参数：e : P₁ ≃ᵃ[k] P₂；p : P₁；v : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.map_vadd'`：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} 
{V₁ : Type u_4} {V₂ : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [in
st_2 : AddC…
-/
theorem map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
  e.map_vadd' p v

@[simp]
/-
**AffineEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv = e
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv = e :=
  rfl
/-
**AffineEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `AffineEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (P₁ ≃ᵃ[k] P₂) (P₁ →ᵃ[k] P₂) :=
  ⟨toAffineMap⟩

@[simp]
/-
**AffineEquiv.coe_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : (e.toAffineMap : P₁ -> P₂) = (e : P₁ -
> P₂)
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : (e.toAffineMap : P₁ → P₂) = (e : P₁ → P₂) :=
  rfl

@[norm_cast, simp]
/-
**AffineEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ ->ᵃ[k] P₂) : P₁ -> P₂) = e
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ →ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl

@[simp]
/-
**AffineEquiv.coe_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_linear (e : P₁ ≃ᵃ[k] P₂) : (e : P₁ ->ᵃ[k] P₂).linear = e.linear
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linear (e : P₁ ≃ᵃ[k] P₂) : (e : P₁ →ᵃ[k] P₂).linear = e.linear :=
  rfl

@[ext]
/-
**AffineEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {e e' : P₁ ≃ᵃ[k] P₂} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h
/-
**AffineEquiv.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coeFn_injective : @Injective (P₁ ≃ᵃ[k] P₂) (P₁ -> P₂) (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Injective (P₁ ≃ᵃ[k] P₂) (P₁ → P₂) (⇑) :=
  DFunLike.coe_injective

@[norm_cast]
/-
**AffineEquiv.coeFn_inj** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coeFn_inj {e e' : P₁ ≃ᵃ[k] P₂} : (e : P₁ -> P₂) = e' ↔ e = e'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coeFn_inj {e e' : P₁ ≃ᵃ[k] P₂} : (e : P₁ → P₂) = e' ↔ e = e' := by simp
/-
**AffineEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toEquiv_injective : Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.ext_iff`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g ↔ ∀ (x :
 α), f x = g x
-/
theorem toEquiv_injective : Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) → P₁ ≃ P₂) := fun _ _ H =>
  ext <| Equiv.ext_iff.1 H

@[simp]
/-
**AffineEquiv.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineEquiv.toEquiv_injective`：toEquiv_injective : Injective (toEquiv : 
(P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂)
-/
theorem toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' :=
  toEquiv_injective.eq_iff

@[simp]
/-
**AffineEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_mk (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h) : ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) 
: P₁ -> P₂) = e
参数：e : P₁ ≃ P₂；e' : V₁ ≃ₗ[k] V₂；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h) : ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ → P₂) = e :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Construct an affine equivalence by verifying the relation between the map and its linear part at
one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear equivalence
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`. -/
/-
**AffineEquiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : forall p' : P₁, e p' =
 e' (p' -ᵥ p) +ᵥ e p) : P₁ ≃ᵃ[k] P₂ where toFun
参数：e : P₁ -> P₂；e' : V₁ ≃ₗ[k] V₂；p : P₁；h : forall p' : P₁, e p' = e' (p' -ᵥ p) 
+ᵥ e p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine equivalence by verifying the relation between the map and it
s linear part at
one base point. Namely, this function takes a map `e : P₁ → P₂`, a linear equiva
lence
`e' : V₁ ≃ₗ[k] V₂`, and a point `p` such that for any other point `p'` we have
`e p' = e' (p' -ᵥ p) +ᵥ e p`.
-/
def mk' (e : P₁ → P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : ∀ p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃ[k] P₂ where
  toFun := e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv p' := by simp [h p', vadd_vsub, vsub_vadd]
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), vadd_vsub, vsub_vadd]
  linear := e'
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), vadd_vsub_assoc, vadd_vadd]

@[simp]
/-
**AffineEquiv.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e
参数：e : P₁ ≃ P₂；e' : V₁ ≃ₗ[k] V₂；p h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl

@[simp]
/-
**AffineEquiv.linear_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : (mk' e e' p h).linear 
= e'
参数：e : P₁ ≃ P₂；e' : V₁ ≃ₗ[k] V₂；p h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : (mk' e e' p h).linear = e' :=
  rfl

/-- Inverse of an affine equivalence as an affine equivalence. -/
@[symm]
/-
**AffineEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where toEquiv
参数：e : P₁ ≃ᵃ[k] P₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Inverse of an affine equivalence as an affine equivalence.
-/
def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
  toEquiv := e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
    e.toEquiv.symm.eq_symm_apply.1 <| by
      rw [Equiv.symm_symm, e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v),
        LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp]
/-
**AffineEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toEquiv_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/-
**AffineEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_symm_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv.symm = e.symm
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv.symm = e.symm :=
  rfl

@[simp]
/-
**AffineEquiv.linear_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：linear_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.linear = e.linear.symm
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.linear = e.linear.symm :=
  rfl

/-- See Note [custom simps projection] -/
/-
**AffineEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv.Simps`。
形式化陈述：{k : Type u_1} →   {P₁ : Type u_2} →     {P₂ : Type u_3} →       {V₁ : Typ
e u_6} →         {V₂ : Type u_7} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : AddCommGroup V₂] →              
   [inst_3 : _root_.Module k V₁] →                   [inst_4 : _root_.Module k V
₂] →                     [inst_5 : AddTorsor V₁ P₁] → [inst_6 : AddTorsor V₂ P₂]
 → (P₁ ≃ᵃ[k] P₂) → P₁ → P₂
参数：P₁ ≃ᵃ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (e : P₁ ≃ᵃ[k] P₂) : P₁ → P₂ :=
  e

/-- See Note [custom simps projection] -/
/-
**AffineEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv.Simps`。
形式化陈述：{k : Type u_1} →   {P₁ : Type u_2} →     {P₂ : Type u_3} →       {V₁ : Typ
e u_6} →         {V₂ : Type u_7} →           [inst : Ring k] →             [inst
_1 : AddCommGroup V₁] →               [inst_2 : AddCommGroup V₂] →              
   [inst_3 : _root_.Module k V₁] →                   [inst_4 : _root_.Module k V
₂] →                     [inst_5 : AddTorsor V₁ P₁] → [inst_6 : AddTorsor V₂ P₂]
 → (P₁ ≃ᵃ[k] P₂) → P₂ → P₁
参数：P₁ ≃ᵃ[k] P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : P₁ ≃ᵃ[k] P₂) : P₂ → P₁ :=
  e.symm

initialize_simps_projections AffineEquiv (toEquiv_toFun → apply, toEquiv_invFun → symm_apply,
  linear → linear, as_prefix linear, -toEquiv)
/-
**AffineEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : AddCommGroup V₂] [
inst_3 : _root_.Module k V₁] [inst_4 : _root_.Module k V₂]   [inst_5 : AddTorsor
 V₁ P₁] [inst_6 : AddTorsor V₂ P₂] (e : P₁ ≃ᵃ[k] P₂), Function.Bijective ⇑e
参数：e : P₁ ≃ᵃ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : P₁ ≃ᵃ[k] P₂) : Bijective e :=
  e.toEquiv.bijective
/-
**AffineEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : AddCommGroup V₂] [
inst_3 : _root_.Module k V₁] [inst_4 : _root_.Module k V₂]   [inst_5 : AddTorsor
 V₁ P₁] [inst_6 : AddTorsor V₂ P₂] (e : P₁ ≃ᵃ[k] P₂), Function.Surjective ⇑e
参数：e : P₁ ≃ᵃ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : P₁ ≃ᵃ[k] P₂) : Surjective e :=
  e.toEquiv.surjective
/-
**AffineEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : AddCommGroup V₂] [
inst_3 : _root_.Module k V₁] [inst_4 : _root_.Module k V₂]   [inst_5 : AddTorsor
 V₁ P₁] [inst_6 : AddTorsor V₂ P₂] (e : P₁ ≃ᵃ[k] P₂), Function.Injective ⇑e
参数：e : P₁ ≃ᵃ[k] P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : P₁ ≃ᵃ[k] P₂) : Injective e :=
  e.toEquiv.injective

/-- Bijective affine maps are affine isomorphisms. -/
@[simps! linear apply]
/-
**AffineEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：ofBijective {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ) : P₁ ≃ᵃ[k] P₂
参数：hφ : Function.Bijective φ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p

--- 原说明 ---
Bijective affine maps are affine isomorphisms.
-/
noncomputable def ofBijective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective φ) : P₁ ≃ᵃ[k] P₂ :=
  { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }
/-
**AffineEquiv.ofBijective.symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv.ofBijec
tive`。
形式化陈述：∀ {k : Type u_1} {P₁ : Type u_2} {P₂ : Type u_3} {V₁ : Type u_6} {V₂ : Typ
e u_7} [inst : Ring k]   [inst_1 : AddCommGroup V₁] [inst_2 : AddCommGroup V₂] [
inst_3 : _root_.Module k V₁] [inst_4 : _root_.Module k V₂]   [inst_5 : AddTorsor
 V₁ P₁] [inst_6 : AddTorsor V₂ P₂] {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective ⇑φ
),   (AffineEquiv.ofBijective hφ).symm.toEquiv = (Equiv.ofBijective (⇑φ) hφ).sym
m
参数：hφ : Function.Bijective ⇑φ；AffineEquiv.ofBijective hφ；Equiv.ofBijective (⇑φ) 
hφ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective.symm_eq {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Bijective φ) :
    (ofBijective hφ).symm.toEquiv = (Equiv.ofBijective _ hφ).symm :=
  rfl
/-
**AffineEquiv.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ := by simp

@[simp]
/-
**AffineEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p
参数：e : P₁ ≃ᵃ[k] P₂；p : P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
/-
**AffineEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p
参数：e : P₁ ≃ᵃ[k] P₂；p : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p
/-
**AffineEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：symm_apply_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e.symm p₁ = p₂ ↔ p₁ = e p₂
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e.symm p₁ = p₂ ↔ p₁ = e p₂ :=
  e.toEquiv.symm_apply_eq
/-
**AffineEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ = e.symm p₁ ↔ e p₂ = p₁
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ = e.symm p₁ ↔ e p₂ = p₁ :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**AffineEquiv.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`
。
形式化陈述：apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.
symm p₂
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AffineEquiv.eq_symm_apply`：eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ 
= e.symm p₁ ↔ e p₂ = p₁
-/
theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.eq_symm_apply.symm
/-
**AffineEquiv.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ := by simp

@[simp]
/-
**AffineEquiv.image_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s
参数：f : P₁ ≃ᵃ[k] P₂；s : Set P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage_symm _

@[simp]
/-
**AffineEquiv.preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s
参数：f : P₁ ≃ᵃ[k] P₂；s : Set P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.image_symm`：image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.sy
mm '' s = f ⁻¹' s
-/
theorem preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm

variable (k P₁)

/-- Identity map as an `AffineEquiv`. -/
@[refl]
/-
**AffineEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：refl : P₁ ≃ᵃ[k] P₁ where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Identity map as an `AffineEquiv`.
-/
def refl : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]
/-
**AffineEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_refl : ⇑(refl k P₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
/-
**AffineEquiv.coe_refl_to_affineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_refl_to_affineMap : ↑(refl k P₁) = AffineMap.id k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl_to_affineMap : ↑(refl k P₁) = AffineMap.id k P₁ :=
  rfl

@[simp]
/-
**AffineEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：refl_apply (x : P₁) : refl k P₁ x = x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
/-
**AffineEquiv.toEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

@[simp]
/-
**AffineEquiv.linear_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：linear_refl : (refl k P₁).linear = LinearEquiv.refl k V₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_refl : (refl k P₁).linear = LinearEquiv.refl k V₁ :=
  rfl

@[simp]
/-
**AffineEquiv.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：symm_refl : (refl k P₁).symm = refl k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

variable {k P₁}

/-- Composition of two `AffineEquiv`alences, applied left to right. -/
@[trans]
/-
**AffineEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where toEquiv
参数：e : P₁ ≃ᵃ[k] P₂；e' : P₂ ≃ᵃ[k] P₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of two `AffineEquiv`alences, applied left to right.
-/
def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
  toEquiv := e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    simp only [LinearEquiv.trans_apply, coe_toEquiv, (· ∘ ·), Equiv.coe_trans, map_vadd]

@[simp]
/-
**AffineEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e
参数：e : P₁ ≃ᵃ[k] P₂；e' : P₂ ≃ᵃ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/-
**AffineEquiv.coe_trans_to_affineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_trans_to_affineMap (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : (e.trans e' 
: P₁ ->ᵃ[k] P₃) = (e' : P₂ ->ᵃ[k] P₃).comp e
参数：e : P₁ ≃ᵃ[k] P₂；e' : P₂ ≃ᵃ[k] P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans_to_affineMap (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) :
    (e.trans e' : P₁ →ᵃ[k] P₃) = (e' : P₂ →ᵃ[k] P₃).comp e :=
  rfl

@[simp]
/-
**AffineEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p =
 e' (e p)
参数：e : P₁ ≃ᵃ[k] P₂；e' : P₂ ≃ᵃ[k] P₃；p : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl
/-
**AffineEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) : (e₁
.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃)
参数：e₁ : P₁ ≃ᵃ[k] P₂；e₂ : P₂ ≃ᵃ[k] P₃；e₃ : P₃ ≃ᵃ[k] P₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
-/
theorem trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ => rfl

@[simp]
/-
**AffineEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
-/
theorem trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ => rfl

@[simp]
/-
**AffineEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
-/
theorem refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ => rfl

@[simp]
/-
**AffineEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `AffineEquiv.symm_apply_apply`：symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁
) : e.symm (e p) = p
-/
theorem self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
/-
**AffineEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂
参数：e : P₁ ≃ᵃ[k] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `AffineEquiv.apply_symm_apply`：apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂
) : e (e.symm p) = p
-/
theorem symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineEquiv.apply_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k) : e (AffineMap.lineMap 
a b c) = AffineMap.lineMap (e a) (e b) c
参数：e : P₁ ≃ᵃ[k] P₂；a b : P₁；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k) :
    e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c :=
  e.toAffineMap.apply_lineMap a b c
/-
**AffineEquiv.group** 是 Mathlib 中的一个实例，位于命名空间 `AffineEquiv`。
形式化陈述：group : Group (P₁ ≃ᵃ[k] P₁) where one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.trans_assoc`：trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P
₃) (e₃ : P₃ ≃ᵃ[k] P₄) : (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃)
· 使用定理 `AffineEquiv.trans_refl`：trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P
₂) = e
· 使用定理 `AffineEquiv.refl_trans`：refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans
 e = e
· 使用定理 `AffineEquiv.self_trans_symm`：self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans
 e.symm = refl k P₁
-/
instance group : Group (P₁ ≃ᵃ[k] P₁) where
  one := refl k P₁
  mul e e' := e'.trans e
  inv := symm
  mul_assoc _ _ _ := trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
/-
**AffineEquiv.one_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ :=
  rfl

@[simp]
/-
**AffineEquiv.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id :=
  rfl
/-
**AffineEquiv.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e
参数：e e' : P₁ ≃ᵃ[k] P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e :=
  rfl

@[simp]
/-
**AffineEquiv.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e'
参数：e e' : P₁ ≃ᵃ[k] P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e' :=
  rfl
/-
**AffineEquiv.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm
参数：e : P₁ ≃ᵃ[k] P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
  rfl

/-- `AffineEquiv.linear` on automorphisms is a `MonoidHom`. -/
@[simps]
/-
**AffineEquiv.linearHom** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：linearHom : (P₁ ≃ᵃ[k] P₁) ->* V₁ ≃ₗ[k] V₁ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AffineEquiv.linear` on automorphisms is a `MonoidHom`.
-/
def linearHom : (P₁ ≃ᵃ[k] P₁) →* V₁ ≃ₗ[k] V₁ where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The group of `AffineEquiv`s are equivalent to the group of units of `AffineMap`.

This is the affine version of `LinearMap.GeneralLinearGroup.generalLinearEquiv`. -/
@[simps -isSimp]
/-
**AffineEquiv.equivUnitsAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ ->ᵃ[k] P₁)ˣ where toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of `AffineEquiv`s are equivalent to the group of units of `AffineMap`.

This is the affine version of `LinearMap.GeneralLinearGroup.generalLinearEquiv`.
-/
def equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ →ᵃ[k] P₁)ˣ where
  toFun e :=
    { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ →ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ →ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := AffineMap.congr_fun u.mul_inv
      linear :=
        LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ <| Units.map AffineMap.linearHom u
      map_vadd' := fun _ _ => (u : P₁ →ᵃ[k] P₁).map_vadd _ _ }
  map_mul' _ _ := rfl

section

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

/-- Product of two affine equivalences. The map comes from `Equiv.prodCongr` -/
@[simps linear]
/-
**AffineEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：prodCongr : P₁ × P₃ ≃ᵃ[k] P₂ × P₄ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of two affine equivalences. The map comes from `Equiv.prodCongr`
-/
def prodCongr : P₁ × P₃ ≃ᵃ[k] P₂ × P₄ where
  __ := Equiv.prodCongr e₁ e₂
  linear := e₁.linear.prodCongr e₂.linear
  map_vadd' := by simp

@[simp]
/-
**AffineEquiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
/-
**AffineEquiv.prodCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
参数：p : P₁ × P₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp, norm_cast]
/-
**AffineEquiv.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_prodCongr : (e₁.prodCongr e₂ : P₁ × P₃ ->ᵃ[k] P₂ × P₄) = (e₁ : P₁ ->ᵃ[
k] P₂).prodMap (e₂ : P₃ ->ᵃ[k] P₄)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr :
    (e₁.prodCongr e₂ : P₁ × P₃ →ᵃ[k] P₂ × P₄) = (e₁ : P₁ →ᵃ[k] P₂).prodMap (e₂ : P₃ →ᵃ[k] P₄) :=
  rfl

end

section

variable (k P₁ P₂ P₃)

/-- Product of affine spaces is commutative up to affine isomorphism. -/
@[simps! apply linear]
/-
**AffineEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：prodComm : P₁ × P₂ ≃ᵃ[k] P₂ × P₁ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of affine spaces is commutative up to affine isomorphism.
-/
def prodComm : P₁ × P₂ ≃ᵃ[k] P₂ × P₁ where
  __ := Equiv.prodComm P₁ P₂
  linear := LinearEquiv.prodComm k V₁ V₂
  map_vadd' := by simp

@[simp]
/-
**AffineEquiv.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁ :=
  rfl

/-- Product of affine spaces is associative up to affine isomorphism. -/
@[simps! apply symm_apply linear]
/-
**AffineEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：prodAssoc : (P₁ × P₂) × P₃ ≃ᵃ[k] P₁ × (P₂ × P₃) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of affine spaces is associative up to affine isomorphism.
-/
def prodAssoc : (P₁ × P₂) × P₃ ≃ᵃ[k] P₁ × (P₂ × P₃) where
  __ := Equiv.prodAssoc P₁ P₂ P₃
  linear := LinearEquiv.prodAssoc k V₁ V₂ V₃
  map_vadd' := by simp

end

variable (k)

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
@[simps! linear apply symm_apply]
/-
**AffineEquiv.vaddConst** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where toEquiv
参数：b : P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine
 space `P` with
tangent space `V`.
-/
def vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
@[simps! linear apply symm_apply]
/-
**AffineEquiv.constVSub** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：constVSub (p : P₁) : P₁ ≃ᵃ[k] V₁ where toEquiv
参数：p : P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`p' ↦ p -ᵥ p'` as an equivalence.
-/
def constVSub (p : P₁) : P₁ ≃ᵃ[k] V₁ where
  toEquiv := Equiv.constVSub p
  linear := LinearEquiv.neg k
  map_vadd' p' v := by simp [vsub_vadd_eq_vsub_sub, neg_add_eq_sub]

@[simp]
/-
**AffineEquiv.coe_constVSub** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_constVSub (p : P₁) : ⇑(constVSub k p) = (p -ᵥ ·)
参数：p : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_constVSub (p : P₁) : ⇑(constVSub k p) = (p -ᵥ ·) :=
  rfl

@[simp]
/-
**AffineEquiv.coe_constVSub_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_constVSub_symm (p : P₁) : ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ 
p
参数：p : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_constVSub_symm (p : P₁) : ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ p :=
  rfl

variable (P₁)

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space.

Note that there is no need for an `AffineMap.constVAdd` as it is always an equivalence.
This is roughly to `DistribMulAction.toLinearEquiv` as `+ᵥ` is to `•`. -/
@[simps! apply linear]
/-
**AffineEquiv.constVAdd** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd (v : V₁) : P₁ ≃ᵃ[k] P₁ where toEquiv
参数：v : V₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space.

Note that there is no need for an `AffineMap.constVAdd` as it is always an equiv
alence.
This is roughly to `DistribMulAction.toLinearEquiv` as `+ᵥ` is to `•`.
-/
def constVAdd (v : V₁) : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _

@[simp]
/-
**AffineEquiv.constVAdd_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd_zero : constVAdd k P₁ 0 = AffineEquiv.refl _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
-/
theorem constVAdd_zero : constVAdd k P₁ 0 = AffineEquiv.refl _ _ :=
  ext <| zero_vadd _

@[simp]
/-
**AffineEquiv.constVAdd_add** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd_add (v w : V₁) : constVAdd k P₁ (v + w) = (constVAdd k P₁ w).tra
ns (constVAdd k P₁ v)
参数：v w : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `AddSemigroupAction.add_vadd`：∀ {G : Type u_9} {P : Type u_10} {inst : Ad
dSemigroup G} [self : AddSemigroupAction G P] (g₁ g₂ : G) (p : P),   (g₁ + g₂) +
ᵥ p = g₁ +ᵥ g₂ +ᵥ…
-/
theorem constVAdd_add (v w : V₁) :
    constVAdd k P₁ (v + w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v) :=
  ext <| add_vadd _ _

@[simp]
/-
**AffineEquiv.constVAdd_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd_symm (v : V₁) : (constVAdd k P₁ v).symm = constVAdd k P₁ (-v)
参数：v : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
-/
theorem constVAdd_symm (v : V₁) : (constVAdd k P₁ v).symm = constVAdd k P₁ (-v) :=
  ext fun _ => rfl

/-- A more bundled version of `AffineEquiv.constVAdd`. -/
@[simps]
/-
**AffineEquiv.constVAddHom** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：constVAddHom : Multiplicative V₁ ->* P₁ ≃ᵃ[k] P₁ where toFun v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.constVAdd_zero`：constVAdd_zero : constVAdd k P₁ 0 = AffineEq
uiv.refl _ _
· 使用定理 `AffineEquiv.constVAdd_add`：constVAdd_add (v w : V₁) : constVAdd k P₁ (v 
+ w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v)

--- 原说明 ---
A more bundled version of `AffineEquiv.constVAdd`.
-/
def constVAddHom : Multiplicative V₁ →* P₁ ≃ᵃ[k] P₁ where
  toFun v := constVAdd k P₁ v.toAdd
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁
/-
**AffineEquiv.constVAdd_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd_nsmul (n : Nat) (v : V₁) : constVAdd k P₁ (n • v) = constVAdd k 
P₁ v ^ n
参数：n : Nat；v : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem constVAdd_nsmul (n : ℕ) (v : V₁) : constVAdd k P₁ (n • v) = constVAdd k P₁ v ^ n :=
  (constVAddHom k P₁).map_pow _ _
/-
**AffineEquiv.constVAdd_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：constVAdd_zsmul (z : Int) (v : V₁) : constVAdd k P₁ (z • v) = constVAdd k 
P₁ v ^ z
参数：z : Int；v : V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
theorem constVAdd_zsmul (z : ℤ) (v : V₁) : constVAdd k P₁ (z • v) = constVAdd k P₁ v ^ z :=
  (constVAddHom k P₁).map_zpow _ _

section Homothety

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AffineSpace V P]

/-- Fixing a point in affine space, homothety about this point gives a group homomorphism from (the
centre of) the units of the scalars into the group of affine equivalences. -/
/-
**AffineEquiv.homothetyUnitsMulHom** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：homothetyUnitsMulHom (p : P) : Rˣ ->* P ≃ᵃ[R] P
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fixing a point in affine space, homothety about this point gives a group homomor
phism from (the
centre of) the units of the scalars into the group of affine equivalences.
-/
def homothetyUnitsMulHom (p : P) : Rˣ →* P ≃ᵃ[R] P :=
  equivUnitsAffineMap.symm.toMonoidHom.comp <| Units.map (AffineMap.homothetyHom p)

@[simp]
/-
**AffineEquiv.coe_homothetyUnitsMulHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEq
uiv`。
形式化陈述：coe_homothetyUnitsMulHom_apply (p : P) (t : Rˣ) : (homothetyUnitsMulHom p 
t : P -> P) = AffineMap.homothety p (t : R)
参数：p : P；t : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_homothetyUnitsMulHom_apply (p : P) (t : Rˣ) :
    (homothetyUnitsMulHom p t : P → P) = AffineMap.homothety p (t : R) :=
  rfl

@[simp]
/-
**AffineEquiv.coe_homothetyUnitsMulHom_apply_symm** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineEquiv`。
形式化陈述：coe_homothetyUnitsMulHom_apply_symm (p : P) (t : Rˣ) : ((homothetyUnitsMul
Hom p t).symm : P -> P) = AffineMap.homothety p (↑t⁻¹ : R)
参数：p : P；t : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_homothetyUnitsMulHom_apply_symm (p : P) (t : Rˣ) :
    ((homothetyUnitsMulHom p t).symm : P → P) = AffineMap.homothety p (↑t⁻¹ : R) :=
  rfl

@[simp]
/-
**AffineEquiv.coe_homothetyUnitsMulHom_eq_homothetyHom_coe** 是 Mathlib 中的一个定理，位于
命名空间 `AffineEquiv`。
形式化陈述：coe_homothetyUnitsMulHom_eq_homothetyHom_coe (p : P) : ((↑) : (P ≃ᵃ[R] P) 
-> P ->ᵃ[R] P) ∘ homothetyUnitsMulHom p = AffineMap.homothetyHom p ∘ ((↑) : Rˣ -
> R)
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem coe_homothetyUnitsMulHom_eq_homothetyHom_coe (p : P) :
    ((↑) : (P ≃ᵃ[R] P) → P →ᵃ[R] P) ∘ homothetyUnitsMulHom p =
      AffineMap.homothetyHom p ∘ ((↑) : Rˣ → R) :=
  funext fun _ => rfl

end Homothety

variable {P₁}

open Function

/-- The affine equivalence given by reflection about the point `x`.
This is `Equiv.pointReflection` as an `AffineEquiv`. -/
/-
**AffineEquiv.pointReflection** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁
参数：x : P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine equivalence given by reflection about the point `x`.
This is `Equiv.pointReflection` as an `AffineEquiv`.
-/
def pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)

@[simp]
/-
**AffineEquiv.coe_pointReflection** 是 Mathlib 中的一个引理，位于命名空间 `AffineEquiv`。
形式化陈述：coe_pointReflection (x y : P₁) : pointReflection k x y = Equiv.pointReflec
tion x y
参数：x y : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_pointReflection (x y : P₁) : pointReflection k x y = Equiv.pointReflection x y :=
  rfl

@[deprecated (since := "2026-06-22")]
alias pointReflection_apply_eq_equivPointReflection_apply := coe_pointReflection
/-
**AffineEquiv.pointReflection_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：pointReflection_apply (x y : P₁) : pointReflection k x y = (x -ᵥ y) +ᵥ x
参数：x y : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointReflection_apply (x y : P₁) : pointReflection k x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/-
**AffineEquiv.pointReflection_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflecti
on k x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.toEquiv_injective`：toEquiv_injective : Injective (toEquiv : 
(P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂)
· 使用定理 `Equiv.pointReflection_symm`：pointReflection_symm (x : P) : (pointReflect
ion x).symm = pointReflection x
-/
theorem pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
  toEquiv_injective <| Equiv.pointReflection_symm x

@[simp]
/-
**AffineEquiv.toEquiv_pointReflection** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：toEquiv_pointReflection (x : P₁) : (pointReflection k x).toEquiv = Equiv.p
ointReflection x
参数：x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_pointReflection (x : P₁) :
    (pointReflection k x).toEquiv = Equiv.pointReflection x :=
  rfl
/-
**AffineEquiv.pointReflection_self** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
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
**AffineEquiv.pointReflection_involutive** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`
。
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

/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
/-
**AffineEquiv.pointReflection_fixed_iff_of_injective_two_nsmul** 是 Mathlib 中的一个定
理，位于命名空间 `AffineEquiv`。
形式化陈述：pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁} (h : Injective
 (2 • · : V₁ -> V₁)) : pointReflection k x y = y ↔ y = x
参数：h : Injective (2 • · : V₁ -> V₁)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.pointReflection_fixed_iff_of_injective_two_nsmul`：pointReflection_
fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G -> G)) : po
intReflection x y = y ↔ y = x

--- 原说明 ---
`x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an e
xplicit argument.
-/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁}
    (h : Injective (2 • · : V₁ → V₁)) : pointReflection k x y = y ↔ y = x :=
  Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h
/-
**AffineEquiv.injective_pointReflection_left_of_injective_two_nsmul** 是 Mathlib 
中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：injective_pointReflection_left_of_injective_two_nsmul (h : Injective (2 • 
· : V₁ -> V₁)) (y : P₁) : Injective fun x : P₁ => pointReflection k x y
参数：h : Injective (2 • · : V₁ -> V₁)；y : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective_pointReflection_left_of_injective_two_nsmul`：injective_p
ointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G] [AddTo
rsor G P] (h : Injective (2 • · : G -> G)) (y : P…
-/
theorem injective_pointReflection_left_of_injective_two_nsmul
    (h : Injective (2 • · : V₁ → V₁)) (y : P₁) :
    Injective fun x : P₁ => pointReflection k x y :=
  Equiv.injective_pointReflection_left_of_injective_two_nsmul h y
/-
**AffineEquiv.injective_pointReflection_left_of_module** 是 Mathlib 中的一个定理，位于命名空间
 `AffineEquiv`。
形式化陈述：injective_pointReflection_left_of_module [Invertible (2 : k)] : forall y, 
Injective fun x : P₁ => pointReflection k x y
参数：2 : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineEquiv.injective_pointReflection_left_of_injective_two_nsmul`：injec
tive_pointReflection_left_of_injective_two_nsmul (h : Injective (2 • · : V₁ -> V
₁)) (y : P₁) : Injective fun x : P₁ => pointReflection …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsUnit.smul_left_cancel`：smul_left_cancel {a : α} (ha : IsUnit a) {x y :
 β} : a • x = a • y ↔ x = y
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
-/
theorem injective_pointReflection_left_of_module [Invertible (2 : k)] :
    ∀ y, Injective fun x : P₁ => pointReflection k x y :=
  injective_pointReflection_left_of_injective_two_nsmul k fun x y h => by
    dsimp at h
    rwa [two_nsmul, two_nsmul, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h
/-
**AffineEquiv.pointReflection_fixed_iff_of_module** 是 Mathlib 中的一个定理，位于命名空间 `Aff
ineEquiv`。
形式化陈述：pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} : poin
tReflection k x y = y ↔ y = x
参数：2 : k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `AffineEquiv.injective_pointReflection_left_of_module`：injective_pointRef
lection_left_of_module [Invertible (2 : k)] : forall y, Injective fun x : P₁ => 
pointReflection k x y
· 使用定理 `AffineEquiv.pointReflection_self`：pointReflection_self (x : P₁) : pointR
eflection k x x = x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    pointReflection k x y = y ↔ y = x :=
  ((injective_pointReflection_left_of_module k y).eq_iff' (pointReflection_self k y)).trans eq_comm

end AffineEquiv

namespace LinearEquiv

/-- Interpret a linear equivalence between modules as an affine equivalence. -/
/-
**LinearEquiv.toAffineEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where toEquiv
参数：e : V₁ ≃ₗ[k] V₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a linear equivalence between modules as an affine equivalence.
-/
def toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where
  toEquiv := e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p

@[simp]
/-
**LinearEquiv.coe_toAffineEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.toAffineEquiv = e
参数：e : V₁ ≃ₗ[k] V₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.toAffineEquiv = e :=
  rfl

end LinearEquiv

namespace AffineEquiv

section ofLinearEquiv

variable {k V P : Type*}
variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- Construct an affine equivalence from a linear equivalence and two base points.

Given a linear equivalence `A : V ≃ₗ[k] V` and base points `p₀ p₁ : P`, this constructs
the affine equivalence `T x = A (x -ᵥ p₀) +ᵥ p₁`. This is the standard way to convert
a linear automorphism into an affine automorphism with specified base point mapping. -/
/-
**AffineEquiv.ofLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) : P ≃ᵃ[k] P
参数：A : V ≃ₗ[k] V；p₀ p₁ : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine equivalence from a linear equivalence and two base points.

Given a linear equivalence `A : V ≃ₗ[k] V` and base points `p₀ p₁ : P`, this con
structs
the affine equivalence `T x = A (x -ᵥ p₀) +ᵥ p₁`. This is the standard way to co
nvert
a linear automorphism into an affine automorphism with specified base point mapp
ing.
-/
def ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) : P ≃ᵃ[k] P :=
  (vaddConst k p₀).symm.trans (A.toAffineEquiv.trans (vaddConst k p₁))

@[simp]
/-
**AffineEquiv.ofLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ofLinearEquiv_apply (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P) : ofLinearEquiv A 
p₀ p₁ x = A (x -ᵥ p₀) +ᵥ p₁
参数：A : V ≃ₗ[k] V；p₀ p₁ : P；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearEquiv_apply (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P) :
    ofLinearEquiv A p₀ p₁ x = A (x -ᵥ p₀) +ᵥ p₁ :=
  rfl

@[simp]
/-
**AffineEquiv.linear_ofLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：linear_ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) : (ofLinearEquiv A p₀ p₁)
.linear = A
参数：A : V ≃ₗ[k] V；p₀ p₁ : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linear_ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) :
    (ofLinearEquiv A p₀ p₁).linear = A :=
  rfl

@[simp]
/-
**AffineEquiv.ofLinearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：ofLinearEquiv_refl (p : P) : ofLinearEquiv (.refl k V) p p = .refl k P
参数：p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLinearEquiv_refl (p : P) :
    ofLinearEquiv (.refl k V) p p = .refl k P := by
  ext x
  simp [ofLinearEquiv_apply]

@[simp]
/-
**AffineEquiv.ofLinearEquiv_trans_ofLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Affin
eEquiv`。
形式化陈述：ofLinearEquiv_trans_ofLinearEquiv (A B : V ≃ₗ[k] V) (p₀ p₁ p₂ : P) : (ofLi
nearEquiv A p₀ p₁).trans (ofLinearEquiv B p₁ p₂) = ofLinearEquiv (A.trans B) p₀ 
p₂
参数：A B : V ≃ₗ[k] V；p₀ p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.ext`：ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e
 = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineEquiv.map_vadd`：map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (
v +ᵥ p) = e.linear v +ᵥ e p
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLinearEquiv_trans_ofLinearEquiv (A B : V ≃ₗ[k] V) (p₀ p₁ p₂ : P) :
    (ofLinearEquiv A p₀ p₁).trans (ofLinearEquiv B p₁ p₂) =
      ofLinearEquiv (A.trans B) p₀ p₂ := by
  ext x
  simp

end ofLinearEquiv

section arrowCongrEquiv

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

/-- Affine isomorphisms between the domains and codomains of two spaces of affine maps give a
bijection between the two function spaces.

See `AffineEquiv.arrowCongr` and `AffineEquiv.arrowCongrₗ` for the affine and linear versions of
this bijection. -/
/-
**AffineEquiv.arrowCongrEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongrEquiv : (P₁ ->ᵃ[k] P₃) ≃ (P₂ ->ᵃ[k] P₄) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Affine isomorphisms between the domains and codomains of two spaces of affine ma
ps give a
bijection between the two function spaces.

See `AffineEquiv.arrowCongr` and `AffineEquiv.arrowCongrₗ` for the affine and li
near versions of
this bijection.
-/
def arrowCongrEquiv : (P₁ →ᵃ[k] P₃) ≃ (P₂ →ᵃ[k] P₄) where
  toFun f := e₂.toAffineMap.comp <| f.comp e₁.symm.toAffineMap
  invFun f := e₂.symm.toAffineMap.comp <| f.comp e₁.toAffineMap
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
/-
**AffineEquiv.arrowCongrEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongrEquiv_apply (f : P₁ ->ᵃ[k] P₃) (x : P₂) : e₁.arrowCongrEquiv e₂ 
f x = e₂ (f (e₁.symm x))
参数：f : P₁ ->ᵃ[k] P₃；x : P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongrEquiv_apply (f : P₁ →ᵃ[k] P₃) (x : P₂) :
    e₁.arrowCongrEquiv e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/-
**AffineEquiv.arrowCongrEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`
。
形式化陈述：arrowCongrEquiv_symm_apply (f : P₂ ->ᵃ[k] P₄) (x : P₁) : (e₁.arrowCongrEqu
iv e₂).symm f x = e₂.symm (f (e₁ x))
参数：f : P₂ ->ᵃ[k] P₄；x : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem arrowCongrEquiv_symm_apply (f : P₂ →ᵃ[k] P₄) (x : P₁) :
    (e₁.arrowCongrEquiv e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongrEquiv

section CommRing

variable {R : Type*} [CommRing R] [Module R V₁] [Module R V₂] [Module R V₃] [Module R V₄]

section arrowCongrₗ

variable (e₁ : P₁ ≃ᵃ[R] P₂) (e₂ : V₃ ≃ₗ[R] V₄)

set_option backward.isDefEq.respectTransparency false in
/-- An affine isomorphism between the domains and a linear isomorphism between the codomains of two
spaces of affine maps give a linear isomorphism between the two function spaces.

See also `AffineEquiv.arrowCongrEquiv` and `AffineEquiv.arrowCongr`. -/
/-
**AffineEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine isomorphism between the domains and a linear isomorphism between the c
odomains of two
spaces of affine maps give a linear isomorphism between the two function spaces.

See also `AffineEquiv.arrowCongrEquiv` and `AffineEquiv.arrowCongr`.
-/
def arrowCongrₗ : (P₁ →ᵃ[R] V₃) ≃ₗ[R] (P₂ →ᵃ[R] V₄) where
  __ := e₁.arrowCongrEquiv e₂.toAffineEquiv
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/-
**AffineEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongrₗ_apply (f : P₁ →ᵃ[R] V₃) (x : P₂) :
    e₁.arrowCongrₗ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/-
**AffineEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongrₗ_symm_apply (f : P₂ →ᵃ[R] V₄) (x : P₁) :
    (e₁.arrowCongrₗ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongrₗ

section arrowCongr

variable (e₁ : P₁ ≃ᵃ[R] P₂) (e₂ : P₃ ≃ᵃ[R] P₄)

/-- Affine isomorphisms between the domains and codomains of two spaces of affine maps give an
affine isomorphism between the two function spaces.

See also `AffineEquiv.arrowCongrEquiv` and `AffineEquiv.arrowCongrₗ`. -/
@[simps linear]
/-
**AffineEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Affine isomorphisms between the domains and codomains of two spaces of affine ma
ps give an
affine isomorphism between the two function spaces.

See also `AffineEquiv.arrowCongrEquiv` and `AffineEquiv.arrowCongrₗ`.
-/
def arrowCongr : (P₁ →ᵃ[R] P₃) ≃ᵃ[R] (P₂ →ᵃ[R] P₄) where
  __ := e₁.arrowCongrEquiv e₂
  linear := e₁.arrowCongrₗ e₂.linear
  map_vadd' _ _ := by ext; simp

@[simp]
/-
**AffineEquiv.arrowCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr_apply (f : P₁ ->ᵃ[R] P₃) (x : P₂) : e₁.arrowCongr e₂ f x = e₂ (
f (e₁.symm x))
参数：f : P₁ ->ᵃ[R] P₃；x : P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_apply (f : P₁ →ᵃ[R] P₃) (x : P₂) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/-
**AffineEquiv.arrowCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：arrowCongr_symm_apply (f : P₂ ->ᵃ[R] P₄) (x : P₁) : (e₁.arrowCongr e₂).sym
m f x = e₂.symm (f (e₁ x))
参数：f : P₂ ->ᵃ[R] P₄；x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem arrowCongr_symm_apply (f : P₂ →ᵃ[R] P₄) (x : P₁) :
    (e₁.arrowCongr e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongr

end CommRing

section congrLeft

variable (R W : Type*) [Ring R] [AddCommGroup W] [Module k W] [Module R W] [SMulCommClass k R W]
  (e : P₁ ≃ᵃ[k] P₂)

/-- An affine isomorphism between the domains of affine spaces induces a linear isomorphism over
another ring between the two function spaces. -/
/-
**AffineEquiv.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine isomorphism between the domains of affine spaces induces a linear isom
orphism over
another ring between the two function spaces.
-/
def congrLeftₗ : (P₁ →ᵃ[k] W) ≃ₗ[R] (P₂ →ᵃ[k] W) where
  __ := e.arrowCongrEquiv (.refl k W)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/-
**AffineEquiv.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLeftₗ_apply (f : P₁ →ᵃ[k] W) (x : P₂) : e.congrLeftₗ R W f x = f (e.symm x) :=
  rfl

@[simp]
/-
**AffineEquiv.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLeftₗ_symm_apply (f : P₂ →ᵃ[k] W) (x : P₁) : (e.congrLeftₗ R W).symm f x = f (e x) :=
  rfl

variable {W} (Q : Type*) [AddTorsor W Q]

/-- An affine isomorphism between the domains of affine spaces induces an affine isomorphism over
another ring between the two function spaces. -/
/-
**AffineEquiv.congrLeft** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine isomorphism between the domains of affine spaces induces an affine iso
morphism over
another ring between the two function spaces.
-/
def congrLeft : (P₁ →ᵃ[k] Q) ≃ᵃ[R] (P₂ →ᵃ[k] Q) where
  __ := e.arrowCongrEquiv (.refl k Q)
  linear := e.congrLeftₗ R W
  map_vadd' _ _ := by ext; simp

@[simp]
/-
**AffineEquiv.congrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft_apply (f : P₁ ->ᵃ[k] Q) (x : P₂) : e.congrLeft R Q f x = f (e.sy
mm x)
参数：f : P₁ ->ᵃ[k] Q；x : P₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLeft_apply (f : P₁ →ᵃ[k] Q) (x : P₂) : e.congrLeft R Q f x = f (e.symm x) :=
  rfl

@[simp]
/-
**AffineEquiv.congrLeft_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：congrLeft_symm_apply (f : P₂ ->ᵃ[k] Q) (x : P₁) : (e.congrLeft R Q).symm f
 x = f (e x)
参数：f : P₂ ->ᵃ[k] Q；x : P₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLeft_symm_apply (f : P₂ →ᵃ[k] Q) (x : P₁) : (e.congrLeft R Q).symm f x = f (e x) :=
  rfl

end congrLeft

end AffineEquiv

namespace AffineMap

open AffineEquiv

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vadd (v v' : V₁) (p : P₁) (c : k) : lineMap v v' c +ᵥ p = lineMap 
(v +ᵥ p) (v' +ᵥ p) c
参数：v v' : V₁；p : P₁；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.apply_lineMap`：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c
 : k) : e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c
-/
theorem lineMap_vadd (v v' : V₁) (p : P₁) (c : k) :
    lineMap v v' c +ᵥ p = lineMap (v +ᵥ p) (v' +ᵥ p) c :=
  (vaddConst k p).apply_lineMap v v' c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) : lineMap p₁ p₂ c -ᵥ p₃ = lineMap (p₁
 -ᵥ p₃) (p₂ -ᵥ p₃) c
参数：p₁ p₂ p₃ : P₁；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.apply_lineMap`：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c
 : k) : e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c
-/
theorem lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) :
    lineMap p₁ p₂ c -ᵥ p₃ = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c :=
  (vaddConst k p₃).symm.apply_lineMap p₁ p₂ c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.vsub_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) : p₁ -ᵥ lineMap p₂ p₃ c = lineMap (p₁
 -ᵥ p₂) (p₁ -ᵥ p₃) c
参数：p₁ p₂ p₃ : P₁；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.apply_lineMap`：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c
 : k) : e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c
-/
theorem vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) :
    p₁ -ᵥ lineMap p₂ p₃ c = lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c :=
  (constVSub k p₁).apply_lineMap p₂ p₃ c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.vadd_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) : v +ᵥ lineMap p₁ p₂ c = lineMa
p (v +ᵥ p₁) (v +ᵥ p₂) c
参数：v : V₁；p₁ p₂ : P₁；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineEquiv.apply_lineMap`：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c
 : k) : e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c
-/
theorem vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) :
    v +ᵥ lineMap p₁ p₂ c = lineMap (v +ᵥ p₁) (v +ᵥ p₂) c :=
  (constVAdd k P₁ v).apply_lineMap p₁ p₂ c

variable {R' : Type*} [CommRing R'] [Module R' V₁]
/-
**AffineMap.homothety_neg_one_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_neg_one_apply (c p : P₁) : homothety c (-1 : R') p = pointReflec
tion R' c p
参数：c p : P₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_neg_one_apply (c p : P₁) : homothety c (-1 : R') p = pointReflection R' c p := by
  simp [homothety_apply, Equiv.pointReflection_apply]

end AffineMap

