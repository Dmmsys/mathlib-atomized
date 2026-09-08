/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Defs
/-!
# Affine maps

This file defines affine maps.

## Main definitions

* `AffineMap` is the type of affine maps between two affine spaces with the same ring `k`.  Various
  basic examples of affine maps are defined, including `const`, `id`, `lineMap` and `homothety`.

## Notation

* `P1 →ᵃ[k] P2` is a notation for `AffineMap k P1 P2`;
* `AffineSpace V P`: a localized notation for `AddTorsor V P` defined in
  `LinearAlgebra.AffineSpace.Basic`.

## Implementation notes

`outParam` is used in the definition of `[AddTorsor V P]` to make `V` an implicit argument
(deduced from `P`) in most cases. As for modules, `k` is an explicit argument rather than implied by
`P` or `V`.

This file only provides purely algebraic definitions and results. Those depending on analysis or
topology are defined elsewhere; see `Analysis.Normed.Affine.AddTorsor` and
`Topology.Algebra.Affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

@[expose] public section

open Affine Module

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
/-
**AffineMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) →   {V1 : Type u_2} →     (P1 : Type u_3) →       {V2 : Typ
e u_4} →         (P2 : Type u_5) →           [inst : Ring k] →             [inst
_1 : AddCommGroup V1] →               [_root_.Module k V1] →                 [Ad
dTorsor V1 P1] →                   [inst_4 : AddCommGroup V2] →                 
    [_root_.Module k V2] → [AddTorsor V2 P2] → Type (max (max (max u_2 u_3) u_4)
 u_5)
参数：max (max u_2 u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`.
-/
structure AffineMap (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*) [Ring k]
  [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
  [AffineSpace V2 P2] where
  /-- The underlying function between the affine spaces `P1` and `P2`. -/
  toFun : P1 → P2
  /-- The linear map between the corresponding vector spaces `V1` and `V2`.
  This represents how the affine map acts on differences of points. -/
  linear : V1 →ₗ[k] V2
  map_vadd' : ∀ (p : P1) (v : V1), toFun (v +ᵥ p) = linear v +ᵥ toFun p

/-- An `AffineMap k P1 P2` (notation: `P1 →ᵃ[k] P2`) is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
notation:25 P1 " →ᵃ[" k:25 "] " P2:0 => AffineMap k P1 P2

/-
**AffineMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AffineMap.instFunLike (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (
P2 : Type*) [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCom
mGroup V2] [Module k V2] [AffineSpace V2 P2] : FunLike (P1 ->ᵃ[k] P2) P1 P2 wher
e coe
参数：k : Type*；P1 : Type*；P2 : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AffineMap.instFunLike (k : Type*) {V1 : Type*} (P1 : Type*) {V2 : Type*} (P2 : Type*)
    [Ring k] [AddCommGroup V1] [Module k V1] [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2]
    [AffineSpace V2 P2] : FunLike (P1 →ᵃ[k] P2) P1 P2 where
  coe := AffineMap.toFun
  coe_injective := fun ⟨f, f_linear, f_add⟩ ⟨g, g_linear, g_add⟩ => fun (h : f = g) => by
    obtain ⟨p⟩ := (AddTorsor.nonempty : Nonempty P1)
    congr with v
    apply vadd_right_cancel (f p)
    rw [← f_add, h, ← g_add]

namespace LinearMap

variable {k : Type*} {V₁ : Type*} {V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] (f : V₁ →ₗ[k] V₂)

/-- Reinterpret a linear map as an affine map. -/
/-
**LinearMap.toAffineMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toAffineMap : V₁ ->ᵃ[k] V₂ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a linear map as an affine map.
-/
def toAffineMap : V₁ →ᵃ[k] V₂ where
  toFun := f
  linear := f
  map_vadd' p v := f.map_add v p

@[simp]
/-
**LinearMap.coe_toAffineMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_toAffineMap : ⇑f.toAffineMap = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAffineMap : ⇑f.toAffineMap = f :=
  rfl

@[simp]
/-
**LinearMap.toAffineMap_linear** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toAffineMap_linear : f.toAffineMap.linear = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAffineMap_linear : f.toAffineMap.linear = f :=
  rfl

end LinearMap

namespace AffineMap

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AffineSpace V1 P1] [AddCommGroup V2] [Module k V2] [AffineSpace V2 P2] [AddCommGroup V3]
  [Module k V3] [AffineSpace V3 P3] [AddCommGroup V4] [Module k V4] [AffineSpace V4 P4]

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp]
/-
**AffineMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_mk (f : P1 -> P2) (linear add) : ((mk f linear add : P1 ->ᵃ[k] P2) : P
1 -> P2) = f
参数：f : P1 -> P2；linear add。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructing an affine map and coercing back to a function
produces the same map.
-/
theorem coe_mk (f : P1 → P2) (linear add) : ((mk f linear add : P1 →ᵃ[k] P2) : P1 → P2) = f :=
  rfl

/-- `toFun` is the same as the result of coercing to a function. -/
@[simp]
/-
**AffineMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：toFun_eq_coe (f : P1 ->ᵃ[k] P2) : f.toFun = ⇑f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toFun` is the same as the result of coercing to a function.
-/
theorem toFun_eq_coe (f : P1 →ᵃ[k] P2) : f.toFun = ⇑f :=
  rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp]
/-
**AffineMap.map_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ
 f p
参数：f : P1 ->ᵃ[k] P2；p : P1；v : V1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.map_vadd'`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V
2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst
_2 : _roo…

--- 原说明 ---
An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point.
-/
theorem map_vadd (f : P1 →ᵃ[k] P2) (p : P1) (v : V1) : f (v +ᵥ p) = f.linear v +ᵥ f p :=
  f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
@[simp]
/-
**AffineMap.linearMap_vsub** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p
1 -ᵥ f p2
参数：f : P1 ->ᵃ[k] P2；p1 p2 : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

--- 原说明 ---
The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points.
-/
theorem linearMap_vsub (f : P1 →ᵃ[k] P2) (p1 p2 : P1) : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2 := by
  conv_rhs => rw [← vsub_vadd p1 p2, map_vadd, vadd_vsub]

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext]
/-
**AffineMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = g
参数：h : forall p, f p = g p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
Two affine maps are equal if they coerce to the same function.
-/
theorem ext {f g : P1 →ᵃ[k] P2} (h : ∀ p, f p = g p) : f = g :=
  DFunLike.ext _ _ h
/-
**AffineMap.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coeFn_injective : @Function.Injective (P1 ->ᵃ[k] P2) (P1 -> P2) (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Function.Injective (P1 →ᵃ[k] P2) (P1 → P2) (⇑) :=
  DFunLike.coe_injective
/-
**AffineMap.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Typ
e u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst_2 : _root_.Module k V1
] [inst_3 : AddTorsor V1 P1] [inst_4 : AddCommGroup V2]   [inst_5 : _root_.Modul
e k V2] [inst_6 : AddTorsor V2 P2] (f : P1 →ᵃ[k] P2) {x y : P1}, x = y → f x = f
 y
参数：f : P1 →ᵃ[k] P2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem congr_arg (f : P1 →ᵃ[k] P2) {x y : P1} (h : x = y) : f x = f y :=
  congr_arg _ h
/-
**AffineMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Typ
e u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst_2 : _root_.Module k V1
] [inst_3 : AddTorsor V1 P1] [inst_4 : AddCommGroup V2]   [inst_5 : _root_.Modul
e k V2] [inst_6 : AddTorsor V2 P2] {f g : P1 →ᵃ[k] P2}, f = g → ∀ (x : P1), f x 
= g x
参数：x : P1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem congr_fun {f g : P1 →ᵃ[k] P2} (h : f = g) (x : P1) : f x = g x :=
  h ▸ rfl

/-- Two affine maps are equal if they have equal linear maps and are equal at some point. -/
/-
**AffineMap.ext_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：ext_linear {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : 
f p = g p) : f = g
参数：h₁ : f.linear = g.linear；h₂ : f p = g p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineMap.map_vadd'`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V
2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst
_2 : _roo…
· 使用定理 `AffineMap.toFun_eq_coe`：toFun_eq_coe (f : P1 ->ᵃ[k] P2) : f.toFun = ⇑f

--- 原说明 ---
Two affine maps are equal if they have equal linear maps and are equal at some p
oint.
-/
theorem ext_linear {f g : P1 →ᵃ[k] P2} (h₁ : f.linear = g.linear) {p : P1} (h₂ : f p = g p) :
    f = g := by
  ext q
  have hgl : g.linear (q -ᵥ p) = toFun g ((q -ᵥ p) +ᵥ q) -ᵥ toFun g q := by simp
  have := f.map_vadd' q (q -ᵥ p)
  rw [h₁, hgl, toFun_eq_coe, map_vadd, linearMap_vsub, h₂] at this
  simpa

/-- Two affine maps are equal if they have equal linear maps and are equal at some point. -/
/-
**AffineMap.ext_linear_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：ext_linear_iff {f g : P1 ->ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (exi
sts p, f p = g p)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AffineMap.ext_linear`：ext_linear {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g
.linear) {p : P1} (h₂ : f p = g p) : f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Two affine maps are equal if they have equal linear maps and are equal at some p
oint.
-/
theorem ext_linear_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (∃ p, f p = g p) :=
  ⟨fun h ↦ ⟨congrArg _ h, by inhabit P1; exact default, by rw [h]⟩,
  fun h ↦ Exists.casesOn h.2 fun _ hp ↦ ext_linear h.1 hp⟩

variable (k P1)

/-- The constant function as an `AffineMap`. -/
/-
**AffineMap.const** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：const (p : P2) : P1 ->ᵃ[k] P2 where toFun
参数：p : P2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function as an `AffineMap`.
-/
def const (p : P2) : P1 →ᵃ[k] P2 where
  toFun := Function.const P1 p
  linear := 0
  map_vadd' _ _ :=
    letI : AddAction V2 P2 := inferInstance
    by simp

@[simp]
/-
**AffineMap.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p
参数：p : P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (p : P2) : ⇑(const k P1 p) = Function.const P1 p :=
  rfl

@[simp]
/-
**AffineMap.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：const_apply (p : P2) (q : P1) : (const k P1 p) q = p
参数：p : P2；q : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (p : P2) (q : P1) : (const k P1 p) q = p := rfl

@[simp]
/-
**AffineMap.const_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：const_linear (p : P2) : (const k P1 p).linear = 0
参数：p : P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_linear (p : P2) : (const k P1 p).linear = 0 :=
  rfl

variable {k P1}
/-
**AffineMap.linear_eq_zero_iff_exists_const** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap
`。
形式化陈述：linear_eq_zero_iff_exists_const (f : P1 ->ᵃ[k] P2) : f.linear = 0 ↔ exists
 q, f = const k P1 q
参数：f : P1 ->ᵃ[k] P2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.coe_const`：coe_const (p : P2) : ⇑(const k P1 p) = Function.con
st P1 p
· 使用定理 `Function.const_apply`：∀ {β : Sort u_1} {α : Sort u_2} {y : β} {x : α}, F
unction.const α y x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `AffineMap.const_linear`：const_linear (p : P2) : (const k P1 p).linear = 
0
-/
theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) :
    f.linear = 0 ↔ ∃ q, f = const k P1 q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · use f (Classical.arbitrary P1)
    ext
    rw [coe_const, Function.const_apply, ← @vsub_eq_zero_iff_eq V2, ← f.linearMap_vsub, h,
      LinearMap.zero_apply]
  · rcases h with ⟨q, rfl⟩
    exact const_linear k P1 q
/-
**AffineMap.nonempty** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
形式化陈述：nonempty : Nonempty (P1 ->ᵃ[k] P2)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
-/
instance nonempty : Nonempty (P1 →ᵃ[k] P2) :=
  (AddTorsor.nonempty : Nonempty P2).map <| const k P1

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
/-
**AffineMap.mk'** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：mk' (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p : P1) (h : forall p' : P1, f p' 
= f' (p' -ᵥ p) +ᵥ f p) : P1 ->ᵃ[k] P2 where toFun
参数：f : P1 -> P2；f' : V1 ->ₗ[k] V2；p : P1；h : forall p' : P1, f p' = f' (p' -ᵥ p)
 +ᵥ f p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an affine map by verifying the relation between the map and its linear
 part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : 
V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f
 p`.
-/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
    P1 →ᵃ[k] P2 where
  toFun := f
  linear := f'
  map_vadd' p' v := by rw [h, h p', vadd_vsub_assoc, f'.map_add, vadd_vadd]

@[simp]
/-
**AffineMap.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_mk' (f : P1 -> P2) (f' : V1 ->ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f
参数：f : P1 -> P2；f' : V1 ->ₗ[k] V2；p h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f :=
  rfl

@[simp]
/-
**AffineMap.mk'_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V2 : Type u_4} {P2 : Typ
e u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst_2 : _root_.Module k V1
] [inst_3 : AddTorsor V1 P1] [inst_4 : AddCommGroup V2]   [inst_5 : _root_.Modul
e k V2] [inst_6 : AddTorsor V2 P2] (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1)   (
h : ∀ (p' : P1), f p' = f' (p' -ᵥ p) +ᵥ f p), (AffineMap.mk' f f' p h).linear = 
f'
参数：f : P1 → P2；f' : V1 →ₗ[k] V2；p : P1；h : ∀ (p' : P1), f p' = f' (p' -ᵥ p) +ᵥ f
 p；AffineMap.mk' f f' p h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' :=
  rfl

section SMul

variable {R : Type*} [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]
/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
/-
**AffineMap.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
形式化陈述：mulAction : MulAction R (P1 ->ᵃ[k] V2) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of affine maps to a module inherits an `R`-action from the action on i
ts codomain.
-/
instance mulAction : MulAction R (P1 →ᵃ[k] V2) where
  smul c f := ⟨c • ⇑f, c • f.linear, fun p v => by simp [smul_add]⟩
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

@[simp, norm_cast]
/-
**AffineMap.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_smul (c : R) (f : P1 ->ᵃ[k] V2) : ⇑(c • f) = c • ⇑f
参数：c : R；f : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (c : R) (f : P1 →ᵃ[k] V2) : ⇑(c • f) = c • ⇑f :=
  rfl

@[simp]
/-
**AffineMap.smul_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：smul_linear (t : R) (f : P1 ->ᵃ[k] V2) : (t • f).linear = t • f.linear
参数：t : R；f : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_linear (t : R) (f : P1 →ᵃ[k] V2) : (t • f).linear = t • f.linear :=
  rfl
/-
**AffineMap.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
形式化陈述：isCentralScalar [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2] : IsCent
ralScalar R (P1 ->ᵃ[k] V2) where op_smul_eq_smul _r _x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ V2] [IsCentralScalar R V2] :
    IsCentralScalar R (P1 →ᵃ[k] V2) where
  op_smul_eq_smul _r _x := ext fun _ => op_smul_eq_smul _ _

end SMul

/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (P1 →ᵃ[k] V2) where zero := ⟨0, 0, fun _ _ => (zero_vadd _ _).symm⟩
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (P1 →ᵃ[k] V2) where
  add f g := ⟨f + g, f.linear + g.linear, fun p v => by simp [add_add_add_comm]⟩
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (P1 →ᵃ[k] V2) where
  sub f g := ⟨f - g, f.linear - g.linear, fun p v => by simp [sub_add_sub_comm]⟩
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (P1 →ᵃ[k] V2) where
  neg f := ⟨-f, -f.linear, fun p v => by simp [add_comm, map_vadd f]⟩

@[simp, norm_cast]
/-
**AffineMap.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_zero : ⇑(0 : P1 ->ᵃ[k] V2) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : P1 →ᵃ[k] V2) = 0 :=
  rfl

@[simp, norm_cast]
/-
**AffineMap.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_add (f g : P1 ->ᵃ[k] V2) : ⇑(f + g) = f + g
参数：f g : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : P1 →ᵃ[k] V2) : ⇑(f + g) = f + g :=
  rfl

@[simp, norm_cast]
/-
**AffineMap.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_neg (f : P1 ->ᵃ[k] V2) : ⇑(-f) = -f
参数：f : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : P1 →ᵃ[k] V2) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/-
**AffineMap.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_sub (f g : P1 ->ᵃ[k] V2) : ⇑(f - g) = f - g
参数：f g : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : P1 →ᵃ[k] V2) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/-
**AffineMap.zero_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：zero_linear : (0 : P1 ->ᵃ[k] V2).linear = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_linear : (0 : P1 →ᵃ[k] V2).linear = 0 :=
  rfl

@[simp]
/-
**AffineMap.add_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：add_linear (f g : P1 ->ᵃ[k] V2) : (f + g).linear = f.linear + g.linear
参数：f g : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_linear (f g : P1 →ᵃ[k] V2) : (f + g).linear = f.linear + g.linear :=
  rfl

@[simp]
/-
**AffineMap.sub_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：sub_linear (f g : P1 ->ᵃ[k] V2) : (f - g).linear = f.linear - g.linear
参数：f g : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_linear (f g : P1 →ᵃ[k] V2) : (f - g).linear = f.linear - g.linear :=
  rfl

@[simp]
/-
**AffineMap.neg_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：neg_linear (f : P1 ->ᵃ[k] V2) : (-f).linear = -f.linear
参数：f : P1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_linear (f : P1 →ᵃ[k] V2) : (-f).linear = -f.linear :=
  rfl

/-- The set of affine maps to a vector space is an additive commutative group. -/
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of affine maps to a vector space is an additive commutative group.
-/
instance : AddCommGroup (P1 →ᵃ[k] V2) :=
  coeFn_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _)
    fun _ _ => coe_smul _ _

/-- The space of affine maps from `P1` to `P2` is an affine space over the space of affine maps
from `P1` to the vector space `V2` corresponding to `P2`. -/
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of affine maps from `P1` to `P2` is an affine space over the space of 
affine maps
from `P1` to the vector space `V2` corresponding to `P2`.
-/
instance : AffineSpace (P1 →ᵃ[k] V2) (P1 →ᵃ[k] P2) where
  vadd f g :=
    ⟨fun p => f p +ᵥ g p, f.linear + g.linear,
      fun p v => by simp [vadd_vadd, add_right_comm]⟩
  zero_vadd f := ext fun p => zero_vadd _ (f p)
  add_vadd f₁ f₂ f₃ := ext fun p => add_vadd (f₁ p) (f₂ p) (f₃ p)
  vsub f g :=
    ⟨fun p => f p -ᵥ g p, f.linear - g.linear, fun p v => by
      simp [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_add_eq_add_sub]⟩
  vsub_vadd' f g := ext fun p => vsub_vadd (f p) (g p)
  vadd_vsub' f g := ext fun p => vadd_vsub (f p) (g p)

@[simp]
/-
**AffineMap.vadd_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vadd_apply (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f
 p +ᵥ g p
参数：f : P1 ->ᵃ[k] V2；g : P1 ->ᵃ[k] P2；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_apply (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) (p : P1) : (f +ᵥ g) p = f p +ᵥ g p :=
  rfl

@[simp]
/-
**AffineMap.vadd_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vadd_linear (f : P1 ->ᵃ[k] V2) (g : P1 ->ᵃ[k] P2) : (f +ᵥ g).linear = f.li
near + g.linear
参数：f : P1 ->ᵃ[k] V2；g : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_linear (f : P1 →ᵃ[k] V2) (g : P1 →ᵃ[k] P2) : (f +ᵥ g).linear = f.linear + g.linear :=
  rfl

@[simp]
/-
**AffineMap.vsub_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vsub_apply (f g : P1 ->ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 ->ᵃ[k] V2) p = f p
 -ᵥ g p
参数：f g : P1 ->ᵃ[k] P2；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vsub_apply (f g : P1 →ᵃ[k] P2) (p : P1) : (f -ᵥ g : P1 →ᵃ[k] V2) p = f p -ᵥ g p :=
  rfl

@[simp]
/-
**AffineMap.vsub_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：vsub_linear (f g : P1 ->ᵃ[k] P2) : (f -ᵥ g).linear = f.linear - g.linear
参数：f g : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vsub_linear (f g : P1 →ᵃ[k] P2) : (f -ᵥ g).linear = f.linear - g.linear :=
  rfl

/-- `Prod.fst` as an `AffineMap`. -/
/-
**AffineMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：fst : P1 × P2 ->ᵃ[k] P1 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.fst` as an `AffineMap`.
-/
def fst : P1 × P2 →ᵃ[k] P1 where
  toFun := Prod.fst
  linear := LinearMap.fst k V1 V2
  map_vadd' _ _ := rfl

@[simp]
/-
**AffineMap.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_fst : ⇑(fst : P1 × P2 ->ᵃ[k] P1) = Prod.fst
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fst : ⇑(fst : P1 × P2 →ᵃ[k] P1) = Prod.fst :=
  rfl

@[simp]
/-
**AffineMap.fst_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：fst_linear : (fst : P1 × P2 ->ᵃ[k] P1).linear = LinearMap.fst k V1 V2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_linear : (fst : P1 × P2 →ᵃ[k] P1).linear = LinearMap.fst k V1 V2 :=
  rfl

/-- `Prod.snd` as an `AffineMap`. -/
/-
**AffineMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：snd : P1 × P2 ->ᵃ[k] P2 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.snd` as an `AffineMap`.
-/
def snd : P1 × P2 →ᵃ[k] P2 where
  toFun := Prod.snd
  linear := LinearMap.snd k V1 V2
  map_vadd' _ _ := rfl

@[simp]
/-
**AffineMap.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_snd : ⇑(snd : P1 × P2 ->ᵃ[k] P2) = Prod.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_snd : ⇑(snd : P1 × P2 →ᵃ[k] P2) = Prod.snd :=
  rfl

@[simp]
/-
**AffineMap.snd_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：snd_linear : (snd : P1 × P2 ->ᵃ[k] P2).linear = LinearMap.snd k V1 V2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_linear : (snd : P1 × P2 →ᵃ[k] P2).linear = LinearMap.snd k V1 V2 :=
  rfl

variable (k P1)
/-- Identity map as an affine map. -/
nonrec def id : P1 →ᵃ[k] P1 where
  toFun := id
  linear := LinearMap.id
  map_vadd' _ _ := rfl

/-- The identity affine map acts as the identity. -/
@[simp, norm_cast]
/-
**AffineMap.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_id : ⇑(id k P1) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity affine map acts as the identity.
-/
theorem coe_id : ⇑(id k P1) = _root_.id :=
  rfl

@[simp]
/-
**AffineMap.id_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：id_linear : (id k P1).linear = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_linear : (id k P1).linear = LinearMap.id :=
  rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
/-
**AffineMap.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：id_apply (p : P1) : id k P1 p = p
参数：p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity affine map acts as the identity.
-/
theorem id_apply (p : P1) : id k P1 p = p :=
  rfl

variable {k}
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (P1 →ᵃ[k] P1) :=
  ⟨id k P1⟩

/-- Composition of affine maps. -/
@[simps linear]
/-
**AffineMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：comp (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) : P1 ->ᵃ[k] P3 where toFun
参数：f : P2 ->ᵃ[k] P3；g : P1 ->ᵃ[k] P2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of affine maps.
-/
def comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : P1 →ᵃ[k] P3 where
  toFun := f ∘ g
  linear := f.linear.comp g.linear
  map_vadd' := by
    intro p v
    rw [Function.comp_apply, g.map_vadd, f.map_vadd]
    rfl

/-- Composition of affine maps acts as applying the two functions. -/
@[simp]
/-
**AffineMap.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_comp (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g
参数：f : P2 ->ᵃ[k] P3；g : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of affine maps acts as applying the two functions.
-/
theorem coe_comp (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) : ⇑(f.comp g) = f ∘ g :=
  rfl

/-- Composition of affine maps acts as applying the two functions. -/
/-
**AffineMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：comp_apply (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) (p : P1) : f.comp g p = f
 (g p)
参数：f : P2 ->ᵃ[k] P3；g : P1 ->ᵃ[k] P2；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of affine maps acts as applying the two functions.
-/
theorem comp_apply (f : P2 →ᵃ[k] P3) (g : P1 →ᵃ[k] P2) (p : P1) : f.comp g p = f (g p) :=
  rfl

@[simp]
/-
**AffineMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：comp_id (f : P1 ->ᵃ[k] P2) : f.comp (id k P1) = f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
-/
theorem comp_id (f : P1 →ᵃ[k] P2) : f.comp (id k P1) = f :=
  ext fun _ => rfl

@[simp]
/-
**AffineMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：id_comp (f : P1 ->ᵃ[k] P2) : (id k P2).comp f = f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
-/
theorem id_comp (f : P1 →ᵃ[k] P2) : (id k P2).comp f = f :=
  ext fun _ => rfl
/-
**AffineMap.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：comp_assoc (f₃₄ : P3 ->ᵃ[k] P4) (f₂₃ : P2 ->ᵃ[k] P3) (f₁₂ : P1 ->ᵃ[k] P2) 
: (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂)
参数：f₃₄ : P3 ->ᵃ[k] P4；f₂₃ : P2 ->ᵃ[k] P3；f₁₂ : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f₃₄ : P3 →ᵃ[k] P4) (f₂₃ : P2 →ᵃ[k] P3) (f₁₂ : P1 →ᵃ[k] P2) :
    (f₃₄.comp f₂₃).comp f₁₂ = f₃₄.comp (f₂₃.comp f₁₂) :=
  rfl
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (P1 →ᵃ[k] P1) where
  one := id k P1
  mul := comp
  one_mul := id_comp
  mul_one := comp_id
  mul_assoc := comp_assoc

@[simp]
/-
**AffineMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_mul (f g : P1 ->ᵃ[k] P1) : ⇑(f * g) = f ∘ g
参数：f g : P1 ->ᵃ[k] P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : P1 →ᵃ[k] P1) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
/-
**AffineMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_one : ⇑(1 : P1 ->ᵃ[k] P1) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : P1 →ᵃ[k] P1) = _root_.id :=
  rfl

/-- `AffineMap.linear` on endomorphisms is a `MonoidHom`. -/
@[simps]
/-
**AffineMap.linearHom** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：linearHom : (P1 ->ᵃ[k] P1) ->* V1 ->ₗ[k] V1 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AffineMap.linear` on endomorphisms is a `MonoidHom`.
-/
def linearHom : (P1 →ᵃ[k] P1) →* V1 →ₗ[k] V1 where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**AffineMap.linear_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：linear_injective_iff (f : P1 ->ᵃ[k] P2) : Function.Injective f.linear ↔ Fu
nction.Injective f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linear_injective_iff (f : P1 →ᵃ[k] P2) :
    Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h, Equiv.comp_injective, Equiv.injective_comp]

@[simp]
/-
**AffineMap.linear_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：linear_surjective_iff (f : P1 ->ᵃ[k] P2) : Function.Surjective f.linear ↔ 
Function.Surjective f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.comp_surjective`：comp_surjective (f : α -> β) (e : β ≃ γ) : Surjec
tive (e ∘ f) ↔ Surjective f
· 使用定理 `Equiv.surjective_comp`：surjective_comp (e : α ≃ β) (f : β -> γ) : Surjec
tive (f ∘ e) ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linear_surjective_iff (f : P1 →ᵃ[k] P2) :
    Function.Surjective f.linear ↔ Function.Surjective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h, Equiv.comp_surjective, Equiv.surjective_comp]

@[simp]
/-
**AffineMap.linear_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：linear_bijective_iff (f : P1 ->ᵃ[k] P2) : Function.Bijective f.linear ↔ Fu
nction.Bijective f
参数：f : P1 ->ᵃ[k] P2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `AffineMap.linear_injective_iff`：linear_injective_iff (f : P1 ->ᵃ[k] P2) 
: Function.Injective f.linear ↔ Function.Injective f
· 使用定理 `AffineMap.linear_surjective_iff`：linear_surjective_iff (f : P1 ->ᵃ[k] P2
) : Function.Surjective f.linear ↔ Function.Surjective f
-/
theorem linear_bijective_iff (f : P1 →ᵃ[k] P2) :
    Function.Bijective f.linear ↔ Function.Bijective f :=
  and_congr f.linear_injective_iff f.linear_surjective_iff
/-
**AffineMap.image_vsub_image** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：image_vsub_image {s t : Set P1} (f : P1 ->ᵃ[k] P2) : f '' s -ᵥ f '' t = f.
linear '' (s -ᵥ t)
参数：f : P1 ->ᵃ[k] P2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
-/
theorem image_vsub_image {s t : Set P1} (f : P1 →ᵃ[k] P2) :
    f '' s -ᵥ f '' t = f.linear '' (s -ᵥ t) := by
  ext v
  simp only [Set.mem_vsub, Set.mem_image,
    exists_exists_and_eq_and, ← f.linearMap_vsub]
  grind

/-- The product of two affine maps is an affine map. -/
@[simps linear]
/-
**AffineMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：prod (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) : P1 ->ᵃ[k] P2 × P3 where toFun
参数：f : P1 ->ᵃ[k] P2；g : P1 ->ᵃ[k] P3。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two affine maps is an affine map.
-/
def prod (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) : P1 →ᵃ[k] P2 × P3 where
  toFun := Function.prod f g
  linear := f.linear.prod g.linear
  map_vadd' := by simp
/-
**AffineMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_prod (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) : prod f g = Function.prod 
f g
参数：f : P1 ->ᵃ[k] P2；g : P1 ->ᵃ[k] P3。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) : prod f g = Function.prod f g :=
  rfl

@[simp]
/-
**AffineMap.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：prod_apply (f : P1 ->ᵃ[k] P2) (g : P1 ->ᵃ[k] P3) (p : P1) : prod f g p = (
f p, g p)
参数：f : P1 ->ᵃ[k] P2；g : P1 ->ᵃ[k] P3；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_apply (f : P1 →ᵃ[k] P2) (g : P1 →ᵃ[k] P3) (p : P1) : prod f g p = (f p, g p) :=
  rfl

/-- `Prod.map` of two affine maps. -/
@[simps linear]
/-
**AffineMap.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：prodMap (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) : P1 × P3 ->ᵃ[k] P2 × P4 whe
re toFun
参数：f : P1 ->ᵃ[k] P2；g : P3 ->ᵃ[k] P4。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two affine maps.
-/
def prodMap (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) : P1 × P3 →ᵃ[k] P2 × P4 where
  toFun := Prod.map f g
  linear := f.linear.prodMap g.linear
  map_vadd' := by simp
/-
**AffineMap.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_prodMap (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) : ⇑(f.prodMap g) = Prod.
map f g
参数：f : P1 ->ᵃ[k] P2；g : P3 ->ᵃ[k] P4。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/-
**AffineMap.prodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：prodMap_apply (f : P1 ->ᵃ[k] P2) (g : P3 ->ᵃ[k] P4) (x) : f.prodMap g x = 
(f x.1, g x.2)
参数：f : P1 ->ᵃ[k] P2；g : P3 ->ᵃ[k] P4；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_apply (f : P1 →ᵃ[k] P2) (g : P3 →ᵃ[k] P4) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl

/-! ### Definition of `AffineMap.lineMap` and lemmas about it -/

/-- The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`. -/
/-
**AffineMap.lineMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：lineMap (p₀ p₁ : P1) : k ->ᵃ[k] P1
参数：p₀ p₁ : P1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine map from `k` to `P1` sending `0` to `p₀` and `1` to `p₁`.
-/
def lineMap (p₀ p₁ : P1) : k →ᵃ[k] P1 :=
  ((LinearMap.id : k →ₗ[k] k).smulRight (p₁ -ᵥ p₀)).toAffineMap +ᵥ const k k p₀

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.coe_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_lineMap (p₀ p₁ : P1) : (lineMap p₀ p₁ : k -> P1) = fun c => c • (p₁ -ᵥ
 p₀) +ᵥ p₀
参数：p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lineMap (p₀ p₁ : P1) : (lineMap p₀ p₁ : k → P1) = fun c => c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p
₀
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_apply_module'** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p
₀) + p₀
参数：p₀ p₁ : V1；c : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineMap_apply_module' (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = c • (p₁ - p₀) + p₀ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_apply_module** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀
 + c • p₁
参数：p₀ p₁ : V1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `_private.Mathlib.LinearAlgebra.AffineSpace.AffineMap.0.AffineMap.lineMap
_apply_module._abel_1_1`：∀ {k : Type u_2} {V1 : Type u_1} [inst : Ring k] [inst_
1 : AddCommGroup V1] [inst_2 : _root_.Module k V1] (p₀ p₁ : V1)   (c : k), c • p
₁ - c…
-/
theorem lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁ := by
  simp [lineMap_apply_module', smul_sub, sub_smul]; abel

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_apply_ring'** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a
参数：a b c : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lineMap_apply_ring' (a b c : k) : lineMap a b c = c * (b - a) + a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_apply_ring** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b
参数：a b c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_apply_module`：lineMap_apply_module (p₀ p₁ : V1) (c : k
) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
-/
theorem lineMap_apply_ring (a b c : k) : lineMap a b c = (1 - c) * a + c * b :=
  lineMap_apply_module a b c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_vadd_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • 
v +ᵥ p
参数：p : P1；v : V1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
-/
theorem lineMap_vadd_apply (p : P1) (v : V1) (c : k) : lineMap p (v +ᵥ p) c = c • v +ᵥ p := by
  rw [lineMap_apply, vadd_vsub]

@[simp]
/-
**AffineMap.lineMap_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_linear (p₀ p₁ : P1) : (lineMap p₀ p₁ : k ->ᵃ[k] P1).linear = Linea
rMap.id.smulRight (p₁ -ᵥ p₀)
参数：p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem lineMap_linear (p₀ p₁ : P1) :
    (lineMap p₀ p₁ : k →ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀) :=
  add_zero _

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_same_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_same_apply (p : P1) (c : k) : lineMap p p c = p
参数：p : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineMap_same_apply (p : P1) (c : k) : lineMap p p c = p := by
  simp [lineMap_apply]

@[simp]
/-
**AffineMap.lineMap_same** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_same (p : P1) : lineMap p p = const k k p
参数：p : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `AffineMap.lineMap_same_apply`：lineMap_same_apply (p : P1) (c : k) : line
Map p p c = p
-/
theorem lineMap_same (p : P1) : lineMap p p = const k k p :=
  ext <| lineMap_same_apply p

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀
参数：p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineMap_apply_zero (p₀ p₁ : P1) : lineMap p₀ p₁ (0 : k) = p₀ := by
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁
参数：p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀ p₁ (1 : k) = p₁ := by
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_eq_lineMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_eq_lineMap_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ 
c₂ : k} : lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lineMap_eq_lineMap_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} :
    lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂ := by
  rw [lineMap_apply, lineMap_apply, ← @vsub_eq_zero_iff_eq V1, vadd_vsub_vadd_cancel_right, ←
    sub_smul, smul_eq_zero, sub_eq_zero, vsub_eq_zero_iff_eq, or_comm, eq_comm]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_eq_left_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k}
 : lineMap p₀ p₁ c = p₀ ↔ p₀ = p₁ ∨ c = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_eq_lineMap_iff`：lineMap_eq_lineMap_iff [IsDomain k] [I
sTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} : lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c
₂ ↔ p₀ = p₁ ∨ c₁ = c₂
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lineMap_eq_left_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₀ ↔ p₀ = p₁ ∨ c = 0 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_zero]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_eq_right_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k
} : lineMap p₀ p₁ c = p₁ ↔ p₀ = p₁ ∨ c = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_eq_lineMap_iff`：lineMap_eq_lineMap_iff [IsDomain k] [I
sTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} : lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c
₂ ↔ p₀ = p₁ ∨ c₁ = c₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lineMap_eq_right_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c : k} :
    lineMap p₀ p₁ c = p₁ ↔ p₀ = p₁ ∨ c = 1 := by
  rw [← @lineMap_eq_lineMap_iff k V1, lineMap_apply_one]

set_option backward.isDefEq.respectTransparency false in
variable (k) in
/-
**AffineMap.lineMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_injective [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} (h : p₀ !
= p₁) : Function.Injective (lineMap p₀ p₁ : k -> P1)
参数：h : p₀ != p₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineMap.lineMap_eq_lineMap_iff`：lineMap_eq_lineMap_iff [IsDomain k] [I
sTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} : lineMap p₀ p₁ c₁ = lineMap p₀ p₁ c
₂ ↔ p₀ = p₁ ∨ c₁ = c₂
-/
theorem lineMap_injective [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} (h : p₀ ≠ p₁) :
    Function.Injective (lineMap p₀ p₁ : k → P1) := fun _c₁ _c₂ hc =>
  (lineMap_eq_lineMap_iff.mp hc).resolve_left h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.apply_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (c : k) : f (lineMap p₀ p₁ c
) = lineMap (f p₀) (f p₁) c
参数：f : P1 ->ᵃ[k] P2；p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem apply_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c := by
  simp [lineMap_apply]

@[simp]
/-
**AffineMap.comp_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：comp_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) : f.comp (lineMap p₀ p₁) = li
neMap (f p₀) (f p₁)
参数：f : P1 ->ᵃ[k] P2；p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem comp_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) :
    f.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁) :=
  ext <| f.apply_lineMap p₀ p₁

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.fst_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：fst_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1
 p₁.1 c
参数：p₀ p₁ : P1 × P2；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem fst_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).1 = lineMap p₀.1 p₁.1 c :=
  fst.apply_lineMap p₀ p₁ c

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.snd_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：snd_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2
 p₁.2 c
参数：p₀ p₁ : P1 × P2；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem snd_lineMap (p₀ p₁ : P1 × P2) (c : k) : (lineMap p₀ p₁ c).2 = lineMap p₀.2 p₁.2 c :=
  snd.apply_lineMap p₀ p₁ c
/-
**AffineMap.lineMap_symm** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_symm (p₀ p₁ : P1) : lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap 
(1 : k) (0 : k))
参数：p₀ p₁ : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.comp_lineMap`：comp_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) : f
.comp (lineMap p₀ p₁) = lineMap (f p₀) (f p₁)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineMap_symm (p₀ p₁ : P1) :
    lineMap p₀ p₁ = (lineMap p₁ p₀).comp (lineMap (1 : k) (0 : k)) := by
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_apply_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineM
ap p₁ p₀ c
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_symm`：lineMap_symm (p₀ p₁ : P1) : lineMap p₀ p₁ = (lin
eMap p₁ p₀).comp (lineMap (1 : k) (0 : k))
· 使用定理 `AffineMap.comp_apply`：comp_apply (f : P2 ->ᵃ[k] P3) (g : P1 ->ᵃ[k] P2) (
p : P1) : f.comp g p = f (g p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lineMap_apply_one_sub (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c := by
  rw [lineMap_symm p₀, comp_apply]
  congr
  simp [lineMap_apply]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -
ᵥ p₀)
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
-/
theorem lineMap_vsub_left (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀) :=
  vadd_vsub _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.left_vsub_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -
ᵥ p₁)
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀ -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁) := by
  rw [← neg_vsub_eq_vsub_rev, lineMap_vsub_left, ← smul_neg, neg_vsub_eq_vsub_rev]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.lineMap_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) 
• (p₀ -ᵥ p₁)
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
-/
theorem lineMap_vsub_right (p₀ p₁ : P1) (c : k) : lineMap p₀ p₁ c -ᵥ p₁ = (1 - c) • (p₀ -ᵥ p₁) := by
  rw [← lineMap_apply_one_sub, lineMap_vsub_left]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AffineMap.right_vsub_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) 
• (p₁ -ᵥ p₀)
参数：p₀ p₁ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
· 使用定理 `AffineMap.left_vsub_lineMap`：left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀
 -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁)
-/
theorem right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← lineMap_apply_one_sub, left_vsub_lineMap]

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_vadd_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) : lineMap v₁ v₂ c +
ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c
参数：v₁ v₂ : V1；p₁ p₂ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c :=
  ((fst : V1 × P1 →ᵃ[k] V1) +ᵥ (snd : V1 × P1 →ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_vsub_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) : lineMap p₁ p₂ c -ᵥ lineM
ap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c
参数：p₁ p₂ p₃ p₄ : P1；c : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) :
    lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c :=
  ((fst : P1 × P1 →ᵃ[k] P1) -ᵥ (snd : P1 × P1 →ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_lineMap_right** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [inst : Ring k] [inst_1 :
 AddCommGroup V1]   [inst_2 : _root_.Module k V1] [inst_3 : AddTorsor V1 P1] (p₀
 p₁ : P1) (c d : k),   (AffineMap.lineMap p₀ ((AffineMap.lineMap p₀ p₁) c)) d = 
(AffineMap.lineMap p₀ p₁) (d * c)
参数：p₀ p₁ : P1；c d : k；AffineMap.lineMap p₀ ((AffineMap.lineMap p₀ p₁) c)；AffineM
ap.lineMap p₀ p₁；d * c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lineMap_lineMap_right (p₀ p₁ : P1) (c d : k) :
    lineMap p₀ (lineMap p₀ p₁ c) d = lineMap p₀ p₁ (d * c) := by simp [lineMap_apply, mul_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.lineMap_lineMap_left** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} [inst : Ring k] [inst_1 :
 AddCommGroup V1]   [inst_2 : _root_.Module k V1] [inst_3 : AddTorsor V1 P1] (p₀
 p₁ : P1) (c d : k),   (AffineMap.lineMap ((AffineMap.lineMap p₀ p₁) c) p₁) d = 
(AffineMap.lineMap p₀ p₁) (1 - (1 - d) * (1 - c))
参数：p₀ p₁ : P1；c d : k；AffineMap.lineMap ((AffineMap.lineMap p₀ p₁) c) p₁；AffineM
ap.lineMap p₀ p₁；1 - (1 - d) * (1 - c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AffineMap.lineMap_lineMap_right`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : 
Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V1]   [inst_2 : _root_.Module k
 V1] [inst_3 : AddTor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lineMap_lineMap_left (p₀ p₁ : P1) (c d : k) :
    lineMap (lineMap p₀ p₁ c) p₁ d = lineMap p₀ p₁ (1 - (1 - d) * (1 - c)) := by
  simp_rw [lineMap_apply_one_sub, ← lineMap_apply_one_sub p₁, lineMap_lineMap_right]
/-
**AffineMap.lineMap_mono** 是 Mathlib 中的一个引理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_mono [LinearOrder k] [Preorder V1] [AddRightMono V1] [SMulPosMono 
k V1] {p₀ p₁ : V1} (h : p₀ <= p₁) : Monotone (lineMap (k
参数：h : p₀ <= p₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.addRightReflectLE_of_addRightMono`：∀ {N : Type u_2} [inst : Add
Group N] [inst_1 : LE N] [AddRightMono N], AddRightReflectLE N
-/
lemma lineMap_mono [LinearOrder k] [Preorder V1] [AddRightMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₀ ≤ p₁) :
    Monotone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices x • (p₁ - p₀) ≤ y • (p₁ - p₀) by simpa [lineMap]
  gcongr
  simpa
/-
**AffineMap.lineMap_anti** 是 Mathlib 中的一个引理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_anti [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k
 V1] {p₀ p₁ : V1} (h : p₁ <= p₀) : Antitone (lineMap (k
参数：h : p₁ <= p₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
lemma lineMap_anti [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₁ ≤ p₀) :
    Antitone (lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices y • (p₁ - p₀) ≤ x • (p₁ - p₀) by simpa [lineMap]
  rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg]
  gcongr
  simpa

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
/-
**AffineMap.decomp** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：decomp (f : V1 ->ᵃ[k] V2) : (f : V1 -> V2) = ⇑f.linear + fun _ => f 0
参数：f : V1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
Decomposition of an affine map in the special case when the point space and vect
or space
are the same.
-/
theorem decomp (f : V1 →ᵃ[k] V2) : (f : V1 → V2) = ⇑f.linear + fun _ => f 0 := by
  ext x
  calc
    f x = f.linear x +ᵥ f 0 := by rw [← f.map_vadd, vadd_eq_add, add_zero]
    _ = (f.linear + fun _ : V1 => f 0) x := rfl

/-- Decomposition of an affine map in the special case when the point space and vector space
are the same. -/
/-
**AffineMap.decomp'** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：decomp' (f : V1 ->ᵃ[k] V2) : (f.linear : V1 -> V2) = ⇑f - fun _ => f 0
参数：f : V1 ->ᵃ[k] V2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.decomp`：decomp (f : V1 ->ᵃ[k] V2) : (f : V1 -> V2) = ⇑f.linear
 + fun _ => f 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Decomposition of an affine map in the special case when the point space and vect
or space
are the same.
-/
theorem decomp' (f : V1 →ᵃ[k] V2) : (f.linear : V1 → V2) = ⇑f - fun _ => f 0 := by
  rw [decomp]
  simp only [map_zero, Pi.add_apply, add_sub_cancel_right, zero_add]
/-
**AffineMap.image_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：image_uIcc {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] (
f : k ->ᵃ[k] k) (a b : k) : f '' Set.uIcc a b = Set.uIcc (f a) (f b)
参数：f : k ->ᵃ[k] k；a b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_mul_const_uIcc`：image_mul_const_uIcc (a b c : α) : (· * a) '' 
[[b, c]] = [[b * a, c * a]]
· 使用定理 `Set.image_add_const_uIcc`：image_add_const_uIcc : (fun x => x + a) '' [[b
, c]] = [[b + a, c + a]]
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem image_uIcc {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
    (f : k →ᵃ[k] k) (a b : k) :
    f '' Set.uIcc a b = Set.uIcc (f a) (f b) := by
  have : ⇑f = (fun x => x + f 0) ∘ fun x => x * (f 1 - f 0) := by
    ext x
    change f x = x • (f 1 -ᵥ f 0) +ᵥ f 0
    rw [← f.linearMap_vsub, ← f.linear.map_smul, ← f.map_vadd]
    simp only [vsub_eq_sub, add_zero, mul_one, vadd_eq_add, sub_zero, smul_eq_mul]
  rw [this, Set.image_comp]
  simp only [Set.image_add_const_uIcc, Set.image_mul_const_uIcc, Function.comp_apply]

section

variable {ι : Type*} {V : ι → Type*} {P : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] [∀ i, AddTorsor (V i) (P i)]

/-- Evaluation at a point as an affine map. -/
/-
**AffineMap.proj** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：proj (i : ι) : (forall i : ι, P i) ->ᵃ[k] P i where toFun f
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point as an affine map.
-/
def proj (i : ι) : (∀ i : ι, P i) →ᵃ[k] P i where
  toFun f := f i
  linear := @LinearMap.proj k ι _ V _ _ i
  map_vadd' _ _ := rfl

@[simp]
/-
**AffineMap.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：proj_apply (i : ι) (f : forall i, P i) : @proj k _ ι V P _ _ _ i f = f i
参数：i : ι；f : forall i, P i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_apply (i : ι) (f : ∀ i, P i) : @proj k _ ι V P _ _ _ i f = f i :=
  rfl

@[simp]
/-
**AffineMap.proj_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k
 ι _ V _ _ i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_linear (i : ι) : (@proj k _ ι V P _ _ _ i).linear = @LinearMap.proj k ι _ V _ _ i :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.pi_lineMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_lineMap_apply (f g : forall i, P i) (c : k) (i : ι) : lineMap f g c i =
 lineMap (f i) (g i) c
参数：f g : forall i, P i；c : k；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem pi_lineMap_apply (f g : ∀ i, P i) (c : k) (i : ι) :
    lineMap f g c i = lineMap (f i) (g i) c :=
  (proj i : (∀ i, P i) →ᵃ[k] P i).apply_lineMap f g c

end

end AffineMap

namespace AffineMap

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

section Ring

variable [Ring k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2] [AffineSpace V2 P2]
variable [AddCommGroup V3] [AffineSpace V3 P3] [Module k V1] [Module k V2] [Module k V3]

section DistribMulAction

variable [Monoid R] [DistribMulAction R V2] [SMulCommClass k R V2]

/-- The space of affine maps to a module inherits an `R`-action from the action on its codomain. -/
/-
**AffineMap.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
形式化陈述：distribMulAction : DistribMulAction R (P1 ->ᵃ[k] V2) where smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of affine maps to a module inherits an `R`-action from the action on i
ts codomain.
-/
instance distribMulAction : DistribMulAction R (P1 →ᵃ[k] V2) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _

end DistribMulAction

section Module

variable [Semiring R] [Module R V2] [SMulCommClass k R V2]

/-- The space of affine maps taking values in an `R`-module is an `R`-module. -/
/-
**AffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `AffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of affine maps taking values in an `R`-module is an `R`-module.
-/
instance : Module R (P1 →ᵃ[k] V2) :=
  { AffineMap.distribMulAction with
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _
    zero_smul := fun _ => ext fun _ => zero_smul _ _ }

variable (R)

/-- The space of affine maps between two modules is linearly equivalent to the product of the
domain with the space of linear maps, by taking the value of the affine map at `(0 : V1)` and the
linear part.

See note [bundled maps over different rings] -/
@[simps]
/-
**AffineMap.toConstProdLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：toConstProdLinearMap : (V1 ->ᵃ[k] V2) ≃ₗ[R] V2 × (V1 ->ₗ[k] V2) where toFu
n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of affine maps between two modules is linearly equivalent to the produ
ct of the
domain with the space of linear maps, by taking the value of the affine map at `
(0 : V1)` and the
linear part.

See note [bundled maps over different rings]
-/
def toConstProdLinearMap : (V1 →ᵃ[k] V2) ≃ₗ[R] V2 × (V1 →ₗ[k] V2) where
  toFun f := ⟨f 0, f.linear⟩
  invFun p := p.2.toAffineMap + const k V1 p.1
  left_inv f := by
    ext
    rw [f.decomp]
    simp
  right_inv := by
    rintro ⟨v, f⟩
    ext <;> simp [const_linear]
  map_add' := by simp
  map_smul' := by simp

end Module

set_option backward.isDefEq.respectTransparency false in
/-- Interpolating between affine maps with `lineMap` commutes with evaluation. -/
@[simp]
/-
**AffineMap.lineMap_apply'** 是 Mathlib 中的一个引理，位于命名空间 `AffineMap`。
形式化陈述：lineMap_apply' [SMulCommClass k k V2] (f g : P1 ->ᵃ[k] P2) (c : k) (p : P1
) : lineMap f g c p = lineMap (f p) (g p) c
参数：f g : P1 ->ᵃ[k] P2；c : k；p : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Interpolating between affine maps with `lineMap` commutes with evaluation.
-/
lemma lineMap_apply' [SMulCommClass k k V2] (f g : P1 →ᵃ[k] P2) (c : k)
    (p : P1) : lineMap f g c p = lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

section Pi

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AffineSpace (φv i) (φp i)]
/-- `pi` construction for affine maps. From a family of affine maps it produces an affine
map into a family of affine spaces.

This is the affine version of `LinearMap.pi`.
-/
@[simps linear]
/-
**AffineMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：pi (f : (i : ι) -> (P1 ->ᵃ[k] φp i)) : P1 ->ᵃ[k] ((i : ι) -> φp i) where t
oFun m a
参数：f : (i : ι) -> (P1 ->ᵃ[k] φp i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi` construction for affine maps. From a family of affine maps it produces an a
ffine
map into a family of affine spaces.

This is the affine version of `LinearMap.pi`.
-/
def pi (f : (i : ι) → (P1 →ᵃ[k] φp i)) : P1 →ᵃ[k] ((i : ι) → φp i) where
  toFun m a := f a m
  linear := LinearMap.pi (fun a ↦ (f a).linear)
  map_vadd' _ _ := funext fun _ ↦ map_vadd _ _ _

--fp for when the image is a dependent AffineSpace φp i, fv for when the
--image is a Module φv i, f' for when the image isn't dependent.
variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

@[simp]
/-
**AffineMap.pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_apply (c : P1) (i : ι) : pi fp c i = fp i c
参数：c : P1；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_apply (c : P1) (i : ι) : pi fp c i = fp i c :=
  rfl
/-
**AffineMap.pi_comp** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_comp (g : P3 ->ᵃ[k] P1) : (pi fp).comp g = pi (fun i => (fp i).comp g)
参数：g : P3 ->ᵃ[k] P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_comp (g : P3 →ᵃ[k] P1) : (pi fp).comp g = pi (fun i => (fp i).comp g) :=
  rfl
/-
**AffineMap.pi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_eq_zero : pi fv = 0 ↔ forall i, fv i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem pi_eq_zero : pi fv = 0 ↔ ∀ i, fv i = 0 := by
  simp only [AffineMap.ext_iff, funext_iff, pi_apply]
  exact forall_comm
/-
**AffineMap.pi_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_zero : pi (fun _ => 0 : (i : ι) -> P1 ->ᵃ[k] φv i) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem pi_zero : pi (fun _ ↦ 0 : (i : ι) → P1 →ᵃ[k] φv i) = 0 := by
  ext; rfl
/-
**AffineMap.proj_pi** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：proj_pi (i : ι) : (proj i).comp (pi fp) = fp i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
-/
theorem proj_pi (i : ι) : (proj i).comp (pi fp) = fp i :=
  ext fun _ => rfl
section Ext

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

/-- Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and at zero. Analogous to `LinearMap.pi_ext`. See also `pi_ext_nonempty`,
  which instead of agreement at zero requires `Nonempty ι`. -/
/-
**AffineMap.pi_ext_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_ext_zero (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : 
f 0 = g 0) : f = g
参数：h : forall i x, f (Pi.single i x) = g (Pi.single i x)；h₂ : f 0 = g 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext_linear`：ext_linear {f g : P1 ->ᵃ[k] P2} (h₁ : f.linear = g
.linear) {p : P1} (h₂ : f p = g p) : f = g
· 使用定理 `LinearMap.pi_ext`：pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.sing
le i x)) : f = g
· 使用定理 `AffineMap.map_vadd`：map_vadd (f : P1 ->ᵃ[k] P2) (p : P1) (v : V1) : f (v
 +ᵥ p) = f.linear v +ᵥ f p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `vadd_right_cancel_iff`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup 
G] [T : AddTorsor G P] {g₁ g₂ : G} (p : P), g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b

--- 原说明 ---
Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are
 equal in their
  operation on `Pi.single` and at zero. Analogous to `LinearMap.pi_ext`. See als
o `pi_ext_nonempty`,
  which instead of agreement at zero requires `Nonempty ι`.
-/
theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  apply ext_linear
  · apply LinearMap.pi_ext
    intro i x
    have s₁ := h i x
    have s₂ := f.map_vadd 0 (Pi.single i x)
    have s₃ := g.map_vadd 0 (Pi.single i x)
    rw [vadd_eq_add, add_zero] at s₂ s₃
    replace h₂ := h i 0
    simp only [Pi.single_zero] at h₂
    rwa [s₂, s₃, h₂, vadd_right_cancel_iff] at s₁
  · exact h₂

/-- Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are equal in their
  operation on `Pi.single` and `ι` is nonempty.  Analogous to `LinearMap.pi_ext`. See also
  `pi_ext_zero`, which instead of `Nonempty ι` requires agreement at 0. -/
/-
**AffineMap.pi_ext_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_ext_nonempty [Nonempty ι] (h : forall i x, f (Pi.single i x) = g (Pi.si
ngle i x)) : f = g
参数：h : forall i x, f (Pi.single i x) = g (Pi.single i x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.pi_ext_zero`：pi_ext_zero (h : forall i x, f (Pi.single i x) = 
g (Pi.single i x)) (h₂ : f 0 = g 0) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.single_zero`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) → Ze
ro (M i)] [inst_1 : DecidableEq ι] (i : ι), Pi.single i 0 = 0

--- 原说明 ---
Two affine maps from a Pi-type of modules `(i : ι) → φv i` are equal if they are
 equal in their
  operation on `Pi.single` and `ι` is nonempty.  Analogous to `LinearMap.pi_ext`
. See also
  `pi_ext_zero`, which instead of `Nonempty ι` requires agreement at 0.
-/
theorem pi_ext_nonempty [Nonempty ι] (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) :
    f = g := by
  apply pi_ext_zero h
  inhabit ι
  rw [← Pi.single_zero default]
  apply h

/-- This is used as the ext lemma instead of `AffineMap.pi_ext_nonempty` for reasons explained in
note [partially-applied ext lemmas]. Analogous to `LinearMap.pi_ext'` -/
@[ext (iff := false)]
/-
**AffineMap.pi_ext_nonempty'** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：pi_ext_nonempty' [Nonempty ι] (h : forall i, f.comp (LinearMap.single _ _ 
i).toAffineMap = g.comp (LinearMap.single _ _ i).toAffineMap) : f = g
参数：h : forall i, f.comp (LinearMap.single _ _ i).toAffineMap = g.comp (LinearMap
.single _ _ i).toAffineMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.pi_ext_nonempty`：pi_ext_nonempty [Nonempty ι] (h : forall i x,
 f (Pi.single i x) = g (Pi.single i x)) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.congr_fun`：∀ {k : Type u_1} {V1 : Type u_2} {P1 : Type u_3} {V
2 : Type u_4} {P2 : Type u_5} [inst : Ring k]   [inst_1 : AddCommGroup V1] [inst
_2 : _roo…

--- 原说明 ---
This is used as the ext lemma instead of `AffineMap.pi_ext_nonempty` for reasons
 explained in
note [partially-applied ext lemmas]. Analogous to `LinearMap.pi_ext'`
-/
theorem pi_ext_nonempty' [Nonempty ι] (h : ∀ i, f.comp (LinearMap.single _ _ i).toAffineMap =
    g.comp (LinearMap.single _ _ i).toAffineMap) : f = g := by
  refine pi_ext_nonempty fun i x => ?_
  convert! AffineMap.congr_fun (h i) x

end Ext

end Pi

end Ring

section CommRing

variable [CommRing k] [AddCommGroup V1] [AffineSpace V1 P1] [AddCommGroup V2]
variable [Module k V1] [Module k V2]

/-- `homothety c r` is the homothety (also known as dilation) about `c` with scale factor `r`. -/
/-
**AffineMap.homothety** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：homothety (c : P1) (r : k) : P1 ->ᵃ[k] P1
参数：c : P1；r : k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`homothety c r` is the homothety (also known as dilation) about `c` with scale f
actor `r`.
-/
def homothety (c : P1) (r : k) : P1 →ᵃ[k] P1 :=
  r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c
/-
**AffineMap.homothety_def** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_def (c : P1) (r : k) : homothety c r = r • (id k P1 -ᵥ const k P
1 c) +ᵥ const k P1 c
参数：c : P1；r : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homothety_def (c : P1) (r : k) :
    homothety c r = r • (id k P1 -ᵥ const k P1 c) +ᵥ const k P1 c :=
  rfl
/-
**AffineMap.coe_homothety** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_homothety (c : P1) (r : k) : homothety c r = fun p => r • (p -ᵥ c) +ᵥ 
c
参数：c : P1；r : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_homothety (c : P1) (r : k) : homothety c r = fun p => r • (p -ᵥ c) +ᵥ c :=
  rfl
/-
**AffineMap.homothety_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c 
: V1) +ᵥ c
参数：c : P1；r : k；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homothety_apply (c : P1) (r : k) (p : P1) : homothety c r p = r • (p -ᵥ c : V1) +ᵥ c :=
  rfl

@[simp]
/-
**AffineMap.homothety_linear** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_linear (c : P1) (r : k) : (homothety c r).linear = r • LinearMap
.id
参数：c : P1；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_linear (c : P1) (r : k) : (homothety c r).linear = r • LinearMap.id := by
  simp [homothety]

set_option backward.isDefEq.respectTransparency false in
/-
**AffineMap.homothety_eq_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_eq_lineMap (c : P1) (r : k) (p : P1) : homothety c r p = lineMap
 c p r
参数：c : P1；r : k；p : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homothety_eq_lineMap (c : P1) (r : k) (p : P1) : homothety c r p = lineMap c p r :=
  rfl

@[simp]
/-
**AffineMap.homothety_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_one (c : P1) : homothety c (1 : k) = id k P1
参数：c : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_one (c : P1) : homothety c (1 : k) = id k P1 := by
  ext p
  simp [homothety_apply]

@[simp]
/-
**AffineMap.homothety_apply_same** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_apply_same (c : P1) (r : k) : homothety c r c = c
参数：c : P1；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.lineMap_same_apply`：lineMap_same_apply (p : P1) (c : k) : line
Map p p c = p
-/
theorem homothety_apply_same (c : P1) (r : k) : homothety c r c = c :=
  lineMap_same_apply c r
/-
**AffineMap.homothety_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) : homothety c (r₁ * r₂) 
p = homothety c r₁ (homothety c r₂ p)
参数：c : P1；r₁ r₂ : k；p : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p) := by
  simp only [homothety_apply, mul_smul, vadd_vsub]
/-
**AffineMap.homothety_mul** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_mul (c : P1) (r₁ r₂ : k) : homothety c (r₁ * r₂) = (homothety c 
r₁).comp (homothety c r₂)
参数：c : P1；r₁ r₂ : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `AffineMap.homothety_mul_apply`：homothety_mul_apply (c : P1) (r₁ r₂ : k) 
(p : P1) : homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p)
-/
theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂) :=
  ext <| homothety_mul_apply c r₁ r₂

@[simp]
/-
**AffineMap.homothety_zero** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c
参数：c : P1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.ext`：ext {f g : P1 ->ᵃ[k] P2} (h : forall p, f p = g p) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_zero (c : P1) : homothety c (0 : k) = const k P1 c := by
  ext p
  simp [homothety_apply]

@[simp]
/-
**AffineMap.homothety_add** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_add (c : P1) (r₁ r₂ : k) : homothety c (r₁ + r₂) = r₁ • (id k P1
 -ᵥ const k P1 c) +ᵥ homothety c r₂
参数：c : P1；r₁ r₂ : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_add (c : P1) (r₁ r₂ : k) :
    homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ const k P1 c) +ᵥ homothety c r₂ := by
  simp only [homothety_def, add_smul, vadd_vadd]
/-
**AffineMap.homothety_eq_iff_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`
。
形式化陈述：homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) 
: homothety c r₁ p = q ↔ homothety c r₂ q = p
参数：h : r₁ * r₂ = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.homothety_mul_apply`：homothety_mul_apply (c : P1) (r₁ r₂ : k) 
(p : P1) : homothety c (r₁ * r₂) p = homothety c r₁ (homothety c r₂ p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_one_comm`：∀ {M : Type u_2} [inst : MulOne M] [IsDedekindFiniteMon
oid M] {a b : M}, a * b = 1 ↔ b * a = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `AffineMap.homothety_one`：homothety_one (c : P1) : homothety c (1 : k) = 
id k P1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    homothety c r₁ p = q ↔ homothety c r₂ q = p := by
  obtain h' : r₂ * r₁ = 1 := mul_eq_one_comm.mp h
  refine ⟨fun h1 ↦ ?_, fun h1 ↦ ?_⟩
  all_goals
    rw [← h1, ← homothety_mul_apply]
    simp [h, h']
/-
**AffineMap.homothety_injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P
1) {r : k} (hr : r != 0) : Function.Injective (homothety c r)
参数：c : P1；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (homothety c r) :=
  fun _ _ h ↦ by simpa [homothety_def, hr] using h

@[simp]
/-
**AffineMap.homothety_inj** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r 
: k} (hr : r != 0) {p q : P1} : homothety c r p = homothety c r q ↔ p = q
参数：c : P1；hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AffineMap.homothety_injective`：homothety_injective [Module.IsTorsionFree
 k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r != 0) : Function.Injective (
homothety c r)
-/
theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r ≠ 0)
    {p q : P1} :
    homothety c r p = homothety c r q ↔ p = q :=
  (homothety_injective c hr).eq_iff

/-- `homothety` as a multiplicative monoid homomorphism. -/
/-
**AffineMap.homothetyHom** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：homothetyHom (c : P1) : k ->* P1 ->ᵃ[k] P1 where toFun
参数：c : P1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.homothety_one`：homothety_one (c : P1) : homothety c (1 : k) = 
id k P1
· 使用定理 `AffineMap.homothety_mul`：homothety_mul (c : P1) (r₁ r₂ : k) : homothety 
c (r₁ * r₂) = (homothety c r₁).comp (homothety c r₂)

--- 原说明 ---
`homothety` as a multiplicative monoid homomorphism.
-/
def homothetyHom (c : P1) : k →* P1 →ᵃ[k] P1 where
  toFun := homothety c
  map_one' := homothety_one c
  map_mul' := homothety_mul c

@[simp]
/-
**AffineMap.coe_homothetyHom** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_homothetyHom (c : P1) : ⇑(homothetyHom c : k ->* _) = homothety c
参数：c : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_homothetyHom (c : P1) : ⇑(homothetyHom c : k →* _) = homothety c :=
  rfl

/-- `homothety` as an affine map. -/
/-
**AffineMap.homothetyAffine** 是 Mathlib 中的一个定义，位于命名空间 `AffineMap`。
形式化陈述：homothetyAffine (c : P1) : k ->ᵃ[k] P1 ->ᵃ[k] P1
参数：c : P1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`homothety` as an affine map.
-/
def homothetyAffine (c : P1) : k →ᵃ[k] P1 →ᵃ[k] P1 :=
  ⟨homothety c, (LinearMap.lsmul k _).flip (id k P1 -ᵥ const k P1 c),
    Function.swap (homothety_add c)⟩

@[simp]
/-
**AffineMap.coe_homothetyAffine** 是 Mathlib 中的一个定理，位于命名空间 `AffineMap`。
形式化陈述：coe_homothetyAffine (c : P1) : ⇑(homothetyAffine c : k ->ᵃ[k] _) = homothe
ty c
参数：c : P1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_homothetyAffine (c : P1) : ⇑(homothetyAffine c : k →ᵃ[k] _) = homothety c :=
  rfl

end CommRing

end AffineMap

section

variable {𝕜 E F : Type*} [Ring 𝕜] [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

/-- Applying an affine map to an affine combination of two points yields an affine combination of
the images. -/
/-
**Convex.combo_affine_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.combo_affine_apply {x y : E} {a b : 𝕜} {f : E ->ᵃ[𝕜] F} (h : a + b 
= 1) : f (a • x + b • y) = a • f x + b • f y
参数：h : a + b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.combo_eq_smul_sub_add`：Convex.combo_eq_smul_sub_add [Module R M] 
{x y : M} {a b : R} (h : a + b = 1) : a • x + b • y = b • (y - x) + x
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c

--- 原说明 ---
Applying an affine map to an affine combination of two points yields an affine c
ombination of
the images.
-/
theorem Convex.combo_affine_apply {x y : E} {a b : 𝕜} {f : E →ᵃ[𝕜] F} (h : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  simp only [Convex.combo_eq_smul_sub_add h, ← vsub_eq_sub]
  exact f.apply_lineMap _ _ _

end

