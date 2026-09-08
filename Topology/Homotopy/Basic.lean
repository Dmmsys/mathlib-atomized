/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Homotopy between functions

In this file, we define a homotopy between two functions `f₀` and `f₁`. First we define
`ContinuousMap.Homotopy` between the two functions, with no restrictions on the intermediate
maps. Then, as in the formalisation in HOL-Analysis, we define
`ContinuousMap.HomotopyWith f₀ f₁ P`, for homotopies between `f₀` and `f₁`, where the
intermediate maps satisfy the predicate `P`. Finally, we define
`ContinuousMap.HomotopyRel f₀ f₁ S`, for homotopies between `f₀` and `f₁` which are fixed
on `S`.

## Definitions

* `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies between `f₀` and `f₁`.
* `ContinuousMap.HomotopyWith f₀ f₁ P` is the type of homotopies between `f₀` and `f₁`, where
  the intermediate maps satisfy the predicate `P`.
* `ContinuousMap.HomotopyRel f₀ f₁ S` is the type of homotopies between `f₀` and `f₁` which
  are fixed on `S`.

For each of the above, we have

* `refl f`, which is the constant homotopy from `f` to `f`.
* `symm F`, which reverses the homotopy `F`. For example, if `F : ContinuousMap.Homotopy f₀ f₁`,
  then `F.symm : ContinuousMap.Homotopy f₁ f₀`.
* `trans F G`, which concatenates the homotopies `F` and `G`. For example, if
  `F : ContinuousMap.Homotopy f₀ f₁` and `G : ContinuousMap.Homotopy f₁ f₂`, then
  `F.trans G : ContinuousMap.Homotopy f₀ f₂`.

We also define the relations

* `ContinuousMap.Homotopic f₀ f₁` is defined to be `Nonempty (ContinuousMap.Homotopy f₀ f₁)`
* `ContinuousMap.HomotopicWith f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyWith f₀ f₁ P)`
* `ContinuousMap.HomotopicRel f₀ f₁ P` is defined to be
  `Nonempty (ContinuousMap.HomotopyRel f₀ f₁ P)`

and for `ContinuousMap.homotopic` and `ContinuousMap.homotopic_rel`, we also define the
`setoid` and `quotient` in `C(X, Y)` by these relations.

## References

- [HOL-Analysis formalisation](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Homotopy.html)
-/

@[expose] public section

noncomputable section

universe u v w x

variable {F : Type*} {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

open unitInterval

namespace ContinuousMap

/-- `ContinuousMap.Homotopy f₀ f₁` is the type of homotopies from `f₀` to `f₁`.

When possible, instead of parametrizing results over `(f : ContinuousMap.Homotopy f₀ f₁)`,
you should parametrize over `{F : Type*} [HomotopyLike F f₀ f₁] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMap.HomotopyLike`. -/
@[wikidata Q746083]
/-
**ContinuousMap.Homotopy** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u} →   {Y : Type v} → [inst : TopologicalSpace X] → [inst_1 : To
pologicalSpace Y] → C(X, Y) → C(X, Y) → Type (max u v)
参数：X, Y；X, Y；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMap.Homotopy f₀ f₁` is the type of homotopies from `f₀` to `f₁`.

When possible, instead of parametrizing results over `(f : ContinuousMap.Homotop
y f₀ f₁)`,
you should parametrize over `{F : Type*} [HomotopyLike F f₀ f₁] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMap.HomotopyLike`
.
-/
structure Homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) where
  /-- value of the homotopy at 0 -/
  map_zero_left : ∀ x, toFun (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left : ∀ x, toFun (1, x) = f₁ x

section

/-- `ContinuousMap.HomotopyLike F f₀ f₁` states that `F` is a type of homotopies between `f₀` and
`f₁`.

You should extend this class when you extend `ContinuousMap.Homotopy`. -/
/-
**ContinuousMap.HomotopyLike** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMap`。
形式化陈述：{X : outParam (Type u_3)} →   {Y : outParam (Type u_4)} →     [inst : Topo
logicalSpace X] →       [inst_1 : TopologicalSpace Y] →         (F : Type u_5) →
 outParam C(X, Y) → outParam C(X, Y) → [FunLike F (↑unitInterval × X) Y] → Prop
参数：Type u_3；Type u_4；F : Type u_5；X, Y；X, Y；↑unitInterval × X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMap.HomotopyLike F f₀ f₁` states that `F` is a type of homotopies bet
ween `f₀` and
`f₁`.

You should extend this class when you extend `ContinuousMap.Homotopy`.
-/
class HomotopyLike {X Y : outParam Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : Type*) (f₀ f₁ : outParam <| C(X, Y)) [FunLike F (I × X) Y] : Prop
    extends ContinuousMapClass F (I × X) Y where
  /-- value of the homotopy at 0 -/
  map_zero_left (f : F) : ∀ x, f (0, x) = f₀ x
  /-- value of the homotopy at 1 -/
  map_one_left (f : F) : ∀ x, f (1, x) = f₁ x

end

namespace Homotopy

section

variable {f₀ f₁ : C(X, Y)}

/-
**ContinuousMap.Homotopy.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.Ho
motopy`。
形式化陈述：instFunLike : FunLike (Homotopy f₀ f₁) (I × X) Y where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Homotopy f₀ f₁) (I × X) Y where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
/-
**ContinuousMap.Homotopy.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomotopyLike (Homotopy f₀ f₁) f₀ f₁ where
  map_continuous f := f.continuous_toFun
  map_zero_left f := f.map_zero_left
  map_one_left f := f.map_one_left

@[ext]
/-
**ContinuousMap.Homotopy.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopy`。
形式化陈述：ext {F G : Homotopy f₀ f₁} (h : forall x, F x = G x) : F = G
参数：h : forall x, F x = G x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {F G : Homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ContinuousMap.Homotopy.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Ho
motopy.Simps`。
形式化陈述：{X : Type u} →   {Y : Type v} →     [inst : TopologicalSpace X] →       [i
nst_1 : TopologicalSpace Y] → {f₀ f₁ : C(X, Y)} → f₀.Homotopy f₁ → ↑unitInterval
 × X → Y
参数：X, Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.apply (F : Homotopy f₀ f₁) : I × X → Y :=
  F

initialize_simps_projections Homotopy (toFun → apply, -toContinuousMap)

/-- Deprecated. Use `map_continuous` instead. -/
/-
**ContinuousMap.Homotopy.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homotopy f₁), Continuous ⇑F
参数：X, Y；F : f₀.Homotopy f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun

--- 原说明 ---
Deprecated. Use `map_continuous` instead.
-/
protected theorem continuous (F : Homotopy f₀ f₁) : Continuous F :=
  F.continuous_toFun

@[simp]
/-
**ContinuousMap.Homotopy.apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
形式化陈述：apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x
参数：F : Homotopy f₀ f₁；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.map_zero_left`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (self : 
f₀.Homotopy f₁) (x : X), s…
-/
theorem apply_zero (F : Homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
/-
**ContinuousMap.Homotopy.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x
参数：F : Homotopy f₀ f₁；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.map_one_left`：∀ {X : Type u} {Y : Type v} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (self : f
₀.Homotopy f₁) (x : X), s…
-/
theorem apply_one (F : Homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

@[simp]
/-
**ContinuousMap.Homotopy.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap.Homotopy`。
形式化陈述：coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F
参数：F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap (F : Homotopy f₀ f₁) : ⇑F.toContinuousMap = F :=
  rfl

/-- Currying a homotopy to a continuous function from `I` to `C(X, Y)`.
-/
/-
**ContinuousMap.Homotopy.curry** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy
`。
形式化陈述：curry (F : Homotopy f₀ f₁) : C(I, C(X, Y))
参数：F : Homotopy f₀ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Currying a homotopy to a continuous function from `I` to `C(X, Y)`.
-/
def curry (F : Homotopy f₀ f₁) : C(I, C(X, Y)) :=
  F.toContinuousMap.curry

@[simp]
/-
**ContinuousMap.Homotopy.curry_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Ho
motopy`。
形式化陈述：curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x)
参数：F : Homotopy f₀ f₁；t : I；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply (F : Homotopy f₀ f₁) (t : I) (x : X) : F.curry t x = F (t, x) :=
  rfl
/-
**ContinuousMap.Homotopy.curry_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homotopy f₁), F.curry 0 = f₀
参数：X, Y；F : f₀.Homotopy f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem curry_zero (F : Homotopy f₀ f₁) : F.curry 0 = f₀ := by ext; simp
/-
**ContinuousMap.Homotopy.curry_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homotopy f₁), F.curry 1 = f₁
参数：X, Y；F : f₀.Homotopy f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem curry_one (F : Homotopy f₀ f₁) : F.curry 1 = f₁ := by ext; simp

/-- Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
/-
**ContinuousMap.Homotopy.extend** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotop
y`。
形式化陈述：extend (F : Homotopy f₀ f₁) : C(Real, C(X, Y))
参数：F : Homotopy f₀ f₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ

--- 原说明 ---
Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : Homotopy f₀ f₁) : C(ℝ, C(X, Y)) :=
  F.curry.IccExtend zero_le_one
/-
**ContinuousMap.Homotopy.extend_apply_of_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap.Homotopy`。
形式化陈述：extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : Real} (ht : t <= 0) (x :
 X) : F.extend t x = f₀ x
参数：F : Homotopy f₀ f₁；ht : t <= 0；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.IccExtend_of_le_left`：IccExtend_of_le_left (f : Icc a b -> β) (hx : 
x <= a) : IccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩
-/
theorem extend_apply_of_le_zero (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ≤ 0) (x : X) :
    F.extend t x = f₀ x := by
  rw [← F.apply_zero]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_le_left (zero_le_one' ℝ) F.curry ht) x
/-
**ContinuousMap.Homotopy.extend_apply_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMap.Homotopy`。
形式化陈述：extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : Real} (ht : 1 <= t) (x : 
X) : F.extend t x = f₁ x
参数：F : Homotopy f₀ f₁；ht : 1 <= t；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.IccExtend_of_right_le`：IccExtend_of_right_le (f : Icc a b -> β) (hx 
: b <= x) : IccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩
-/
theorem extend_apply_of_one_le (F : Homotopy f₀ f₁) {t : ℝ} (ht : 1 ≤ t) (x : X) :
    F.extend t x = f₁ x := by
  rw [← F.apply_one]
  exact ContinuousMap.congr_fun (Set.IccExtend_of_right_le (zero_le_one' ℝ) F.curry ht) x
/-
**ContinuousMap.Homotopy.extend_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap.Homotopy`。
形式化陈述：extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (
t, x)
参数：F : Homotopy f₀ f₁；t : I；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `Set.IccExtend_val`：IccExtend_val (f : Icc a b -> β) (x : Icc a b) : IccE
xtend h f x = f x
-/
theorem extend_apply_coe (F : Homotopy f₀ f₁) (t : I) (x : X) : F.extend t x = F (t, x) :=
  ContinuousMap.congr_fun (Set.IccExtend_val (zero_le_one' ℝ) F.curry t) x

@[simp]
/-
**ContinuousMap.Homotopy.extend_of_mem_I** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.Homotopy`。
形式化陈述：extend_of_mem_I (F : Homotopy f₀ f₁) {t : Real} (ht : t in I) : F.extend t
 = F.curry ⟨t, ht⟩
参数：F : Homotopy f₀ f₁；ht : t in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IccExtend_of_mem`：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc
 a b) : IccExtend h f x = f ⟨x, hx⟩
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
-/
theorem extend_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) :
    F.extend t = F.curry ⟨t, ht⟩ :=
  Set.IccExtend_of_mem (zero_le_one' ℝ) F.curry ht
/-
**ContinuousMap.Homotopy.extend_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Ho
motopy`。
形式化陈述：extend_zero (F : Homotopy f₀ f₁) : F.extend 0 = f₀
参数：F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousMap.Homotopy.extend_of_mem_I`：extend_of_mem_I (F : Homotopy f₀
 f₁) {t : Real} (ht : t in I) : F.extend t = F.curry ⟨t, ht⟩
· 使用定理 `ContinuousMap.Homotopy.curry_zero`：∀ {X : Type u} {Y : Type v} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Hom
otopy f₁), F.curry 0 = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_zero (F : Homotopy f₀ f₁) : F.extend 0 = f₀ := by simp
/-
**ContinuousMap.Homotopy.extend_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
形式化陈述：extend_one (F : Homotopy f₀ f₁) : F.extend 1 = f₁
参数：F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousMap.Homotopy.extend_of_mem_I`：extend_of_mem_I (F : Homotopy f₀
 f₁) {t : Real} (ht : t in I) : F.extend t = F.curry ⟨t, ht⟩
· 使用定理 `ContinuousMap.Homotopy.curry_one`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homo
topy f₁), F.curry 1 = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_one (F : Homotopy f₀ f₁) : F.extend 1 = f₁ := by simp
/-
**ContinuousMap.Homotopy.extend_apply_of_mem_I** 是 Mathlib 中的一个定理，位于命名空间 `Contin
uousMap.Homotopy`。
形式化陈述：extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : Real} (ht : t in I) (x : X
) : F.extend t x = F (⟨t, ht⟩, x)
参数：F : Homotopy f₀ f₁；ht : t in I；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.extend_of_mem_I`：extend_of_mem_I (F : Homotopy f₀
 f₁) {t : Real} (ht : t in I) : F.extend t = F.curry ⟨t, ht⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_apply_of_mem_I (F : Homotopy f₀ f₁) {t : ℝ} (ht : t ∈ I) (x : X) :
    F.extend t x = F (⟨t, ht⟩, x) := by
  simp [ht]
/-
**ContinuousMap.Homotopy.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   {F G : f₀.Homotopy f₁}, F = G → ∀ (x : ↑unitInte
rval × X), F x = G x
参数：X, Y；x : ↑unitInterval × X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.congr_fun`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f g : C(X, Y)},   f = g → ∀ (x : X),
 f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem congr_fun {F G : Homotopy f₀ f₁} (h : F = G) (x : I × X) : F x = G x :=
  ContinuousMap.congr_fun (congr_arg _ h) x
/-
**ContinuousMap.Homotopy.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homotopy f₁) {x y : ↑unitInterval × X}, 
x = y → F x = F y
参数：X, Y；F : f₀.Homotopy f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.congr_arg`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)) {x y : X},   x = y → f 
x = f y
-/
protected theorem congr_arg (F : Homotopy f₀ f₁) {x y : I × X} (h : x = y) : F x = F y :=
  F.toContinuousMap.congr_arg h

end

/-- Given a continuous function `f`, we can define a `ContinuousMap.Homotopy f f` by
`F (t, x) = f x`
-/
@[simps]
/-
**ContinuousMap.Homotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`
。
形式化陈述：refl (f : C(X, Y)) : Homotopy f f where toFun x
参数：f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous function `f`, we can define a `ContinuousMap.Homotopy f f` by
`F (t, x) = f x`
-/
def refl (f : C(X, Y)) : Homotopy f f where
  toFun x := f x.2
  map_zero_left _ := rfl
  map_one_left _ := rfl
/-
**ContinuousMap.Homotopy.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `ContinuousMap.Homotopy f₀ f₁`, we can define a `ContinuousMap.Homotopy f₁ f₀` by
reversing the homotopy.
-/
@[simps]
/-
**ContinuousMap.Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`
。
形式化陈述：symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where toFun x
参数：X, Y；F : Homotopy f₀ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `ContinuousMap.Homotopy f₀ f₁`, we can define a `ContinuousMap.Homotopy 
f₁ f₀` by
reversing the homotopy.
-/
def symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  toFun x := F (σ x.1, x.2)
  map_zero_left := by simp
  map_one_left := by norm_num

@[simp]
/-
**ContinuousMap.Homotopy.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topy`。
形式化陈述：symm_symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : F.symm.symm = F
参数：X, Y；F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.ext`：ext {F G : Homotopy f₀ f₁} (h : forall x, F 
x = G x) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.symm_apply`：∀ {X : Type u} {Y : Type v} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Hom
otopy f₁) (x : ↑unitInt…
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext
  simp
/-
**ContinuousMap.Homotopy.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.Homotopy`。
形式化陈述：symm_bijective {f₀ f₁ : C(X, Y)} : Function.Bijective (Homotopy.symm : Hom
otopy f₀ f₁ -> Homotopy f₁ f₀)
参数：X, Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousMap.Homotopy.symm_symm`：symm_symm {f₀ f₁ : C(X, Y)} (F : Homot
opy f₀ f₁) : F.symm.symm = F
-/
theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `ContinuousMap.Homotopy f₀ f₁` and `ContinuousMap.Homotopy f₁ f₂`, we can define a
`ContinuousMap.Homotopy f₀ f₂` by putting the first homotopy on `[0, 1/2]` and the second
on `[1/2, 1]`.
-/
/-
**ContinuousMap.Homotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy
`。
形式化陈述：trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Hom
otopy f₀ f₂ where toFun x
参数：X, Y；F : Homotopy f₀ f₁；G : Homotopy f₁ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ContinuousMap.Homotopy f₀ f₁` and `ContinuousMap.Homotopy f₁ f₂`, we can 
define a
`ContinuousMap.Homotopy f₀ f₂` by putting the first homotopy on `[0, 1/2]` and t
he second
on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homotopy f₀ f₂ where
  toFun x := if (x.1 : ℝ) ≤ 1 / 2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2
  continuous_toFun :=
    continuous_if_le (by fun_prop) continuous_const
      (F.continuous.comp (by fun_prop)).continuousOn
      (G.continuous.comp (by fun_prop)).continuousOn (fun x hx ↦ by norm_num [hx])
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
/-
**ContinuousMap.Homotopy.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Ho
motopy`。
形式化陈述：trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)
 (x : I × X) : (F.trans G) x = if h : (x.1 : Real) <= 1 / 2 then F (⟨2 * x.1, (u
nitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2) else G (⟨2 * x.1 
- 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2)
参数：X, Y；F : Homotopy f₀ f₁；G : Homotopy f₁ f₂；x : I × X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.Homotopy.extend.eq_1`：∀ {X : Type u} {Y : Type v} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Ho
motopy f₁), F.extend = C…
· 使用定理 `ContinuousMap.coe_IccExtend`：coe_IccExtend (f : C(Set.Icc a b, β)) : ((I
ccExtend h f : C(α, β)) : α -> β) = Set.IccExtend h f
· 使用定理 `Set.IccExtend_of_mem`：IccExtend_of_mem (f : Icc a b -> β) (hx : x in Icc
 a b) : IccExtend h f x = f ⟨x, hx⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  show ite _ _ _ = _ by
    split_ifs <;>
      · rw [extend, ContinuousMap.coe_IccExtend, Set.IccExtend_of_mem]
        rfl

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMap.Homotopy.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopy`。
形式化陈述：symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) 
: (F.trans G).symm = G.symm.trans F.symm
参数：X, Y；F : Homotopy f₀ f₁；G : Homotopy f₁ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.ext`：ext {F G : Homotopy f₀ f₁} (h : forall x, F 
x = G x) : F = G
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.Homotopy.trans_apply`：trans_apply {f₀ f₁ f₂ : C(X, Y)} (F 
: Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) : (F.trans G) x = if h : (x.1
 : Real) <= 1 / 2 then F…
· 使用定理 `ContinuousMap.Homotopy.symm_apply`：∀ {X : Type u} {Y : Type v} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Hom
otopy f₁) (x : ↑unitInt…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
（共 100 条，此处仅展示前 30 条）
-/
theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
  ext ⟨t, _⟩
  rw [trans_apply, symm_apply, trans_apply]
  simp only [coe_symm_eq, symm_apply]
  split_ifs with h₁ h₂ h₂
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    norm_num [ht]
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · congr 2
    apply Subtype.ext
    simp only [coe_symm_eq]
    linarith
  · exfalso
    linarith

/-- Casting a `ContinuousMap.Homotopy f₀ f₁` to a `ContinuousMap.Homotopy g₀ g₁` where `f₀ = g₀`
and `f₁ = g₁`.
-/
@[simps]
/-
**ContinuousMap.Homotopy.cast** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`
。
形式化陈述：cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ 
= g₁) : Homotopy g₀ g₁ where toFun
参数：X, Y；F : Homotopy f₀ f₁；h₀ : f₀ = g₀；h₁ : f₁ = g₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casting a `ContinuousMap.Homotopy f₀ f₁` to a `ContinuousMap.Homotopy g₀ g₁` whe
re `f₀ = g₀`
and `f₁ = g₁`.
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : Homotopy f₀ f₁) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    Homotopy g₀ g₁ where
  toFun := F
  map_zero_left := by simp [← h₀]
  map_one_left := by simp [← h₁]

/-- If we have a `ContinuousMap.Homotopy g₀ g₁` and a `ContinuousMap.Homotopy f₀ f₁`, then we can
compose them and get a `ContinuousMap.Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
@[simps]
/-
**ContinuousMap.Homotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`
。
形式化陈述：comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotop
y f₀ f₁) : Homotopy (g₀.comp f₀) (g₁.comp f₁) where toFun x
参数：X, Y；Y, Z；G : Homotopy g₀ g₁；F : Homotopy f₀ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we have a `ContinuousMap.Homotopy g₀ g₁` and a `ContinuousMap.Homotopy f₀ f₁`
, then we can
compose them and get a `ContinuousMap.Homotopy (g₀.comp f₀) (g₁.comp f₁)`.
-/
def comp {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (g₀.comp f₀) (g₁.comp f₁) where
  toFun x := G (x.1, F x)
  map_zero_left := by simp
  map_one_left := by simp

/-- Composition of a `ContinuousMap.Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy between
`g₀.comp f` and `g₁.comp f`. -/
@[simps!]
/-
**ContinuousMap.Homotopy.compContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
Map.Homotopy`。
形式化陈述：compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) : H
omotopy (g₀.comp f) (g₁.comp f)
参数：Y, Z；G : Homotopy g₀ g₁；f : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a `ContinuousMap.Homotopy g₀ g₁` and `f : C(X, Y)` as a homotopy 
between
`g₀.comp f` and `g₁.comp f`.
-/
def compContinuousMap {g₀ g₁ : C(Y, Z)} (G : Homotopy g₀ g₁) (f : C(X, Y)) :
    Homotopy (g₀.comp f) (g₁.comp f) :=
  G.comp (.refl f)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(X, Z)` and `g₁ : C(X, Z)`. Then `F.prodMk G` is the homotopy between `f₀.prodMk g₀` and
`f₁.prodMk g₁` that sends `p` to `(F p, G p)`. -/
nonrec def prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMk g₀) (f₁.prodMk g₁) where
  toContinuousMap := F.prodMk G
  map_zero_left _ := Prod.ext (F.map_zero_left _) (G.map_zero_left _)
  map_one_left _ := Prod.ext (F.map_one_left _) (G.map_one_left _)

/-- Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a homotopy between
`g₀ : C(Z, Z')` and `g₁ : C(Z, Z')`. Then `F.prodMap G` is the homotopy between `f₀.prodMap g₀` and
`f₁.prodMap g₁` that sends `(t, x, z)` to `(F (t, x), G (t, z))`. -/
/-
**ContinuousMap.Homotopy.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homoto
py`。
形式化陈述：prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Hom
otopy g₀ g₁) : Homotopy (f₀.prodMap g₀) (f₁.prodMap g₁)
参数：X, Y；Z, Z'；F : Homotopy f₀ f₁；G : Homotopy g₀ g₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `F` be a homotopy between `f₀ : C(X, Y)` and `f₁ : C(X, Y)`. Let `G` be a ho
motopy between
`g₀ : C(Z, Z')` and `g₁ : C(Z, Z')`. Then `F.prodMap G` is the homotopy between 
`f₀.prodMap g₀` and
`f₁.prodMap g₁` that sends `(t, x, z)` to `(F (t, x), G (t, z))`.
-/
def prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} (F : Homotopy f₀ f₁) (G : Homotopy g₀ g₁) :
    Homotopy (f₀.prodMap g₀) (f₁.prodMap g₁) :=
  .prodMk (F.compContinuousMap .fst) (G.compContinuousMap .snd)

/-- Given a family of homotopies `F i` between `f₀ i : C(X, Y i)` and `f₁ i : C(X, Y i)`, returns a
homotopy between `ContinuousMap.pi f₀` and `ContinuousMap.pi f₁`. -/
/-
**ContinuousMap.Homotopy.pi** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy`。
形式化陈述：{X : Type u} →   {ι : Type u_2} →     [inst : TopologicalSpace X] →       
{Y : ι → Type u_3} →         [inst_1 : (i : ι) → TopologicalSpace (Y i)] →      
     {f₀ f₁ : (i : ι) → C(X, Y i)} →             ((i : ι) → (f₀ i).Homotopy (f₁ 
i)) → (ContinuousMap.pi f₀).Homotopy (ContinuousMap.pi f₁)
参数：i : ι；Y i；i : ι；X, Y i；(i : ι) → (f₀ i).Homotopy (f₁ i)；ContinuousMap.pi f₀；C
ontinuousMap.pi f₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of homotopies `F i` between `f₀ i : C(X, Y i)` and `f₁ i : C(X, Y
 i)`, returns a
homotopy between `ContinuousMap.pi f₀` and `ContinuousMap.pi f₁`.
-/
protected def pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
    (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.pi f₀) (.pi f₁) where
  toContinuousMap := .pi fun i ↦ F i
  map_zero_left x := funext fun i ↦ (F i).map_zero_left x
  map_one_left x := funext fun i ↦ (F i).map_one_left x

/-- Given a family of homotopies `F i` between `f₀ i : C(X i, Y i)` and `f₁ i : C(X i, Y i)`,
returns a homotopy between `ContinuousMap.piMap f₀` and `ContinuousMap.piMap f₁`. -/
/-
**ContinuousMap.Homotopy.piMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotopy
`。
形式化陈述：{ι : Type u_2} →   {X : ι → Type u_3} →     {Y : ι → Type u_4} →       [in
st : (i : ι) → TopologicalSpace (X i)] →         [inst_1 : (i : ι) → Topological
Space (Y i)] →           {f₀ f₁ : (i : ι) → C(X i, Y i)} →             ((i : ι) 
→ (f₀ i).Homotopy (f₁ i)) → (ContinuousMap.piMap f₀).Homotopy (ContinuousMap.piM
ap f₁)
参数：i : ι；X i；i : ι；Y i；i : ι；X i, Y i；(i : ι) → (f₀ i).Homotopy (f₁ i)；Continuou
sMap.piMap f₀；ContinuousMap.piMap f₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of homotopies `F i` between `f₀ i : C(X i, Y i)` and `f₁ i : C(X 
i, Y i)`,
returns a homotopy between `ContinuousMap.piMap f₀` and `ContinuousMap.piMap f₁`
.
-/
protected def piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopy (f₀ i) (f₁ i)) :
    Homotopy (.piMap f₀) (.piMap f₁) :=
  .pi fun i ↦ (F i).compContinuousMap <| .eval i

end Homotopy

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there exists a
`ContinuousMap.Homotopy f₀ f₁`.
-/
/-
**ContinuousMap.Homotopic** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：Homotopic (f₀ f₁ : C(X, Y)) : Prop
参数：f₀ f₁ : C(X, Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic if there
 exists a
`ContinuousMap.Homotopy f₀ f₁`.
-/
def Homotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Homotopy f₀ f₁)

namespace Homotopic

@[refl]
/-
**ContinuousMap.Homotopic.refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopi
c`。
形式化陈述：refl (f : C(X, Y)) : Homotopic f f
参数：f : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (f : C(X, Y)) : Homotopic f f :=
  ⟨Homotopy.refl f⟩

@[symm]
/-
**ContinuousMap.Homotopic.symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopi
c`。
形式化陈述：symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm

@[trans]
/-
**ContinuousMap.Homotopic.trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotop
ic`。
形式化陈述：trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homoto
pic f h
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁
/-
**ContinuousMap.Homotopic.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopi
c`。
形式化陈述：comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homo
topic f₀ f₁) : Homotopic (g₀.comp f₀) (g₁.comp f₁)
参数：Y, Z；X, Y；hg : Homotopic g₀ g₁；hf : Homotopic f₀ f₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) :
    Homotopic (g₀.comp f₀) (g₁.comp f₁) :=
  hg.map2 Homotopy.comp hf
/-
**ContinuousMap.Homotopic.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.H
omotopic`。
形式化陈述：equivalence : Equivalence (@Homotopic X Y _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f
· 使用定理 `ContinuousMap.Homotopic.symm`：symm ⦃f g : C(X, Y)⦄ (h : Homotopic f g) :
 Homotopic g f
· 使用定理 `ContinuousMap.Homotopic.trans`：trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopic f
 g) (h₁ : Homotopic g h) : Homotopic f h
-/
theorem equivalence : Equivalence (@Homotopic X Y _ _) :=
  ⟨refl, by apply symm, by apply trans⟩

nonrec theorem prodMk {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(X, Z)} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (f₀.prodMk g₀) (f₁.prodMk g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMk G⟩

nonrec theorem prodMap {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Z, Z')} :
    Homotopic f₀ f₁ → Homotopic g₀ g₁ → Homotopic (f₀.prodMap g₀) (f₁.prodMap g₁)
  | ⟨F⟩, ⟨G⟩ => ⟨F.prodMap G⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
/-
**ContinuousMap.Homotopic.pi** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotopic`
。
形式化陈述：∀ {X : Type u} {ι : Type u_2} [inst : TopologicalSpace X] {Y : ι → Type u_
3} [inst_1 : (i : ι) → TopologicalSpace (Y i)]   {f₀ f₁ : (i : ι) → C(X, Y i)}, 
  (∀ (i : ι), (f₀ i).Homotopic (f₁ i)) → (ContinuousMap.pi f₀).Homotopic (Contin
uousMap.pi f₁)
参数：i : ι；Y i；i : ι；X, Y i；∀ (i : ι), (f₀ i).Homotopic (f₁ i)；ContinuousMap.pi f₀
；ContinuousMap.pi f₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousM
ap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`.
-/
protected theorem pi {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X, Y i)}
    (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.pi f₀) (.pi f₁) :=
  ⟨.pi fun i ↦ (F i).some⟩

/-- If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousMap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`. -/
/-
**ContinuousMap.Homotopic.piMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homotop
ic`。
形式化陈述：∀ {ι : Type u_2} {X : ι → Type u_3} {Y : ι → Type u_4} [inst : (i : ι) → T
opologicalSpace (X i)]   [inst_1 : (i : ι) → TopologicalSpace (Y i)] {f₀ f₁ : (i
 : ι) → C(X i, Y i)},   (∀ (i : ι), (f₀ i).Homotopic (f₁ i)) → (ContinuousMap.pi
Map f₀).Homotopic (ContinuousMap.piMap f₁)
参数：i : ι；X i；i : ι；Y i；i : ι；X i, Y i；∀ (i : ι), (f₀ i).Homotopic (f₁ i)；Continu
ousMap.piMap f₀；ContinuousMap.piMap f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopic.pi`：∀ {X : Type u} {ι : Type u_2} [inst : Topolo
gicalSpace X] {Y : ι → Type u_3} [inst_1 : (i : ι) → TopologicalSpace (Y i)]   {
f₀ f₁ : (i : ι) …
· 使用定理 `ContinuousMap.Homotopic.comp`：comp {g₀ g₁ : C(Y, Z)} {f₀ f₁ : C(X, Y)} (
hg : Homotopic g₀ g₁) (hf : Homotopic f₀ f₁) : Homotopic (g₀.comp f₀) (g₁.comp f
₁)
· 使用定理 `ContinuousMap.Homotopic.refl`：refl (f : C(X, Y)) : Homotopic f f

--- 原说明 ---
If each `f₀ i : C(X, Y i)` is homotopic to `f₁ i : C(X, Y i)`, then `ContinuousM
ap.pi f₀` is
homotopic to `ContinuousMap.pi f₁`.
-/
protected theorem piMap {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f₀ f₁ : ∀ i, C(X i, Y i)} (F : ∀ i, Homotopic (f₀ i) (f₁ i)) :
    Homotopic (.piMap f₀) (.piMap f₁) :=
  .pi fun i ↦ .comp (F i) (.refl <| .eval i)

end Homotopic

/--
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps satisfy the predicate
`P : C(X, Y) → Prop`
-/
/-
**ContinuousMap.HomotopyWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u} →   {Y : Type v} →     [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → C(X, Y) → C(X, Y) → (C(X, Y) → Prop) → Type (max u v)
参数：X, Y；X, Y；C(X, Y) → Prop；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of homotopies between `f₀ f₁ : C(X, Y)`, where the intermediate maps sa
tisfy the predicate
`P : C(X, Y) → Prop`
-/
structure HomotopyWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) extends Homotopy f₀ f₁ where
  -- TODO: use `toHomotopy.curry t`
  /-- the intermediate maps of the homotopy satisfy the property -/
  prop' : ∀ t, P ⟨fun x ↦ toFun (t, x), continuous_toFun.comp (by fun_prop)⟩

namespace HomotopyWith

section

variable {f₀ f₁ : C(X, Y)} {P : C(X, Y) → Prop}

/-
**ContinuousMap.HomotopyWith.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMa
p.HomotopyWith`。
形式化陈述：instFunLike : FunLike (HomotopyWith f₀ f₁ P) (I × X) Y where coe F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (HomotopyWith f₀ f₁ P) (I × X) Y where
  coe F := ⇑F.toHomotopy
  coe_injective
  | ⟨⟨⟨_, _⟩, _, _⟩, _⟩, ⟨⟨⟨_, _⟩, _, _⟩, _⟩, rfl => rfl
/-
**ContinuousMap.HomotopyWith.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.HomotopyW
ith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomotopyLike (HomotopyWith f₀ f₁ P) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left
/-
**ContinuousMap.HomotopyWith.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap.HomotopyWith`。
形式化陈述：coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X -> Y) 
(⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Function.Injective (HomotopyWith f₀ f₁ P) (I × X → Y) (⇑) :=
  DFunLike.coe_injective

@[ext]
/-
**ContinuousMap.HomotopyWith.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homoto
pyWith`。
形式化陈述：ext {F G : HomotopyWith f₀ f₁ P} (h : forall x, F x = G x) : F = G
参数：h : forall x, F x = G x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {F G : HomotopyWith f₀ f₁ P} (h : ∀ x, F x = G x) : F = G := DFunLike.ext F G h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ContinuousMap.HomotopyWith.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMa
p.HomotopyWith.Simps`。
形式化陈述：{X : Type u} →   {Y : Type v} →     [inst : TopologicalSpace X] →       [i
nst_1 : TopologicalSpace Y] →         {f₀ f₁ : C(X, Y)} → {P : C(X, Y) → Prop} →
 f₀.HomotopyWith f₁ P → ↑unitInterval × X → Y
参数：X, Y；X, Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.apply (F : HomotopyWith f₀ f₁ P) : I × X → Y := F

initialize_simps_projections HomotopyWith (toFun → apply, -toHomotopy_toContinuousMap)

@[continuity]
/-
**ContinuousMap.HomotopyWith.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopyWith`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)}   {P : C(X, Y) → Prop} (F : f₀.HomotopyWith f₁ P),
 Continuous ⇑F
参数：X, Y；X, Y；F : f₀.HomotopyWith f₁ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
protected theorem continuous (F : HomotopyWith f₀ f₁ P) : Continuous F :=
  F.continuous_toFun

@[simp]
/-
**ContinuousMap.HomotopyWith.apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopyWith`。
形式化陈述：apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x
参数：F : HomotopyWith f₀ f₁ P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.map_zero_left`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (self : 
f₀.Homotopy f₁) (x : X), s…
-/
theorem apply_zero (F : HomotopyWith f₀ f₁ P) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
/-
**ContinuousMap.HomotopyWith.apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
HomotopyWith`。
形式化陈述：apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x
参数：F : HomotopyWith f₀ f₁ P；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.map_one_left`：∀ {X : Type u} {Y : Type v} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (self : f
₀.Homotopy f₁) (x : X), s…
-/
theorem apply_one (F : HomotopyWith f₀ f₁ P) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x
/-
**ContinuousMap.HomotopyWith.coe_toContinuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap.HomotopyWith`。
形式化陈述：coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F
参数：F : HomotopyWith f₀ f₁ P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousMap (F : HomotopyWith f₀ f₁ P) : ⇑F.toContinuousMap = F :=
  rfl

@[simp]
/-
**ContinuousMap.HomotopyWith.coe_toHomotopy** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap.HomotopyWith`。
形式化陈述：coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F
参数：F : HomotopyWith f₀ f₁ P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomotopy (F : HomotopyWith f₀ f₁ P) : ⇑F.toHomotopy = F :=
  rfl
/-
**ContinuousMap.HomotopyWith.prop** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homot
opyWith`。
形式化陈述：prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t)
参数：F : HomotopyWith f₀ f₁ P；t : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.prop'`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   {P : C(X, Y)
 → Prop} (self : f₀.Ho…
-/
theorem prop (F : HomotopyWith f₀ f₁ P) (t : I) : P (F.toHomotopy.curry t) := F.prop' t
/-
**ContinuousMap.HomotopyWith.extendProp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopyWith`。
形式化陈述：extendProp (F : HomotopyWith f₀ f₁ P) (t : Real) : P (F.toHomotopy.extend 
t)
参数：F : HomotopyWith f₀ f₁ P；t : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.prop`：prop (F : HomotopyWith f₀ f₁ P) (t : I)
 : P (F.toHomotopy.curry t)
-/
theorem extendProp (F : HomotopyWith f₀ f₁ P) (t : ℝ) : P (F.toHomotopy.extend t) := F.prop _

end

variable {P : C(X, Y) → Prop}

/-- Given a continuous function `f`, and a proof `h : P f`, we can define a `HomotopyWith f f P` by
`F (t, x) = f x`
-/
@[simps!]
/-
**ContinuousMap.HomotopyWith.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homot
opyWith`。
形式化陈述：refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where toHomotopy
参数：f : C(X, Y)；hf : P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous function `f`, and a proof `h : P f`, we can define a `Homotop
yWith f f P` by
`F (t, x) = f x`
-/
def refl (f : C(X, Y)) (hf : P f) : HomotopyWith f f P where
  toHomotopy := Homotopy.refl f
  prop' := fun _ => hf
/-
**ContinuousMap.HomotopyWith.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.HomotopyW
ith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomotopyWith (ContinuousMap.id X) (ContinuousMap.id X) fun _ => True) :=
  ⟨HomotopyWith.refl _ trivial⟩

/--
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by reversing the homotopy.
-/
@[simps!]
/-
**ContinuousMap.HomotopyWith.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homot
opyWith`。
形式化陈述：symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P w
here toHomotopy
参数：X, Y；F : HomotopyWith f₀ f₁ P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `HomotopyWith f₀ f₁ P`, we can define a `HomotopyWith f₁ f₀ P` by revers
ing the homotopy.
-/
def symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : HomotopyWith f₁ f₀ P where
  toHomotopy := F.toHomotopy.symm
  prop' := fun t => F.prop (σ t)

@[simp]
/-
**ContinuousMap.HomotopyWith.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
HomotopyWith`。
形式化陈述：symm_symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F
参数：X, Y；F : HomotopyWith f₀ f₁ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.ext`：ext {F G : HomotopyWith f₀ f₁ P} (h : fo
rall x, F x = G x) : F = G
· 使用定理 `ContinuousMap.Homotopy.congr_fun`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   {F G : f₀.Ho
motopy f₁}, F = G → ∀ …
· 使用定理 `ContinuousMap.Homotopy.symm_symm`：symm_symm {f₀ f₁ : C(X, Y)} (F : Homot
opy f₀ f₁) : F.symm.symm = F
-/
theorem symm_symm {f₀ f₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) : F.symm.symm = F :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_symm _
/-
**ContinuousMap.HomotopyWith.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sMap.HomotopyWith`。
形式化陈述：symm_bijective {f₀ f₁ : C(X, Y)} : Function.Bijective (HomotopyWith.symm :
 HomotopyWith f₀ f₁ P -> HomotopyWith f₁ f₀ P)
参数：X, Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousMap.HomotopyWith.symm_symm`：symm_symm {f₀ f₁ : C(X, Y)} (F : H
omotopyWith f₀ f₁ P) : F.symm.symm = F
-/
theorem symm_bijective {f₀ f₁ : C(X, Y)} :
    Function.Bijective (HomotopyWith.symm : HomotopyWith f₀ f₁ P → HomotopyWith f₁ f₀ P) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `HomotopyWith f₀ f₁ P` and `HomotopyWith f₁ f₂ P`, we can define a `HomotopyWith f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
/-
**ContinuousMap.HomotopyWith.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homo
topyWith`。
形式化陈述：trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁
 f₂ P) : HomotopyWith f₀ f₂ P
参数：X, Y；F : HomotopyWith f₀ f₁ P；G : HomotopyWith f₁ f₂ P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `HomotopyWith f₀ f₁ P` and `HomotopyWith f₁ f₂ P`, we can define a `Homoto
pyWith f₀ f₂ P`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    HomotopyWith f₀ f₂ P :=
  { F.toHomotopy.trans G.toHomotopy with
    prop' := fun t => by
      simp only [Homotopy.trans]
      change P ⟨fun _ => ite ((t : ℝ) ≤ _) _ _, _⟩
      split_ifs
      · exact F.extendProp _
      · exact G.extendProp _ }
/-
**ContinuousMap.HomotopyWith.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.HomotopyWith`。
形式化陈述：trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyW
ith f₁ f₂ P) (x : I × X) : (F.trans G) x = if h : (x.1 : Real) <= 1 / 2 then F (
⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2) else 
G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.
2⟩⟩, x.2)
参数：X, Y；F : HomotopyWith f₀ f₁ P；G : HomotopyWith f₁ f₂ P；x : I × X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.trans_apply`：trans_apply {f₀ f₁ f₂ : C(X, Y)} (F 
: Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) : (F.trans G) x = if h : (x.1
 : Real) <= 1 / 2 then F…
-/
theorem trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P)
    (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
/-
**ContinuousMap.HomotopyWith.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopyWith`。
形式化陈述：symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWi
th f₁ f₂ P) : (F.trans G).symm = G.symm.trans F.symm
参数：X, Y；F : HomotopyWith f₀ f₁ P；G : HomotopyWith f₁ f₂ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.ext`：ext {F G : HomotopyWith f₀ f₁ P} (h : fo
rall x, F x = G x) : F = G
· 使用定理 `ContinuousMap.Homotopy.congr_fun`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   {F G : f₀.Ho
motopy f₁}, F = G → ∀ …
· 使用定理 `ContinuousMap.Homotopy.symm_trans`：symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : 
Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : (F.trans G).symm = G.symm.trans F.symm
-/
theorem symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (G : HomotopyWith f₁ f₂ P) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
/-
**ContinuousMap.HomotopyWith.cast** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homot
opyWith`。
形式化陈述：cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁
 : f₁ = g₁) : HomotopyWith g₀ g₁ P where toHomotopy
参数：X, Y；F : HomotopyWith f₀ f₁ P；h₀ : f₀ = g₀；h₁ : f₁ = g₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.prop`：prop (F : HomotopyWith f₀ f₁ P) (t : I)
 : P (F.toHomotopy.curry t)

--- 原说明 ---
Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and
 `f₁ = g₁`.
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop

end HomotopyWith

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with respect to the
predicate `P` if there exists a `HomotopyWith f₀ f₁ P`.
-/
/-
**ContinuousMap.HomotopicWith** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) -> Prop) : Prop
参数：f₀ f₁ : C(X, Y)；P : C(X, Y) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic with res
pect to the
predicate `P` if there exists a `HomotopyWith f₀ f₁ P`.
-/
def HomotopicWith (f₀ f₁ : C(X, Y)) (P : C(X, Y) → Prop) : Prop :=
  Nonempty (HomotopyWith f₀ f₁ P)

namespace HomotopicWith

variable {P : C(X, Y) → Prop}

/-
**ContinuousMap.HomotopicWith.refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topicWith`。
形式化陈述：refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P
参数：f : C(X, Y)；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (f : C(X, Y)) (hf : P f) : HomotopicWith f f P :=
  ⟨HomotopyWith.refl f hf⟩

@[symm]
/-
**ContinuousMap.HomotopicWith.symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topicWith`。
形式化陈述：symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicWith f g P) : HomotopicWith g f P :=
  ⟨h.some.symm⟩

-- Note: this was formerly tagged with `@[trans]`, and although the `trans` attribute accepted it
-- the `trans` tactic could not use it.
-- An update to the trans tactic coming in https://github.com/leanprover-community/mathlib4/pull/7014 will reject this attribute.
-- It could be restored by changing the argument order to `HomotopicWith P f g`.
@[trans]
/-
**ContinuousMap.HomotopicWith.trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Hom
otopicWith`。
形式化陈述：trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h
 P) : HomotopicWith f h P
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicWith f g P) (h₁ : HomotopicWith g h P) :
    HomotopicWith f h P :=
  ⟨h₀.some.trans h₁.some⟩

end HomotopicWith

/--
A `HomotopyRel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on the points in `S`.
-/
/-
**ContinuousMap.HomotopyRel** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousMap`。
形式化陈述：HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X)
参数：f₀ f₁ : C(X, Y)；S : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomotopyRel f₀ f₁ S` is a homotopy between `f₀` and `f₁` which is fixed on th
e points in `S`.
-/
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) :=
  HomotopyWith f₀ f₁ fun f ↦ ∀ x ∈ S, f x = f₀ x

namespace HomotopyRel

section

variable {f₀ f₁ : C(X, Y)} {S : Set X}

/-
**ContinuousMap.HomotopyRel.eq_fst** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topyRel`。
形式化陈述：eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S) : F (t, x) 
= f₀ x
参数：F : HomotopyRel f₀ f₁ S；t : I；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.prop`：prop (F : HomotopyWith f₀ f₁ P) (t : I)
 : P (F.toHomotopy.curry t)
-/
theorem eq_fst (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₀ x :=
  F.prop t x hx
/-
**ContinuousMap.HomotopyRel.eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topyRel`。
形式化陈述：eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x in S) : F (t, x) 
= f₁ x
参数：F : HomotopyRel f₀ f₁ S；t : I；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.HomotopyWith.apply_one`：apply_one (F : HomotopyWith f₀ f₁ 
P) (x : X) : F (1, x) = f₁ x
-/
theorem eq_snd (F : HomotopyRel f₀ f₁ S) (t : I) {x : X} (hx : x ∈ S) : F (t, x) = f₁ x := by
  rw [F.eq_fst t hx, ← F.eq_fst 1 hx, F.apply_one]
/-
**ContinuousMap.HomotopyRel.fst_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
HomotopyRel`。
形式化陈述：fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x in S) : f₀ x = f₁ x
参数：F : HomotopyRel f₀ f₁ S；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.eq_snd`：eq_snd (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₁ x
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
-/
theorem fst_eq_snd (F : HomotopyRel f₀ f₁ S) {x : X} (hx : x ∈ S) : f₀ x = f₁ x :=
  F.eq_fst 0 hx ▸ F.eq_snd 0 hx

end

variable {f₀ f₁ f₂ : C(X, Y)} {S : Set X}

/-- Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but with the proof
filled in.
-/
@[simps!]
/-
**ContinuousMap.HomotopyRel.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homoto
pyRel`。
形式化陈述：refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S
参数：f : C(X, Y)；S : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : C(X, Y)` and a set `S`, we can define a `HomotopyRel f f S` by 
setting
`F (t, x) = f x` for all `t`. This is defined using `HomotopyWith.refl`, but wit
h the proof
filled in.
-/
def refl (f : C(X, Y)) (S : Set X) : HomotopyRel f f S :=
  HomotopyWith.refl f fun _ _ ↦ rfl

/--
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversing the homotopy.
-/
@[simps!]
/-
**ContinuousMap.HomotopyRel.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homoto
pyRel`。
形式化陈述：symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where toHomotopy
参数：F : HomotopyRel f₀ f₁ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `HomotopyRel f₀ f₁ S`, we can define a `HomotopyRel f₁ f₀ S` by reversin
g the homotopy.
-/
def symm (F : HomotopyRel f₀ f₁ S) : HomotopyRel f₁ f₀ S where
  toHomotopy := F.toHomotopy.symm
  prop' := fun _ _ hx ↦ F.eq_snd _ hx

@[simp]
/-
**ContinuousMap.HomotopyRel.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.H
omotopyRel`。
形式化陈述：symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F
参数：F : HomotopyRel f₀ f₁ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.symm_symm`：symm_symm {f₀ f₁ : C(X, Y)} (F : H
omotopyWith f₀ f₁ P) : F.symm.symm = F
-/
theorem symm_symm (F : HomotopyRel f₀ f₁ S) : F.symm.symm = F :=
  HomotopyWith.symm_symm F
/-
**ContinuousMap.HomotopyRel.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map.HomotopyRel`。
形式化陈述：symm_bijective : Function.Bijective (HomotopyRel.symm : HomotopyRel f₀ f₁ 
S -> HomotopyRel f₁ f₀ S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousMap.HomotopyRel.symm_symm`：symm_symm (F : HomotopyRel f₀ f₁ S)
 : F.symm.symm = F
-/
theorem symm_bijective :
    Function.Bijective (HomotopyRel.symm : HomotopyRel f₀ f₁ S → HomotopyRel f₁ f₀ S) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- Given `HomotopyRel f₀ f₁ S` and `HomotopyRel f₁ f₂ S`, we can define a `HomotopyRel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
/-
**ContinuousMap.HomotopyRel.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homot
opyRel`。
形式化陈述：trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀
 f₂ S where toHomotopy
参数：F : HomotopyRel f₀ f₁ S；G : HomotopyRel f₁ f₂ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `HomotopyRel f₀ f₁ S` and `HomotopyRel f₁ f₂ S`, we can define a `Homotopy
Rel f₀ f₂ S`
by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : HomotopyRel f₀ f₂ S where
  toHomotopy := F.toHomotopy.trans G.toHomotopy
  prop' t x hx := by
    simp only [Homotopy.trans]
    split_ifs
    · simp [HomotopyWith.extendProp F (2 * t) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
    · simp [HomotopyWith.extendProp G (2 * t - 1) x hx, F.fst_eq_snd hx, G.fst_eq_snd hx]
/-
**ContinuousMap.HomotopyRel.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopyRel`。
形式化陈述：trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X
) : (F.trans G) x = if h : (x.1 : Real) <= 1 / 2 then F (⟨2 * x.1, (unitInterval
.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2) else G (⟨2 * x.1 - 1, unitIn
terval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2)
参数：F : HomotopyRel f₀ f₁ S；G : HomotopyRel f₁ f₂ S；x : I × X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.trans_apply`：trans_apply {f₀ f₁ f₂ : C(X, Y)} (F 
: Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : I × X) : (F.trans G) x = if h : (x.1
 : Real) <= 1 / 2 then F…
-/
theorem trans_apply (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply _ _ _
/-
**ContinuousMap.HomotopyRel.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
HomotopyRel`。
形式化陈述：symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) : (F.trans 
G).symm = G.symm.trans F.symm
参数：F : HomotopyRel f₀ f₁ S；G : HomotopyRel f₁ f₂ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyWith.ext`：ext {F G : HomotopyWith f₀ f₁ P} (h : fo
rall x, F x = G x) : F = G
· 使用定理 `ContinuousMap.Homotopy.congr_fun`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   {F G : f₀.Ho
motopy f₁}, F = G → ∀ …
· 使用定理 `ContinuousMap.Homotopy.symm_trans`：symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : 
Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : (F.trans G).symm = G.symm.trans F.symm
-/
theorem symm_trans (F : HomotopyRel f₀ f₁ S) (G : HomotopyRel f₁ f₂ S) :
    (F.trans G).symm = G.symm.trans F.symm :=
  HomotopyWith.ext <| Homotopy.congr_fun <| Homotopy.symm_trans _ _

/-- Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
/-
**ContinuousMap.HomotopyRel.cast** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homoto
pyRel`。
形式化陈述：cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ 
: f₁ = g₁) : HomotopyRel g₀ g₁ S where toHomotopy
参数：X, Y；F : HomotopyRel f₀ f₁ S；h₀ : f₀ = g₀；h₁ : f₁ = g₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casting a `HomotopyRel f₀ f₁ S` to a `HomotopyRel g₀ g₁ S` where `f₀ = g₀` and `
f₁ = g₁`.
-/
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyRel f₀ f₁ S) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyRel g₀ g₁ S where
  toHomotopy := Homotopy.cast F.toHomotopy h₀ h₁
  prop' t x hx := by simpa only [← h₀, ← h₁] using! F.prop t x hx

/-- Post-compose a homotopy relative to a set by a continuous function. -/
/-
**ContinuousMap.HomotopyRel.compContinuousMap** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousMap.HomotopyRel`。
形式化陈述：{X : Type u} →   {Y : Type v} →     {Z : Type w} →       [inst : Topologic
alSpace X] →         [inst_1 : TopologicalSpace Y] →           [inst_2 : Topolog
icalSpace Z] →             {S : Set X} →               {f₀ f₁ : C(X, Y)} → f₀.Ho
motopyRel f₁ S → (g : C(Y, Z)) → (g.comp f₀).HomotopyRel (g.comp f₁) S
参数：X, Y；g : C(Y, Z)；g.comp f₀；g.comp f₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Post-compose a homotopy relative to a set by a continuous function.
-/
@[simps!] def compContinuousMap {f₀ f₁ : C(X, Y)} (F : f₀.HomotopyRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopyRel (g.comp f₁) S where
  toHomotopy := .comp (.refl g) F.toHomotopy
  prop' t x hx := congr_arg g (F.prop t x hx)

end HomotopyRel

/-- Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
/-
**ContinuousMap.HomotopicRel** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop
参数：f₀ f₁ : C(X, Y)；S : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given continuous maps `f₀` and `f₁`, we say `f₀` and `f₁` are homotopic relative
 to a set `S` if
there exists a `HomotopyRel f₀ f₁ S`.
-/
def HomotopicRel (f₀ f₁ : C(X, Y)) (S : Set X) : Prop :=
  Nonempty (HomotopyRel f₀ f₁ S)

namespace HomotopicRel

variable {S : Set X}

/-- If two maps are homotopic relative to a set, then they are homotopic. -/
/-
**ContinuousMap.HomotopicRel.homotopic** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.
HomotopicRel`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {S : Set X} {f₀ f₁ : C(X, Y)},   f₀.HomotopicRel f₁ S → f₀.Homotopic
 f₁
参数：X, Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
If two maps are homotopic relative to a set, then they are homotopic.
-/
protected theorem homotopic {f₀ f₁ : C(X, Y)} (h : HomotopicRel f₀ f₁ S) : Homotopic f₀ f₁ :=
  h.map fun F ↦ F.1

/-- If two maps are homotopic relative to a set, then they agree on it. -/
/-
**ContinuousMap.HomotopicRel.fst_eq_snd** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
.HomotopicRel`。
形式化陈述：fst_eq_snd ⦃f₀ f₁ : C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x in
 S) : f₀ x = f₁ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `ContinuousMap.HomotopyRel.fst_eq_snd`：fst_eq_snd (F : HomotopyRel f₀ f₁ 
S) {x : X} (hx : x in S) : f₀ x = f₁ x

--- 原说明 ---
If two maps are homotopic relative to a set, then they agree on it.
-/
theorem fst_eq_snd ⦃f₀ f₁ : C(X, Y)⦄ (h : HomotopicRel f₀ f₁ S) {x : X} (hx : x ∈ S) :
    f₀ x = f₁ x :=
  Nonempty.elim h (HomotopyRel.fst_eq_snd · hx)
/-
**ContinuousMap.HomotopicRel.refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homot
opicRel`。
形式化陈述：refl (f : C(X, Y)) : HomotopicRel f f S
参数：f : C(X, Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (f : C(X, Y)) : HomotopicRel f f S :=
  ⟨HomotopyRel.refl f S⟩

@[symm]
/-
**ContinuousMap.HomotopicRel.symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homot
opicRel`。
形式化陈述：symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel f g S) : HomotopicRel g f S :=
  h.map HomotopyRel.symm

@[trans]
/-
**ContinuousMap.HomotopicRel.trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap.Homo
topicRel`。
形式化陈述：trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S
) : HomotopicRel f h S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem trans ⦃f g h : C(X, Y)⦄ (h₀ : HomotopicRel f g S) (h₁ : HomotopicRel g h S) :
    HomotopicRel f h S :=
  h₀.map2 HomotopyRel.trans h₁
/-
**ContinuousMap.HomotopicRel.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.HomotopicRel`。
形式化陈述：equivalence : Equivalence fun f g : C(X, Y) => HomotopicRel f g S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopicRel.refl`：refl (f : C(X, Y)) : HomotopicRel f f S
· 使用定理 `ContinuousMap.HomotopicRel.symm`：symm ⦃f g : C(X, Y)⦄ (h : HomotopicRel 
f g S) : HomotopicRel g f S
· 使用定理 `ContinuousMap.HomotopicRel.trans`：trans ⦃f g h : C(X, Y)⦄ (h₀ : Homotopi
cRel f g S) (h₁ : HomotopicRel g h S) : HomotopicRel f h S
-/
theorem equivalence : Equivalence fun f g : C(X, Y) => HomotopicRel f g S :=
  ⟨refl, by apply symm, by apply trans⟩
/-
**ContinuousMap.HomotopicRel.comp_continuousMap** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousMap.HomotopicRel`。
形式化陈述：comp_continuousMap ⦃f₀ f₁ : C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, 
Z)) : (g.comp f₀).HomotopicRel (g.comp f₁) S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem comp_continuousMap ⦃f₀ f₁ : C(X, Y)⦄ (h : f₀.HomotopicRel f₁ S) (g : C(Y, Z)) :
    (g.comp f₀).HomotopicRel (g.comp f₁) S := h.map (·.compContinuousMap g)

end HomotopicRel

/-
**ContinuousMap.homotopicRel_empty** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace X] [inst_1 : Topologi
calSpace Y] {f₀ f₁ : C(X, Y)},   f₀.HomotopicRel f₁ ∅ ↔ f₀.Homotopic f₁
参数：X, Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopicRel.homotopic`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y] {S : Set X} {f₀ f₁ : C(X, Y)
},   f₀.HomotopicRel f₁ S …
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
-/
@[simp] theorem homotopicRel_empty {f₀ f₁ : C(X, Y)} : HomotopicRel f₀ f₁ ∅ ↔ Homotopic f₀ f₁ :=
  ⟨fun h ↦ h.homotopic, fun ⟨F⟩ ↦ ⟨⟨F, fun _ _ ↦ False.elim⟩⟩⟩

end ContinuousMap

