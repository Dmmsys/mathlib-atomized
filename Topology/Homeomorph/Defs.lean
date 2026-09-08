/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
module

public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

## Main definitions and results

* `Homeomorph X Y`: The type of homeomorphisms from `X` to `Y`.
  This type can be denoted using the following notation: `X ≃ₜ Y`.
* `HomeomorphClass`: `HomeomorphClass F A B` states that `F` is a type of homeomorphisms.

* `Homeomorph.symm`: the inverse of a homeomorphism
* `Homeomorph.trans`: composing two homeomorphisms
* Homeomorphisms are open and closed embeddings, inducing, quotient maps etc.
* `Homeomorph.homeomorphOfContinuousOpen`: A continuous bijection that is
  an open map is a homeomorphism.
* `Homeomorph.homeomorphOfUnique`: if both `X` and `Y` have a unique element, then `X ≃ₜ Y`.
* `Equiv.toHomeomorph`: an equivalence between topological spaces respecting openness
  is a homeomorphism.

* `IsHomeomorph`: the predicate that a function is a homeomorphism

-/

@[expose] public section

open Set Topology Filter

variable {X Y W Z : Type*}

/-- Homeomorphism between `X` and `Y`, also called topological isomorphism -/
/-
**Homeomorph** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace 
Y] extends X ≃ Y where /-- The forward map of a homeomorphism is a continuous fu
nction. -/ continuous_toFun : Continuous toFun
参数：X : Type*；Y : Type*。
继承自：X ≃ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homeomorphism between `X` and `Y`, also called topological isomorphism
-/
structure Homeomorph (X : Type*) (Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    extends X ≃ Y where
  /-- The forward map of a homeomorphism is a continuous function. -/
  continuous_toFun : Continuous toFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip
  /-- The inverse map of a homeomorphism is a continuous function. -/
  continuous_invFun : Continuous invFun := by
    first | fun_prop | eta_expand; dsimp; fun_prop | skip

@[inherit_doc]
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/-
**Homeomorph.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y],   Function.Injective Homeomorph.toEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_injective : Function.Injective (toEquiv : X ≃ₜ Y → X ≃ Y)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
/-
**Homeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `Homeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (X ≃ₜ Y) X Y where
  coe h := h.toEquiv
  inv h := h.toEquiv.symm
  left_inv h := h.left_inv
  right_inv h := h.right_inv
  coe_injective' _ _ H _ := toEquiv_injective <| DFunLike.ext' H
/-
**Homeomorph.homeomorph_mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (a : X ≃ Y)   (b : Continuous a.toFun) (c : Continuous a.invFun)
,   ⇑{ toEquiv := a, continuous_toFun := b, continuous_invFun := c } = ⇑a
参数：a : X ≃ Y；b : Continuous a.toFun；c : Continuous a.invFun。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem homeomorph_mk_coe (a : X ≃ Y) (b c) : (Homeomorph.mk a b c : X → Y) = a :=
  rfl

/-- The unique homeomorphism between two empty types. -/
/-
**Homeomorph.empty** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 
: TopologicalSpace Y] → [IsEmpty X] → [IsEmpty Y] → X ≃ₜ Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique homeomorphism between two empty types.
-/
protected def empty [IsEmpty X] [IsEmpty Y] : X ≃ₜ Y where
  __ := Equiv.equivOfIsEmpty X Y

/-- Inverse of a homeomorphism. -/
@[symm]
/-
**Homeomorph.symm** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
TopologicalSpace Y] → X ≃ₜ Y → Y ≃ₜ X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun

--- 原说明 ---
Inverse of a homeomorphism.
-/
protected def symm (h : X ≃ₜ Y) : Y ≃ₜ X where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
/-
**Homeomorph.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y), h.symm.symm = h
参数：h : X ≃ₜ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_symm (h : X ≃ₜ Y) : h.symm.symm = h := rfl
/-
**Homeomorph.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_bijective : Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) -> Y ≃ₜ X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Homeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), h.symm.symm = h
-/
theorem symm_bijective : Function.Bijective (Homeomorph.symm : (X ≃ₜ Y) → Y ≃ₜ X) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- See Note [custom simps projection] -/
/-
**Homeomorph.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph.Simps`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
TopologicalSpace Y] → X ≃ₜ Y → Y → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : X ≃ₜ Y) : Y → X :=
  h.symm

initialize_simps_projections Homeomorph (toFun → apply, invFun → symm_apply, as_prefix toEquiv)

@[simp]
/-
**Homeomorph.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv = h
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv = h :=
  rfl

@[simp]
/-
**Homeomorph.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_symm_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv.symm = h.symm
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (h : X ≃ₜ Y) : ⇑h.toEquiv.symm = h.symm :=
  rfl

@[ext]
/-
**Homeomorph.ext** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
参数：H : forall x, h x = h' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {h h' : X ≃ₜ Y} (H : ∀ x, h x = h' x) : h = h' :=
  DFunLike.ext _ _ H

/-- Identity map as a homeomorphism. -/
@[simps! -fullyApplied apply]
/-
**Homeomorph.refl** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：(X : Type u_7) → [inst : TopologicalSpace X] → X ≃ₜ X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Identity map as a homeomorphism.
-/
protected def refl (X : Type*) [TopologicalSpace X] : X ≃ₜ X where
  toEquiv := Equiv.refl X

/-- Composition of two homeomorphisms. -/
@[trans]
/-
**Homeomorph.trans** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     {Z : Type u_4} →       [inst : Top
ologicalSpace X] →         [inst_1 : TopologicalSpace Y] → [inst_2 : Topological
Space Z] → X ≃ₜ Y → Y ≃ₜ Z → X ≃ₜ Z
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of two homeomorphisms.
-/
protected def trans (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) : X ≃ₜ Z where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv

@[simp]
/-
**Homeomorph.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x
)
参数：h₁ : X ≃ₜ Y；h₂ : Y ≃ₜ Z；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (h₁ : X ≃ₜ Y) (h₂ : Y ≃ₜ Z) (x : X) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

@[simp]
/-
**Homeomorph.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_trans_apply (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z) : (f.trans g).symm z = 
f.symm (g.symm z)
参数：f : X ≃ₜ Y；g : Y ≃ₜ Z；z : Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (f : X ≃ₜ Y) (g : Y ≃ₜ Z) (z : Z) :
    (f.trans g).symm z = f.symm (g.symm z) := rfl

@[simp]
/-
**Homeomorph.homeomorph_mk_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：homeomorph_mk_coe_symm (a : X ≃ Y) (b c) : ((Homeomorph.mk a b c).symm : Y
 -> X) = a.symm
参数：a : X ≃ Y；b c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeomorph_mk_coe_symm (a : X ≃ Y) (b c) :
    ((Homeomorph.mk a b c).symm : Y → X) = a.symm :=
  rfl

@[simp]
/-
**Homeomorph.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：refl_symm : (Homeomorph.refl X).symm = Homeomorph.refl X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (Homeomorph.refl X).symm = Homeomorph.refl X :=
  rfl

@[continuity, fun_prop]
/-
**Homeomorph.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_toFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous sel
f.toFun
-/
protected theorem continuous (h : X ≃ₜ Y) : Continuous h :=
  h.continuous_toFun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
/-
**Homeomorph.continuous_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y),   Continuous ⇑h.symm
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous_invFun`：∀ {X : Type u_5} {Y : Type u_6} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (self : X ≃ₜ Y),   Continuous se
lf.invFun
-/
protected theorem continuous_symm (h : X ≃ₜ Y) : Continuous h.symm :=
  h.continuous_invFun

@[simp]
/-
**Homeomorph.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y
参数：h : X ≃ₜ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
/-
**Homeomorph.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x
参数：h : X ≃ₜ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
/-
**Homeomorph.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_apply_eq (h : X ≃ₜ Y) {x : X} {y : Y} : h.symm y = x ↔ y = h x
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (h : X ≃ₜ Y) {x : X} {y : Y} : h.symm y = x ↔ y = h x :=
  Equiv.symm_apply_eq _
/-
**Homeomorph.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：eq_symm_apply (h : X ≃ₜ Y) {x : X} {y : Y} : x = h.symm y ↔ h x = y
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (h : X ≃ₜ Y) {x : X} {y : Y} : x = h.symm y ↔ h x = y :=
  Equiv.eq_symm_apply _

@[simp]
/-
**Homeomorph.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：self_trans_symm (h : X ≃ₜ Y) : h.trans h.symm = Homeomorph.refl X
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
-/
theorem self_trans_symm (h : X ≃ₜ Y) : h.trans h.symm = Homeomorph.refl X := by
  ext
  apply symm_apply_apply

@[simp]
/-
**Homeomorph.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_trans_self (h : X ≃ₜ Y) : h.symm.trans h = Homeomorph.refl Y
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.ext`：ext {h h' : X ≃ₜ Y} (H : forall x, h x = h' x) : h = h'
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
-/
theorem symm_trans_self (h : X ≃ₜ Y) : h.symm.trans h = Homeomorph.refl Y := by
  ext
  apply apply_symm_apply

@[simps -isSimp]
/-
**Homeomorph.** 是 Mathlib 中的一个实例，位于命名空间 `Homeomorph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (X ≃ₜ X) where
  mul f g := g.trans f
  mul_assoc f g h := rfl
  one := .refl X
  one_mul f := rfl
  mul_one f := rfl
  inv := .symm
  inv_mul_cancel := self_trans_symm

@[simp]
/-
**Homeomorph.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：one_apply (x : X) : (1 : X ≃ₜ X) x = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : X) : (1 : X ≃ₜ X) x = x := rfl

@[simp]
/-
**Homeomorph.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：inv_apply (f : X ≃ₜ X) (x : X) : f⁻¹ x = f.symm x
参数：f : X ≃ₜ X；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply (f : X ≃ₜ X) (x : X) : f⁻¹ x = f.symm x := rfl

@[simp]
/-
**Homeomorph.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：mul_apply (f g : X ≃ₜ X) (x : X) : (f * g) x = f (g x)
参数：f g : X ≃ₜ X；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : X ≃ₜ X) (x : X) : (f * g) x = f (g x) := rfl
/-
**Homeomorph.bijective** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y),   Function.Bijective ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (h : X ≃ₜ Y) : Function.Bijective h :=
  h.toEquiv.bijective
/-
**Homeomorph.injective** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (h : X ≃ₜ Y) : Function.Injective h :=
  h.toEquiv.injective
/-
**Homeomorph.surjective** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (h : X ≃ₜ Y) : Function.Surjective h :=
  h.toEquiv.surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
/-
**Homeomorph.changeInv** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：changeInv (f : X ≃ₜ Y) (g : Y -> X) (hg : Function.RightInverse g f) : X ≃
ₜ Y
参数：f : X ≃ₜ Y；g : Y -> X；hg : Function.RightInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h

--- 原说明 ---
Change the homeomorphism `f` to make the inverse function definitionally equal t
o `g`.
-/
def changeInv (f : X ≃ₜ Y) (g : Y → X) (hg : Function.RightInverse g f) : X ≃ₜ Y :=
  haveI : g = f.symm := (f.left_inv.eq_rightInverse hg).symm
  { toFun := f
    invFun := g
    left_inv := by convert! f.left_inv
    right_inv := by convert! f.right_inv using 1
    continuous_toFun := f.continuous
    continuous_invFun := by convert! f.symm.continuous }

@[simp]
/-
**Homeomorph.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
-/
theorem symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id :=
  funext h.symm_apply_apply

@[simp]
/-
**Homeomorph.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
-/
theorem self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id :=
  funext h.apply_symm_apply
/-
**Homeomorph.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：range_coe (h : X ≃ₜ Y) : range h = univ
参数：h : X ≃ₜ Y。
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
theorem range_coe (h : X ≃ₜ Y) : range h = univ := by simp
/-
**Homeomorph.image_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_symm (h : X ≃ₜ Y) : image h.symm = preimage h
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_symm (h : X ≃ₜ Y) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage_symm
/-
**Homeomorph.preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：preimage_symm (h : X ≃ₜ Y) : preimage h.symm = image h
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem preimage_symm (h : X ≃ₜ Y) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage_symm).symm

@[simp]
/-
**Homeomorph.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_preimage (h : X ≃ₜ Y) (s : Set Y) : h '' h ⁻¹' s = s
参数：h : X ≃ₜ Y；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_preimage`：image_preimage {α β} (e : α ≃ β) (s : Set β) : e '
' e ⁻¹' s = s
-/
theorem image_preimage (h : X ≃ₜ Y) (s : Set Y) : h '' h ⁻¹' s = s :=
  h.toEquiv.image_preimage s

@[simp]
/-
**Homeomorph.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻¹' h '' s = s
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.preimage_image`：preimage_image {α β} (e : α ≃ β) (s : Set α) : e ⁻
¹' e '' s = s
-/
theorem preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻¹' h '' s = s :=
  h.toEquiv.preimage_image s
/-
**Homeomorph.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_eq_preimage_symm (h : X ≃ₜ Y) (s : Set X) : h '' s = h.symm ⁻¹' s
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (h : X ≃ₜ Y) (s : Set X) : h '' s = h.symm ⁻¹' s :=
  h.toEquiv.image_eq_preimage_symm s
/-
**Homeomorph.image_compl** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ) = (h '' s)ᶜ
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.image_compl`：∀ {α : Type u_3} {β : Type u_4} (f : α ≃ β) (s : Set 
α), ⇑f '' sᶜ = (⇑f '' s)ᶜ
-/
lemma image_compl (h : X ≃ₜ Y) (s : Set X) : h '' (sᶜ) = (h '' s)ᶜ :=
  h.toEquiv.image_compl s
/-
**Homeomorph.isInducing** 是 Mathlib 中的一个引理，位于命名空间 `Homeomorph`。
形式化陈述：isInducing (h : X ≃ₜ Y) : IsInducing h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace Y]   [inst_1 : TopologicalS
pace X] [inst_2 :…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_comp_self`：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
-/
lemma isInducing (h : X ≃ₜ Y) : IsInducing h :=
  .of_comp h.continuous h.symm.continuous <| by simp only [symm_comp_self, IsInducing.id]
/-
**Homeomorph.induced_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induced h ‹_› = ‹_›
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem induced_eq (h : X ≃ₜ Y) : TopologicalSpace.induced h ‹_› = ‹_› := h.isInducing.1.symm
/-
**Homeomorph.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Typ
e u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologic
alSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.self_comp_symm`：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id
-/
theorem isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h :=
  IsQuotientMap.of_comp h.symm.continuous h.continuous <| by
    simp only [self_comp_symm, IsQuotientMap.id]
/-
**Homeomorph.coinduced_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_›
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
theorem coinduced_eq (h : X ≃ₜ Y) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.isQuotientMap.isCoinducing.eq_coinduced.symm
/-
**Homeomorph.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
-/
theorem isEmbedding (h : X ≃ₜ Y) : IsEmbedding h := ⟨h.isInducing, h.injective⟩
/-
**Homeomorph.discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ Y), DiscreteTopology Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
-/
protected theorem discreteTopology [DiscreteTopology X] (h : X ≃ₜ Y) : DiscreteTopology Y :=
  h.symm.isEmbedding.discreteTopology
/-
**Homeomorph.discreteTopology_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：discreteTopology_iff (h : X ≃ₜ Y) : DiscreteTopology X ↔ DiscreteTopology 
Y
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
-/
theorem discreteTopology_iff (h : X ≃ₜ Y) : DiscreteTopology X ↔ DiscreteTopology Y :=
  ⟨fun _ ↦ h.discreteTopology, fun _ ↦ h.symm.discreteTopology⟩
/-
**Homeomorph.indiscreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [IndiscreteTopology X]   (h : X ≃ₜ Y), IndiscreteTopology Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.indiscreteTopology`：indiscreteTopology [IndiscreteTo
pology Y] {f : X -> Y} (hf : IsInducing f) : IndiscreteTopology X where eq_top
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
protected theorem indiscreteTopology [IndiscreteTopology X] (h : X ≃ₜ Y) :
    IndiscreteTopology Y :=
  h.symm.isInducing.indiscreteTopology
/-
**Homeomorph.indiscreteTopology_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：indiscreteTopology_iff (h : X ≃ₜ Y) : IndiscreteTopology X ↔ IndiscreteTop
ology Y
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.indiscreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] [IndiscreteTopology X]   (h : X
 ≃ₜ Y), IndiscreteT…
-/
theorem indiscreteTopology_iff (h : X ≃ₜ Y) : IndiscreteTopology X ↔ IndiscreteTopology Y :=
  ⟨fun _ ↦ h.indiscreteTopology, fun _ ↦ h.symm.indiscreteTopology⟩
/-
**Homeomorph.nontrivialTopology** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [NontrivialTopology X]   (h : X ≃ₜ Y), NontrivialTopology Y
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.nontrivialTopology`：nontrivialTopology [NontrivialTo
pology X] {f : X -> Y} (hf : IsInducing f) : NontrivialTopology Y
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
protected theorem nontrivialTopology [NontrivialTopology X] (h : X ≃ₜ Y) :
    NontrivialTopology Y :=
  h.isInducing.nontrivialTopology
/-
**Homeomorph.nontrivialTopology_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：nontrivialTopology_iff (h : X ≃ₜ Y) : NontrivialTopology X ↔ NontrivialTop
ology Y
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.nontrivialTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] [NontrivialTopology X]   (h : X
 ≃ₜ Y), NontrivialT…
-/
theorem nontrivialTopology_iff (h : X ≃ₜ Y) : NontrivialTopology X ↔ NontrivialTopology Y :=
  ⟨fun _ ↦ h.nontrivialTopology, fun _ ↦ h.symm.nontrivialTopology⟩

@[simp]
/-
**Homeomorph.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : IsOpen (h ⁻¹' s) ↔ IsOpen s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsCoinducing.isOpen_preimage`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsCoinducing f → ∀ {s : Se…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
theorem isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.isQuotientMap.isOpen_preimage

@[simp]
/-
**Homeomorph.isOpen_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.isOpen_preimage`：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : I
sOpen (h ⁻¹' s) ↔ IsOpen s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, isOpen_preimage]
/-
**Homeomorph.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
-/
protected theorem isOpenMap (h : X ≃ₜ Y) : IsOpenMap h := fun _ => h.isOpen_image.2
/-
**Homeomorph.isOpenQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y),   IsOpenQuotientMap ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
protected theorem isOpenQuotientMap (h : X ≃ₜ Y) : IsOpenQuotientMap h :=
  ⟨h.surjective, h.continuous, h.isOpenMap⟩

@[simp]
/-
**Homeomorph.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isClosed_preimage (h : X ≃ₜ Y) {s : Set Y} : IsClosed (h ⁻¹' s) ↔ IsClosed
 s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_preimage (h : X ≃ₜ Y) {s : Set Y} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, isOpen_preimage]

@[simp]
/-
**Homeomorph.isClosed_image** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsClosed (h '' s) ↔ IsClosed s
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.isClosed_preimage`：isClosed_preimage (h : X ≃ₜ Y) {s : Set Y}
 : IsClosed (h ⁻¹' s) ↔ IsClosed s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, isClosed_preimage]
/-
**Homeomorph.isClosedMap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
-/
protected theorem isClosedMap (h : X ≃ₜ Y) : IsClosedMap h := fun _ => h.isClosed_image.2
/-
**Homeomorph.isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbedding h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap`：∀ {X : Type u_1} {Y :
 Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
,   Topology.IsEmbedding f → IsOpenMap …
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbedding h :=
  .of_isEmbedding_isOpenMap h.isEmbedding h.isOpenMap
/-
**Homeomorph.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedEmbedding h
参数：h : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.of_isEmbedding_isClosedMap`：∀ {X : Type u_1} 
{Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpac
e Y],   Topology.IsEmbedding f → IsClosedMa…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `Homeomorph.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsClosedMap ⇑h
-/
theorem isClosedEmbedding (h : X ≃ₜ Y) : IsClosedEmbedding h :=
  .of_isEmbedding_isClosedMap h.isEmbedding h.isClosedMap
/-
**Homeomorph.preimage_closure** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻
¹' s)
参数：h : X ≃ₜ Y；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_closure_eq_closure_preimage`：∀ {X : Type u_1} {Y : Ty
pe u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],  
 IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem preimage_closure (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous _
/-
**Homeomorph.image_closure** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' closure s = closure (h '' s)
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
-/
theorem image_closure (h : X ≃ₜ Y) (s : Set X) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]
/-
**Homeomorph.preimage_interior** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：preimage_interior (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' interior s = interior (
h ⁻¹' s)
参数：h : X ≃ₜ Y；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_interior_eq_interior_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem preimage_interior (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.isOpenMap.preimage_interior_eq_interior_preimage h.continuous _
/-
**Homeomorph.image_interior** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_interior (h : X ≃ₜ Y) (s : Set X) : h '' interior s = interior (h ''
 s)
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.preimage_interior`：preimage_interior (h : X ≃ₜ Y) (s : Set Y)
 : h ⁻¹' interior s = interior (h ⁻¹' s)
-/
theorem image_interior (h : X ≃ₜ Y) (s : Set X) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]
/-
**Homeomorph.preimage_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：preimage_frontier (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' frontier s = frontier (
h ⁻¹' s)
参数：h : X ≃ₜ Y；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.preimage_frontier_eq_frontier_preimage`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   IsOpenMap f → Continuous f → ∀ (s :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
-/
theorem preimage_frontier (h : X ≃ₜ Y) (s : Set Y) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.isOpenMap.preimage_frontier_eq_frontier_preimage h.continuous _
/-
**Homeomorph.image_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：image_frontier (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h ''
 s)
参数：h : X ≃ₜ Y；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.preimage_symm`：preimage_symm (h : X ≃ₜ Y) : preimage h.symm =
 image h
· 使用定理 `Homeomorph.preimage_frontier`：preimage_frontier (h : X ≃ₜ Y) (s : Set Y)
 : h ⁻¹' frontier s = frontier (h ⁻¹' s)
-/
theorem image_frontier (h : X ≃ₜ Y) (s : Set X) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm, preimage_frontier]

@[simp]
/-
**Homeomorph.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuous_iff (h : X ≃ₜ Y) {f : Z -> X} : Continuous (h ∘ f) ↔ Conti
nuous f
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem comp_continuous_iff (h : X ≃ₜ Y) {f : Z → X} : Continuous (h ∘ f) ↔ Continuous f :=
  h.isInducing.continuous_iff.symm

@[simp]
/-
**Homeomorph.comp_continuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuous_iff' (h : X ≃ₜ Y) {f : Y -> Z} : Continuous (f ∘ h) ↔ Cont
inuous f
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
-/
theorem comp_continuous_iff' (h : X ≃ₜ Y) {f : Y → Z} : Continuous (f ∘ h) ↔ Continuous f :=
  h.isQuotientMap.continuous_iff.symm
/-
**Homeomorph.comp_continuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuousAt_iff (h : X ≃ₜ Y) (f : Z -> X) (z : Z) : ContinuousAt (h 
∘ f) z ↔ ContinuousAt f z
参数：h : X ≃ₜ Y；f : Z -> X；z : Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuousAt_iff`：continuousAt_iff (hg : IsInducing 
g) {x : X} : ContinuousAt f x ↔ ContinuousAt (g ∘ f) x
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem comp_continuousAt_iff (h : X ≃ₜ Y) (f : Z → X) (z : Z) :
    ContinuousAt (h ∘ f) z ↔ ContinuousAt f z :=
  h.isInducing.continuousAt_iff.symm
/-
**Homeomorph.comp_continuousAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_continuousAt_iff' (h : X ≃ₜ Y) (f : Y -> Z) (x : X) : ContinuousAt (f
 ∘ h) x ↔ ContinuousAt f (h x)
参数：h : X ≃ₜ Y；f : Y -> Z；x : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousAt_iff'`：continuousAt_iff' (hf : IsInducin
g f) {x : X} (h : range f in 𝓝 (f x)) : ContinuousAt (g ∘ f) x ↔ ContinuousAt g 
(f x)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
-/
theorem comp_continuousAt_iff' (h : X ≃ₜ Y) (f : Y → Z) (x : X) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.isInducing.continuousAt_iff' (by simp)

@[simp]
/-
**Homeomorph.comp_isOpenMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_isOpenMap_iff (h : X ≃ₜ Y) {f : Z -> X} : IsOpenMap (h ∘ f) ↔ IsOpenM
ap f
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Homeomorph.symm_comp_self`：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem comp_isOpenMap_iff (h : X ≃ₜ Y) {f : Z → X} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => h.isOpenMap.comp hf⟩
  intro hf
  rw [← Function.id_comp f, ← h.symm_comp_self, Function.comp_assoc]
  exact h.symm.isOpenMap.comp hf

@[simp]
/-
**Homeomorph.comp_isOpenMap_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_isOpenMap_iff' (h : X ≃ₜ Y) {f : Y -> Z} : IsOpenMap (f ∘ h) ↔ IsOpen
Map f
参数：h : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
· 使用定理 `Homeomorph.self_comp_symm`：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem comp_isOpenMap_iff' (h : X ≃ₜ Y) {f : Y → Z} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine ⟨?_, fun hf => hf.comp h.isOpenMap⟩
  intro hf
  rw [← Function.comp_id f, ← h.self_comp_symm, ← Function.comp_assoc]
  exact hf.comp h.symm.isOpenMap

/-- Open quotient maps are preserved by precomposing with a homeomorphism. -/
@[simp]
/-
**Homeomorph.isOpenQuotient_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isOpenQuotient_comp_iff (e : X ≃ₜ Y) {f : Y -> Z} : IsOpenQuotientMap (f ∘
 e) ↔ IsOpenQuotientMap f
参数：e : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.self_comp_symm`：self_comp_symm (h : X ≃ₜ Y) : h ∘ h.symm = id
· 使用定理 `IsOpenQuotientMap.comp`：comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf
 : IsOpenQuotientMap f) : IsOpenQuotientMap (g ∘ f)
· 使用定理 `Homeomorph.isOpenQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   IsOpenQuotientMa
p ⇑h

--- 原说明 ---
Open quotient maps are preserved by precomposing with a homeomorphism.
-/
theorem isOpenQuotient_comp_iff (e : X ≃ₜ Y) {f : Y → Z} :
    IsOpenQuotientMap (f ∘ e) ↔ IsOpenQuotientMap f :=
  ⟨fun h ↦ by simpa [Function.comp_assoc] using h.comp e.symm.isOpenQuotientMap,
    fun hf ↦ hf.comp e.isOpenQuotientMap⟩

/-- Open quotient maps are preserved by postcomposing with a homeomorphism. -/
@[simp]
/-
**Homeomorph.comp_isOpenQuotientMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comp_isOpenQuotientMap_iff (e : Y ≃ₜ Z) {f : X -> Y} : IsOpenQuotientMap (
e ∘ f) ↔ IsOpenQuotientMap f
参数：e : Y ≃ₜ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Homeomorph.symm_comp_self`：symm_comp_self (h : X ≃ₜ Y) : h.symm ∘ h = id
· 使用定理 `IsOpenQuotientMap.comp`：comp {g : Y -> Z} (hg : IsOpenQuotientMap g) (hf
 : IsOpenQuotientMap f) : IsOpenQuotientMap (g ∘ f)
· 使用定理 `Homeomorph.isOpenQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   IsOpenQuotientMa
p ⇑h

--- 原说明 ---
Open quotient maps are preserved by postcomposing with a homeomorphism.
-/
theorem comp_isOpenQuotientMap_iff (e : Y ≃ₜ Z) {f : X → Y} :
    IsOpenQuotientMap (e ∘ f) ↔ IsOpenQuotientMap f :=
  ⟨fun h ↦ by simpa [← Function.comp_assoc] using e.symm.isOpenQuotientMap.comp h,
    fun hf ↦ e.isOpenQuotientMap.comp hf⟩

variable (X Y) in
/-- If both `X` and `Y` have a unique element, then `X ≃ₜ Y`. -/
@[simps!]
/-
**Homeomorph.homeomorphOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：homeomorphOfUnique [Unique X] [Unique Y] : X ≃ₜ Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If both `X` and `Y` have a unique element, then `X ≃ₜ Y`.
-/
def homeomorphOfUnique [Unique X] [Unique Y] : X ≃ₜ Y :=
  { Equiv.ofUnique X Y with }

@[simp]
/-
**Homeomorph.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) = 𝓝 (h x)
参数：h : X ≃ₜ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.map_nhds_of_mem`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsEmbedding f → ∀ (x : X),…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
-/
theorem map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) = 𝓝 (h x) :=
  h.isEmbedding.map_nhds_of_mem _ (by simp)
/-
**Homeomorph.symm_map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h.symm (𝓝 (h x)) = 𝓝 x
参数：h : X ≃ₜ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
-/
theorem symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]
/-
**Homeomorph.nhds_eq_comap** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = comap h (𝓝 (h x))
参数：h : X ≃ₜ Y；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
-/
theorem nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.isInducing.nhds_eq_comap x

@[simp]
/-
**Homeomorph.comap_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (𝓝 y) = 𝓝 (h.symm y)
参数：h : X ≃ₜ Y；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.nhds_eq_comap`：nhds_eq_comap (h : X ≃ₜ Y) (x : X) : 𝓝 x = com
ap h (𝓝 (h x))
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
-/
theorem comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]
/-
**Homeomorph.isClosed_setOfPred_iff** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isClosed_setOfPred_iff {p : X -> Prop} {q : Y -> Prop} (f : X ≃ₜ Y) (hs : 
IsClopen {x | p x}) (ht : IsClopen {y | q y}) : IsClosed { x : X | p x ↔ q (f x)
 }
参数：f : X ≃ₜ Y；hs : IsClopen {x | p x}；ht : IsClopen {y | q y}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_imp`：isClosed_imp {p q : X -> Prop} (hp : IsOpen { x | p x }) (
hq : IsClosed { x | q x }) : IsClosed { x | p x -> q x }
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isClosed_preimage`：isClosed_preimage (h : X ≃ₜ Y) {s : Set Y}
 : IsClosed (h ⁻¹' s) ↔ IsClosed s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Homeomorph.isOpen_preimage`：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : I
sOpen (h ⁻¹' s) ↔ IsOpen s
-/
theorem isClosed_setOfPred_iff {p : X → Prop} {q : Y → Prop} (f : X ≃ₜ Y) (hs : IsClopen {x | p x})
    (ht : IsClopen {y | q y}) : IsClosed { x : X | p x ↔ q (f x) } := by
  simpa [iff_def] using! (isClosed_imp hs.2 (f.isClosed_preimage.2 ht.1)).inter
    (isClosed_imp (f.isOpen_preimage.2 ht.2) hs.1)

@[deprecated (since := "2026-07-09")] alias isClosed_setOf_iff := isClosed_setOfPred_iff

end Homeomorph

namespace Equiv
variable {Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- An equivalence between topological spaces respecting openness is a homeomorphism. -/
@[simps toEquiv]
/-
**Equiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toHomeomorph (e : X ≃ Y) (he : forall s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : X 
≃ₜ Y where toEquiv
参数：e : X ≃ Y；he : forall s, IsOpen (e ⁻¹' s) ↔ IsOpen s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between topological spaces respecting openness is a homeomorphism
.
-/
def toHomeomorph (e : X ≃ Y) (he : ∀ s, IsOpen (e ⁻¹' s) ↔ IsOpen s) : X ≃ₜ Y where
  toEquiv := e
  continuous_toFun := continuous_def.2 fun _ ↦ (he _).2
  continuous_invFun := continuous_def.2 fun s ↦ by simpa using (he (e.symm ⁻¹' s)).1
/-
**Equiv.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : X ≃ Y)   (he : ∀ (s : Set Y), IsOpen (⇑e ⁻¹' s) ↔ IsOpen s)
, ⇑(e.toHomeomorph he) = ⇑e
参数：e : X ≃ Y；he : ∀ (s : Set Y), IsOpen (⇑e ⁻¹' s) ↔ IsOpen s；e.toHomeomorph he。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toHomeomorph (e : X ≃ Y) (he) : ⇑(e.toHomeomorph he) = e := rfl
/-
**Equiv.toHomeomorph_apply** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：toHomeomorph_apply (e : X ≃ Y) (he) (x : X) : e.toHomeomorph he x = e x
参数：e : X ≃ Y；he；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_apply (e : X ≃ Y) (he) (x : X) : e.toHomeomorph he x = e x := rfl
/-
**Equiv.toHomeomorph_refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], (Equiv.refl X).toHomeomorph 
⋯ = Homeomorph.refl X
参数：Equiv.refl X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toHomeomorph_refl :
    (Equiv.refl X).toHomeomorph (fun _s ↦ Iff.rfl) = Homeomorph.refl _ := rfl
/-
**Equiv.symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (e : X ≃ Y)   (he : ∀ (s : Set Y), IsOpen (⇑e ⁻¹' s) ↔ IsOpen s)
, (e.toHomeomorph he).symm = e.symm.toHomeomorph ⋯
参数：e : X ≃ Y；he : ∀ (s : Set Y), IsOpen (⇑e ⁻¹' s) ↔ IsOpen s；e.toHomeomorph he。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_toHomeomorph (e : X ≃ Y) (he) :
    (e.toHomeomorph he).symm = e.symm.toHomeomorph fun s ↦ by convert! (he _).symm; simp := rfl
/-
**Equiv.toHomeomorph_trans** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：toHomeomorph_trans (e : X ≃ Y) (f : Y ≃ Z) (he hf) : (e.trans f).toHomeomo
rph (fun _s => (he _).trans (hf _)) = (e.toHomeomorph he).trans (f.toHomeomorph 
hf)
参数：e : X ≃ Y；f : Y ≃ Z；he hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
lemma toHomeomorph_trans (e : X ≃ Y) (f : Y ≃ Z) (he hf) :
    (e.trans f).toHomeomorph (fun _s ↦ (he _).trans (hf _)) =
    (e.toHomeomorph he).trans (f.toHomeomorph hf) := rfl

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps toEquiv]
/-
**Equiv.toHomeomorphOfIsInducing** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfIsInducing (f : X ≃ Y) (hf : IsInducing f) : X ≃ₜ Y
参数：f : X ≃ Y；hf : IsInducing f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inducing equiv between topological spaces is a homeomorphism.
-/
def toHomeomorphOfIsInducing (f : X ≃ Y) (hf : IsInducing f) : X ≃ₜ Y :=
  { f with
    continuous_toFun := hf.continuous
    continuous_invFun := hf.continuous_iff.2 <| by simpa using continuous_id }
/-
**Equiv.toHomeomorphOfIsInducing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : X ≃ Y)   (hf : Topology.IsInducing ⇑f), ⇑(f.toHomeomorphOfI
sInducing hf) = ⇑f
参数：f : X ≃ Y；hf : Topology.IsInducing ⇑f；f.toHomeomorphOfIsInducing hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toHomeomorphOfIsInducing_apply (f : X ≃ Y) (hf : IsInducing f) :
    ⇑(f.toHomeomorphOfIsInducing hf) = f := rfl
/-
**Equiv.toHomeomorphOfIsInducing_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (f : X ≃ Y)   (hf : Topology.IsInducing ⇑f), ⇑(f.toHomeomorphOfI
sInducing hf).symm = ⇑f.symm
参数：f : X ≃ Y；hf : Topology.IsInducing ⇑f；f.toHomeomorphOfIsInducing hf。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toHomeomorphOfIsInducing_symm_apply (f : X ≃ Y) (hf : IsInducing f) :
    ⇑(f.toHomeomorphOfIsInducing hf).symm = f.symm := rfl

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps! toEquiv]
/-
**Equiv.toHomeomorphOfContinuousOpen** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfContinuousOpen (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenM
ap e) : X ≃ₜ Y
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsOpenMap e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphis
m.
-/
def toHomeomorphOfContinuousOpen (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) : X ≃ₜ Y :=
  e.toHomeomorphOfIsInducing <|
    IsOpenEmbedding.of_continuous_injective_isOpenMap h₁ e.injective h₂ |>.toIsInducing

@[simp]
/-
**Equiv.toHomeomorphOfContinuousOpen_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfContinuousOpen_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : I
sOpenMap e) : ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂) = e
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsOpenMap e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorphOfContinuousOpen_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂) = e := rfl

@[simp]
/-
**Equiv.toHomeomorphOfContinuousOpen_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
`。
形式化陈述：toHomeomorphOfContinuousOpen_symm_apply (e : X ≃ Y) (h₁ : Continuous e) (h
₂ : IsOpenMap e) : ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂).symm = e.symm
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsOpenMap e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorphOfContinuousOpen_symm_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsOpenMap e) :
    ⇑(e.toHomeomorphOfContinuousOpen h₁ h₂).symm = e.symm := rfl

/-- If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphism. -/
@[simps! toEquiv]
/-
**Equiv.toHomeomorphOfContinuousClosed** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfContinuousClosed (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClo
sedMap e) : X ≃ₜ Y
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsClosedMap e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a bijective map `e : X ≃ Y` is continuous and open, then it is a homeomorphis
m.
-/
def toHomeomorphOfContinuousClosed (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) : X ≃ₜ Y :=
  e.toHomeomorphOfIsInducing <|
    IsClosedEmbedding.of_continuous_injective_isClosedMap h₁ e.injective h₂ |>.toIsInducing

@[simp]
/-
**Equiv.toHomeomorphOfContinuousClosed_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfContinuousClosed_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ :
 IsClosedMap e) : ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂) = e
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsClosedMap e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorphOfContinuousClosed_apply (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) :
    ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂) = e := rfl

@[simp]
/-
**Equiv.toHomeomorphOfContinuousClosed_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv`。
形式化陈述：toHomeomorphOfContinuousClosed_symm_apply (e : X ≃ Y) (h₁ : Continuous e) 
(h₂ : IsClosedMap e) : ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂).symm = e.symm
参数：e : X ≃ Y；h₁ : Continuous e；h₂ : IsClosedMap e。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHomeomorphOfContinuousClosed_symm_apply
    (e : X ≃ Y) (h₁ : Continuous e) (h₂ : IsClosedMap e) :
    ⇑(e.toHomeomorphOfContinuousClosed h₁ h₂).symm = e.symm := rfl

/-- Any bijection between discrete spaces is a homeomorphism. -/
/-
**Equiv.toHomeomorphOfDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toHomeomorphOfDiscrete [DiscreteTopology X] [DiscreteTopology Y] (e : X ≃ 
Y) : X ≃ₜ Y
参数：e : X ≃ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any bijection between discrete spaces is a homeomorphism.
-/
def toHomeomorphOfDiscrete [DiscreteTopology X] [DiscreteTopology Y] (e : X ≃ Y) : X ≃ₜ Y :=
  e.toHomeomorph (by simp)

end Equiv

/-- `HomeomorphClass F A B` states that `F` is a type of homeomorphisms. -/
/-
**HomeomorphClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   (A : outParam (Type u_6)) →     (B : outParam (Type u_7
)) → [TopologicalSpace A] → [TopologicalSpace B] → [h : EquivLike F A B] → Prop
参数：Type u_6；Type u_7。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomeomorphClass F A B` states that `F` is a type of homeomorphisms.
-/
class HomeomorphClass (F : Type*) (A B : outParam Type*)
    [TopologicalSpace A] [TopologicalSpace B] [h : EquivLike F A B] : Prop where
  map_continuous : ∀ (f : F), Continuous f
  inv_continuous : ∀ (f : F), Continuous (h.inv f)

namespace HomeomorphClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `HomeomorphClass F α β` into an actual
`Homeomorph`. This is declared as the default coercion from `F` to `α ≃ₜ β`. -/
@[coe]
/-
**HomeomorphClass.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `HomeomorphClass`。
形式化陈述：toHomeomorph [h : HomeomorphClass F α β] (f : F) : α ≃ₜ β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomeomorphClass.map_continuous`：∀ {F : Type u_5} {A : outParam (Type u_6
)} {B : outParam (Type u_7)} {inst : TopologicalSpace A}   {inst_1 : Topological
Space B} {h : EquivL…
· 使用定理 `HomeomorphClass.inv_continuous`：∀ {F : Type u_5} {A : outParam (Type u_6
)} {B : outParam (Type u_7)} {inst : TopologicalSpace A}   {inst_1 : Topological
Space B} {h : EquivL…

--- 原说明 ---
Turn an element of a type `F` satisfying `HomeomorphClass F α β` into an actual
`Homeomorph`. This is declared as the default coercion from `F` to `α ≃ₜ β`.
-/
def toHomeomorph [h : HomeomorphClass F α β] (f : F) : α ≃ₜ β :=
  { (f : α ≃ β) with
    continuous_toFun := h.map_continuous f
    continuous_invFun := h.inv_continuous f }

@[simp]
/-
**HomeomorphClass.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `HomeomorphClass`。
形式化陈述：coe_coe [h : HomeomorphClass F α β] (f : F) : ⇑(h.toHomeomorph f) = ⇑f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe [h : HomeomorphClass F α β] (f : F) : ⇑(h.toHomeomorph f) = ⇑f := rfl
/-
**HomeomorphClass.** 是 Mathlib 中的一个实例，位于命名空间 `HomeomorphClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HomeomorphClass F α β] : CoeOut F (α ≃ₜ β) :=
  ⟨HomeomorphClass.toHomeomorph⟩
/-
**HomeomorphClass.toHomeomorph_injective** 是 Mathlib 中的一个定理，位于命名空间 `HomeomorphCl
ass`。
形式化陈述：toHomeomorph_injective [HomeomorphClass F α β] : Function.Injective ((↑) :
 F -> α ≃ₜ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toHomeomorph_injective [HomeomorphClass F α β] : Function.Injective ((↑) : F → α ≃ₜ β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃ₜ β ↦ e.toFun a) e
/-
**HomeomorphClass.** 是 Mathlib 中的一个实例，位于命名空间 `HomeomorphClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HomeomorphClass F α β] : ContinuousMapClass F α β where
  map_continuous f := map_continuous f
/-
**HomeomorphClass.** 是 Mathlib 中的一个实例，位于命名空间 `HomeomorphClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HomeomorphClass (α ≃ₜ β) α β where
  map_continuous e := e.continuous_toFun
  inv_continuous e := e.continuous_invFun

end HomeomorphClass

section IsHomeomorph

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y}

/-- Predicate saying that `f` is a homeomorphism.

This should be used only when `f` is a concrete function whose continuous inverse is not easy to
write down. Otherwise, `Homeomorph` should be preferred as it bundles the continuous inverse.

Having both `Homeomorph` and `IsHomeomorph` is justified by the fact that so many function
properties are unbundled in the topology part of the library, and by the fact that a homeomorphism
is not merely a continuous bijection, that is `IsHomeomorph f` is not equivalent to
`Continuous f ∧ Bijective f` but to `Continuous f ∧ Bijective f ∧ IsOpenMap f`. -/
/-
**IsHomeomorph** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：IsHomeomorph (f : X -> Y) : Prop where continuous : Continuous f isOpenMap
 : IsOpenMap f bijective : Function.Bijective f  protected theorem Homeomorph.is
Homeomorph (h : X ≃ₜ Y) : IsHomeomorph h
参数：f : X -> Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate saying that `f` is a homeomorphism.

This should be used only when `f` is a concrete function whose continuous invers
e is not easy to
write down. Otherwise, `Homeomorph` should be preferred as it bundles the contin
uous inverse.

Having both `Homeomorph` and `IsHomeomorph` is justified by the fact that so man
y function
properties are unbundled in the topology part of the library, and by the fact th
at a homeomorphism
is not merely a continuous bijection, that is `IsHomeomorph f` is not equivalent
 to
`Continuous f ∧ Bijective f` but to `Continuous f ∧ Bijective f ∧ IsOpenMap f`.
-/
structure IsHomeomorph (f : X → Y) : Prop where
  continuous : Continuous f
  isOpenMap : IsOpenMap f
  bijective : Function.Bijective f
/-
**Homeomorph.isHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
参数：h : X ≃ₜ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
· 使用定理 `Homeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Bijective ⇑h
-/
protected theorem Homeomorph.isHomeomorph (h : X ≃ₜ Y) : IsHomeomorph h :=
  ⟨h.continuous, h.isOpenMap, h.bijective⟩

namespace IsHomeomorph

/-- Bundled homeomorphism constructed from a map that is a homeomorphism. -/
@[simps! toEquiv apply symm_apply]
/-
**IsHomeomorph.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `IsHomeomorph`。
形式化陈述：homeomorph (f : X -> Y) (hf : IsHomeomorph f) : X ≃ₜ Y where continuous_to
Fun
参数：f : X -> Y；hf : IsHomeomorph f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f

--- 原说明 ---
Bundled homeomorphism constructed from a map that is a homeomorphism.
-/
noncomputable def homeomorph (f : X → Y) (hf : IsHomeomorph f) : X ≃ₜ Y where
  continuous_toFun := hf.1
  continuous_invFun :=
    Equiv.ofBijective f hf.bijective |>.continuous_symm_iff.2 hf.isOpenMap
  toEquiv := Equiv.ofBijective f hf.bijective
/-
**IsHomeomorph.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsHomeomorph f → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
-/
protected lemma injective (hf : IsHomeomorph f) : Function.Injective f := hf.bijective.injective
/-
**IsHomeomorph.surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   IsHomeomorph f → Function.Surjective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
-/
protected lemma surjective (hf : IsHomeomorph f) : Function.Surjective f := hf.bijective.surjective
/-
**IsHomeomorph.id** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X], IsHomeomorph id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `IsOpenMap.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], IsOpenMap id
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
protected lemma id : IsHomeomorph (@id X) := ⟨continuous_id, .id, Function.bijective_id⟩
/-
**IsHomeomorph.image_interior** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：image_interior (hf : IsHomeomorph f) (s : Set X) : f '' interior s = inter
ior (f '' s)
参数：hf : IsHomeomorph f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.image_interior`：image_interior (h : X ≃ₜ Y) (s : Set X) : h '
' interior s = interior (h '' s)
-/
theorem image_interior (hf : IsHomeomorph f) (s : Set X) :
  f '' interior s = interior (f '' s) := hf.homeomorph.image_interior s
/-
**IsHomeomorph.image_closure** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：image_closure (hf : IsHomeomorph f) (s : Set X) : f '' closure s = closure
 (f '' s)
参数：hf : IsHomeomorph f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem image_closure (hf : IsHomeomorph f) (s : Set X) :
  f '' closure s = closure (f '' s) := hf.homeomorph.image_closure s
/-
**IsHomeomorph.image_frontier** 是 Mathlib 中的一个定理，位于命名空间 `IsHomeomorph`。
形式化陈述：image_frontier (hf : IsHomeomorph f) (s : Set X) : f '' frontier s = front
ier (f '' s)
参数：hf : IsHomeomorph f；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.image_frontier`：image_frontier (h : X ≃ₜ Y) (s : Set X) : h '
' frontier s = frontier (h '' s)
-/
theorem image_frontier (hf : IsHomeomorph f) (s : Set X) :
  f '' frontier s = frontier (f '' s) := hf.homeomorph.image_frontier s
/-
**IsHomeomorph.comp** 是 Mathlib 中的一个引理，位于命名空间 `IsHomeomorph`。
形式化陈述：comp {g : Y -> Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) : IsHomeomor
ph (g ∘ f)
参数：hg : IsHomeomorph g；hf : IsHomeomorph f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsHomeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Conti
nuous f
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用定理 `IsHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → IsOpen
Map f
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `IsHomeomorph.bijective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Functi
on.Bijective…
-/
lemma comp {g : Y → Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) : IsHomeomorph (g ∘ f) :=
  ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩

end IsHomeomorph

end IsHomeomorph

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/-- Precomposing by a homeomorphism does not change the image of the interior of a preimage. -/
/-
**image_interior_preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_interior_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> 
Z) (s : Set Z) : (f ∘ e) '' interior ((f ∘ e) ⁻¹' s) = f '' interior (f ⁻¹' s)
参数：e : X -> Y；he : IsHomeomorph e；f : Y -> Z；s : Set Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `IsHomeomorph.image_interior`：image_interior (hf : IsHomeomorph f) (s : S
et X) : f '' interior s = interior (f '' s)
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `IsHomeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Funct
ion.Surjectiv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Precomposing by a homeomorphism does not change the image of the interior of a p
reimage.
-/
theorem image_interior_preimage_comp (e : X → Y) (he : IsHomeomorph e) (f : Y → Z) (s : Set Z) :
    (f ∘ e) '' interior ((f ∘ e) ⁻¹' s) = f '' interior (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_interior,
    Set.image_preimage_eq _ he.surjective]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/-- Precomposing by a homeomorphism does not change the image of the frontier of a preimage. -/
/-
**image_frontier_preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_frontier_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> 
Z) (s : Set Z) : (f ∘ e) '' frontier ((f ∘ e) ⁻¹' s) = f '' frontier (f ⁻¹' s)
参数：e : X -> Y；he : IsHomeomorph e；f : Y -> Z；s : Set Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `IsHomeomorph.image_frontier`：image_frontier (hf : IsHomeomorph f) (s : S
et X) : f '' frontier s = frontier (f '' s)
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `IsHomeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Funct
ion.Surjectiv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Precomposing by a homeomorphism does not change the image of the frontier of a p
reimage.
-/
theorem image_frontier_preimage_comp (e : X → Y) (he : IsHomeomorph e) (f : Y → Z) (s : Set Z) :
    (f ∘ e) '' frontier ((f ∘ e) ⁻¹' s) = f '' frontier (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_frontier,
    Set.image_preimage_eq _ he.surjective]

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] in
/-- Precomposing by a homeomorphism does not change the image of the closure of a preimage. -/
/-
**image_closure_preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_closure_preimage_comp (e : X -> Y) (he : IsHomeomorph e) (f : Y -> Z
) (s : Set Z) : (f ∘ e) '' closure ((f ∘ e) ⁻¹' s) = f '' closure (f ⁻¹' s)
参数：e : X -> Y；he : IsHomeomorph e；f : Y -> Z；s : Set Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `IsHomeomorph.image_closure`：image_closure (hf : IsHomeomorph f) (s : Set
 X) : f '' closure s = closure (f '' s)
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `IsHomeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsHomeomorph f → Funct
ion.Surjectiv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Precomposing by a homeomorphism does not change the image of the closure of a pr
eimage.
-/
theorem image_closure_preimage_comp (e : X → Y) (he : IsHomeomorph e) (f : Y → Z) (s : Set Z) :
    (f ∘ e) '' closure ((f ∘ e) ⁻¹' s) = f '' closure (f ⁻¹' s) := by
  simp only [Set.preimage_comp, Set.image_comp, he.image_closure,
    Set.image_preimage_eq _ he.surjective]
