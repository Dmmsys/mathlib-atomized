/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!

# Homotopy equivalences between topological spaces

In this file, we define homotopy equivalences between topological spaces `X` and `Y` as a pair of
functions `f : C(X, Y)` and `g : C(Y, X)` such that `f.comp g` and `g.comp f` are both homotopic
to `ContinuousMap.id`.

## Main definitions

- `ContinuousMap.HomotopyEquiv` is the type of homotopy equivalences between topological spaces.

## Notation

We introduce the notation `X ≃ₕ Y` for `ContinuousMap.HomotopyEquiv X Y` in the `ContinuousMap`
locale.

-/

@[expose] public section

universe u v w x

variable {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

namespace ContinuousMap

/-- A homotopy equivalence between topological spaces `X` and `Y` are a pair of functions
`toFun : C(X, Y)` and `invFun : C(Y, X)` such that `toFun.comp invFun` and `invFun.comp toFun`
are both homotopic to corresponding identity maps.
-/
@[ext]
/-
**ContinuousMap.HomotopyEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMap`。
形式化陈述：(X : Type u) → (Y : Type v) → [TopologicalSpace X] → [TopologicalSpace Y] 
→ Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy equivalence between topological spaces `X` and `Y` are a pair of func
tions
`toFun : C(X, Y)` and `invFun : C(Y, X)` such that `toFun.comp invFun` and `invF
un.comp toFun`
are both homotopic to corresponding identity maps.
-/
structure HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  /-- The forward map of a homotopy.

  Do NOT use directly. Use the coercion instead. -/
  toFun : C(X, Y)
  /-- The backward map of a homotopy.

  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/
  invFun : C(Y, X)
  left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
  right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)

@[inherit_doc] scoped infixl:25 " ≃ₕ " => ContinuousMap.HomotopyEquiv

namespace HomotopyEquiv

/-
**ContinuousMap.HomotopyEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.Homotopy
Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (X ≃ₕ Y) fun _ => X → Y := ⟨fun f => f.toFun⟩

@[continuity]
/-
**ContinuousMap.HomotopyEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.HomotopyEquiv`。
形式化陈述：continuous (h : HomotopyEquiv X Y) : Continuous h
参数：h : HomotopyEquiv X Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.continuous

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

/-- Any homeomorphism is a homotopy equivalence.
-/
/-
**Homeomorph.toHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where toFun
参数：h : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any homeomorphism is a homotopy equivalence.
-/
def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where
  toFun := h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]

@[simp]
/-
**Homeomorph.coe_toHomotopyEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X -> Y) = h
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X → Y) = h :=
  rfl

end Homeomorph

namespace ContinuousMap

namespace HomotopyEquiv

/-- If `X` is homotopy equivalent to `Y`, then `Y` is homotopy equivalent to `X`.
-/
/-
**ContinuousMap.HomotopyEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homo
topyEquiv`。
形式化陈述：symm (h : X ≃ₕ Y) : Y ≃ₕ X where toFun
参数：h : X ≃ₕ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyEquiv.right_inv`：∀ {X : Type u} {Y : Type v} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : ContinuousMap.Hom
otopyEquiv X Y), (self.toFu…
· 使用定理 `ContinuousMap.HomotopyEquiv.left_inv`：∀ {X : Type u} {Y : Type v} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : ContinuousMap.Homo
topyEquiv X Y), (self.invF…

--- 原说明 ---
If `X` is homotopy equivalent to `Y`, then `Y` is homotopy equivalent to `X`.
-/
def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv

@[simp]
/-
**ContinuousMap.HomotopyEquiv.coe_invFun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.HomotopyEquiv`。
形式化陈述：coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y -> X) = ⇑h.symm
参数：h : HomotopyEquiv X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y → X) = ⇑h.symm :=
  rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ContinuousMap.HomotopyEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousM
ap.HomotopyEquiv.Simps`。
形式化陈述：{X : Type u} →   {Y : Type v} → [inst : TopologicalSpace X] → [inst_1 : To
pologicalSpace Y] → ContinuousMap.HomotopyEquiv X Y → X → Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.apply (h : X ≃ₕ Y) : X → Y :=
  h

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
/-
**ContinuousMap.HomotopyEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousMap.HomotopyEquiv.Simps`。
形式化陈述：{X : Type u} →   {Y : Type v} → [inst : TopologicalSpace X] → [inst_1 : To
pologicalSpace Y] → ContinuousMap.HomotopyEquiv X Y → Y → X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
because it is a composition of multiple projections.
-/
def Simps.symm_apply (h : X ≃ₕ Y) : Y → X :=
  h.symm

initialize_simps_projections HomotopyEquiv (toFun_toFun → apply, invFun_toFun → symm_apply,
  -toFun, -invFun)

/-- Any topological space is homotopy equivalent to itself.
-/
@[simps!]
/-
**ContinuousMap.HomotopyEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homo
topyEquiv`。
形式化陈述：refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X
参数：X : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any topological space is homotopy equivalent to itself.
-/
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv
/-
**ContinuousMap.HomotopyEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap.Homotopy
Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomotopyEquiv Unit Unit) :=
  ⟨refl Unit⟩

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
@[simps!]
/-
**ContinuousMap.HomotopyEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Hom
otopyEquiv`。
形式化陈述：trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where toFun
参数：h₁ : X ≃ₕ Y；h₂ : Y ≃ₕ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, the
n `X` is homotopy
equivalent to `Z`.
-/
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact .comp (.refl _) (.comp h₂.left_inv (.refl _))
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
    exact .comp (.refl _) <| .comp h₁.right_inv (.refl _)
/-
**ContinuousMap.HomotopyEquiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMa
p.HomotopyEquiv`。
形式化陈述：symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.tran
s h₁.symm
参数：h₁ : X ≃ₕ Y；h₂ : Y ≃ₕ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl

/-- If `X` is homotopy equivalent to `Y` and `Z` is homotopy equivalent to `Z'`, then `X × Z` is
homotopy equivalent to `Z × Z'`. -/
/-
**ContinuousMap.HomotopyEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap
.HomotopyEquiv`。
形式化陈述：prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where toFun
参数：h₁ : X ≃ₕ Y；h₂ : Z ≃ₕ Z'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is homotopy equivalent to `Y` and `Z` is homotopy equivalent to `Z'`, the
n `X × Z` is
homotopy equivalent to `Z × Z'`.
-/
def prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where
  toFun := h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

/-- If `X i` is homotopy equivalent to `Y i` for each `i`, then the space of functions (a.k.a. the
indexed product) `∀ i, X i` is homotopy equivalent to `∀ i, Y i`. -/
/-
**ContinuousMap.HomotopyEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
Map.HomotopyEquiv`。
形式化陈述：piCongrRight {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (X
 i)] [forall i, TopologicalSpace (Y i)] (h : forall i, X i ≃ₕ Y i) : (forall i, 
X i) ≃ₕ (forall i, Y i) where toFun
参数：X i；Y i；h : forall i, X i ≃ₕ Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X i` is homotopy equivalent to `Y i` for each `i`, then the space of functio
ns (a.k.a. the
indexed product) `∀ i, X i` is homotopy equivalent to `∀ i, Y i`.
-/
def piCongrRight {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (h : ∀ i, X i ≃ₕ Y i) :
    (∀ i, X i) ≃ₕ (∀ i, Y i) where
  toFun := .piMap fun i ↦ (h i).toFun
  invFun := .piMap fun i ↦ (h i).invFun
  left_inv := .piMap fun i ↦ (h i).left_inv
  right_inv := .piMap fun i ↦ (h i).right_inv

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

@[simp]
/-
**Homeomorph.refl_toHomotopyEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] : (Homeomorph.refl 
X).toHomotopyEquiv = HomotopyEquiv.refl X
参数：X : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (Homeomorph.refl X).toHomotopyEquiv = HomotopyEquiv.refl X :=
  rfl

@[simp]
/-
**Homeomorph.symm_toHomotopyEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyE
quiv.symm
参数：h : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm :=
  rfl

@[simp]
/-
**Homeomorph.trans_toHomotopyEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) : (h₀.trans h₁).toHomoto
pyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv
参数：h₀ : X ≃ₜ Y；h₁ : Y ≃ₜ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
    (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv :=
  rfl

end Homeomorph

