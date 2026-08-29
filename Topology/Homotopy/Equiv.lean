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
/--
Definition of `HomotopyEquiv` / `HomotopyEquiv` 的定义

English:
structure HomotopyEquiv
  parameters: (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
  axioms and operations (4):
    - toFun : C(X, Y)
    - invFun : C(Y, X)
    - left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
    - right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)

中文:
结构 HomotopyEquiv
  参数: (X : 类型u) (Y : 类型v) [TopologicalSpace X] [TopologicalSpace Y]
  公理与运算 (4 个):
    - toFun : C(X, Y)
    - invFun : C(Y, X)
    - left_inv : (invFun.comp toFun).Homotopic (ContinuousMap.id X)
    - right_inv : (toFun.comp invFun).Homotopic (ContinuousMap.id Y)
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (X ≃ₕ Y) fun _ => X -> Y
  body: ⟨fun f => f.toFun⟩

@[continuity]

中文:
实例 :
  签名: CoeFun (X ≃ₕ Y) fun _ => X -> Y
  定义体: ⟨fun f => f.toFun⟩

@[continuity]

Depends on / 依赖: f.toFun
-/
instance : CoeFun (X ≃ₕ Y) fun _ => X -> Y := ⟨fun f => f.toFun⟩

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (h : HomotopyEquiv X Y)
  statement: Continuous h
  proof: h.toFun.continuous

中文:
定理 continuous
  条件: (h : HomotopyEquiv X Y)
  结论: Continuous h
  证明: h.toFun.continuous

Depends on / 依赖: continuous, h.toFun.continuous
-/
theorem continuous (h : HomotopyEquiv X Y) : Continuous h :=
  h.toFun.continuous

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

/--
Definition of `toHomotopyEquiv` / `toHomotopyEquiv` 的定义

English:
definition toHomotopyEquiv
  signature: (h : X ≃ₜ Y)
  body: h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]

@[simp]

中文:
定义 toHomotopyEquiv
  签名: (h : X ≃ₜ Y)
  定义体: h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]

@[simp]
-/
def toHomotopyEquiv (h : X ≃ₜ Y) : X ≃ₕ Y where
  toFun := h
  invFun := h.symm
  left_inv := by rw [symm_comp_toContinuousMap]
  right_inv := by rw [toContinuousMap_comp_symm]

@[simp]
/--
theorem `coe_toHomotopyEquiv` / 定理 `coe_toHomotopyEquiv`

English:
theorem coe_toHomotopyEquiv
  given: (h : X ≃ₜ Y)
  statement: (h.toHomotopyEquiv : X -> Y) = h
  proof: rfl

中文:
定理 coe_toHomotopyEquiv
  条件: (h : X ≃ₜ Y)
  结论: (h.toHomotopyEquiv : X -> Y) = h
  证明: rfl
-/
theorem coe_toHomotopyEquiv (h : X ≃ₜ Y) : (h.toHomotopyEquiv : X -> Y) = h :=
  rfl

end Homeomorph

namespace ContinuousMap

namespace HomotopyEquiv

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (h : X ≃ₕ Y)
  body: h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv

@[simp]

中文:
定义 symm
  签名: (h : X ≃ₕ Y)
  定义体: h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv

@[simp]

Depends on / 依赖: h.invFun, invFun
-/
def symm (h : X ≃ₕ Y) : Y ≃ₕ X where
  toFun := h.invFun
  invFun := h.toFun
  left_inv := h.right_inv
  right_inv := h.left_inv

@[simp]
/--
theorem `coe_invFun` / 定理 `coe_invFun`

English:
theorem coe_invFun
  given: (h : HomotopyEquiv X Y)
  statement: (⇑h.invFun : Y -> X) = ⇑h.symm
  proof: rfl

中文:
定理 coe_invFun
  条件: (h : HomotopyEquiv X Y)
  结论: (⇑h.invFun : Y -> X) = ⇑h.symm
  证明: rfl
-/
theorem coe_invFun (h : HomotopyEquiv X Y) : (⇑h.invFun : Y -> X) = ⇑h.symm :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : X ≃ₕ Y)
  body: h

中文:
定义 Simps.apply
  签名: (h : X ≃ₕ Y)
  定义体: h
-/
def Simps.apply (h : X ≃ₕ Y) : X -> Y :=
  h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : X ≃ₕ Y)
  body: h.symm

initialize_simps_projections HomotopyEquiv (toFun_toFun -> apply, invFun_toFun -> symm_apply,
  -toFun, -invFun)

中文:
定义 Simps.symm_apply
  签名: (h : X ≃ₕ Y)
  定义体: h.symm

initialize_simps_projections HomotopyEquiv (toFun_toFun -> apply, invFun_toFun -> symm_apply,
  -toFun, -invFun)
-/
def Simps.symm_apply (h : X ≃ₕ Y) : Y -> X :=
  h.symm

initialize_simps_projections HomotopyEquiv (toFun_toFun -> apply, invFun_toFun -> symm_apply,
  -toFun, -invFun)

/-- Any topological space is homotopy equivalent to itself.
-/
@[simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : Type u) [TopologicalSpace X]
  body: (Homeomorph.refl X).toHomotopyEquiv

中文:
定义 refl
  签名: (X : 类型u) [TopologicalSpace X]
  定义体: (Homeomorph.refl X).toHomotopyEquiv

Depends on / 依赖: Homeomorph, Homeomorph.refl, toHomotopyEquiv
-/
def refl (X : Type u) [TopologicalSpace X] : X ≃ₕ X :=
  (Homeomorph.refl X).toHomotopyEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HomotopyEquiv Unit Unit)
  body: ⟨refl Unit⟩

中文:
实例 :
  签名: Inhabited (HomotopyEquiv Unit Unit)
  定义体: ⟨refl Unit⟩
-/
instance : Inhabited (HomotopyEquiv Unit Unit) :=
  ⟨refl Unit⟩

/--
If `X` is homotopy equivalent to `Y`, and `Y` is homotopy equivalent to `Z`, then `X` is homotopy
equivalent to `Z`.
-/
@[simps!]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z)
  body: h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact .comp (.refl _) (.comp h₂.left_inv (.refl _))
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
exact .comp (.refl _) .comp h₁.right_inv (.refl _)

中文:
定义 trans
  签名: (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z)
  定义体: h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact .comp (.refl _) (.comp h₂.left_inv (.refl _))
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
exact .comp (.refl _) .comp h₁.right_inv (.refl _)

Depends on / 依赖: toFun.comp
-/
def trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : X ≃ₕ Z where
  toFun := h₂.toFun.comp h₁.toFun
  invFun := h₁.invFun.comp h₂.invFun
  left_inv := by
    refine Homotopic.trans ?_ h₁.left_inv
    exact .comp (.refl _) (.comp h₂.left_inv (.refl _))
  right_inv := by
    refine Homotopic.trans ?_ h₂.right_inv
exact .comp (.refl _) .comp h₁.right_inv (.refl _)

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z)
  statement: (h₁.trans h₂).symm = h₂.symm.trans h₁.symm
  proof: rfl

中文:
定理 symm_trans
  条件: (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z)
  结论: (h₁.trans h₂).symm = h₂.symm.trans h₁.symm
  证明: rfl
-/
theorem symm_trans (h₁ : X ≃ₕ Y) (h₂ : Y ≃ₕ Z) : (h₁.trans h₂).symm = h₂.symm.trans h₁.symm := rfl

/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z')
  body: h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

中文:
定义 prodCongr
  签名: (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z')
  定义体: h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

Depends on / 依赖: prodMap, toFun.prodMap
-/
def prodCongr (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z') : (X × Z) ≃ₕ (Y × Z') where
  toFun := h₁.toFun.prodMap h₂.toFun
  invFun := h₁.invFun.prodMap h₂.invFun
  left_inv := h₁.left_inv.prodMap h₂.left_inv
  right_inv := h₁.right_inv.prodMap h₂.right_inv

/--
Definition of `piCongrRight` / `piCongrRight` 的定义

English:
definition piCongrRight
  signature: {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
  body: .piMap fun i => (h i).toFun
  invFun := .piMap fun i => (h i).invFun
  left_inv := .piMap fun i => (h i).left_inv
  right_inv := .piMap fun i => (h i).right_inv

中文:
定义 piCongrRight
  签名: {ι : 类型} {X Y : ι -> 类型} [对任意 i, TopologicalSpace (X i)]
  定义体: .piMap fun i => (h i).toFun
  invFun := .piMap fun i => (h i).invFun
  left_inv := .piMap fun i => (h i).left_inv
  right_inv := .piMap fun i => (h i).right_inv
-/
def piCongrRight {ι : Type*} {X Y : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, TopologicalSpace (Y i)] (h : forall i, X i ≃ₕ Y i) :
    (forall i, X i) ≃ₕ (forall i, Y i) where
  toFun := .piMap fun i => (h i).toFun
  invFun := .piMap fun i => (h i).invFun
  left_inv := .piMap fun i => (h i).left_inv
  right_inv := .piMap fun i => (h i).right_inv

end HomotopyEquiv

end ContinuousMap

open ContinuousMap

namespace Homeomorph

@[simp]
/--
theorem `refl_toHomotopyEquiv` / 定理 `refl_toHomotopyEquiv`

English:
theorem refl_toHomotopyEquiv
  given: (X : Type u) [TopologicalSpace X]
  proof: rfl

@[simp]

中文:
定理 refl_toHomotopyEquiv
  条件: (X : 类型u) [TopologicalSpace X]
  证明: rfl

@[simp]
-/
theorem refl_toHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (Homeomorph.refl X).toHomotopyEquiv = HomotopyEquiv.refl X :=
  rfl

@[simp]
/--
theorem `symm_toHomotopyEquiv` / 定理 `symm_toHomotopyEquiv`

English:
theorem symm_toHomotopyEquiv
  given: (h : X ≃ₜ Y)
  statement: h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm
  proof: rfl

@[simp]

中文:
定理 symm_toHomotopyEquiv
  条件: (h : X ≃ₜ Y)
  结论: h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm
  证明: rfl

@[simp]
-/
theorem symm_toHomotopyEquiv (h : X ≃ₜ Y) : h.symm.toHomotopyEquiv = h.toHomotopyEquiv.symm :=
  rfl

@[simp]
/--
theorem `trans_toHomotopyEquiv` / 定理 `trans_toHomotopyEquiv`

English:
theorem trans_toHomotopyEquiv
  given: (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z)
  proof: rfl

中文:
定理 trans_toHomotopyEquiv
  条件: (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z)
  证明: rfl
-/
theorem trans_toHomotopyEquiv (h₀ : X ≃ₜ Y) (h₁ : Y ≃ₜ Z) :
    (h₀.trans h₁).toHomotopyEquiv = h₀.toHomotopyEquiv.trans h₁.toHomotopyEquiv :=
  rfl

end Homeomorph
