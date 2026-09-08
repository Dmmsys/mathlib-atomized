/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.TopCat.Path

/-!
# `ZerothHomotopy` and connected components of `TopCat.toSSet.obj X`

In this file, given `X : TopCat`, we define a bijection
`TopCat.zerothHomotopyEquiv` between `ZerothHomotopy X` and
`(TopCat.toSSet.obj X).π₀`.

-/

@[expose] public section

universe u

open Simplicial

namespace TopCat

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Given `X : TopCat`, this is the bijection between `1`-simplices of the
singular simplicial set of `X` and the type of morphisms `I ⟶ X`. -/
/-
**TopCat.toSSetObj** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : TopCat`, this is the bijection between `1`-simplices of the
singular simplicial set of `X` and the type of morphisms `I ⟶ X`.
-/
noncomputable def toSSetObj₁Equiv :
    toSSet.obj X _⦋1⦌ ≃ (I ⟶ X) :=
  (toSSetObjEquiv _ _).trans
    { toFun f := ofHom (f.comp (toContinuousMap TopCat.stdSimplexHomeomorphI.symm))
      invFun f := f.hom.comp TopCat.stdSimplexHomeomorphI
      left_inv _ := by simp
      right_inv _ := by simp }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TopCat.toSSetObj** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSetObj₁Equiv_apply_zero (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 0 = toSSetObj₀Equiv ((toSSet.obj X).δ 1 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TopCat.toSSetObj** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSSetObj₁Equiv_apply_one (s : toSSet.obj X _⦋1⦌) :
    X.toSSetObj₁Equiv s 1 = toSSetObj₀Equiv ((toSSet.obj X).δ 0 s) := by
  simp [toSSetObj₀Equiv, toSSetObj₁Equiv, -ContinuousMap.coe_mk,
    Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]

@[simp]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_one_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 1 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 0) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_zero])

@[simp]
/-
**TopCat.** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_zero_toSSetObj₁Equiv.symm (f : I ⟶ X) :
    (toSSet.obj X).δ 0 (toSSetObj₁Equiv.symm f) =
      toSSetObj₀Equiv.symm (f 1) :=
  toSSetObj₀Equiv.injective (by simp [← toSSetObj₁Equiv_apply_one])

/-- Given two points `x` and `y` of `X : TopCat`, this is the bijection between
edges in the simplicial set `toSSet.obj X` connecting the vertices corresponding
to `x` and `y`, and paths from `x` to `y`. -/
@[simps]
/-
**TopCat.toSSetObjEdgeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：toSSetObjEdgeEquiv {x y : X} : SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetO
bj₀Equiv.symm y) ≃ X.Path x y where toFun e
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given two points `x` and `y` of `X : TopCat`, this is the bijection between
edges in the simplicial set `toSSet.obj X` connecting the vertices corresponding
to `x` and `y`, and paths from `x` to `y`.
-/
noncomputable def toSSetObjEdgeEquiv {x y : X} :
    SSet.Edge (toSSetObj₀Equiv.symm x) (toSSetObj₀Equiv.symm y) ≃ X.Path x y where
  toFun e := { hom := toSSetObj₁Equiv e.edge }
  invFun p := SSet.Edge.mk (toSSetObj₁Equiv.symm p.hom)
  left_inv _ := by aesop
  right_inv _ := by aesop

/-- Given `X : TopCat`, this is the bijection between `ZerothHomotopy X` and the
type of connected components of the simplicial set `toSSet.obj X`. -/
/-
**TopCat.zerothHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TopCat`。
形式化陈述：zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `X : TopCat`, this is the bijection between `ZerothHomotopy X` and the
type of connected components of the simplicial set `toSSet.obj X`.
-/
noncomputable def zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀ where
  toFun :=
    ZerothHomotopy.lift (SSet.π₀.mk ∘ toSSetObj₀Equiv.symm)
      (fun _ _ p ↦ SSet.π₀.sound (toSSetObjEdgeEquiv.symm (pathEquiv.symm p)))
  invFun := SSet.π₀.lift (ZerothHomotopy.mk ∘ toSSetObj₀Equiv) (fun x y e ↦ by
    obtain ⟨x, rfl⟩ := toSSetObj₀Equiv.symm.surjective x
    obtain ⟨y, rfl⟩ := toSSetObj₀Equiv.symm.surjective y
    exact ZerothHomotopy.sound (pathEquiv (toSSetObjEdgeEquiv e)))
  left_inv x := by induction x; simp
  right_inv x := by induction x; simp

@[simp]
/-
**TopCat.zerothHomotopyEquiv_mk** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：zerothHomotopyEquiv_mk (x : X) : zerothHomotopyEquiv (.mk x) = .mk (toSSet
Obj₀Equiv.symm x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zerothHomotopyEquiv_mk (x : X) :
    zerothHomotopyEquiv (.mk x) = .mk (toSSetObj₀Equiv.symm x) := rfl

@[simp]
/-
**TopCat.zerothHomotopyEquiv_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 `TopCat`。
形式化陈述：zerothHomotopyEquiv_symm_mk (x : (toSSet.obj X) _⦋0⦌) : zerothHomotopyEqui
v.symm (.mk x) = .mk (toSSetObj₀Equiv x)
参数：x : (toSSet.obj X) _⦋0⦌。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma zerothHomotopyEquiv_symm_mk (x : (toSSet.obj X) _⦋0⦌) :
    zerothHomotopyEquiv.symm (.mk x) = .mk (toSSetObj₀Equiv x) := rfl
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PathConnectedSpace X] : (toSSet.obj X).IsConnected := by
  let : Unique (ZerothHomotopy X) := Nonempty.some (by
    rw [unique_iff_subsingleton_and_nonempty]
    constructor <;> infer_instance)
  rw [SSet.isConnected_iff_nonempty_unique]
  exact ⟨zerothHomotopyEquiv.symm.unique⟩

end TopCat

