/-
Copyright (c) 2021 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Fundamental group of a space

Given a topological space `X` and a basepoint `x`, the fundamental group is the automorphism group
of `x` i.e. the group with elements being loops based at `x` (quotiented by homotopy equivalence).
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open CategoryTheory

variable (X)

/-- The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid. -/
/-
**FundamentalGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FundamentalGroup (x : X)
参数：x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fundamental group is the automorphism group (vertex group) of the basepoint
in the fundamental groupoid.
-/
abbrev FundamentalGroup (x : X) :=
  End (FundamentalGroupoid.mk x)

variable {X}

namespace FundamentalGroup

variable {x : X} {p q : FundamentalGroup X x}

/-
**FundamentalGroup.one_def** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroup`。
形式化陈述：one_def : (1 : FundamentalGroup X x) = .refl x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : FundamentalGroup X x) = .refl x := rfl
/-
**FundamentalGroup.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroup`。
形式化陈述：mul_def : p * q = q.trans p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def : p * q = q.trans p := rfl
/-
**FundamentalGroup.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroup`。
形式化陈述：inv_def : p⁻¹ = p.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def : p⁻¹ = p.symm := rfl

/-- Get an isomorphism between the fundamental groups at two points given a path -/
/-
**FundamentalGroup.fundamentalGroupMulEquivOfPath** 是 Mathlib 中的一个定义，位于命名空间 `Fun
damentalGroup`。
形式化陈述：fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) : FundamentalGroup X x₀ ≃*
 FundamentalGroup X x₁
参数：p : Path x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Get an isomorphism between the fundamental groups at two points given a path
-/
def fundamentalGroupMulEquivOfPath (p : Path x₀ x₁) :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  ((Groupoid.isoEquivHom ..).symm ⟦p⟧).conj

variable (x₀ x₁)

/-- The fundamental group of a path connected space is independent of the choice of basepoint. -/
/-
**FundamentalGroup.fundamentalGroupMulEquivOfPathConnected** 是 Mathlib 中的一个定义，位于
命名空间 `FundamentalGroup`。
形式化陈述：fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] : Fundament
alGroup X x₀ ≃* FundamentalGroup X x₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fundamental group of a path connected space is independent of the choice of 
basepoint.
-/
def fundamentalGroupMulEquivOfPathConnected [PathConnectedSpace X] :
    FundamentalGroup X x₀ ≃* FundamentalGroup X x₁ :=
  fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath x₀ x₁)

/-- An element of the fundamental group as an arrow in the fundamental groupoid. -/
/-
**FundamentalGroup.toArrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroup`。
形式化陈述：toArrow {x : X} (p : FundamentalGroup X x) : FundamentalGroupoid.mk x ⟶ Fu
ndamentalGroupoid.mk x
参数：p : FundamentalGroup X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the fundamental group as an arrow in the fundamental groupoid.
-/
abbrev toArrow {x : X} (p : FundamentalGroup X x) :
    FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
  p

/-- An element of the fundamental group as a quotient of homotopic paths. -/
/-
**FundamentalGroup.toPath** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroup`。
形式化陈述：toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x
参数：p : FundamentalGroup X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the fundamental group as a quotient of homotopic paths.
-/
abbrev toPath {x : X} (p : FundamentalGroup X x) : Path.Homotopic.Quotient x x :=
  toArrow p

/-- An element of the fundamental group, constructed from an arrow in the fundamental groupoid. -/
/-
**FundamentalGroup.fromArrow** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroup`。
形式化陈述：fromArrow {x : X} (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x
) : FundamentalGroup X x
参数：p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the fundamental group, constructed from an arrow in the fundamenta
l groupoid.
-/
abbrev fromArrow {x : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) :
    FundamentalGroup X x :=
  p

/-- An element of the fundamental group, constructed from a quotient of homotopic paths. -/
/-
**FundamentalGroup.fromPath** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroup`。
形式化陈述：fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x
参数：p : Path.Homotopic.Quotient x x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the fundamental group, constructed from a quotient of homotopic pa
ths.
-/
abbrev fromPath {x : X} (p : Path.Homotopic.Quotient x x) : FundamentalGroup X x :=
  fromArrow p

/-- The homomorphism between fundamental groups induced by a continuous map. -/
/-
**FundamentalGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroup`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] →     
  [inst_1 : TopologicalSpace Y] → (f : C(X, Y)) → (x : X) → FundamentalGroup X x
 →* FundamentalGroup Y (f x)
参数：f : C(X, Y)；x : X；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism between fundamental groups induced by a continuous map.
-/
@[simps!] def map (f : C(X, Y)) (x : X) : FundamentalGroup X x →* FundamentalGroup Y (f x) :=
  (FundamentalGroupoid.map f).mapEnd _

variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- The homomorphism from π₁(X, x) to π₁(Y, y) induced by a continuous map `f` with `f x = y`. -/
/-
**FundamentalGroup.mapOfEq** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroup`。
形式化陈述：mapOfEq : FundamentalGroup X x ->* FundamentalGroup Y y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homomorphism from π₁(X, x) to π₁(Y, y) induced by a continuous map `f` with 
`f x = y`.
-/
def mapOfEq : FundamentalGroup X x →* FundamentalGroup Y y :=
  (eqToIso <| congr_arg FundamentalGroupoid.mk h).conj.toMonoidHom.comp (map f x)
/-
**FundamentalGroup.mapOfEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroup`。
形式化陈述：mapOfEq_apply (p : FundamentalGroup X x) : mapOfEq f h p = (Path.Homotopic
.Quotient.map p f).cast h.symm h.symm
参数：p : FundamentalGroup X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FundamentalGroupoid.conj_eqToHom`：conj_eqToHom {x y x' y' : X} {p : Path
.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y) : eqToHom congr(mk $hx) ≫ p
 ≫ eqToHom congr(mk $h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mapOfEq_apply (p : FundamentalGroup X x) :
    mapOfEq f h p = (Path.Homotopic.Quotient.map p f).cast h.symm h.symm :=
  FundamentalGroupoid.conj_eqToHom ..

end FundamentalGroup

