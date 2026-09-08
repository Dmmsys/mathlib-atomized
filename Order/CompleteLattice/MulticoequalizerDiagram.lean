/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.SetLike

/-!
# Multicoequalizer diagrams in complete lattices

We introduce the notion of bi-Cartesian square (`Lattice.BicartSq`) in a lattice `T`.
This consists of elements `x₁`, `x₂`, `x₃` and `x₄` such that `x₂ ⊔ x₃ = x₄` and
`x₂ ⊓ x₃ = x₁`.

It shall be shown (TODO) that if `T := Set X`, then the image of the
associated commutative square in the category `Type _` is a bi-Cartesian square
in a categorical sense (both pushout and pullback).

More generally, if `T` is a complete lattice, `x : T`, `u : ι → T`, `v : ι → ι → T`,
we introduce a property `MulticoequalizerDiagram x u v` which says that `x` is
the supremum of `u`, and that for all `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
Again, when `T := Set X`, we shall show (TODO) that we obtain a multicoequalizer diagram
in the category of types.

-/

@[expose] public section

universe u

open CategoryTheory Limits

local grind_pattern inf_le_left => a ⊓ b
local grind_pattern inf_le_right => a ⊓ b
local grind_pattern le_sup_left => a ⊔ b
local grind_pattern le_sup_right => a ⊔ b

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

/-- A bi-Cartesian square in a lattice consists of elements `x₁`, `x₂`, `x₃` and `x₄`
such that `x₂ ⊔ x₃ = x₄` and `x₂ ⊓ x₃ = x₁`. -/
/-
**Lattice.BicartSq** 是 Mathlib 中的一个归纳类型，位于命名空间 `Lattice`。
形式化陈述：{T : Type u} → T → T → T → T → [Lattice T] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bi-Cartesian square in a lattice consists of elements `x₁`, `x₂`, `x₃` and `x₄
`
such that `x₂ ⊔ x₃ = x₄` and `x₂ ⊓ x₃ = x₁`.
-/
structure BicartSq : Prop where
  sup_eq : x₂ ⊔ x₃ = x₄
  inf_eq : x₂ ⊓ x₃ = x₁

attribute [grind cases] BicartSq

namespace BicartSq

variable {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq

/-
**Lattice.BicartSq.le** 是 Mathlib 中的一个引理，位于命名空间 `Lattice.BicartSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₁₂ : x₁ ≤ x₂ := by grind
/-
**Lattice.BicartSq.le** 是 Mathlib 中的一个引理，位于命名空间 `Lattice.BicartSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₁₃ : x₁ ≤ x₃ := by grind
/-
**Lattice.BicartSq.le** 是 Mathlib 中的一个引理，位于命名空间 `Lattice.BicartSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₂₄ : x₂ ≤ x₄ := by grind
/-
**Lattice.BicartSq.le** 是 Mathlib 中的一个引理，位于命名空间 `Lattice.BicartSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le₃₄ : x₃ ≤ x₄ := by grind

/-- The commutative square associated to a bi-Cartesian square in a lattice. -/
/-
**Lattice.BicartSq.commSq** 是 Mathlib 中的一个引理，位于命名空间 `Lattice.BicartSq`。
形式化陈述：commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃) (homOfLE sq.le₂₄) (hom
OfLE sq.le₃₄)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Lattice.BicartSq.le₁₂`：le₁₂ : x₁ <= x₂
· 使用引理 `Lattice.BicartSq.le₁₃`：le₁₃ : x₁ <= x₃
· 使用引理 `Lattice.BicartSq.le₂₄`：le₂₄ : x₂ <= x₄
· 使用引理 `Lattice.BicartSq.le₃₄`：le₃₄ : x₃ <= x₄

--- 原说明 ---
The commutative square associated to a bi-Cartesian square in a lattice.
-/
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice

namespace CompleteLattice

variable {T : Type u} [CompleteLattice T] {ι : Type*} (x : T) (u : ι → T) (v : ι → ι → T)

/-- A multicoequalizer diagram in a complete lattice `T` consists of families of elements
`u : ι → T`, `v : ι → ι → T`, and an element `x : T` such that `x` is the supremum of `u`,
and for any `i` and `j`, `v i j` is the minimum of `u i` and `u j`. -/
/-
**CompleteLattice.MulticoequalizerDiagram** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompleteL
attice`。
形式化陈述：{T : Type u} → [CompleteLattice T] → {ι : Type u_1} → T → (ι → T) → (ι → ι
 → T) → Prop
参数：ι → T；ι → ι → T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multicoequalizer diagram in a complete lattice `T` consists of families of ele
ments
`u : ι → T`, `v : ι → ι → T`, and an element `x : T` such that `x` is the suprem
um of `u`,
and for any `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
-/
structure MulticoequalizerDiagram : Prop where
  iSup_eq : ⨆ (i : ι), u i = x
  eq_inf (i j : ι) : v i j = u i ⊓ u j

namespace MulticoequalizerDiagram

attribute [local grind] MulticoequalizerDiagram
attribute [local grind =] MultispanShape.prod_fst MultispanShape.prod_snd

variable {x u v} (d : MulticoequalizerDiagram x u v)

/-- The multispan index in the category associated to the complete lattice `T`
given by the objects `u i` and the minima `v i j = u i ⊓ u j`,
when `d : MulticoequalizerDiagram x u v`. -/
@[simps]
/-
**CompleteLattice.MulticoequalizerDiagram.multispanIndex** 是 Mathlib 中的一个定义，位于命名
空间 `CompleteLattice.MulticoequalizerDiagram`。
形式化陈述：multispanIndex : MultispanIndex (.prod ι) T where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multispan index in the category associated to the complete lattice `T`
given by the objects `u i` and the minima `v i j = u i ⊓ u j`,
when `d : MulticoequalizerDiagram x u v`.
-/
def multispanIndex : MultispanIndex (.prod ι) T where
  left := fun ⟨i, j⟩ ↦ v i j
  right := u
  fst _ := homOfLE (by grind)
  snd _ := homOfLE (by grind)

/-- The multicofork in the category associated to the complete lattice `T`
associated to `d : MulticoequalizerDiagram x u v` with `x : T`.
(In the case `T := Set X`, this multicofork becomes colimit after the application
of the obvious functor `Set X ⥤ Type _`.) -/
@[simps! pt]
/-
**CompleteLattice.MulticoequalizerDiagram.multicofork** 是 Mathlib 中的一个定义，位于命名空间 
`CompleteLattice.MulticoequalizerDiagram`。
形式化陈述：multicofork : Multicofork d.multispanIndex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multicofork in the category associated to the complete lattice `T`
associated to `d : MulticoequalizerDiagram x u v` with `x : T`.
(In the case `T := Set X`, this multicofork becomes colimit after the applicatio
n
of the obvious functor `Set X ⥤ Type _`.)
-/
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ x (fun i ↦ homOfLE (by grind [multispanIndex_right, le_iSup_iff]))
    (fun _ ↦ rfl)

end MulticoequalizerDiagram

end CompleteLattice

/-
**Lattice.BicartSq.multicoequalizerDiagram** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Lattice.BicartSq.multicoequalizerDiagram {T : Type u} [CompleteLattice T] 
{x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄) : CompleteLattice.MulticoequalizerDiag
ram (T
参数：sq : BicartSq x₁ x₂ x₃ x₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lattice.BicartSq.sup_eq`：∀ {T : Type u} {x₁ x₂ x₃ x₄ : T} [inst : Lattic
e T], Lattice.BicartSq x₁ x₂ x₃ x₄ → x₂ ⊔ x₃ = x₄
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
-/
lemma Lattice.BicartSq.multicoequalizerDiagram {T : Type u} [CompleteLattice T]
    {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄) :
    CompleteLattice.MulticoequalizerDiagram (T := T) x₄
      (fun i ↦ bif i then x₃ else x₂)
      (fun i j ↦ bif i then bif j then x₃ else x₁
        else bif j then x₁ else x₂) where
  iSup_eq := by rw [← sq.sup_eq, sup_comm, sup_eq_iSup]
  eq_inf i j := by grind
