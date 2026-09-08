/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/

@[expose] public section


universe u v

namespace MvQPF

open MvFunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
/-
**MvQPF.Prj** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Prj (v : TypeVec.{u} n) : Type u
参数：v : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `i` functor
-/
def Prj (v : TypeVec.{u} n) : Type u := v i
/-
**MvQPF.Prj.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → {v : TypeVec.{u} n} → [Inhabited (v i)] → Inhabit
ed (MvQPF.Prj i v)
参数：i : Fin2 n；v i；MvQPF.Prj i v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prj.inhabited {v : TypeVec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩

/-- `map` on functor `Prj i` -/
/-
**MvQPF.Prj.map** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → ⦃α : TypeVec.{u_1} n⦄ → ⦃β : TypeVec.{u_2} n⦄ → α
.Arrow β → MvQPF.Prj i α → MvQPF.Prj i β
参数：i : Fin2 n。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map` on functor `Prj i`
-/
def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α → Prj i β := f _
/-
**MvQPF.Prj.mvfunctor** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → MvFunctor (MvQPF.Prj i)
参数：i : Fin2 n；MvQPF.Prj i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prj.mvfunctor : MvFunctor (Prj i) where map := @Prj.map _ i

/-- Polynomial representation of the projection functor -/
/-
**MvQPF.Prj.P** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → Fin2 n → MvPFunctor.{u} n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Polynomial representation of the projection functor
-/
def Prj.P : MvPFunctor.{u} n where
  A := PUnit
  B _ j := ULift <| PLift <| i = j

/-- Abstraction function of the `QPF` instance -/
/-
**MvQPF.Prj.abs** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → ⦃α : TypeVec.{u_1} n⦄ → ↑(MvQPF.Prj.P i) α → MvQP
F.Prj i α
参数：i : Fin2 n。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abstraction function of the `QPF` instance
-/
def Prj.abs ⦃α : TypeVec n⦄ : Prj.P i α → Prj i α
  | ⟨_x, f⟩ => f _ ⟨⟨rfl⟩⟩

/-- Representation function of the `QPF` instance -/
/-
**MvQPF.Prj.repr** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → ⦃α : TypeVec.{u_1} n⦄ → MvQPF.Prj i α → ↑(MvQPF.P
rj.P i) α
参数：i : Fin2 n。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representation function of the `QPF` instance
-/
def Prj.repr ⦃α : TypeVec n⦄ : Prj i α → Prj.P i α := fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩
/-
**MvQPF.Prj.mvqpf** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Prj`。
形式化陈述：{n : ℕ} → (i : Fin2 n) → MvQPF (MvQPF.Prj i)
参数：i : Fin2 n；MvQPF.Prj i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prj.mvqpf : MvQPF (Prj i) where
  P := Prj.P i
  abs := @Prj.abs _ i
  repr := @Prj.repr _ i
  abs_repr := by intros; rfl
  abs_map := by intro α β f P; cases P; rfl

end MvQPF

