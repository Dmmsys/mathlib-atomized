/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# Dependent product and sum of QPFs are QPFs
-/

@[expose] public section


universe u

namespace MvQPF

open MvFunctor

variable {n : ℕ} {A : Type u}
variable (F : A → TypeVec.{u} n → Type u)

/-- Dependent sum of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
/-
**MvQPF.Sigma** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Sigma (v : TypeVec.{u} n) : Type u
参数：v : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent sum of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}`
-/
def Sigma (v : TypeVec.{u} n) : Type u :=
  Σ α : A, F α v

/-- Dependent product of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
/-
**MvQPF.Pi** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Pi (v : TypeVec.{u} n) : Type u
参数：v : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent product of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}`
-/
def Pi (v : TypeVec.{u} n) : Type u :=
  ∀ α : A, F α v
/-
**MvQPF.Sigma.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Sigma`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) →       {α
 : TypeVec.{u} n} → [inst : Inhabited A] → [Inhabited (F default α)] → Inhabited
 (MvQPF.Sigma F α)
参数：F : A → TypeVec.{u} n → Type u；F default α；MvQPF.Sigma F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sigma.inhabited {α} [Inhabited A] [Inhabited (F default α)] : Inhabited (Sigma F α) :=
  ⟨⟨default, default⟩⟩
/-
**MvQPF.Pi.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Pi`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) → {α : Typ
eVec.{u} n} → [(a : A) → Inhabited (F a α)] → Inhabited (MvQPF.Pi F α)
参数：F : A → TypeVec.{u} n → Type u；a : A；F a α；MvQPF.Pi F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.inhabited {α} [∀ a, Inhabited (F a α)] : Inhabited (Pi F α) :=
  ⟨fun _a => default⟩

namespace Sigma

/-
**MvQPF.Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ α, MvFunctor <| F α] : MvFunctor (Sigma F) where
  map := fun f ⟨a, x⟩ => ⟨a, f <$$> x⟩


variable [∀ α, MvQPF <| F α]

/-- polynomial functor representation of a dependent sum -/
/-
**MvQPF.Sigma.P** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Sigma`。
形式化陈述：{n : ℕ} → {A : Type u} → (F : A → TypeVec.{u} n → Type u) → [(α : A) → MvQ
PF (F α)] → MvPFunctor.{u} n
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
polynomial functor representation of a dependent sum
-/
protected def P : MvPFunctor n :=
  ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩

/-- abstraction function for dependent sums -/
/-
**MvQPF.Sigma.abs** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Sigma`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) →       [i
nst : (α : A) → MvQPF (F α)] → ⦃α : TypeVec.{u} n⦄ → ↑(MvQPF.Sigma.P F) α → MvQP
F.Sigma F α
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
abstraction function for dependent sums
-/
protected def abs ⦃α⦄ : Sigma.P F α → Sigma F α
  | ⟨a, f⟩ => ⟨a.1, MvQPF.abs ⟨a.2, f⟩⟩

/-- representation function for dependent sums -/
/-
**MvQPF.Sigma.repr** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Sigma`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) →       [i
nst : (α : A) → MvQPF (F α)] → ⦃α : TypeVec.{u} n⦄ → MvQPF.Sigma F α → ↑(MvQPF.S
igma.P F) α
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
representation function for dependent sums
-/
protected def repr ⦃α⦄ : Sigma F α → Sigma.P F α
  | ⟨a, f⟩ =>
    let x := MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MvQPF (Sigma F) where
  P := Sigma.P F
  abs {α} := @Sigma.abs _ _ F _ α
  repr {α} := @Sigma.repr _ _ F _ α
  abs_repr := by rintro α ⟨x, f⟩; simp only [Sigma.abs, Sigma.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Sigma.abs, MvPFunctor.map_eq]
                simp only [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]

end Sigma

namespace Pi

/-
**MvQPF.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ α, MvFunctor <| F α] : MvFunctor (Pi F) where map f x a := f <$$> x a

variable [∀ α, MvQPF <| F α]

/-- polynomial functor representation of a dependent product -/
/-
**MvQPF.Pi.P** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Pi`。
形式化陈述：{n : ℕ} → {A : Type u} → (F : A → TypeVec.{u} n → Type u) → [(α : A) → MvQ
PF (F α)] → MvPFunctor.{u} n
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
polynomial functor representation of a dependent product
-/
protected def P : MvPFunctor n :=
  ⟨∀ a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩

/-- abstraction function for dependent products -/
/-
**MvQPF.Pi.abs** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Pi`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) →       [i
nst : (α : A) → MvQPF (F α)] → ⦃α : TypeVec.{u} n⦄ → ↑(MvQPF.Pi.P F) α → MvQPF.P
i F α
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
abstraction function for dependent products
-/
protected def abs ⦃α⦄ : Pi.P F α → Pi F α
  | ⟨a, f⟩ => fun x => MvQPF.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩

/-- representation function for dependent products -/
/-
**MvQPF.Pi.repr** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Pi`。
形式化陈述：{n : ℕ} →   {A : Type u} →     (F : A → TypeVec.{u} n → Type u) →       [i
nst : (α : A) → MvQPF (F α)] → ⦃α : TypeVec.{u} n⦄ → MvQPF.Pi F α → ↑(MvQPF.Pi.P
 F) α
参数：F : A → TypeVec.{u} n → Type u；α : A；F α。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
representation function for dependent products
-/
protected def repr ⦃α⦄ : Pi F α → Pi.P F α
  | f => ⟨fun a => (MvQPF.repr (f a)).1, fun _i a => (MvQPF.repr (f _)).2 _ a.2⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.Pi.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MvQPF (Pi F) where
  P := Pi.P F
  abs := @Pi.abs _ _ F _
  repr := @Pi.repr _ _ F _
  abs_repr := by
    rintro α f
    simp +instances only [Pi.abs, Pi.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Pi.abs, (· <$$> ·), ← abs_map]; rfl

end Pi

end MvQPF

