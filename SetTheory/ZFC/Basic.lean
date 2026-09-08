/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.SetTheory.ZFC.PSet

/-!
# A model of ZFC

In this file, we model Zermelo-Fraenkel set theory (+ choice) using Lean's underlying type theory,
building on the pre-sets defined in `Mathlib/SetTheory/ZFC/PSet.lean`.

The theory of classes is developed in `Mathlib/SetTheory/ZFC/Class.lean`.

## Main definitions

* `ZFSet`: ZFC set. Defined as `PSet` quotiented by `PSet.Equiv`, the extensional equivalence.
* `ZFSet.choice`: Axiom of choice. Proved from Lean's axiom of choice.
* `ZFSet.omega`: The von Neumann ordinal `ω` as a `Set`.
* `Classical.allZFSetDefinable`: All functions are classically definable.
* `ZFSet.IsFunc` : Predicate that a ZFC set is a subset of `x × y` that can be considered as a ZFC
  function `x → y`. That is, each member of `x` is related by the ZFC set to exactly one member of
  `y`.
* `ZFSet.funs`: ZFC set of ZFC functions `x → y`.
* `ZFSet.Hereditarily p x`: Predicate that every set in the transitive closure of `x` has property
  `p`.

## Notes

To avoid confusion between the Lean `Set` and the ZFC `Set`, docstrings in this file refer to them
respectively as "`Set`" and "ZFC set".
-/

@[expose] public section


universe u

/-- The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence. -/
@[pp_with_univ, use_set_notation_for_order]
/-
**ZFSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ZFSet : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ZFC universe of sets consists of the type of pre-sets,
  quotiented by extensional equivalence.
-/
def ZFSet : Type (u + 1) :=
  Quotient PSet.setoid.{u}

namespace ZFSet

/-- Turns a pre-set into a ZFC set. -/
/-
**ZFSet.mk** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：mk : PSet -> ZFSet
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Turns a pre-set into a ZFC set.
-/
def mk : PSet → ZFSet :=
  Quotient.mk''

@[simp]
/-
**ZFSet.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x)
参数：x : PSet。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x) :=
  rfl

@[simp]
/-
**ZFSet.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mk_out : forall x : ZFSet, mk x.out = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem mk_out : ∀ x : ZFSet, mk x.out = x :=
  Quotient.out_eq

/-- A set function is "definable" if it is the image of some n-ary `PSet`
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set function is "definable" if it is the image of some n-ary `PSet`
  function. This isn't exactly definability, but is useful as a sufficient
  condition for functions that have a computable image.
-/
class Definable (n) (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) where
  /-- Turns a definable function into an n-ary `PSet` function. -/
  out : (Fin n → PSet.{u}) → PSet.{u}
  /-- A set function `f` is the image of `Definable.out f`. -/
  mk_out xs : mk (out xs) = f (mk <| xs ·) := by simp

attribute [simp] Definable.mk_out

/-- An abbrev of `ZFSet.Definable` for unary functions. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbrev of `ZFSet.Definable` for unary functions.
-/
abbrev Definable₁ (f : ZFSet.{u} → ZFSet.{u}) := Definable 1 (fun s ↦ f (s 0))

/-- A simpler constructor for `ZFSet.Definable₁`. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simpler constructor for `ZFSet.Definable₁`.
-/
abbrev Definable₁.mk {f : ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u}) (mk_out : ∀ x, ⟦out x⟧ = f ⟦x⟧) :
    Definable₁ f where
  out xs := out (xs 0)
  mk_out xs := mk_out (xs 0)

/-- Turns a unary definable function into a unary `PSet` function. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a unary definable function into a unary `PSet` function.
-/
abbrev Definable₁.out (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f] :
    PSet.{u} → PSet.{u} :=
  fun x ↦ Definable.out (fun s ↦ f (s 0)) ![x]
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Definable₁.mk_out {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f]
    {x : PSet} :
    .mk (out f x) = f (.mk x) :=
  Definable.mk_out ![x]

/-- An abbrev of `ZFSet.Definable` for binary functions. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbrev of `ZFSet.Definable` for binary functions.
-/
abbrev Definable₂ (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) := Definable 2 (fun s ↦ f (s 0) (s 1))

/-- A simpler constructor for `ZFSet.Definable₂`. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simpler constructor for `ZFSet.Definable₂`.
-/
abbrev Definable₂.mk {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    (out : PSet.{u} → PSet.{u} → PSet.{u}) (mk_out : ∀ x y, ⟦out x y⟧ = f ⟦x⟧ ⟦y⟧) :
    Definable₂ f where
  out xs := out (xs 0) (xs 1)
  mk_out xs := mk_out (xs 0) (xs 1)

/-- Turns a binary definable function into a binary `PSet` function. -/
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turns a binary definable function into a binary `PSet` function.
-/
abbrev Definable₂.out (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f] :
    PSet.{u} → PSet.{u} → PSet.{u} :=
  fun x y ↦ Definable.out (fun s ↦ f (s 0) (s 1)) ![x, y]
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Definable₂.mk_out {f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}} [Definable₂ f]
    {x y : PSet} :
    .mk (out f x y) = f (.mk x) (.mk y) :=
  Definable.mk_out ![x, y]
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f) [Definable₁ f] (n g) [Definable n g] :
    Definable n (fun s ↦ f (g s)) where
  out xs := Definable₁.out f (Definable.out g xs)
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f) [Definable₂ f] (n g₁ g₂) [Definable n g₁] [Definable n g₂] :
    Definable n (fun s ↦ f (g₁ s) (g₂ s)) where
  out xs := Definable₂.out f (Definable.out g₁ xs) (Definable.out g₂ xs)
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n) (i) : Definable n (fun s ↦ s i) where
  out s := s i
/-
**ZFSet.Definable.out_equiv** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.Definable`。
形式化陈述：∀ {n : ℕ} (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) [inst : ZFSet.Definable n 
f] {xs ys : Fin n → PSet.{u}},   (∀ (i : Fin n), xs i ≈ ys i) → ZFSet.Definable.
out f xs ≈ ZFSet.Definable.out f ys
参数：f : (Fin n → ZFSet.{u}) → ZFSet.{u}；∀ (i : Fin n), xs i ≈ ys i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.eq_iff_equiv`：Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : 
Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
· 使用定理 `ZFSet.mk_eq`：mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x)
· 使用定理 `ZFSet.Definable.mk_out`：∀ {n : ℕ} {f : (Fin n → ZFSet.{u}) → ZFSet.{u}} 
[self : ZFSet.Definable n f] (xs : Fin n → PSet.{u}),   ZFSet.mk (ZFSet.Definabl
e.out f xs) …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
lemma Definable.out_equiv {n} (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) [Definable n f]
    {xs ys : Fin n → PSet} (h : ∀ i, xs i ≈ ys i) :
    out f xs ≈ out f ys := by
  rw [← Quotient.eq_iff_equiv, mk_eq, mk_eq, mk_out, mk_out]
  exact congrArg _ (funext fun i ↦ Quotient.sound (h i))
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Definable₁.out_equiv (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f]
    {x y : PSet} (h : x ≈ y) :
    out f x ≈ out f y :=
  Definable.out_equiv _ (by simp [h])
/-
**ZFSet.Definable** 是 Mathlib 中的一个类，位于命名空间 `ZFSet`。
形式化陈述：Definable (n) (f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) where /-- Turns a de
finable function into an n-ary `PSet` function. -/ out : (Fin n -> PSet.{u}) -> 
PSet.{u} /-- A set function `f` is the image of `Definable.out f`. -/ mk_out xs 
: mk (out xs) = f (mk <| xs ·)
参数：n；f : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Definable₂.out_equiv (f : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}) [Definable₂ f]
    {x₁ y₁ x₂ y₂ : PSet} (h₁ : x₁ ≈ y₁) (h₂ : x₂ ≈ y₂) :
    out f x₁ x₂ ≈ out f y₁ y₂ :=
  Definable.out_equiv _ (by simp [Fin.forall_fin_succ, h₁, h₂])

end ZFSet

namespace Classical

open PSet ZFSet

/-- All functions are classically definable. -/
@[instance_reducible]
/-
**Classical.allZFSetDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Classical`。
形式化陈述：allZFSetDefinable {n} (F : (Fin n -> ZFSet.{u}) -> ZFSet.{u}) : Definable 
n F where out xs
参数：F : (Fin n -> ZFSet.{u}) -> ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All functions are classically definable.
-/
noncomputable def allZFSetDefinable {n} (F : (Fin n → ZFSet.{u}) → ZFSet.{u}) : Definable n F where
  out xs := (F (mk <| xs ·)).out

end Classical

namespace ZFSet
variable {x y z : ZFSet.{u}}

open PSet

/-
**ZFSet.eq** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：eq {x y : PSet} : mk x = mk y ↔ Equiv x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem eq {x y : PSet} : mk x = mk y ↔ Equiv x y :=
  Quotient.eq
/-
**ZFSet.sound** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y
参数：h : PSet.Equiv x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y :=
  Quotient.sound h
/-
**ZFSet.exact** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：exact {x y : PSet} : mk x = mk y -> PSet.Equiv x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
theorem exact {x y : PSet} : mk x = mk y → PSet.Equiv x y :=
  Quotient.exact

/-- Convert a ZFC set into a `Set` of ZFC sets -/
/-
**ZFSet.toSet** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：toSet (x : ZFSet) : Set ZFSet
参数：x : ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a ZFC set into a `Set` of ZFC sets
-/
def toSet (x : ZFSet) : Set ZFSet :=
  {y | Quotient.lift₂ (· ∈ ·) (fun _ _ _ _ hx hy =>
    propext ((Mem.congr_left hx).trans (Mem.congr_right hy))) y x}
/-
**ZFSet.ext_aux** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ext_aux : (∀ z : ZFSet.{u}, z ∈ x.toSet ↔ z ∈ y.toSet) → x = y :=
  Quotient.inductionOn₂ x y fun _ _ h => Quotient.sound (Mem.ext fun w => h ⟦w⟧)
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike ZFSet.{u} ZFSet.{u} where
  coe := toSet
  coe_injective x y hxy := by apply ext_aux; intro z; exact congr(z ∈ $hxy)

/-- The membership relation for ZFC sets is inherited from the membership relation for pre-sets. -/
@[deprecated "use `∈` notation" (since := "2026-03-16")]
/-
**ZFSet.Mem** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u_1} → ZFSet.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The membership relation for ZFC sets is inherited from the membership relation f
or pre-sets.
-/
protected def Mem : ZFSet → ZFSet → Prop := (· ∈ ·)

@[simp]
/-
**ZFSet.mk_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mk_mem_iff {x y : PSet} : mk x in mk y ↔ x in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_mem_iff {x y : PSet} : mk x ∈ mk y ↔ x ∈ y :=
  Iff.rfl
/-
**ZFSet.ext** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x = y
参数：∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.SetTheory.ZFC.Basic.0.ZFSet.ext_aux`：∀ {x y : ZFSet.{u}
}, (∀ (z : ZFSet.{u}), z ∈ x.toSet ↔ z ∈ y.toSet) → x = y
-/
@[ext] lemma ext : (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y := ext_aux
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder ZFSet.{u} := .ofSetLike ZFSet.{u} ZFSet.{u}
/-
**ZFSet.small_coe** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
形式化陈述：small_coe (x : ZFSet.{u}) : Small.{u} x
参数：x : ZFSet.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `PSet.func_mem`：func_mem (x : PSet) (i : x.Type) : x.Func i in x
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
-/
instance small_coe (x : ZFSet.{u}) : Small.{u} x :=
  Quotient.inductionOn x fun a => by
    let f (i : a.Type) : mk a := ⟨mk <| a.Func i, func_mem a i⟩
    suffices Function.Surjective f by exact small_of_surjective this
    rintro ⟨y, hb⟩
    induction y using Quotient.inductionOn
    obtain ⟨i, h⟩ := hb
    exact ⟨i, Subtype.coe_injective (Quotient.sound h.symm)⟩

/-- A nonempty set is one that contains some element. -/
/-
**ZFSet.Nonempty** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty set is one that contains some element.
-/
protected def Nonempty (u : ZFSet.{u}) : Prop := (u : Set ZFSet.{u}).Nonempty
/-
**ZFSet.nonempty_def** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：nonempty_def (u : ZFSet) : u.Nonempty ↔ exists x, x in u
参数：u : ZFSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_def (u : ZFSet) : u.Nonempty ↔ ∃ x, x ∈ u :=
  Iff.rfl
/-
**ZFSet.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：nonempty_of_mem {x u : ZFSet} (h : x in u) : u.Nonempty
参数：h : x in u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_of_mem {x u : ZFSet} (h : x ∈ u) : u.Nonempty :=
  ⟨x, h⟩
/-
**ZFSet.nonempty_coe** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x : ZFSet.{u}}, (↑x).Nonempty ↔ x.Nonempty
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma nonempty_coe : (x : Set ZFSet.{u}).Nonempty ↔ x.Nonempty := .rfl

@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/-
**ZFSet.le_def** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：le_def : x <= y ↔ x subseteq y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def : x ≤ y ↔ x ⊆ y := .rfl
@[deprecated "This is now a syntactic equality" (since := "2026-03-18"), nolint synTaut]
/-
**ZFSet.lt_def** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：lt_def : x < y ↔ x ⊂ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_def : x < y ↔ x ⊂ y := .rfl
/-
**ZFSet.subset_def** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：subset_def {x y : ZFSet.{u}} : x subseteq y ↔ forall ⦃z⦄, z in x -> z in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subset_def {x y : ZFSet.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  Iff.rfl
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Refl ZFSet (· ⊆ ·) :=
  ⟨fun _ _ => id⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans ZFSet (· ⊆ ·) :=
  ⟨fun _ _ _ hxy hyz _ ha => hyz (hxy ha)⟩

@[simp]
/-
**ZFSet.subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：subset_iff : forall {x y : PSet}, mk x subseteq mk y ↔ x subseteq y | ⟨_, 
A⟩, ⟨_, _⟩ => ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z => Quotient.inductionOn
 z fun _ ⟨a, za⟩ => let ⟨b, ab⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `PSet.Equiv.trans`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}} {z : PSet.{u_3}}, 
x.Equiv y → y.Equiv z → x.Equiv z
-/
theorem subset_iff : ∀ {x y : PSet}, mk x ⊆ mk y ↔ x ⊆ y
  | ⟨_, A⟩, ⟨_, _⟩ =>
    ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z =>
      Quotient.inductionOn z fun _ ⟨a, za⟩ =>
        let ⟨b, ab⟩ := h a
        ⟨b, za.trans ab⟩⟩
/-
**ZFSet.coe_subset_coe** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_subset_coe : (x : Set ZFSet.{u}) subseteq y ↔ x subseteq y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
-/
lemma coe_subset_coe : (x : Set ZFSet.{u}) ⊆ y ↔ x ⊆ y := SetLike.coe_subset_coe
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Antisymm ZFSet (· ⊆ ·) :=
  ⟨@le_antisymm ZFSet _⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNonstrictStrictOrder ZFSet (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ ↦ Iff.rfl⟩

/-- The empty ZFC set -/
/-
**ZFSet.empty** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty ZFC set
-/
protected def empty : ZFSet :=
  mk ∅
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection ZFSet :=
  ⟨ZFSet.empty⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ZFSet :=
  ⟨∅⟩

@[simp]
/-
**ZFSet.notMem_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
参数：x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `PSet.notMem_empty`：notMem_empty (x : PSet.{u}) : x ∉ (∅ : PSet.{u})
-/
theorem notMem_empty (x) : x ∉ (∅ : ZFSet.{u}) :=
  Quotient.inductionOn x PSet.notMem_empty
/-
**ZFSet.coe_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：↑∅ = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma coe_empty : ((∅ : ZFSet.{u}) : Set ZFSet.{u}) = ∅ := by ext; simp

@[simp]
/-
**ZFSet.empty_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) subseteq x
参数：x : ZFSet.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.subset_iff`：subset_iff : forall {x y : PSet}, mk x subseteq mk y ↔
 x subseteq y | ⟨_, A⟩, ⟨_, _⟩ => ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z => 
Quotie…
· 使用定理 `PSet.empty_subset`：empty_subset (x : PSet.{u}) : (∅ : PSet) subseteq x
-/
theorem empty_subset (x : ZFSet.{u}) : (∅ : ZFSet) ⊆ x :=
  Quotient.inductionOn x fun y => subset_iff.2 <| PSet.empty_subset y

@[simp]
/-
**ZFSet.not_nonempty_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：not_nonempty_empty : ¬ZFSet.Nonempty ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.coe_empty`：↑∅ = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_nonempty_empty : ¬ZFSet.Nonempty ∅ := by simp [ZFSet.Nonempty]

@[simp]
/-
**ZFSet.nonempty_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem nonempty_mk_iff {x : PSet} : (mk x).Nonempty ↔ x.Nonempty := by
  refine ⟨?_, fun ⟨a, h⟩ => ⟨mk a, h⟩⟩
  rintro ⟨a, h⟩
  induction a using Quotient.inductionOn
  exact ⟨_, h⟩
/-
**ZFSet.eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u}, y ∉ x
参数：x : ZFSet.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_empty (x : ZFSet.{u}) : x = ∅ ↔ ∀ y : ZFSet.{u}, y ∉ x := by
  simp [ZFSet.ext_iff]
/-
**ZFSet.eq_empty_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u.Nonempty
参数：u : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.eq_empty`：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u},
 y ∉ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
-/
theorem eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u.Nonempty := by
  rw [eq_empty, ← not_exists]
  apply em'

/-- `Insert x y` is the set `{x} ∪ y` -/
/-
**ZFSet.Insert** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u_1} → ZFSet.{u_1} → ZFSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Insert x y` is the set `{x} ∪ y`
-/
protected def Insert : ZFSet → ZFSet → ZFSet :=
  Quotient.map₂ PSet.insert
    fun _ _ uv ⟨_, _⟩ ⟨_, _⟩ ⟨αβ, βα⟩ =>
      ⟨fun o =>
        match o with
        | some a =>
          let ⟨b, hb⟩ := αβ a
          ⟨some b, hb⟩
        | none => ⟨none, uv⟩,
        fun o =>
        match o with
        | some b =>
          let ⟨a, ha⟩ := βα b
          ⟨some a, ha⟩
        | none => ⟨none, uv⟩⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Insert ZFSet ZFSet :=
  ⟨ZFSet.Insert⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Singleton ZFSet ZFSet :=
  ⟨fun x => insert x ∅⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulSingleton ZFSet ZFSet :=
  ⟨fun _ => rfl⟩

@[simp]
/-
**ZFSet.mem_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_insert_iff {x y z : ZFSet.{u}} : x in insert y z ↔ x = y ∨ x in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₃`：∀ {α : Sort uA} {β : Sort uB} {φ : Sort uC} {s₁ :
 Setoid α} {s₂ : Setoid β} {s₃ : Setoid φ}   {motive : Quotient s₁ → Quotient s₂
 → Quotient…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.mem_insert_iff`：∀ {x y z : PSet.{u}}, x ∈ insert y z ↔ x.Equiv y ∨ 
x ∈ z
· 使用定理 `or_congr_left`：∀ {a b c : Prop}, (a ↔ b) → (a ∨ c ↔ b ∨ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ZFSet.eq`：eq {x y : PSet} : mk x = mk y ↔ Equiv x y
-/
theorem mem_insert_iff {x y z : ZFSet.{u}} : x ∈ insert y z ↔ x = y ∨ x ∈ z :=
  Quotient.inductionOn₃ x y z fun _ _ _ => PSet.mem_insert_iff.trans (or_congr_left eq.symm)
/-
**ZFSet.mem_insert** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_insert (x y : ZFSet) : x in insert x y
参数：x y : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.mem_insert_iff`：mem_insert_iff {x y z : ZFSet.{u}} : x in insert y
 z ↔ x = y ∨ x in z
-/
theorem mem_insert (x y : ZFSet) : x ∈ insert x y :=
  mem_insert_iff.2 <| Or.inl rfl
/-
**ZFSet.mem_insert_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_insert_of_mem {y z : ZFSet} (x) (h : z in y) : z in insert x y
参数：x；h : z in y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.mem_insert_iff`：mem_insert_iff {x y z : ZFSet.{u}} : x in insert y
 z ↔ x = y ∨ x in z
-/
theorem mem_insert_of_mem {y z : ZFSet} (x) (h : z ∈ y) : z ∈ insert x y :=
  mem_insert_iff.2 <| Or.inr h

@[simp, norm_cast]
/-
**ZFSet.coe_insert** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_insert (x y : ZFSet) : ↑(insert x y) = (insert x ↑y : Set ZFSet)
参数：x y : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_insert (x y : ZFSet) : ↑(insert x y) = (insert x ↑y : Set ZFSet) := by ext; simp

@[simp]
/-
**ZFSet.mem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_singleton {x y : ZFSet.{u}} : x in ({y} : ZFSet.{u}) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.mem_singleton`：mem_singleton {x y : PSet} : x in ({y} : PSet) ↔ Equ
iv x y
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ZFSet.eq`：eq {x y : PSet} : mk x = mk y ↔ Equiv x y
-/
theorem mem_singleton {x y : ZFSet.{u}} : x ∈ ({y} : ZFSet.{u}) ↔ x = y :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_singleton.trans eq.symm
/-
**ZFSet.notMem_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：notMem_singleton {x y : ZFSet.{u}} : x ∉ ({y} : ZFSet.{u}) ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZFSet.mem_singleton`：mem_singleton {x y : ZFSet.{u}} : x in ({y} : ZFSet
.{u}) ↔ x = y
-/
theorem notMem_singleton {x y : ZFSet.{u}} : x ∉ ({y} : ZFSet.{u}) ↔ x ≠ y :=
  mem_singleton.not

@[simp, norm_cast]
/-
**ZFSet.coe_singleton** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_singleton (x : ZFSet) : (({x} : ZFSet) : Set ZFSet) = {x}
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_singleton (x : ZFSet) : (({x} : ZFSet) : Set ZFSet) = {x} := by ext; simp
/-
**ZFSet.insert_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：insert_nonempty (u v : ZFSet) : (insert u v).Nonempty
参数：u v : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_insert`：mem_insert (x y : ZFSet) : x in insert x y
-/
theorem insert_nonempty (u v : ZFSet) : (insert u v).Nonempty :=
  ⟨u, mem_insert u v⟩
/-
**ZFSet.singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：singleton_nonempty (u : ZFSet) : ZFSet.Nonempty {u}
参数：u : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.insert_nonempty`：insert_nonempty (u v : ZFSet) : (insert u v).None
mpty
-/
theorem singleton_nonempty (u : ZFSet) : ZFSet.Nonempty {u} :=
  insert_nonempty u ∅
/-
**ZFSet.mem_pair** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_pair {x y z : ZFSet.{u}} : x in ({y, z} : ZFSet) ↔ x = y ∨ x = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_pair {x y z : ZFSet.{u}} : x ∈ ({y, z} : ZFSet) ↔ x = y ∨ x = z := by
  simp

@[simp]
/-
**ZFSet.pair_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：pair_eq_singleton (x : ZFSet) : {x, x} = ({x} : ZFSet)
参数：x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pair_eq_singleton (x : ZFSet) : {x, x} = ({x} : ZFSet) := by
  ext
  simp

@[simp]
/-
**ZFSet.pair_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：pair_eq_singleton_iff {x y z : ZFSet} : ({x, y} : ZFSet) = {z} ↔ x = z ∧ y
 = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.mem_singleton`：mem_singleton {x y : ZFSet.{u}} : x in ({y} : ZFSet
.{u}) ↔ x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ZFSet.pair_eq_singleton`：pair_eq_singleton (x : ZFSet) : {x, x} = ({x} :
 ZFSet)
-/
theorem pair_eq_singleton_iff {x y z : ZFSet} : ({x, y} : ZFSet) = {z} ↔ x = z ∧ y = z := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← mem_singleton, ← mem_singleton]
    simp [← h]
  · rintro ⟨rfl, rfl⟩
    exact pair_eq_singleton y

@[simp]
/-
**ZFSet.singleton_eq_pair_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：singleton_eq_pair_iff {x y z : ZFSet} : ({x} : ZFSet) = {y, z} ↔ x = y ∧ x
 = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ZFSet.pair_eq_singleton_iff`：pair_eq_singleton_iff {x y z : ZFSet} : ({x
, y} : ZFSet) = {z} ↔ x = z ∧ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_eq_pair_iff {x y z : ZFSet} : ({x} : ZFSet) = {y, z} ↔ x = y ∧ x = z := by
  rw [eq_comm, pair_eq_singleton_iff]
  simp_rw [eq_comm]

/-- `omega` is the first infinite von Neumann ordinal -/
/-
**ZFSet.omega** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：omega : ZFSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`omega` is the first infinite von Neumann ordinal
-/
def omega : ZFSet :=
  mk PSet.omega

@[simp]
/-
**ZFSet.omega_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：omega_zero : ∅ in omega
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSet.Equiv.rfl`：∀ {x : PSet.{u_1}}, x.Equiv x
-/
theorem omega_zero : ∅ ∈ omega :=
  ⟨⟨0⟩, Equiv.rfl⟩

@[simp]
/-
**ZFSet.omega_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：omega_succ {n} : n in omega.{u} -> insert n n in omega.{u}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `ZFSet.exact`：exact {x y : PSet} : mk x = mk y -> PSet.Equiv x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.sound`：sound {x y : PSet} (h : PSet.Equiv x y) : mk x = mk y
-/
theorem omega_succ {n} : n ∈ omega.{u} → insert n n ∈ omega.{u} :=
  Quotient.inductionOn n fun x ⟨⟨n⟩, h⟩ =>
    ⟨⟨n + 1⟩,
      ZFSet.exact <|
        show insert (mk x) (mk x) = insert (mk <| ofNat n) (mk <| ofNat n) by
          rw [ZFSet.sound h]
          rfl⟩

/-- `{x ∈ a | p x}` is the set of elements in `a` satisfying `p` -/
/-
**ZFSet.sep** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：(ZFSet.{u_1} → Prop) → ZFSet.{u_1} → ZFSet.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`{x ∈ a | p x}` is the set of elements in `a` satisfying `p`
-/
protected def sep (p : ZFSet → Prop) : ZFSet → ZFSet :=
  Quotient.map (PSet.sep fun y => p (mk y))
    fun ⟨α, A⟩ ⟨β, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun ⟨a, pa⟩ =>
        let ⟨b, hb⟩ := αβ a
        ⟨⟨b, by simpa only [mk_func, ← ZFSet.sound hb]⟩, hb⟩,
        fun ⟨b, pb⟩ =>
        let ⟨a, ha⟩ := βα b
        ⟨⟨a, by simpa only [mk_func, ZFSet.sound ha]⟩, ha⟩⟩

-- Porting note: the { x | p x } notation appears to be disabled in Lean 4.
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sep ZFSet ZFSet :=
  ⟨ZFSet.sep⟩

@[simp]
/-
**ZFSet.mem_sep** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} : y in ZFSet.sep p x ↔ y
 in x ∧ p y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `PSet.mem_sep`：∀ {p : PSet.{u_1} → Prop},   (∀ (x y : PSet.{u_1}), x.Equi
v y → p x → p y) → ∀ {x y : PSet.{u_1}}, y ∈ PSet.sep p x ↔ y ∈ x ∧ p y
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem mem_sep {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}} :
    y ∈ ZFSet.sep p x ↔ y ∈ x ∧ p y :=
  Quotient.inductionOn₂ x y fun _ _ =>
    PSet.mem_sep (p := p ∘ mk) fun _ _ h => (Quotient.sound h).subst

@[simp]
/-
**ZFSet.sep_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sep_empty (p : ZFSet -> Prop) : (∅ : ZFSet).sep p = ∅
参数：p : ZFSet -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.eq_empty`：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u},
 y ∉ x
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sep`：mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} : y in 
ZFSet.sep p x ↔ y in x ∧ p y
-/
theorem sep_empty (p : ZFSet → Prop) : (∅ : ZFSet).sep p = ∅ :=
  (eq_empty _).mpr fun _ h ↦ notMem_empty _ (mem_sep.mp h).1
/-
**ZFSet.sep_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sep_subset {x p} : ZFSet.sep p x subseteq x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sep`：mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} : y in 
ZFSet.sep p x ↔ y in x ∧ p y
-/
theorem sep_subset {x p} : ZFSet.sep p x ⊆ x :=
  fun _ h => (mem_sep.1 h).1

@[simp, norm_cast]
/-
**ZFSet.coe_sep** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_sep (a : ZFSet) (p : ZFSet -> Prop) : (ZFSet.sep p a : Set ZFSet) = {x
 in a | p x}
参数：a : ZFSet；p : ZFSet -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sep (a : ZFSet) (p : ZFSet → Prop) : (ZFSet.sep p a : Set ZFSet) = {x ∈ a | p x} := by
  ext
  simp

/-- The powerset operation, the collection of subsets of a ZFC set -/
/-
**ZFSet.powerset** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：powerset : ZFSet -> ZFSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The powerset operation, the collection of subsets of a ZFC set
-/
def powerset : ZFSet → ZFSet :=
  Quotient.map PSet.powerset
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨fun p =>
        ⟨{ b | ∃ a, a ∈ p ∧ Equiv (A a) (B b) }, fun ⟨a, pa⟩ =>
          let ⟨b, ab⟩ := αβ a
          ⟨⟨b, a, pa, ab⟩, ab⟩,
          fun ⟨_, a, pa, ab⟩ => ⟨⟨a, pa⟩, ab⟩⟩,
        fun q =>
        ⟨{ a | ∃ b, b ∈ q ∧ Equiv (A a) (B b) }, fun ⟨_, b, qb, ab⟩ => ⟨⟨b, qb⟩, ab⟩, fun ⟨b, qb⟩ =>
          let ⟨a, ab⟩ := βα b
          ⟨⟨a, b, qb, ab⟩, ab⟩⟩⟩

@[simp]
/-
**ZFSet.mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y subseteq x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.mem_powerset`：mem_powerset : forall {x y : PSet}, y in powerset x ↔
 y subseteq x | ⟨_, A⟩, ⟨_, B⟩ => ⟨fun ⟨_, e⟩ => (Subset.congr_left e).2 fun ⟨a,
 _⟩ => …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ZFSet.subset_iff`：subset_iff : forall {x y : PSet}, mk x subseteq mk y ↔
 x subseteq y | ⟨_, A⟩, ⟨_, _⟩ => ⟨fun h a => @h ⟦A a⟧ (Mem.mk A a), fun h z => 
Quotie…
-/
theorem mem_powerset {x y : ZFSet.{u}} : y ∈ powerset x ↔ y ⊆ x :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_powerset.trans subset_iff.symm
/-
**ZFSet.sUnion_lem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sUnion_lem {α β : Type u} (A : α -> PSet) (B : β -> PSet) (αβ : forall a, 
exists b, Equiv (A a) (B b)) : forall a, exists b, Equiv ((sUnion ⟨α, A⟩).Func a
) ((sUnion ⟨β, B⟩).Func b) | ⟨a, c⟩ => by let ⟨b, hb⟩
参数：A : α -> PSet；B : β -> PSet；αβ : forall a, exists b, Equiv (A a) (B b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sUnion_lem {α β : Type u} (A : α → PSet) (B : β → PSet) (αβ : ∀ a, ∃ b, Equiv (A a) (B b)) :
    ∀ a, ∃ b, Equiv ((sUnion ⟨α, A⟩).Func a) ((sUnion ⟨β, B⟩).Func b)
  | ⟨a, c⟩ => by
    let ⟨b, hb⟩ := αβ a
    induction ea : A a with | _ γ Γ
    induction eb : B b with | _ δ Δ
    rw [ea, eb] at hb
    obtain ⟨γδ, δγ⟩ := hb
    let c : (A a).Type := c
    let ⟨d, hd⟩ := γδ (by rwa [ea] at c)
    use ⟨b, Eq.ndrec d (Eq.symm eb)⟩
    change PSet.Equiv ((A a).Func c) ((B b).Func (Eq.ndrec d eb.symm))
    match A a, B b, ea, eb, c, d, hd with
    | _, _, rfl, rfl, _, _, hd => exact hd

/-- The union operator, the collection of elements of elements of a ZFC set. Uses `⋃₀` notation,
scoped under the `ZFSet` namespace.
-/
/-
**ZFSet.sUnion** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：sUnion : ZFSet -> ZFSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union operator, the collection of elements of elements of a ZFC set. Uses `⋃
₀` notation,
scoped under the `ZFSet` namespace.
-/
def sUnion : ZFSet → ZFSet :=
  Quotient.map PSet.sUnion
    fun ⟨_, A⟩ ⟨_, B⟩ ⟨αβ, βα⟩ =>
      ⟨sUnion_lem A B αβ, fun a =>
        Exists.elim
          (sUnion_lem B A (fun b => Exists.elim (βα b) fun c hc => ⟨c, PSet.Equiv.symm hc⟩) a)
          fun b hb => ⟨b, PSet.Equiv.symm hb⟩⟩

@[inherit_doc]
scoped prefix:110 "⋃₀ " => ZFSet.sUnion

/-- The intersection operator, the collection of elements in all of the elements of a ZFC set. We
define `⋂₀ ∅ = ∅`. Uses `⋂₀` notation, scoped under the `ZFSet` namespace. -/
/-
**ZFSet.sInter** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：sInter (x : ZFSet) : ZFSet
参数：x : ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection operator, the collection of elements in all of the elements of 
a ZFC set. We
define `⋂₀ ∅ = ∅`. Uses `⋂₀` notation, scoped under the `ZFSet` namespace.
-/
def sInter (x : ZFSet) : ZFSet := (⋃₀ x).sep (fun y => ∀ z ∈ x, y ∈ z)

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFSet.sInter

@[simp]
/-
**ZFSet.mem_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in x, y in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.mem_sUnion`：mem_sUnion : forall {x y : PSet.{u}}, y in ⋃₀ x ↔ exist
s z in x, y in z | ⟨α, A⟩, y => ⟨fun ⟨⟨a, c⟩, (e : Equiv y ((A a).Func c))⟩ => h
ave :…
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem mem_sUnion {x y : ZFSet.{u}} : y ∈ ⋃₀ x ↔ ∃ z ∈ x, y ∈ z :=
  Quotient.inductionOn₂ x y fun _ _ => PSet.mem_sUnion.trans
    ⟨fun ⟨z, h⟩ => ⟨⟦z⟧, h⟩, fun ⟨z, h⟩ => Quotient.inductionOn z (fun z h => ⟨z, h⟩) h⟩
/-
**ZFSet.mem_sInter** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x ↔ forall z in x, y i
n z
参数：h : x.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
-/
theorem mem_sInter {x y : ZFSet} (h : x.Nonempty) : y ∈ ⋂₀ x ↔ ∀ z ∈ x, y ∈ z := by
  unfold sInter
  simp only [and_iff_right_iff_imp, mem_sep]
  intro mem
  apply mem_sUnion.mpr
  replace ⟨s, h⟩ := h
  exact ⟨_, h, mem _ h⟩

@[simp]
/-
**ZFSet.sUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅ := by
  ext
  simp

@[simp]
/-
**ZFSet.sInter_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sInter_empty : ⋂₀ (∅ : ZFSet) = ∅
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ZFSet.sUnion_empty`：sUnion_empty : ⋃₀ (∅ : ZFSet.{u}) = ∅
· 使用定理 `ZFSet.sep_empty`：sep_empty (p : ZFSet -> Prop) : (∅ : ZFSet).sep p = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInter_empty : ⋂₀ (∅ : ZFSet) = ∅ := by simp [sInter]
/-
**ZFSet.mem_of_mem_sInter** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_of_mem_sInter {x y z : ZFSet} (hy : y in ⋂₀ x) (hz : z in x) : y in z
参数：hy : y in ⋂₀ x；hz : z in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.eq_empty_or_nonempty`：eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u
.Nonempty
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sInter`：mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x 
↔ forall z in x, y in z
-/
theorem mem_of_mem_sInter {x y z : ZFSet} (hy : y ∈ ⋂₀ x) (hz : z ∈ x) : y ∈ z := by
  rcases eq_empty_or_nonempty x with (rfl | hx)
  · exact (notMem_empty z hz).elim
  · exact (mem_sInter hx).1 hy z hz
/-
**ZFSet.mem_sUnion_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_sUnion_of_mem {x y z : ZFSet} (hy : y in z) (hz : z in x) : y in ⋃₀ x
参数：hy : y in z；hz : z in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
-/
theorem mem_sUnion_of_mem {x y z : ZFSet} (hy : y ∈ z) (hz : z ∈ x) : y ∈ ⋃₀ x :=
  mem_sUnion.2 ⟨z, hz, hy⟩
/-
**ZFSet.notMem_sInter_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：notMem_sInter_of_notMem {x y z : ZFSet} (hy : y ∉ z) (hz : z in x) : y ∉ ⋂
₀ x
参数：hy : y ∉ z；hz : z in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_of_mem_sInter`：mem_of_mem_sInter {x y z : ZFSet} (hy : y in ⋂₀
 x) (hz : z in x) : y in z
-/
theorem notMem_sInter_of_notMem {x y z : ZFSet} (hy : y ∉ z) (hz : z ∈ x) : y ∉ ⋂₀ x :=
  fun hx => hy <| mem_of_mem_sInter hx hz

@[simp]
/-
**ZFSet.sUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFSet) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sUnion, mem_singleton, exists_eq_left]

@[simp]
/-
**ZFSet.sInter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：sInter_singleton {x : ZFSet.{u}} : ⋂₀ ({x} : ZFSet) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_sInter`：mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x 
↔ forall z in x, y in z
· 使用定理 `ZFSet.singleton_nonempty`：singleton_nonempty (u : ZFSet) : ZFSet.Nonempt
y {u}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sInter_singleton {x : ZFSet.{u}} : ⋂₀ ({x} : ZFSet) = x :=
  ext fun y => by simp_rw [mem_sInter (singleton_nonempty x), mem_singleton, forall_eq]

@[simp, norm_cast]
/-
**ZFSet.coe_sUnion** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_sUnion (x : ZFSet.{u}) : (⋃₀ x : Set ZFSet) = ⋃₀ (SetLike.coe '' (x : 
Set ZFSet))
参数：x : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sUnion (x : ZFSet.{u}) : (⋃₀ x : Set ZFSet) = ⋃₀ (SetLike.coe '' (x : Set ZFSet)) := by
  ext
  simp

@[simp, norm_cast]
/-
**ZFSet.coe_sInter** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_sInter (h : x.Nonempty) : (⋂₀ x : Set ZFSet) = ⋂₀ (SetLike.coe '' (x :
 Set ZFSet))
参数：h : x.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_sInter`：mem_sInter {x y : ZFSet} (h : x.Nonempty) : y in ⋂₀ x 
↔ forall z in x, y in z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sInter (h : x.Nonempty) : (⋂₀ x : Set ZFSet) = ⋂₀ (SetLike.coe '' (x : Set ZFSet)) := by
  ext
  simp [mem_sInter h]
/-
**ZFSet.singleton_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：singleton_injective : Function.Injective (@singleton ZFSet ZFSet _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.sUnion_singleton`：sUnion_singleton {x : ZFSet.{u}} : ⋃₀ ({x} : ZFS
et) = x
-/
theorem singleton_injective : Function.Injective (@singleton ZFSet ZFSet _) := fun x y H => by
  let := congr_arg sUnion H
  rwa [sUnion_singleton, sUnion_singleton] at this

@[simp]
/-
**ZFSet.singleton_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：singleton_inj {x y : ZFSet} : ({x} : ZFSet) = {y} ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ZFSet.singleton_injective`：singleton_injective : Function.Injective (@si
ngleton ZFSet ZFSet _)
-/
theorem singleton_inj {x y : ZFSet} : ({x} : ZFSet) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/-- The binary union operation -/
/-
**ZFSet.union** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary union operation
-/
protected def union (x y : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ {x, y}

/-- The binary intersection operation -/
/-
**ZFSet.inter** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary intersection operation
-/
protected def inter (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ y) x -- { z ∈ x | z ∈ y }

/-- The set difference operation -/
/-
**ZFSet.diff** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set difference operation
-/
protected def diff (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ y) x -- { z ∈ x | z ∉ y }
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Union ZFSet :=
  ⟨ZFSet.union⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inter ZFSet :=
  ⟨ZFSet.inter⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SDiff ZFSet :=
  ⟨ZFSet.diff⟩
/-
**ZFSet.sUnion_pair** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ (x y : ZFSet.{u}), {x, y}.sUnion = x ∪ y
参数：x y : ZFSet.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sUnion_pair (x y : ZFSet.{u}) : ⋃₀ ({x, y} : ZFSet.{u}) = x ∪ y := rfl
/-
**ZFSet.sep_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ (x y : ZFSet.{u}), ZFSet.sep (fun x => x ∈ y) x = x ∩ y
参数：x y : ZFSet.{u}；fun x => x ∈ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sep_mem (x y : ZFSet.{u}) : x.sep (· ∈ y) = x ∩ y := rfl
/-
**ZFSet.sep_notMem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ (x y : ZFSet.{u}), ZFSet.sep (fun x => x ∉ y) x = x \ y
参数：x y : ZFSet.{u}；fun x => x ∉ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sep_notMem (x y : ZFSet.{u}) : x.sep (· ∉ y) = x \ y := rfl
/-
**ZFSet.mem_union** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y z : ZFSet.{u}}, z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_union : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by simp [← sUnion_pair]
/-
**ZFSet.mem_inter** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y z : ZFSet.{u}}, z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_inter : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by simp [← sep_mem]
/-
**ZFSet.mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y z : ZFSet.{u}}, z ∈ x \ y ↔ z ∈ x ∧ z ∉ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sdiff : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := by simp [← sep_notMem]

@[simp, norm_cast]
/-
**ZFSet.coe_union** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_union (x y : ZFSet.{u}) : ↑(x union y) = (↑x union ↑y : Set ZFSet)
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_union (x y : ZFSet.{u}) : ↑(x ∪ y) = (↑x ∪ ↑y : Set ZFSet) := by ext; simp

@[simp, norm_cast]
/-
**ZFSet.coe_inter** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_inter (x y : ZFSet.{u}) : ↑(x inter y) = (↑x inter ↑y : Set ZFSet)
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_inter (x y : ZFSet.{u}) : ↑(x ∩ y) = (↑x ∩ ↑y : Set ZFSet) := by ext; simp

@[simp, norm_cast]
/-
**ZFSet.coe_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (↑x \ ↑y : Set ZFSet)
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_sdiff (x y : ZFSet.{u}) : ↑(x \ y) = (↑x \ ↑y : Set ZFSet) := by ext; simp
/-
**ZFSet.inter_eq_left_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y : ZFSet.{u}}, x ⊆ y → x ∩ y = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] lemma inter_eq_left_of_subset (hxy : x ⊆ y) : x ∩ y = x := by ext; simpa using @hxy _
/-
**ZFSet.inter_eq_right_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：∀ {x y : ZFSet.{u}}, y ⊆ x → x ∩ y = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
@[simp] lemma inter_eq_right_of_subset (hyx : y ⊆ x) : x ∩ y = y := by ext; simpa using @hyx _

/-- `ZFSet.powerset` is equivalent to `Set.powerset`. -/
/-
**ZFSet.powersetEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：powersetEquiv (x : ZFSet.{u}) : x.powerset ≃ 𝒫 (x : Set ZFSet) where toFun
 y
参数：x : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZFSet.powerset` is equivalent to `Set.powerset`.
-/
def powersetEquiv (x : ZFSet.{u}) : x.powerset ≃ 𝒫 (x : Set ZFSet) where
  toFun y := ⟨y.1, Set.mem_powerset (mem_powerset.1 y.2)⟩
  invFun s := ⟨x.sep (· ∈ s.1), mem_powerset.2 sep_subset⟩
  left_inv := by simp +contextual [Function.LeftInverse]
  right_inv := by simp +contextual [Function.LeftInverse, Function.RightInverse, Set.ofPred_and]
/-
**ZFSet.insert_eq** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：insert_eq (x y : ZFSet) : insert x y = {x} union y
参数：x y : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem insert_eq (x y : ZFSet) : insert x y = {x} ∪ y := by
  ext; simp
/-
**ZFSet.mem_wf** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_wf : @WellFounded ZFSet (· in ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `PSet.Mem.congr_left`：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, x
 ∈ w ↔ y ∈ w
· 使用定理 `PSet.Mem.congr_right`：∀ {x y : PSet.{u}}, x.Equiv y → ∀ {w : PSet.{u}}, 
w ∈ x ↔ w ∈ y
· 使用定理 `wellFounded_lift₂_iff`：wellFounded_lift₂_iff {_ : Setoid α} {r : α -> α 
-> Prop} {H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂}
 : WellFoun…
· 使用定理 `PSet.mem_wf`：mem_wf : @WellFounded PSet (· in ·)
-/
theorem mem_wf : @WellFounded ZFSet (· ∈ ·) :=
  (wellFounded_lift₂_iff (H := fun a b c d hx hy =>
    propext ((@Mem.congr_left a c hx).trans (@Mem.congr_right b d hy _)))).mpr PSet.mem_wf

/-- Induction on the `∈` relation. -/
@[elab_as_elim]
/-
**ZFSet.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (forall y in x, p y) ->
 p x) : p x
参数：x；h : forall x, (forall y in x, p y) -> p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用定理 `ZFSet.mem_wf`：mem_wf : @WellFounded ZFSet (· in ·)

--- 原说明 ---
Induction on the `∈` relation.
-/
theorem inductionOn {p : ZFSet → Prop} (x) (h : ∀ x, (∀ y ∈ x, p y) → p x) : p x :=
  mem_wf.induction x h
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsWellFounded ZFSet (· ∈ ·) :=
  ⟨mem_wf⟩
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation ZFSet :=
  ⟨_, mem_wf⟩
/-
**ZFSet.mem_asymm** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_asymm {x y : ZFSet} : x in y -> y ∉ x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `asymm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Asymm r], r
 a b → ¬r b a
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `ZFSet.instIsWellFoundedMem`：IsWellFounded ZFSet.{u_1} fun x1 x2 => x1 ∈ 
x2
-/
theorem mem_asymm {x y : ZFSet} : x ∈ y → y ∉ x :=
  asymm_of (· ∈ ·)
/-
**ZFSet.mem_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_irrefl (x : ZFSet) : x ∉ x
参数：x : ZFSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `Function.instIrreflSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Ir
refl r], Std.Irrefl (Function.swap r)
· 使用定理 `Std.instIrreflOfAsymm`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asymm r]
, Std.Irrefl r
· 使用定理 `Function.instAsymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Asy
mm r], Std.Asymm (Function.swap r)
· 使用定理 `instAsymmOfIsWellFounded`：∀ {α : Type u} (r : α → α → Prop) [IsWellFound
ed α r], Std.Asymm r
· 使用定理 `ZFSet.instIsWellFoundedMem`：IsWellFounded ZFSet.{u_1} fun x1 x2 => x1 ∈ 
x2
-/
theorem mem_irrefl (x : ZFSet) : x ∉ x :=
  irrefl_of (· ∈ ·) x
/-
**ZFSet.not_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：not_subset_of_mem {x y : ZFSet} (h : x in y) : ¬ y subseteq x
参数：h : x in y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_irrefl`：mem_irrefl (x : ZFSet) : x ∉ x
-/
theorem not_subset_of_mem {x y : ZFSet} (h : x ∈ y) : ¬ y ⊆ x :=
  fun h' ↦ mem_irrefl _ (h' h)
/-
**ZFSet.notMem_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：notMem_of_subset {x y : ZFSet} (h : x subseteq y) : y ∉ x
参数：h : x subseteq y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `ZFSet.not_subset_of_mem`：not_subset_of_mem {x y : ZFSet} (h : x in y) : 
¬ y subseteq x
-/
theorem notMem_of_subset {x y : ZFSet} (h : x ⊆ y) : y ∉ x :=
  imp_not_comm.2 not_subset_of_mem h
/-
**ZFSet.regularity** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：regularity (x : ZFSet.{u}) (h : x != ∅) : exists y in x, x inter y = ∅
参数：x : ZFSet.{u}；h : x != ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.eq_empty`：eq_empty (x : ZFSet.{u}) : x = ∅ ↔ forall y : ZFSet.{u},
 y ∉ x
· 使用定理 `ZFSet.inductionOn`：inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (f
orall y in x, p y) -> p x) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_inter`：∀ {x y z : ZFSet.{u}}, z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y
-/
theorem regularity (x : ZFSet.{u}) (h : x ≠ ∅) : ∃ y ∈ x, x ∩ y = ∅ :=
  by_contradiction fun ne =>
    h <| (eq_empty x).2 fun y =>
      @inductionOn (fun z => z ∉ x) y fun z IH zx =>
        ne ⟨z, zx, (eq_empty _).2 fun w wxz =>
          let ⟨wx, wz⟩ := mem_inter.1 wxz
          IH w wz wx⟩

/-- The image of a (definable) ZFC set function -/
/-
**ZFSet.image** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：image (f : ZFSet -> ZFSet) [Definable₁ f] : ZFSet -> ZFSet
参数：f : ZFSet -> ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a (definable) ZFC set function
-/
def image (f : ZFSet → ZFSet) [Definable₁ f] : ZFSet → ZFSet :=
  let r := Definable₁.out f
  Quotient.map (PSet.image r)
    fun _ _ e =>
      Mem.ext fun _ =>
        (mem_image (fun _ _ ↦ Definable₁.out_equiv _)).trans <|
          Iff.trans
              ⟨fun ⟨w, h1, h2⟩ => ⟨w, (Mem.congr_right e).1 h1, h2⟩, fun ⟨w, h1, h2⟩ =>
                ⟨w, (Mem.congr_right e).2 h1, h2⟩⟩ <|
            (mem_image (fun _ _ ↦ Definable₁.out_equiv _)).symm
/-
**ZFSet.image.mk** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.image`。
形式化陈述：∀ (f : ZFSet.{u} → ZFSet.{u}) [inst : ZFSet.Definable₁ f] (x : ZFSet.{u}) 
{y : ZFSet.{u}}, y ∈ x → f y ∈ ZFSet.image f x
参数：f : ZFSet.{u} → ZFSet.{u}；x : ZFSet.{u}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.Definable₁.mk_out`：∀ {f : ZFSet.{u} → ZFSet.{u}} [inst : ZFSet.Def
inable₁ f] {x : PSet.{u}},   ZFSet.mk (ZFSet.Definable₁.out f x) = f (ZFSet.mk x
)
· 使用定理 `ZFSet.Definable₁.out_equiv`：∀ (f : ZFSet.{u} → ZFSet.{u}) [inst : ZFSet.
Definable₁ f] {x y : PSet.{u}},   x ≈ y → ZFSet.Definable₁.out f x ≈ ZFSet.Defin
able₁.out f y
-/
theorem image.mk (f : ZFSet.{u} → ZFSet.{u}) [Definable₁ f] (x) {y} : y ∈ x → f y ∈ image f x :=
  Quotient.inductionOn₂ x y fun ⟨_, _⟩ _ ⟨a, ya⟩ => by
    simp only [mk_eq, ← Definable₁.mk_out (f := f)]
    exact ⟨a, Definable₁.out_equiv f ya⟩

@[simp]
/-
**ZFSet.mem_image** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_image {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}} : 
y in image f x ↔ exists z in x, f z = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `PSet.Mem.mk`：∀ {α : Type u} (A : α → PSet.{u}) (a : α), A a ∈ PSet.mk α 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `ZFSet.Definable₁.mk_out`：∀ {f : ZFSet.{u} → ZFSet.{u}} [inst : ZFSet.Def
inable₁ f] {x : PSet.{u}},   ZFSet.mk (ZFSet.Definable₁.out f x) = f (ZFSet.mk x
)
· 使用定理 `ZFSet.image.mk`：∀ (f : ZFSet.{u} → ZFSet.{u}) [inst : ZFSet.Definable₁ f
] (x : ZFSet.{u}) {y : ZFSet.{u}}, y ∈ x → f y ∈ ZFSet.image f x
-/
theorem mem_image {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x y : ZFSet.{u}} :
    y ∈ image f x ↔ ∃ z ∈ x, f z = y :=
  Quotient.inductionOn₂ x y fun ⟨_, A⟩ _ =>
    ⟨fun ⟨a, ya⟩ => ⟨⟦A a⟧, Mem.mk A a, ((Quotient.sound ya).trans Definable₁.mk_out).symm⟩,
      fun ⟨_, hz, e⟩ => e ▸ image.mk _ _ hz⟩

@[simp, norm_cast]
/-
**ZFSet.coe_image** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_image (f : ZFSet -> ZFSet) [Definable₁ f] (x : ZFSet) : (image f x : S
et ZFSet) = f '' x
参数：f : ZFSet -> ZFSet；x : ZFSet。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_image (f : ZFSet → ZFSet) [Definable₁ f] (x : ZFSet) :
    (image f x : Set ZFSet) = f '' x := by ext; simp

section Small

variable {α : Type*} [Small.{u} α]

/-- The range of a type-indexed family of sets. -/
/-
**ZFSet.range** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：range (f : α -> ZFSet.{u}) : ZFSet.{u}
参数：f : α -> ZFSet.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The range of a type-indexed family of sets.
-/
noncomputable def range (f : α → ZFSet.{u}) : ZFSet.{u} :=
  ⟦⟨_, Quotient.out ∘ f ∘ (equivShrink α).symm⟩⟧

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ZFSet.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_range {f : α -> ZFSet.{u}} {x : ZFSet.{u}} : x in range f ↔ exists i, 
f i = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.eq_mk_iff_out`：Quotient.eq_mk_iff_out {s : Setoid α} {x : Quoti
ent s} {y : α} : x = ⟦y⟧ ↔ Quotient.out x ≈ y
· 使用定理 `PSet.Equiv.symm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y → y.Equi
v x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Quotient.mk_out`：Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quoti
ent s).out a
-/
theorem mem_range {f : α → ZFSet.{u}} {x : ZFSet.{u}} : x ∈ range f ↔ ∃ i, f i = x :=
  Quotient.inductionOn x fun y => by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(equivShrink α).symm z, Quotient.eq_mk_iff_out.2 hz.symm⟩
    · rintro ⟨z, hz⟩
      use equivShrink α z
      simpa [hz] using PSet.Equiv.symm (Quotient.mk_out y)

@[simp, norm_cast]
/-
**ZFSet.coe_range** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_range (f : α -> ZFSet.{u}) : (range f : Set ZFSet) = .range f
参数：f : α -> ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_range (f : α → ZFSet.{u}) : (range f : Set ZFSet) = .range f := by ext; simp
/-
**ZFSet.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_range_self {f : α -> ZFSet.{u}} (a : α) : f a in range f
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mem_range_self {f : α → ZFSet.{u}} (a : α) : f a ∈ range f := by simp

/-- Indexed union of a family of ZFC sets. Uses `⋃` notation, scoped under the `ZFSet` namespace. -/
/-
**ZFSet.iUnion** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：iUnion (f : α -> ZFSet.{u}) : ZFSet.{u}
参数：f : α -> ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indexed union of a family of ZFC sets. Uses `⋃` notation, scoped under the `ZFSe
t` namespace.
-/
noncomputable def iUnion (f : α → ZFSet.{u}) : ZFSet.{u} :=
  sUnion (range f)

@[inherit_doc iUnion] scoped notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

@[simp]
/-
**ZFSet.mem_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_iUnion {f : α -> ZFSet.{u}} {x : ZFSet.{u}} : x in ⋃ i, f i ↔ exists i
, x in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iUnion {f : α → ZFSet.{u}} {x : ZFSet.{u}} : x ∈ ⋃ i, f i ↔ ∃ i, x ∈ f i := by
  simp [iUnion]

@[simp, norm_cast]
/-
**ZFSet.coe_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_iUnion (f : α -> ZFSet.{u}) : ↑(⋃ i, f i) = ⋃ i, (f i : Set ZFSet)
参数：f : α -> ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_iUnion (f : α → ZFSet.{u}) : ↑(⋃ i, f i) = ⋃ i, (f i : Set ZFSet) := by
  ext
  simp
/-
**ZFSet.subset_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：subset_iUnion (f : α -> ZFSet.{u}) (i : α) : f i subseteq ⋃ i, f i
参数：f : α -> ZFSet.{u}；i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_iUnion (f : α → ZFSet.{u}) (i : α) : f i ⊆ ⋃ i, f i := by
  intro x hx
  simpa using ⟨i, hx⟩

end Small

/-- Kuratowski ordered pair -/
/-
**ZFSet.pair** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：pair (x y : ZFSet.{u}) : ZFSet.{u}
参数：x y : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Kuratowski ordered pair
-/
def pair (x y : ZFSet.{u}) : ZFSet.{u} :=
  {{x}, {x, y}}

@[simp, norm_cast]
/-
**ZFSet.coe_pair** 是 Mathlib 中的一个引理，位于命名空间 `ZFSet`。
形式化陈述：coe_pair (x y : ZFSet.{u}) : (pair x y : Set ZFSet) = {{x}, {x, y}}
参数：x y : ZFSet.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZFSet.coe_insert`：coe_insert (x y : ZFSet) : ↑(insert x y) = (insert x ↑
y : Set ZFSet)
· 使用引理 `ZFSet.coe_singleton`：coe_singleton (x : ZFSet) : (({x} : ZFSet) : Set ZF
Set) = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_pair (x y : ZFSet.{u}) : (pair x y : Set ZFSet) = {{x}, {x, y}} := by simp [pair]

/-- A subset of pairs `{(a, b) ∈ x × y | p a b}` -/
/-
**ZFSet.pairSep** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：pairSep (p : ZFSet.{u} -> ZFSet.{u} -> Prop) (x y : ZFSet.{u}) : ZFSet.{u}
参数：p : ZFSet.{u} -> ZFSet.{u} -> Prop；x y : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of pairs `{(a, b) ∈ x × y | p a b}`
-/
def pairSep (p : ZFSet.{u} → ZFSet.{u} → Prop) (x y : ZFSet.{u}) : ZFSet.{u} :=
  (powerset (powerset (x ∪ y))).sep fun z => ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b

@[simp]
/-
**ZFSet.mem_pairSep** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_pairSep {p} {x y z : ZFSet.{u}} : z in pairSep p x y ↔ exists a in x, 
exists b in y, z = pair a b ∧ p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ZFSet.mem_sep`：mem_sep {p : ZFSet.{u} -> Prop} {x y : ZFSet.{u}} : y in 
ZFSet.sep p x ↔ y in x ∧ p y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_pairSep {p} {x y z : ZFSet.{u}} :
    z ∈ pairSep p x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b ∧ p a b := by
  refine mem_sep.trans ⟨And.right, fun e => ⟨?_, e⟩⟩
  grind [mem_pair, mem_powerset, mem_singleton, mem_union, pair, subset_def]
/-
**ZFSet.pair_injective** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：pair_injective : Function.Injective2 pair
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ZFSet.pair_eq_singleton`：pair_eq_singleton (x : ZFSet) : {x, x} = ({x} :
 ZFSet)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.ext_iff`：∀ {x y : ZFSet.{u}}, x = y ↔ ∀ (z : ZFSet.{u}), z ∈ x ↔ z
 ∈ y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem pair_injective : Function.Injective2 pair := by
  intro x x' y y' H
  simp_rw [ZFSet.ext_iff, pair, mem_pair] at H
  obtain rfl : x = x' := And.left <| by simpa [or_and_left] using (H {x}).1 (Or.inl rfl)
  have he : y = x → y = y' := by
    rintro rfl
    simpa [eq_comm] using H {y, y'}
  have hx := H {x, y}
  simp_rw [pair_eq_singleton_iff, true_and, or_true, true_iff] at hx
  refine ⟨rfl, hx.elim he fun hy ↦ Or.elim ?_ he id⟩
  simpa using ZFSet.ext_iff.1 hy y

@[simp]
/-
**ZFSet.pair_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：pair_inj {x y x' y' : ZFSet} : pair x y = pair x' y' ↔ x = x' ∧ y = y'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective2.eq_iff`：eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f
 a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
· 使用定理 `ZFSet.pair_injective`：pair_injective : Function.Injective2 pair
-/
theorem pair_inj {x y x' y' : ZFSet} : pair x y = pair x' y' ↔ x = x' ∧ y = y' :=
  pair_injective.eq_iff

/-- The Cartesian product, `{(a, b) | a ∈ x, b ∈ y}` -/
/-
**ZFSet.prod** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：prod : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product, `{(a, b) | a ∈ x, b ∈ y}`
-/
def prod : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  pairSep fun _ _ => True

@[simp]
/-
**ZFSet.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_prod {x y z : ZFSet.{u}} : z in prod x y ↔ exists a in x, exists b in 
y, z = pair a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_prod {x y z : ZFSet.{u}} : z ∈ prod x y ↔ ∃ a ∈ x, ∃ b ∈ y, z = pair a b := by
  simp [prod]
/-
**ZFSet.pair_mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：pair_mem_prod {x y a b : ZFSet.{u}} : pair a b in prod x y ↔ a in x ∧ b in
 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pair_mem_prod {x y a b : ZFSet.{u}} : pair a b ∈ prod x y ↔ a ∈ x ∧ b ∈ y := by
  simp

/-- `isFunc x y f` is the assertion that `f` is a subset of `x × y` which relates to each element
of `x` a unique element of `y`, so that we can consider `f` as a ZFC function `x → y`. -/
/-
**ZFSet.IsFunc** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：IsFunc (x y f : ZFSet.{u}) : Prop
参数：x y f : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`isFunc x y f` is the assertion that `f` is a subset of `x × y` which relates to
 each element
of `x` a unique element of `y`, so that we can consider `f` as a ZFC function `x
 → y`.
-/
def IsFunc (x y f : ZFSet.{u}) : Prop :=
  f ⊆ prod x y ∧ ∀ z : ZFSet.{u}, z ∈ x → ∃! w, pair z w ∈ f

/-- `funs x y` is `y ^ x`, the set of all set functions `x → y` -/
/-
**ZFSet.funs** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：funs (x y : ZFSet.{u}) : ZFSet.{u}
参数：x y : ZFSet.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`funs x y` is `y ^ x`, the set of all set functions `x → y`
-/
def funs (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsFunc x y) (powerset (prod x y))

@[simp]
/-
**ZFSet.mem_funs** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_funs {x y f : ZFSet.{u}} : f in funs x y ↔ IsFunc x y f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_funs {x y f : ZFSet.{u}} : f ∈ funs x y ↔ IsFunc x y f := by simp [funs, IsFunc]
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Definable₁ ({·}) := .mk ({·}) (fun _ ↦ rfl)
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Definable₂ insert := .mk insert (fun _ _ ↦ rfl)
/-
**ZFSet.** 是 Mathlib 中的一个实例，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Definable₂ pair := inferInstanceAs <| Definable₂ fun x y ↦ {{x}, {x, y}}

/-- Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a` -/
/-
**ZFSet.map** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：map (f : ZFSet -> ZFSet) [Definable₁ f] : ZFSet -> ZFSet
参数：f : ZFSet -> ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph of a function: `map f x` is the ZFC function which maps `a ∈ x` to `f a`
-/
def map (f : ZFSet → ZFSet) [Definable₁ f] : ZFSet → ZFSet :=
  image fun y => pair y (f y)

@[simp]
/-
**ZFSet.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：mem_map {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet} : y in map f x ↔
 exists z in x, pair z (f z) = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_image`：mem_image {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {
x y : ZFSet.{u}} : y in image f x ↔ exists z in x, f z = y
-/
theorem mem_map {f : ZFSet → ZFSet} [Definable₁ f] {x y : ZFSet} :
    y ∈ map f x ↔ ∃ z ∈ x, pair z (f z) = y :=
  mem_image
/-
**ZFSet.map_unique** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：map_unique {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}} (
zx : z in x) : exists! w, pair z w in map f x
参数：zx : z in x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.image.mk`：∀ (f : ZFSet.{u} → ZFSet.{u}) [inst : ZFSet.Definable₁ f
] (x : ZFSet.{u}) {y : ZFSet.{u}}, y ∈ x → f y ∈ ZFSet.image f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_image`：mem_image {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {
x y : ZFSet.{u}} : y in image f x ↔ exists z in x, f z = y
· 使用定理 `ZFSet.pair_injective`：pair_injective : Function.Injective2 pair
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_unique {f : ZFSet.{u} → ZFSet.{u}} [Definable₁ f] {x z : ZFSet.{u}}
    (zx : z ∈ x) : ∃! w, pair z w ∈ map f x :=
  ⟨f z, image.mk _ _ zx, fun y yx => by
    let ⟨w, _, we⟩ := mem_image.1 yx
    let ⟨wz, fy⟩ := pair_injective we
    rw [← fy, wz]⟩

@[simp]
/-
**ZFSet.map_isFunc** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：map_isFunc {f : ZFSet -> ZFSet} [Definable₁ f] {x y : ZFSet} : IsFunc x y 
(map f x) ↔ forall z in x, f z in y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.pair_mem_prod`：pair_mem_prod {x y a b : ZFSet.{u}} : pair a b in p
rod x y ↔ a in x ∧ b in y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.image.mk`：∀ (f : ZFSet.{u} → ZFSet.{u}) [inst : ZFSet.Definable₁ f
] (x : ZFSet.{u}) {y : ZFSet.{u}}, y ∈ x → f y ∈ ZFSet.image f x
· 使用定理 `ZFSet.mem_image`：mem_image {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f] {
x y : ZFSet.{u}} : y in image f x ↔ exists z in x, f z = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.map_unique`：map_unique {f : ZFSet.{u} -> ZFSet.{u}} [Definable₁ f]
 {x z : ZFSet.{u}} (zx : z in x) : exists! w, pair z w in map f x
-/
theorem map_isFunc {f : ZFSet → ZFSet} [Definable₁ f] {x y : ZFSet} :
    IsFunc x y (map f x) ↔ ∀ z ∈ x, f z ∈ y :=
  ⟨fun ⟨ss, h⟩ z zx =>
    let ⟨_, t1, t2⟩ := h z zx
    (t2 (f z) (image.mk _ _ zx)).symm ▸ (pair_mem_prod.1 (ss t1)).right,
    fun h =>
    ⟨fun _ yx =>
      let ⟨z, zx, ze⟩ := mem_image.1 yx
      ze ▸ pair_mem_prod.2 ⟨zx, h z zx⟩,
      fun _ => map_unique⟩⟩

/-- Given a predicate `p` on ZFC sets. `Hereditarily p x` means that `x` has property `p` and the
members of `x` are all `Hereditarily p`. -/
/-
**ZFSet.Hereditarily** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：Hereditarily (p : ZFSet -> Prop) (x : ZFSet) : Prop
参数：p : ZFSet -> Prop；x : ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a predicate `p` on ZFC sets. `Hereditarily p x` means that `x` has propert
y `p` and the
members of `x` are all `Hereditarily p`.
-/
def Hereditarily (p : ZFSet → Prop) (x : ZFSet) : Prop :=
  p x ∧ ∀ y ∈ x, Hereditarily p y
termination_by x

section Hereditarily

variable {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}}

/-
**ZFSet.hereditarily_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：hereditarily_iff : Hereditarily p x ↔ p x ∧ forall y in x, Hereditarily p 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.Hereditarily.eq_1`：∀ (p : ZFSet.{u_1} → Prop) (x : ZFSet.{u_1}), Z
FSet.Hereditarily p x = (p x ∧ ∀ y ∈ x, ZFSet.Hereditarily p y)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hereditarily_iff : Hereditarily p x ↔ p x ∧ ∀ y ∈ x, Hereditarily p y := by
  rw [← Hereditarily]

alias ⟨Hereditarily.def, _⟩ := hereditarily_iff
/-
**ZFSet.Hereditarily.self** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.Hereditarily`。
形式化陈述：∀ {p : ZFSet.{u} → Prop} {x : ZFSet.{u}}, ZFSet.Hereditarily p x → p x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ZFSet.Hereditarily.def`：∀ {p : ZFSet.{u} → Prop} {x : ZFSet.{u}}, ZFSet.
Hereditarily p x → p x ∧ ∀ y ∈ x, ZFSet.Hereditarily p y
-/
theorem Hereditarily.self (h : x.Hereditarily p) : p x :=
  h.def.1
/-
**ZFSet.Hereditarily.mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.Hereditarily`。
形式化陈述：∀ {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}}, ZFSet.Hereditarily p x → y ∈ x
 → ZFSet.Hereditarily p y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ZFSet.Hereditarily.def`：∀ {p : ZFSet.{u} → Prop} {x : ZFSet.{u}}, ZFSet.
Hereditarily p x → p x ∧ ∀ y ∈ x, ZFSet.Hereditarily p y
-/
theorem Hereditarily.mem (h : x.Hereditarily p) (hy : y ∈ x) : y.Hereditarily p :=
  h.def.2 _ hy
/-
**ZFSet.Hereditarily.empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.Hereditarily`。
形式化陈述：∀ {p : ZFSet.{u} → Prop} {x : ZFSet.{u}}, ZFSet.Hereditarily p x → p ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.inductionOn`：inductionOn {p : ZFSet -> Prop} (x) (h : forall x, (f
orall y in x, p y) -> p x) : p x
· 使用定理 `ZFSet.eq_empty_or_nonempty`：eq_empty_or_nonempty (u : ZFSet) : u = ∅ ∨ u
.Nonempty
· 使用定理 `ZFSet.Hereditarily.self`：∀ {p : ZFSet.{u} → Prop} {x : ZFSet.{u}}, ZFSet
.Hereditarily p x → p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.Hereditarily.mem`：∀ {p : ZFSet.{u} → Prop} {x y : ZFSet.{u}}, ZFSe
t.Hereditarily p x → y ∈ x → ZFSet.Hereditarily p y
-/
theorem Hereditarily.empty : Hereditarily p x → p ∅ := by
  apply @ZFSet.inductionOn _ x
  intro y IH h
  rcases ZFSet.eq_empty_or_nonempty y with (rfl | ⟨a, ha⟩)
  · exact h.self
  · exact IH a ha (h.mem ha)

end Hereditarily

end ZFSet

