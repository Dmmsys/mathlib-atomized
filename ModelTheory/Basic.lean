/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Basics on First-Order Structures

This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions

- A `FirstOrder.Language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
- A `FirstOrder.Language.Structure` interprets the symbols of a given `FirstOrder.Language` in the
  context of a given type.
- A `FirstOrder.Language.Hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
- A `FirstOrder.Language.Embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
- A `FirstOrder.Language.Equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References

For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
  [flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
  the continuum hypothesis*][flypitch_itp]
-/

@[expose] public section

universe u v u' v' w w'

open Cardinal

namespace FirstOrder

/-! ### Languages and Structures -/


-- intended to be used with explicit universe parameters
set_option linter.checkUnivs false in
/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
/-
**FirstOrder.Language** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder`。
形式化陈述：Type (max (u + 1) (v + 1))
参数：max (u + 1) (v + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order language consists of a type of functions of every natural-number a
rity and a
  type of relations of every natural-number arity.
-/
structure Language where
  /-- For every arity, a `Type u` of functions of that arity -/
  Functions : ℕ → Type u
  /-- For every arity, a `Type v` of relations of that arity -/
  Relations : ℕ → Type v

namespace Language

variable (L : Language.{u, v})

/-- A language is relational when it has no function symbols. -/
/-
**FirstOrder.Language.IsRelational** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：IsRelational : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language is relational when it has no function symbols.
-/
abbrev IsRelational : Prop := ∀ n, IsEmpty (L.Functions n)

/-- A language is algebraic when it has no relation symbols. -/
/-
**FirstOrder.Language.IsAlgebraic** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：IsAlgebraic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A language is algebraic when it has no relation symbols.
-/
abbrev IsAlgebraic : Prop := ∀ n, IsEmpty (L.Relations n)

/-- The empty language has no symbols. -/
/-
**FirstOrder.Language.empty** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty language has no symbols.
-/
protected def empty : Language := ⟨fun _ => Empty, fun _ => Empty⟩
  deriving IsAlgebraic, IsRelational
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Language :=
  ⟨Language.empty⟩

/-- The sum of two languages consists of the disjoint union of their symbols. -/
/-
**FirstOrder.Language.sum** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language → FirstOrder.Language → FirstOrder.Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two languages consists of the disjoint union of their symbols.
-/
protected def sum (L' : Language.{u', v'}) : Language :=
  ⟨fun n => L.Functions n ⊕ L'.Functions n, fun n => L.Relations n ⊕ L'.Relations n⟩

/-- The type of constants in a given language. -/
/-
**FirstOrder.Language.Constants** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of constants in a given language.
-/
protected abbrev Constants :=
  L.Functions 0

/-- The type of symbols in a given language. -/
/-
**FirstOrder.Language.Symbols** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：Symbols
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of symbols in a given language.
-/
abbrev Symbols :=
  (Σ l, L.Functions l) ⊕ (Σ l, L.Relations l)

/-- The cardinality of a language is the cardinality of its type of symbols. -/
/-
**FirstOrder.Language.card** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：card : Cardinal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of a language is the cardinality of its type of symbols.
-/
def card : Cardinal :=
  #L.Symbols

variable {L} {L' : Language.{u', v'}}
/-
**FirstOrder.Language.card_eq_card_functions_add_card_relations** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language`。
形式化陈述：card_eq_card_functions_add_card_relations : L.card = (Cardinal.sum fun l =
> Cardinal.lift.{v} #(L.Functions l)) + Cardinal.sum fun l => Cardinal.lift.{u} 
#(L.Relations l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.lift_sum`：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardi
nal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_card_functions_add_card_relations :
    L.card =
      (Cardinal.sum fun l => Cardinal.lift.{v} #(L.Functions l)) +
        Cardinal.sum fun l => Cardinal.lift.{u} #(L.Relations l) := by
  simp only [card, mk_sum, mk_sigma, lift_sum]
/-
**FirstOrder.Language.isRelational_sum** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum 
L')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isRelational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.sum L') :=
  fun _ => instIsEmptySum
/-
**FirstOrder.Language.isAlgebraic_sum** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage`。
形式化陈述：isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isAlgebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.sum L') :=
  fun _ => instIsEmptySum

@[simp]
/-
**FirstOrder.Language.card_empty** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language`
。
形式化陈述：card_empty : Language.empty.card = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `FirstOrder.Language.instIsRelationalEmpty`：FirstOrder.Language.empty.IsR
elational
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `FirstOrder.Language.instIsAlgebraicEmpty`：FirstOrder.Language.empty.IsAl
gebraic
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_empty : Language.empty.card = 0 := by simp only [card, mk_sum, mk_sigma, mk_eq_zero,
  sum_const, mk_eq_aleph0, lift_id', mul_zero, add_zero]
/-
**FirstOrder.Language.isEmpty_empty** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：isEmpty_empty : IsEmpty Language.empty.Symbols
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.instIsRelationalEmpty`：FirstOrder.Language.empty.IsR
elational
· 使用定理 `FirstOrder.Language.instIsAlgebraicEmpty`：FirstOrder.Language.empty.IsAl
gebraic
-/
instance isEmpty_empty : IsEmpty Language.empty.Symbols := by
  simp only [Language.Symbols, isEmpty_sum, isEmpty_sigma]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩
/-
**FirstOrder.Language.Countable.countable_functions** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Countable`。
形式化陈述：∀ {L : FirstOrder.Language} [h : Countable L.Symbols], Countable ((l : ℕ) 
× L.Functions l)
参数：(l : ℕ) × L.Functions l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
{f : α → β}, Function.Injective f → Countable α
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
instance Countable.countable_functions [h : Countable L.Symbols] : Countable (Σ l, L.Functions l) :=
  @Function.Injective.countable _ _ h _ Sum.inl_injective

@[simp]
/-
**FirstOrder.Language.card_functions_sum** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：card_functions_sum (i : Nat) : #((L.sum L').Functions i) = (Cardinal.lift.
{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal)
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_functions_sum (i : ℕ) :
    #((L.sum L').Functions i)
      = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.{u} #(L'.Functions i) : Cardinal) := by
  simp [Language.sum]

@[simp]
/-
**FirstOrder.Language.card_relations_sum** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage`。
形式化陈述：card_relations_sum (i : Nat) : #((L.sum L').Relations i) = Cardinal.lift.{
v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i)
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_relations_sum (i : ℕ) :
    #((L.sum L').Relations i) =
      Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{v} #(L'.Relations i) := by
  simp [Language.sum]
/-
**FirstOrder.Language.card_sum** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language`。
形式化陈述：card_sum : (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.l
ift.{max u v} L'.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.card_functions_sum`：card_functions_sum (i : Nat) : #
((L.sum L').Functions i) = (Cardinal.lift.{u'} #(L.Functions i) + Cardinal.lift.
{u} #(L'.Functions i) : Card…
· 使用定理 `Cardinal.sum_add_distrib'`：sum_add_distrib' {ι} (f g : ι -> Cardinal) : 
(Cardinal.sum fun i => f i + g i) = sum f + sum g
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `Cardinal.lift_sum`：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardi
nal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `FirstOrder.Language.card_relations_sum`：card_relations_sum (i : Nat) : #
((L.sum L').Relations i) = Cardinal.lift.{v'} #(L.Relations i) + Cardinal.lift.{
v} #(L'.Relations i)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sum :
    (L.sum L').card = Cardinal.lift.{max u' v'} L.card + Cardinal.lift.{max u v} L'.card := by
  simp only [card, mk_sum, mk_sigma, card_functions_sum, sum_add_distrib', lift_add, lift_sum,
    lift_lift, card_relations_sum, add_assoc,
    add_comm (Cardinal.sum fun i => (#(L'.Functions i)).lift)]

/-- Passes a `DecidableEq` instance on a type of function symbols through the  `Language`
constructor. Despite the fact that this is proven by `inferInstance`, it is still needed -
see the `example`s in `ModelTheory/Ring/Basic`. -/
/-
**FirstOrder.Language.instDecidableEqFunctions** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language`。
形式化陈述：instDecidableEqFunctions {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [
DecidableEq (f n)] : DecidableEq ((⟨f, R⟩ : Language).Functions n)
参数：n : Nat；f n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Passes a `DecidableEq` instance on a type of function symbols through the  `Lang
uage`
constructor. Despite the fact that this is proven by `inferInstance`, it is stil
l needed -
see the `example`s in `ModelTheory/Ring/Basic`.
-/
instance instDecidableEqFunctions {f : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (f n)] :
    DecidableEq ((⟨f, R⟩ : Language).Functions n) := inferInstance

/-- Passes a `DecidableEq` instance on a type of relation symbols through the  `Language`
constructor. Despite the fact that this is proven by `inferInstance`, it is still needed -
see the `example`s in `ModelTheory/Ring/Basic`. -/
/-
**FirstOrder.Language.instDecidableEqRelations** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language`。
形式化陈述：instDecidableEqRelations {f : Nat -> Type*} {R : Nat -> Type*} (n : Nat) [
DecidableEq (R n)] : DecidableEq ((⟨f, R⟩ : Language).Relations n)
参数：n : Nat；R n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Passes a `DecidableEq` instance on a type of relation symbols through the  `Lang
uage`
constructor. Despite the fact that this is proven by `inferInstance`, it is stil
l needed -
see the `example`s in `ModelTheory/Ring/Basic`.
-/
instance instDecidableEqRelations {f : ℕ → Type*} {R : ℕ → Type*} (n : ℕ) [DecidableEq (R n)] :
    DecidableEq ((⟨f, R⟩ : Language).Relations n) := inferInstance

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
@[ext]
/-
**FirstOrder.Language.Structure** 是 Mathlib 中的一个类，位于命名空间 `FirstOrder.Language`。
形式化陈述：Structure where /-- Interpretation of the function symbols -/ funMap : for
all {n}, L.Functions n -> (Fin n -> M) -> M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order structure on a type `M` consists of interpretations of all the sym
bols in a given
  language. Each function of arity `n` is interpreted as a function sending tupl
es of length `n`
  (modeled as `(Fin n → M)`) to `M`, and a relation of arity `n` is a function f
rom tuples of length
  `n` to `Prop`.
-/
class Structure where
  /-- Interpretation of the function symbols -/
  funMap : ∀ {n}, L.Functions n → (Fin n → M) → M := by
    exact fun {n} => isEmptyElim
  /-- Interpretation of the relation symbols -/
  RelMap : ∀ {n}, L.Relations n → (Fin n → M) → Prop := by
    exact fun {n} => isEmptyElim

variable (N : Type w') [L.Structure M] [L.Structure N]

open Structure

/-- Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`. -/
@[instance_reducible]
/-
**FirstOrder.Language.Inhabited.trivialStructure** 是 Mathlib 中的一个定义，位于命名空间 `Firs
tOrder.Language.Inhabited`。
形式化陈述：(L : FirstOrder.Language) → {α : Type u_1} → [Inhabited α] → L.Structure α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Used for defining `FirstOrder.Language.Theory.ModelType.instInhabited`.
-/
def Inhabited.trivialStructure {α : Type*} [Inhabited α] : L.Structure α :=
  ⟨default, default⟩

/-! ### Maps -/


/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
/-
**FirstOrder.Language.Hom** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.Language`。
形式化陈述：Hom where /-- The underlying function of a homomorphism of structures -/ t
oFun : M -> N /-- The homomorphism commutes with the interpretations of the func
tion symbols -/ -- Porting note: -- The autoparam here used to be `obviously`. W
e would like to replace it with `aesop` -- but that isn't currently sufficient. 
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aes
op.20and.20cases -- If that can be improved, we should change this to `by aesop`
 and remove the proofs bel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism between first-order structures is a function that commutes with t
he
  interpretations of functions and maps tuples in one structure where a given re
lation is true to
  tuples in the second structure where that relation is still true.
-/
structure Hom where
  /-- The underlying function of a homomorphism of structures -/
  toFun : M → N
  /-- The homomorphism commutes with the interpretations of the function symbols -/
  -- Porting note:
  -- The autoparam here used to be `obviously`. We would like to replace it with `aesop`
  -- but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should change this to `by aesop` and remove the proofs below.
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    intros; trivial
  /-- The homomorphism sends related elements to related elements -/
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r x → RelMap r (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " →[" L "] " B => FirstOrder.Language.Hom L A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
/-
**FirstOrder.Language.Embedding** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.Language`。
形式化陈述：Embedding extends M ↪ N where map_fun' : forall {n} (f : L.Functions n) (x
), toFun (funMap f x) = funMap f (toFun ∘ x)
继承自：M ↪ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations.
-/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ↪[" L "] " B => FirstOrder.Language.Embedding L A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
/-
**FirstOrder.Language.Equiv** 是 Mathlib 中的一个结构，位于命名空间 `FirstOrder.Language`。
形式化陈述：Equiv extends M ≃ N where map_fun' : forall {n} (f : L.Functions n) (x), t
oFun (funMap f x) = funMap f (toFun ∘ x)
继承自：M ≃ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of first-order structures is an equivalence that commutes with th
e
  interpretations of functions and relations.
-/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} (f : L.Functions n) (x), toFun (funMap f x) = funMap f (toFun ∘ x) := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial
  map_rel' : ∀ {n} (r : L.Relations n) (x), RelMap r (toFun ∘ x) ↔ RelMap r x := by
    -- Porting note: see porting note on `Hom.map_fun'`
    intros; trivial

@[inherit_doc]
scoped[FirstOrder] notation:25 A " ≃[" L "] " B => FirstOrder.Language.Equiv L A B

variable {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

/-- Interpretation of a constant symbol -/
@[coe]
/-
**FirstOrder.Language.constantMap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
`。
形式化陈述：constantMap (c : L.Constants) : M
参数：c : L.Constants。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpretation of a constant symbol
-/
def constantMap (c : L.Constants) : M := funMap c default
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC L.Constants M :=
  ⟨constantMap⟩
/-
**FirstOrder.Language.funMap_eq_coe_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language`。
形式化陈述：funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 -> M} : funMap c x = 
c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem funMap_eq_coe_constants {c : L.Constants} {x : Fin 0 → M} : funMap c x = c :=
  congr rfl (funext finZeroElim)

variable (L M) in
/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
/-
**FirstOrder.Language.nonempty_of_nonempty_constants** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language`。
形式化陈述：nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…

--- 原说明 ---
Given a language with a nonempty type of constants, any structure will be nonemp
ty. This cannot
  be a global instance, because `L` becomes a metavariable.
-/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map (↑)

/-- `HomClass L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `FirstOrder.Language.Hom`. -/
/-
**FirstOrder.Language.HomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language`
。
形式化陈述：(L : outParam FirstOrder.Language) →   (F : Type u_3) →     (M : outParam 
(Type u_4)) → (N : outParam (Type u_5)) → [FunLike F M N] → [L.Structure M] → [L
.Structure N] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HomClass L F M N` states that `F` is a type of `L`-homomorphisms. You should ex
tend this
  typeclass when you extend `FirstOrder.Language.Hom`.
-/
class HomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r x → RelMap r (φ ∘ x)

/-- `StrongHomClass L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
/-
**FirstOrder.Language.StrongHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Lan
guage`。
形式化陈述：(L : outParam FirstOrder.Language) →   (F : Type u_3) →     (M : outParam 
(Type u_4)) → (N : outParam (Type u_5)) → [FunLike F M N] → [L.Structure M] → [L
.Structure N] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`StrongHomClass L F M N` states that `F` is a type of `L`-homomorphisms which pr
eserve
  relations in both directions.
-/
class StrongHomClass (L : outParam Language) (F : Type*) (M N : outParam Type*)
  [FunLike F M N] [L.Structure M] [L.Structure N] : Prop where
  map_fun : ∀ (φ : F) {n} (f : L.Functions n) (x), φ (funMap f x) = funMap f (φ ∘ x)
  map_rel : ∀ (φ : F) {n} (r : L.Relations n) (x), RelMap r (φ ∘ x) ↔ RelMap r x
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) StrongHomClass.homClass {F : Type*}
    [FunLike F M N] [StrongHomClass L F M N] : HomClass L F M N where
  map_fun := StrongHomClass.map_fun
  map_rel φ _ R x := (StrongHomClass.map_rel φ R x).2

/-- Not an instance to avoid a loop. -/
/-
**FirstOrder.Language.HomClass.strongHomClassOfIsAlgebraic** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.HomClass`。
形式化陈述：∀ {L : FirstOrder.Language} [L.IsAlgebraic] {F : Type u_3} {M : Type u_4} 
{N : Type u_5} [inst : L.Structure M]   [inst_1 : L.Structure N] [inst_2 : FunLi
ke F M N] [L.HomClass F M N], L.StrongHomClass F M N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…

--- 原说明 ---
Not an instance to avoid a loop.
-/
theorem HomClass.strongHomClassOfIsAlgebraic [L.IsAlgebraic] {F M N} [L.Structure M] [L.Structure N]
    [FunLike F M N] [HomClass L F M N] : StrongHomClass L F M N where
  map_fun := HomClass.map_fun
  map_rel _ _ := isEmptyElim
/-
**FirstOrder.Language.HomClass.map_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.HomClass`。
形式化陈述：∀ {L : FirstOrder.Language} {F : Type u_3} {M : Type u_4} {N : Type u_5} [
inst : L.Structure M] [inst_1 : L.Structure N]   [inst_2 : FunLike F M N] [L.Hom
Class F M N] (φ : F) (c : L.Constants), φ ↑c = ↑c
参数：φ : F；c : L.Constants。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem HomClass.map_constants {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] (φ : F) (c : L.Constants) : φ c = c :=
  (HomClass.map_fun φ c default).trans (congr rfl (funext default))

attribute [inherit_doc FirstOrder.Language.Hom.map_fun'] FirstOrder.Language.Embedding.map_fun'
  FirstOrder.Language.HomClass.map_fun FirstOrder.Language.StrongHomClass.map_fun
  FirstOrder.Language.Equiv.map_fun'

attribute [inherit_doc FirstOrder.Language.Hom.map_rel'] FirstOrder.Language.Embedding.map_rel'
  FirstOrder.Language.HomClass.map_rel FirstOrder.Language.StrongHomClass.map_rel
  FirstOrder.Language.Equiv.map_rel'

namespace Hom

/-
**FirstOrder.Language.Hom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Lang
uage.Hom`。
形式化陈述：instFunLike : FunLike (M ->[L] N) M N where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (M →[L] N) M N where
  coe := Hom.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl
/-
**FirstOrder.Language.Hom.homClass** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Languag
e.Hom`。
形式化陈述：homClass : HomClass L (M ->[L] N) M N where map_fun
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.map_fun'`：∀ {L : FirstOrder.Language} {M : Type 
w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   (self : L.Hom
 M N) {n : ℕ} (f : L.F…
· 使用定理 `FirstOrder.Language.Hom.map_rel'`：∀ {L : FirstOrder.Language} {M : Type 
w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   (self : L.Hom
 M N) {n : ℕ} (r : L.R…
-/
instance homClass : HomClass L (M →[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'
/-
**FirstOrder.Language.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.IsAlgebraic] : StrongHomClass L (M →[L] N) M N :=
  HomClass.strongHomClassOfIsAlgebraic

@[simp]
/-
**FirstOrder.Language.Hom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Hom`。
形式化陈述：toFun_eq_coe {f : M ->[L] N} : f.toFun = (f : M -> N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl

@[ext]
/-
**FirstOrder.Language.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Hom
`。
形式化陈述：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/-
**FirstOrder.Language.Hom.map_fun** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language
.Hom`。
形式化陈述：map_fun (φ : M ->[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) : φ
 (funMap f x) = funMap f (φ ∘ x)
参数：φ : M ->[L] N；f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
-/
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/-
**FirstOrder.Language.Hom.map_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Hom`。
形式化陈述：map_constants (φ : M ->[L] N) (c : L.Constants) : φ c = c
参数：φ : M ->[L] N；c : L.Constants。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_constants`：∀ {L : FirstOrder.Language} 
{F : Type u_3} {M : Type u_4} {N : Type u_5} [inst : L.Structure M] [inst_1 : L.
Structure N]   [inst_2 : FunLike…
-/
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/-
**FirstOrder.Language.Hom.map_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language
.Hom`。
形式化陈述：map_rel (φ : M ->[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) : R
elMap r x -> RelMap r (φ ∘ x)
参数：φ : M ->[L] N；r : L.Relations n；x : Fin n -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_rel`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
-/
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r x → RelMap r (φ ∘ x) :=
  HomClass.map_rel φ r x

variable (L) (M)

/-- The identity map from a structure to itself. -/
@[refl]
/-
**FirstOrder.Language.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.Hom`
。
形式化陈述：id : M ->[L] M where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map from a structure to itself.
-/
def id : M →[L] M where
  toFun m := m

variable {L} {M}
/-
**FirstOrder.Language.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
/-
**FirstOrder.Language.Hom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.Hom`。
形式化陈述：id_apply (x : M) : id L M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : M) : id L M x = x :=
  rfl

/-- Composition of first-order homomorphisms. -/
@[trans]
/-
**FirstOrder.Language.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.Ho
m`。
形式化陈述：comp (hnp : N ->[L] P) (hmn : M ->[L] N) : M ->[L] P where toFun
参数：hnp : N ->[L] P；hmn : M ->[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of first-order homomorphisms.
-/
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp ∘ hmn
  -- Porting note: should be done by autoparam?
  map_fun' _ _ := by simp; rfl
  -- Porting note: should be done by autoparam?
  map_rel' _ _ h := map_rel _ _ _ (map_rel _ _ _ h)

@[simp]
/-
**FirstOrder.Language.Hom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Hom`。
形式化陈述：comp_apply (g : N ->[L] P) (f : M ->[L] N) (x : M) : g.comp f x = g (f x)
参数：g : N ->[L] P；f : M ->[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
/-
**FirstOrder.Language.Hom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langu
age.Hom`。
形式化陈述：comp_assoc (f : M ->[L] N) (g : N ->[L] P) (h : P ->[L] Q) : (h.comp g).co
mp f = h.comp (g.comp f)
参数：f : M ->[L] N；g : N ->[L] P；h : P ->[L] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of first-order homomorphisms is associative.
-/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Hom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language
.Hom`。
形式化陈述：comp_id (f : M ->[L] N) : f.comp (id L M) = f
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : M →[L] N) : f.comp (id L M) = f :=
  rfl

@[simp]
/-
**FirstOrder.Language.Hom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language
.Hom`。
形式化陈述：id_comp (f : M ->[L] N) : (id L N).comp f = f
参数：f : M ->[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : M →[L] N) : (id L N).comp f = f :=
  rfl

end Hom

/-- Any element of a `HomClass` can be realized as a first order homomorphism. -/
/-
**FirstOrder.Language.HomClass.toHom** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.HomClass`。
形式化陈述：{L : FirstOrder.Language} →   {F : Type u_3} →     {M : Type u_4} →       
{N : Type u_5} →         [inst : L.Structure M] →           [inst_1 : L.Structur
e N] → [inst_2 : FunLike F M N] → [L.HomClass F M N] → F → L.Hom M N
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.HomClass.map_rel`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…

--- 原说明 ---
Any element of a `HomClass` can be realized as a first order homomorphism.
-/
@[simps] def HomClass.toHom {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [HomClass L F M N] : F → M →[L] N := fun φ =>
  ⟨φ, HomClass.map_fun φ, HomClass.map_rel φ⟩

namespace Embedding

/-
**FirstOrder.Language.Embedding.funLike** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.La
nguage.Embedding`。
形式化陈述：funLike : FunLike (M ↪[L] N) M N where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (M ↪[L] N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact funext_iff.1 h x
/-
**FirstOrder.Language.Embedding.embeddingLike** 是 Mathlib 中的一个实例，位于命名空间 `FirstOr
der.Language.Embedding`。
形式化陈述：embeddingLike : EmbeddingLike (M ↪[L] N) M N where injective' f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
instance embeddingLike : EmbeddingLike (M ↪[L] N) M N where
  injective' f := f.toEmbedding.injective
/-
**FirstOrder.Language.Embedding.strongHomClass** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language.Embedding`。
形式化陈述：strongHomClass : StrongHomClass L (M ↪[L] N) M N where map_fun
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.map_fun'`：∀ {L : FirstOrder.Language} {M :
 Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   (self :
 L.Embedding M N) {n : ℕ} (f…
· 使用定理 `FirstOrder.Language.Embedding.map_rel'`：∀ {L : FirstOrder.Language} {M :
 Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   (self :
 L.Embedding M N) {n : ℕ} (r…
-/
instance strongHomClass : StrongHomClass L (M ↪[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

@[simp]
/-
**FirstOrder.Language.Embedding.map_fun** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Embedding`。
形式化陈述：map_fun (φ : M ↪[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) : φ 
(funMap f x) = funMap f (φ ∘ x)
参数：φ : M ↪[L] N；f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
-/
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/-
**FirstOrder.Language.Embedding.map_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Embedding`。
形式化陈述：map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c
参数：φ : M ↪[L] N；c : L.Constants。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_constants`：∀ {L : FirstOrder.Language} 
{F : Type u_3} {M : Type u_4} {N : Type u_5} [inst : L.Structure M] [inst_1 : L.
Structure N]   [inst_2 : FunLike…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
-/
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/-
**FirstOrder.Language.Embedding.map_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.La
nguage.Embedding`。
形式化陈述：map_rel (φ : M ↪[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) : Re
lMap r (φ ∘ x) ↔ RelMap r x
参数：φ : M ↪[L] N；r : L.Relations n；x : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
-/
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order embedding is also a first-order homomorphism. -/
/-
**FirstOrder.Language.Embedding.toHom** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Embedding`。
形式化陈述：toHom : (M ↪[L] N) -> M ->[L] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order embedding is also a first-order homomorphism.
-/
def toHom : (M ↪[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
/-
**FirstOrder.Language.Embedding.coe_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Embedding`。
形式化陈述：coe_toHom {f : M ↪[L] N} : (f.toHom : M -> N) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl
/-
**FirstOrder.Language.Embedding.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Embedding`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type w} {N : Type w'} [inst : L.Structure
 M] [inst_1 : L.Structure N],   Function.Injective DFunLike.coe
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) (↑)
  | _, _, h => DFunLike.ext'_iff.mpr h

@[ext]
/-
**FirstOrder.Language.Embedding.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Embedding`。
形式化陈述：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.coe_injective`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   F
unction.Injective DFunLike.coe
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
/-
**FirstOrder.Language.Embedding.toHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Embedding`。
形式化陈述：toHom_injective : @Function.Injective (M ↪[L] N) (M ->[L] N) (·.toHom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toHom_injective : @Function.Injective (M ↪[L] N) (M →[L] N) (·.toHom) := by
  intro f f' h
  ext
  exact congr_fun (congr_arg (↑) h) _

@[simp]
/-
**FirstOrder.Language.Embedding.toHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Embedding`。
形式化陈述：toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.toHom_injective`：toHom_injective : @Functi
on.Injective (M ↪[L] N) (M ->[L] N) (·.toHom)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toHom_inj {f g : M ↪[L] N} : f.toHom = g.toHom ↔ f = g :=
  ⟨fun h ↦ toHom_injective h, fun h ↦ congr_arg (·.toHom) h⟩
/-
**FirstOrder.Language.Embedding.injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Embedding`。
形式化陈述：injective (f : M ↪[L] N) : Function.Injective f
参数：f : M ↪[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps!]
/-
**FirstOrder.Language.Embedding.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrde
r.Language.Embedding`。
形式化陈述：ofInjective [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective f) : 
M ↪[L] N
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.map_fun'`：∀ {L : FirstOrder.Language} {M : Type 
w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N]   (self : L.Hom
 M N) {n : ℕ} (f : L.F…

--- 原说明 ---
In an algebraic language, any injective homomorphism is an embedding.
-/
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with
    inj' := hf
    map_rel' := fun {_} r x => StrongHomClass.map_rel f r x }

@[simp]
/-
**FirstOrder.Language.Embedding.coeFn_ofInjective** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Embedding`。
形式化陈述：coeFn_ofInjective [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective
 f) : (ofInjective hf : M -> N) = f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf : M → N) = f :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.ofInjective_toHom** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Embedding`。
形式化陈述：ofInjective_toHom [L.IsAlgebraic] {f : M ->[L] N} (hf : Function.Injective
 f) : (ofInjective hf).toHom = f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.ext`：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = 
g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Embedding.ofInjective_toFun`：∀ {L : FirstOrder.Langu
age} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] 
  [inst_2 : L.IsAlgebraic] {f : L.Hom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofInjective_toHom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (ofInjective hf).toHom = f := by
  ext; simp

variable (L) (M)

/-- The identity embedding from a structure to itself. -/
@[refl]
/-
**FirstOrder.Language.Embedding.refl** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Embedding`。
形式化陈述：refl : M ↪[L] M where toEmbedding
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity embedding from a structure to itself.
-/
def refl : M ↪[L] M where toEmbedding := Function.Embedding.refl M

variable {L} {M}
/-
**FirstOrder.Language.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.
Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
/-
**FirstOrder.Language.Embedding.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：refl_apply (x : M) : refl L M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order embeddings. -/
@[trans]
/-
**FirstOrder.Language.Embedding.comp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age.Embedding`。
形式化陈述：comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where toFun
参数：hnp : N ↪[L] P；hmn : M ↪[L] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of first-order embeddings.
-/
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.injective.comp hmn.injective
  -- Porting note: should be done by autoparam?
  map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
  -- Porting note: should be done by autoparam?
  map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel]

@[simp]
/-
**FirstOrder.Language.Embedding.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x)
参数：g : N ↪[L] P；f : M ↪[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order embeddings is associative. -/
/-
**FirstOrder.Language.Embedding.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) : (h.comp g).comp 
f = h.comp (g.comp f)
参数：f : M ↪[L] N；g : N ↪[L] P；h : P ↪[L] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of first-order embeddings is associative.
-/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
/-
**FirstOrder.Language.Embedding.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Embedding`。
形式化陈述：comp_injective (h : N ↪[L] P) : Function.Injective (h.comp : (M ↪[L] N) ->
 (M ↪[L] P))
参数：h : N ↪[L] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.ext`：ext ⦃f g : M ↪[L] N⦄ (h : forall x, f
 x = g x) : f = g
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem comp_injective (h : N ↪[L] P) :
    Function.Injective (h.comp : (M ↪[L] N) → (M ↪[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
/-
**FirstOrder.Language.Embedding.comp_inj** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Embedding`。
形式化陈述：comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g
参数：h : N ↪[L] P；f g : M ↪[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.comp_injective`：comp_injective (h : N ↪[L]
 P) : Function.Injective (h.comp : (M ↪[L] N) -> (M ↪[L] P))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp_inj (h : N ↪[L] P) (f g : M ↪[L] N) : h.comp f = h.comp g ↔ f = g :=
  ⟨fun eq ↦ h.comp_injective eq, congr_arg h.comp⟩
/-
**FirstOrder.Language.Embedding.toHom_comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Embedding`。
形式化陈述：toHom_comp_injective (h : N ↪[L] P) : Function.Injective (h.toHom.comp : (
M ->[L] N) -> (M ->[L] P))
参数：h : N ↪[L] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Hom.ext`：ext ⦃f g : M ->[L] N⦄ (h : forall x, f x = 
g x) : f = g
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toHom_comp_injective (h : N ↪[L] P) :
    Function.Injective (h.toHom.comp : (M →[L] N) → (M →[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (DFunLike.congr_fun hfg x)

@[simp]
/-
**FirstOrder.Language.Embedding.toHom_comp_inj** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.Embedding`。
形式化陈述：toHom_comp_inj (h : N ↪[L] P) (f g : M ->[L] N) : h.toHom.comp f = h.toHom
.comp g ↔ f = g
参数：h : N ↪[L] P；f g : M ->[L] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Embedding.toHom_comp_injective`：toHom_comp_injective
 (h : N ↪[L] P) : Function.Injective (h.toHom.comp : (M ->[L] N) -> (M ->[L] P))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toHom_comp_inj (h : N ↪[L] P) (f g : M →[L] N) : h.toHom.comp f = h.toHom.comp g ↔ f = g :=
  ⟨fun eq ↦ h.toHom_comp_injective eq, congr_arg h.toHom.comp⟩

@[simp]
/-
**FirstOrder.Language.Embedding.comp_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) : (hnp.comp hmn).toHom = hnp.
toHom.comp hmn.toHom
参数：hnp : N ↪[L] P；hmn : M ↪[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toHom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
/-
**FirstOrder.Language.Embedding.comp_refl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Embedding`。
形式化陈述：comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f
参数：f : M ↪[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem comp_refl (f : M ↪[L] N) : f.comp (refl L M) = f := DFunLike.coe_injective rfl

@[simp]
/-
**FirstOrder.Language.Embedding.refl_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Embedding`。
形式化陈述：refl_comp (f : M ↪[L] N) : (refl L N).comp f = f
参数：f : M ↪[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem refl_comp (f : M ↪[L] N) : (refl L N).comp f = f := DFunLike.coe_injective rfl

@[simp]
/-
**FirstOrder.Language.Embedding.refl_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Embedding`。
形式化陈述：refl_toHom : (refl L M).toHom = Hom.id L M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

end Embedding

/-- Any element of an injective `StrongHomClass` can be realized as a first order embedding. -/
/-
**FirstOrder.Language.StrongHomClass.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Firs
tOrder.Language.StrongHomClass`。
形式化陈述：{L : FirstOrder.Language} →   {F : Type u_3} →     {M : Type u_4} →       
{N : Type u_5} →         [inst : L.Structure M] →           [inst_1 : L.Structur
e N] →             [inst_2 : FunLike F M N] → [EmbeddingLike F M N] → [L.StrongH
omClass F M N] → F → L.Embedding M N
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
· 使用定理 `FirstOrder.Language.StrongHomClass.map_fun`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…

--- 原说明 ---
Any element of an injective `StrongHomClass` can be realized as a first order em
bedding.
-/
@[simps] def StrongHomClass.toEmbedding {F M N} [L.Structure M] [L.Structure N] [FunLike F M N]
    [EmbeddingLike F M N] [StrongHomClass L F M N] : F → M ↪[L] N := fun φ =>
  ⟨⟨φ, EmbeddingLike.injective φ⟩, StrongHomClass.map_fun φ, StrongHomClass.map_rel φ⟩

namespace Equiv

/-
**FirstOrder.Language.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Equi
v`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃[L] N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    simp only [mk.injEq]
    ext x
    exact funext_iff.1 h₁ x
/-
**FirstOrder.Language.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Equi
v`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StrongHomClass L (M ≃[L] N) M N where
  map_fun := map_fun'
  map_rel := map_rel'

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
/-
**FirstOrder.Language.Equiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Equiv`。
形式化陈述：symm (f : M ≃[L] N) : N ≃[L] M
参数：f : M ≃[L] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The inverse of a first-order equivalence is a first-order equivalence.
-/
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' {x} => by
      simp only [Equiv.toFun_as_coe]
      rw [Equiv.symm_apply_eq]
      refine Eq.trans ?_ (f.map_fun' f' (f.toEquiv.symm ∘ x)).symm
      rw [← Function.comp_assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp]
    map_rel' := fun n r {x} => by
      simp only [Equiv.toFun_as_coe]
      refine (f.map_rel' r (f.toEquiv.symm ∘ x)).symm.trans ?_
      rw [← Function.comp_assoc, Equiv.toFun_as_coe, Equiv.self_comp_symm, Function.id_comp] }

@[simp]
/-
**FirstOrder.Language.Equiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：symm_symm (f : M ≃[L] N) : f.symm.symm = f
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : M ≃[L] N) :
    f.symm.symm = f :=
  rfl
/-
**FirstOrder.Language.Equiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Equiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (M ≃[L] N) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `FirstOrder.Language.Equiv.symm_symm`：symm_symm (f : M ≃[L] N) : f.symm.s
ymm = f
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃[L] N) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**FirstOrder.Language.Equiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Equiv`。
形式化陈述：apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a
参数：f : M ≃[L] N；a : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a

@[simp]
/-
**FirstOrder.Language.Equiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Equiv`。
形式化陈述：symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a
参数：f : M ≃[L] N；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp]
/-
**FirstOrder.Language.Equiv.map_fun** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Equiv`。
形式化陈述：map_fun (φ : M ≃[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) : φ 
(funMap f x) = funMap f (φ ∘ x)
参数：φ : M ≃[L] N；f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_fun`：∀ {L : outParam FirstOrder.Languag
e} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {inst : 
FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
-/
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) :=
  HomClass.map_fun φ f x

@[simp]
/-
**FirstOrder.Language.Equiv.map_constants** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Equiv`。
形式化陈述：map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c
参数：φ : M ≃[L] N；c : L.Constants。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.HomClass.map_constants`：∀ {L : FirstOrder.Language} 
{F : Type u_3} {M : Type u_4} {N : Type u_5} [inst : L.Structure M] [inst_1 : L.
Structure N]   [inst_2 : FunLike…
· 使用定理 `FirstOrder.Language.StrongHomClass.homClass`：∀ {L : FirstOrder.Language}
 {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N] {F :
 Type u_3}   [inst_2 : FunLike F …
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
-/
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

@[simp]
/-
**FirstOrder.Language.Equiv.map_rel** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge.Equiv`。
形式化陈述：map_rel (φ : M ≃[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) : Re
lMap r (φ ∘ x) ↔ RelMap r x
参数：φ : M ≃[L] N；r : L.Relations n；x : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.StrongHomClass.map_rel`：∀ {L : outParam FirstOrder.L
anguage} {F : Type u_3} {M : outParam (Type u_4)} {N : outParam (Type u_5)}   {i
nst : FunLike F M N} {inst_1 : L…
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N
-/
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  StrongHomClass.map_rel φ r x

/-- A first-order equivalence is also a first-order embedding. -/
/-
**FirstOrder.Language.Equiv.toEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.La
nguage.Equiv`。
形式化陈述：toEmbedding : (M ≃[L] N) -> M ↪[L] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.instStrongHomClass`：∀ {L : FirstOrder.Language
} {M : Type w} {N : Type w'} [inst : L.Structure M] [inst_1 : L.Structure N],   
L.StrongHomClass (L.Equiv M N) M N

--- 原说明 ---
A first-order equivalence is also a first-order embedding.
-/
def toEmbedding : (M ≃[L] N) → M ↪[L] N :=
  StrongHomClass.toEmbedding

/-- A first-order equivalence is also a first-order homomorphism. -/
/-
**FirstOrder.Language.Equiv.toHom** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language
.Equiv`。
形式化陈述：toHom : (M ≃[L] N) -> M ->[L] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A first-order equivalence is also a first-order homomorphism.
-/
def toHom : (M ≃[L] N) → M →[L] N :=
  HomClass.toHom

@[simp]
/-
**FirstOrder.Language.Equiv.toEmbedding_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Equiv`。
形式化陈述：toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEmbedding_toHom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.coe_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：coe_toHom {f : M ≃[L] N} : (f.toHom : M -> N) = (f : M -> N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.coe_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Language.Equiv`。
形式化陈述：coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M -> N) = (f : M -> N)
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEmbedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl
/-
**FirstOrder.Language.Equiv.injective_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Fir
stOrder.Language.Equiv`。
形式化陈述：injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) -> M 
↪[L] N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_toEmbedding : Function.Injective (toEmbedding : (M ≃[L] N) → M ↪[L] N) := by
  intro _ _ h; apply DFunLike.coe_injective; exact congr_arg (DFunLike.coe ∘ Embedding.toHom) h
/-
**FirstOrder.Language.Equiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Equiv`。
形式化陈述：coe_injective : @Function.Injective (M ≃[L] N) (M -> N) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) (↑) :=
  DFunLike.coe_injective

@[ext]
/-
**FirstOrder.Language.Equiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.E
quiv`。
形式化陈述：ext ⦃f g : M ≃[L] N⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.coe_injective`：coe_injective : @Function.Injec
tive (M ≃[L] N) (M -> N) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)
/-
**FirstOrder.Language.Equiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：bijective (f : M ≃[L] N) : Function.Bijective f
参数：f : M ≃[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
theorem bijective (f : M ≃[L] N) : Function.Bijective f :=
  EquivLike.bijective f
/-
**FirstOrder.Language.Equiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：injective (f : M ≃[L] N) : Function.Injective f
参数：f : M ≃[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
theorem injective (f : M ≃[L] N) : Function.Injective f :=
  EquivLike.injective f
/-
**FirstOrder.Language.Equiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：surjective (f : M ≃[L] N) : Function.Surjective f
参数：f : M ≃[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
theorem surjective (f : M ≃[L] N) : Function.Surjective f :=
  EquivLike.surjective f

variable (L) (M)

/-- The identity equivalence from a structure to itself. -/
@[refl]
/-
**FirstOrder.Language.Equiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Equiv`。
形式化陈述：refl : M ≃[L] M where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity equivalence from a structure to itself.
-/
def refl : M ≃[L] M where toEquiv := _root_.Equiv.refl M

variable {L} {M}
/-
**FirstOrder.Language.Equiv.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.Equi
v`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
/-
**FirstOrder.Language.Equiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：refl_apply (x : M) : refl L M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem refl_apply (x : M) : refl L M x = x := by simp [refl]; rfl

/-- Composition of first-order equivalences. -/
@[trans]
/-
**FirstOrder.Language.Equiv.comp** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language.
Equiv`。
形式化陈述：comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P
参数：hnp : N ≃[L] P；hmn : M ≃[L] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Composition of first-order equivalences.
-/
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with
    toFun := hnp ∘ hmn
    -- Porting note: should be done by autoparam?
    map_fun' := by intros; simp only [Function.comp_apply, map_fun]; trivial
    -- Porting note: should be done by autoparam?
    map_rel' := by intros; rw [Function.comp_assoc, map_rel, map_rel] }

@[simp]
/-
**FirstOrder.Language.Equiv.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x)
参数：g : N ≃[L] P；f : M ≃[L] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.comp_refl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g
参数：g : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_refl (g : M ≃[L] N) : g.comp (refl L M) = g :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.refl_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：refl_comp (g : M ≃[L] N) : (refl L N).comp g = g
参数：g : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_comp (g : M ≃[L] N) : (refl L N).comp g = g :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.refl_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Equiv`。
形式化陈述：refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toEmbedding : (refl L M).toEmbedding = Embedding.refl L M :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.refl_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：refl_toHom : (refl L M).toHom = Hom.id L M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toHom : (refl L M).toHom = Hom.id L M :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
/-
**FirstOrder.Language.Equiv.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) : (h.comp g).comp 
f = h.comp (g.comp f)
参数：f : M ≃[L] N；g : N ≃[L] P；h : P ≃[L] Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of first-order homomorphisms is associative.
-/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
/-
**FirstOrder.Language.Equiv.injective_comp** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Equiv`。
形式化陈述：injective_comp (h : N ≃[L] P) : Function.Injective (h.comp : (M ≃[L] N) ->
 (M ≃[L] P))
参数：h : N ≃[L] P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.ext`：ext ⦃f g : M ≃[L] N⦄ (h : forall x, f x =
 g x) : f = g
· 使用定理 `FirstOrder.Language.Equiv.injective`：injective (f : M ≃[L] N) : Function
.Injective f
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_comp (h : N ≃[L] P) :
    Function.Injective (h.comp : (M ≃[L] N) → (M ≃[L] P)) := by
  intro f g hfg
  ext x; exact h.injective (congr_fun (congr_arg DFunLike.coe hfg) x)

@[simp]
/-
**FirstOrder.Language.Equiv.comp_toHom** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Equiv`。
形式化陈述：comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) : (hnp.comp hmn).toHom = hnp.
toHom.comp hmn.toHom
参数：hnp : N ≃[L] P；hmn : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toHom (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.comp_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Equiv`。
形式化陈述：comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) : (hnp.comp hmn).toEmbe
dding = hnp.toEmbedding.comp hmn.toEmbedding
参数：hnp : N ≃[L] P；hmn : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toEmbedding (hnp : N ≃[L] P) (hmn : M ≃[L] N) :
    (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.toEmbedding :=
  rfl

@[simp]
/-
**FirstOrder.Language.Equiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Equiv`。
形式化陈述：self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.ext`：ext ⦃f g : M ≃[L] N⦄ (h : forall x, f x =
 g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Equiv.comp_apply`：comp_apply (g : N ≃[L] P) (f : M ≃
[L] N) (x : M) : g.comp f x = g (f x)
· 使用定理 `FirstOrder.Language.Equiv.apply_symm_apply`：apply_symm_apply (f : M ≃[L]
 N) (a : N) : f (f.symm a) = a
· 使用定理 `FirstOrder.Language.Equiv.refl_apply`：refl_apply (x : M) : refl L M x = 
x
-/
theorem self_comp_symm (f : M ≃[L] N) : f.comp f.symm = refl L N := by
  ext; rw [comp_apply, apply_symm_apply, refl_apply]

@[simp]
/-
**FirstOrder.Language.Equiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Equiv`。
形式化陈述：symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.ext`：ext ⦃f g : M ≃[L] N⦄ (h : forall x, f x =
 g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Equiv.comp_apply`：comp_apply (g : N ≃[L] P) (f : M ≃
[L] N) (x : M) : g.comp f x = g (f x)
· 使用定理 `FirstOrder.Language.Equiv.symm_apply_apply`：symm_apply_apply (f : M ≃[L]
 N) (a : M) : f.symm (f a) = a
· 使用定理 `FirstOrder.Language.Equiv.refl_apply`：refl_apply (x : M) : refl L M x = 
x
-/
theorem symm_comp_self (f : M ≃[L] N) : f.symm.comp f = refl L M := by
  ext; rw [comp_apply, symm_apply_apply, refl_apply]

@[simp]
/-
**FirstOrder.Language.Equiv.symm_comp_self_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Equiv`。
形式化陈述：symm_comp_self_toEmbedding (f : M ≃[L] N) : f.symm.toEmbedding.comp f.toEm
bedding = Embedding.refl L M
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.comp_toEmbedding`：comp_toEmbedding (hnp : N ≃[
L] P) (hmn : M ≃[L] N) : (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.t
oEmbedding
· 使用定理 `FirstOrder.Language.Equiv.symm_comp_self`：symm_comp_self (f : M ≃[L] N) 
: f.symm.comp f = refl L M
· 使用定理 `FirstOrder.Language.Equiv.refl_toEmbedding`：refl_toEmbedding : (refl L M
).toEmbedding = Embedding.refl L M
-/
theorem symm_comp_self_toEmbedding (f : M ≃[L] N) :
    f.symm.toEmbedding.comp f.toEmbedding = Embedding.refl L M := by
  rw [← comp_toEmbedding, symm_comp_self, refl_toEmbedding]

@[simp]
/-
**FirstOrder.Language.Equiv.self_comp_symm_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Equiv`。
形式化陈述：self_comp_symm_toEmbedding (f : M ≃[L] N) : f.toEmbedding.comp f.symm.toEm
bedding = Embedding.refl L N
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.comp_toEmbedding`：comp_toEmbedding (hnp : N ≃[
L] P) (hmn : M ≃[L] N) : (hnp.comp hmn).toEmbedding = hnp.toEmbedding.comp hmn.t
oEmbedding
· 使用定理 `FirstOrder.Language.Equiv.self_comp_symm`：self_comp_symm (f : M ≃[L] N) 
: f.comp f.symm = refl L N
· 使用定理 `FirstOrder.Language.Equiv.refl_toEmbedding`：refl_toEmbedding : (refl L M
).toEmbedding = Embedding.refl L M
-/
theorem self_comp_symm_toEmbedding (f : M ≃[L] N) :
    f.toEmbedding.comp f.symm.toEmbedding = Embedding.refl L N := by
  rw [← comp_toEmbedding, self_comp_symm, refl_toEmbedding]

@[simp]
/-
**FirstOrder.Language.Equiv.symm_comp_self_toHom** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Equiv`。
形式化陈述：symm_comp_self_toHom (f : M ≃[L] N) : f.symm.toHom.comp f.toHom = Hom.id L
 M
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.comp_toHom`：comp_toHom (hnp : N ≃[L] P) (hmn :
 M ≃[L] N) : (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom
· 使用定理 `FirstOrder.Language.Equiv.symm_comp_self`：symm_comp_self (f : M ≃[L] N) 
: f.symm.comp f = refl L M
· 使用定理 `FirstOrder.Language.Equiv.refl_toHom`：refl_toHom : (refl L M).toHom = Ho
m.id L M
-/
theorem symm_comp_self_toHom (f : M ≃[L] N) :
    f.symm.toHom.comp f.toHom = Hom.id L M := by
  rw [← comp_toHom, symm_comp_self, refl_toHom]

@[simp]
/-
**FirstOrder.Language.Equiv.self_comp_symm_toHom** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Equiv`。
形式化陈述：self_comp_symm_toHom (f : M ≃[L] N) : f.toHom.comp f.symm.toHom = Hom.id L
 N
参数：f : M ≃[L] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Equiv.comp_toHom`：comp_toHom (hnp : N ≃[L] P) (hmn :
 M ≃[L] N) : (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom
· 使用定理 `FirstOrder.Language.Equiv.self_comp_symm`：self_comp_symm (f : M ≃[L] N) 
: f.comp f.symm = refl L N
· 使用定理 `FirstOrder.Language.Equiv.refl_toHom`：refl_toHom : (refl L M).toHom = Ho
m.id L M
-/
theorem self_comp_symm_toHom (f : M ≃[L] N) :
    f.toHom.comp f.symm.toHom = Hom.id L N := by
  rw [← comp_toHom, self_comp_symm, refl_toHom]

@[simp]
/-
**FirstOrder.Language.Equiv.comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Equiv`。
形式化陈述：comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.
symm
参数：f : M ≃[L] N；g : N ≃[L] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_symm (f : M ≃[L] N) (g : N ≃[L] P) : (g.comp f).symm = f.symm.comp g.symm :=
  rfl
/-
**FirstOrder.Language.Equiv.comp_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Equiv`。
形式化陈述：comp_right_injective (h : M ≃[L] N) : Function.Injective (fun f => f.comp 
h : (N ≃[L] P) -> (M ≃[L] P))
参数：h : M ≃[L] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Equiv.comp_assoc`：comp_assoc (f : M ≃[L] N) (g : N ≃
[L] P) (h : P ≃[L] Q) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `FirstOrder.Language.Equiv.self_comp_symm`：self_comp_symm (f : M ≃[L] N) 
: f.comp f.symm = refl L N
· 使用定理 `FirstOrder.Language.Equiv.comp_refl`：comp_refl (g : M ≃[L] N) : g.comp (
refl L M) = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp_right_injective (h : M ≃[L] N) :
    Function.Injective (fun f ↦ f.comp h : (N ≃[L] P) → (M ≃[L] P)) := by
  intro f g hfg
  convert! (congr_arg (fun r : (M ≃[L] P) ↦ r.comp h.symm) hfg) <;>
    rw [comp_assoc, self_comp_symm, comp_refl]

@[simp]
/-
**FirstOrder.Language.Equiv.comp_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.Equiv`。
形式化陈述：comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f =
 g
参数：h : M ≃[L] N；f g : N ≃[L] P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Equiv.comp_right_injective`：comp_right_injective (h 
: M ≃[L] N) : Function.Injective (fun f => f.comp h : (N ≃[L] P) -> (M ≃[L] P))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem comp_right_inj (h : M ≃[L] N) (f g : N ≃[L] P) : f.comp h = g.comp h ↔ f = g :=
  ⟨fun eq ↦ h.comp_right_injective eq, congr_arg (fun (r : N ≃[L] P) ↦ r.comp h)⟩

end Equiv

/-- Any element of a bijective `StrongHomClass` can be realized as a first order isomorphism. -/
/-
**FirstOrder.Language.StrongHomClass.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language.StrongHomClass`。
形式化陈述：{L : FirstOrder.Language} →   {F : Type u_3} →     {M : Type u_4} →       
{N : Type u_5} →         [inst : L.Structure M] →           [inst_1 : L.Structur
e N] → [inst_2 : EquivLike F M N] → [L.StrongHomClass F M N] → F → L.Equiv M N
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.left_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : outP
aram (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.LeftInverse (Equiv
Like.inv…
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…

--- 原说明 ---
Any element of a bijective `StrongHomClass` can be realized as a first order iso
morphism.
-/
@[simps] def StrongHomClass.toEquiv {F M N} [L.Structure M] [L.Structure N] [EquivLike F M N]
    [StrongHomClass L F M N] : F → M ≃[L] N := fun φ =>
  ⟨⟨φ, EquivLike.inv φ, EquivLike.left_inv φ, EquivLike.right_inv φ⟩, StrongHomClass.map_fun φ,
    StrongHomClass.map_rel φ⟩

section SumStructure

variable (L₁ L₂ : Language) (S : Type*) [L₁.Structure S] [L₂.Structure S]

/-
**FirstOrder.Language.sumStructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Languag
e`。
形式化陈述：sumStructure : (L₁.sum L₂).Structure S where funMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sumStructure : (L₁.sum L₂).Structure S where
  funMap := Sum.elim funMap funMap
  RelMap := Sum.elim RelMap RelMap

variable {L₁ L₂ S}

@[simp]
/-
**FirstOrder.Language.funMap_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：funMap_sumInl {n : Nat} (f : L₁.Functions n) : @funMap (L₁.sum L₂) S _ n (
Sum.inl f) = funMap f
参数：f : L₁.Functions n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funMap_sumInl {n : ℕ} (f : L₁.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl

@[simp]
/-
**FirstOrder.Language.funMap_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：funMap_sumInr {n : Nat} (f : L₂.Functions n) : @funMap (L₁.sum L₂) S _ n (
Sum.inr f) = funMap f
参数：f : L₂.Functions n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funMap_sumInr {n : ℕ} (f : L₂.Functions n) :
    @funMap (L₁.sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl

@[simp]
/-
**FirstOrder.Language.relMap_sumInl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：relMap_sumInl {n : Nat} (R : L₁.Relations n) : @RelMap (L₁.sum L₂) S _ n (
Sum.inl R) = RelMap R
参数：R : L₁.Relations n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relMap_sumInl {n : ℕ} (R : L₁.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl

@[simp]
/-
**FirstOrder.Language.relMap_sumInr** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Langua
ge`。
形式化陈述：relMap_sumInr {n : Nat} (R : L₂.Relations n) : @RelMap (L₁.sum L₂) S _ n (
Sum.inr R) = RelMap R
参数：R : L₂.Relations n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relMap_sumInr {n : ℕ} (R : L₂.Relations n) :
    @RelMap (L₁.sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl


end SumStructure

section Empty

/-- Any type can be made uniquely into a structure over the empty language. -/
@[instance_reducible]
/-
**FirstOrder.Language.emptyStructure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：{M : Type w} → FirstOrder.Language.empty.Structure M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.instIsRelationalEmpty`：FirstOrder.Language.empty.IsR
elational
· 使用定理 `FirstOrder.Language.instIsAlgebraicEmpty`：FirstOrder.Language.empty.IsAl
gebraic

--- 原说明 ---
Any type can be made uniquely into a structure over the empty language.
-/
def emptyStructure : Language.empty.Structure M where
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (Language.empty.Structure M) :=
  ⟨⟨Language.emptyStructure⟩, fun a => by
    ext _ f <;> exact Empty.elim f⟩

variable [Language.empty.Structure M] [Language.empty.Structure N]
/-
**FirstOrder.Language.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) strongHomClassEmpty {F} [FunLike F M N] :
    StrongHomClass Language.empty F M N :=
  ⟨fun _ _ f => Empty.elim f, fun _ _ r => Empty.elim r⟩

@[simp]
/-
**FirstOrder.Language.empty.nonempty_embedding_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.empty`。
形式化陈述：∀ {M : Type w} {N : Type w'} [inst : FirstOrder.Language.empty.Structure M
]   [inst_1 : FirstOrder.Language.empty.Structure N],   Nonempty (FirstOrder.Lan
guage.empty.Embedding M N) ↔     Cardinal.lift.{w', w} (Cardinal.mk M) ≤ Cardina
l.lift.{w, w'} (Cardinal.mk N)
参数：FirstOrder.Language.empty.Embedding M N；Cardinal.mk M；Cardinal.mk N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `FirstOrder.Language.strongHomClassEmpty`：∀ {M : Type w} {N : Type w'} [i
nst : FirstOrder.Language.empty.Structure M]   [inst_1 : FirstOrder.Language.emp
ty.Structure N] {F : Type u_3…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
-/
theorem empty.nonempty_embedding_iff :
    Nonempty (M ↪[Language.empty] N) ↔ Cardinal.lift.{w'} #M ≤ Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEmbedding, Nonempty.map StrongHomClass.toEmbedding⟩
    Cardinal.lift_mk_le'.symm

@[simp]
/-
**FirstOrder.Language.empty.nonempty_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstO
rder.Language.empty`。
形式化陈述：∀ {M : Type w} {N : Type w'} [inst : FirstOrder.Language.empty.Structure M
]   [inst_1 : FirstOrder.Language.empty.Structure N],   Nonempty (FirstOrder.Lan
guage.empty.Equiv M N) ↔     Cardinal.lift.{w', w} (Cardinal.mk M) = Cardinal.li
ft.{w, w'} (Cardinal.mk N)
参数：FirstOrder.Language.empty.Equiv M N；Cardinal.mk M；Cardinal.mk N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
-/
theorem empty.nonempty_equiv_iff :
    Nonempty (M ≃[Language.empty] N) ↔ Cardinal.lift.{w'} #M = Cardinal.lift.{w} #N :=
  _root_.trans ⟨Nonempty.map fun f => f.toEquiv, Nonempty.map fun f => { toEquiv := f }⟩
    Cardinal.lift_mk_eq'.symm

/-- Makes a `Language.empty.Hom` out of any function.
This is only needed because there is no instance of `FunLike (M → N) M N`, and thus no instance of
`Language.empty.HomClass M N`. -/
@[simps]
/-
**FirstOrder.Language._root_.Function.emptyHom** 是 Mathlib 中的一个定义，位于命名空间 `FirstO
rder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes a `Language.empty.Hom` out of any function.
This is only needed because there is no instance of `FunLike (M → N) M N`, and t
hus no instance of
`Language.empty.HomClass M N`.
-/
def _root_.Function.emptyHom (f : M → N) : M →[Language.empty] N where toFun := f

end Empty

end Language

end FirstOrder

namespace Equiv

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {L : Language} {M : Type*} {N : Type*} [L.Structure M]

/-- A structure induced by a bijection. -/
@[simps!, instance_reducible]
/-
**Equiv.inducedStructure** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：inducedStructure (e : M ≃ N) : L.Structure N
参数：e : M ≃ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A structure induced by a bijection.
-/
def inducedStructure (e : M ≃ N) : L.Structure N :=
  ⟨fun f x => e (funMap f (e.symm ∘ x)), fun r x => RelMap r (e.symm ∘ x)⟩

/-- A bijection as a first-order isomorphism with the induced structure on the codomain. -/
/-
**Equiv.inducedStructureEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStruct
ure e)
参数：e : M ≃ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bijection as a first-order isomorphism with the induced structure on the codom
ain.
-/
def inducedStructureEquiv (e : M ≃ N) : @Language.Equiv L M N _ (inducedStructure e) := by
  letI : L.Structure N := inducedStructure e
  exact
  { e with
    map_fun' := @fun n f x => by simp [← Function.comp_assoc e.symm e x]
    map_rel' := @fun n r x => by simp [← Function.comp_assoc e.symm e x] }

@[simp]
/-
**Equiv.toEquiv_inducedStructureEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toEquiv_inducedStructureEquiv (e : M ≃ N) : @Language.Equiv.toEquiv L M N 
_ (inducedStructure e) (inducedStructureEquiv e) = e
参数：e : M ≃ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_inducedStructureEquiv (e : M ≃ N) :
    @Language.Equiv.toEquiv L M N _ (inducedStructure e) (inducedStructureEquiv e) = e :=
  rfl

@[simp]
/-
**Equiv.toFun_inducedStructureEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toFun_inducedStructureEquiv (e : M ≃ N) : DFunLike.coe (@inducedStructureE
quiv L M N _ e) = e
参数：e : M ≃ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_inducedStructureEquiv (e : M ≃ N) :
    DFunLike.coe (@inducedStructureEquiv L M N _ e) = e :=
  rfl

@[simp]
/-
**Equiv.toFun_inducedStructureEquiv_Symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toFun_inducedStructureEquiv_Symm (e : M ≃ N) : (by letI : L.Structure N
参数：e : M ≃ N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_inducedStructureEquiv_Symm (e : M ≃ N) :
    (by
    letI : L.Structure N := inducedStructure e
    exact DFunLike.coe (@inducedStructureEquiv L M N _ e).symm) = (e.symm : N → M) :=
  rfl

end Equiv

