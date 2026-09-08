/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.ArithMult

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions

* `ArithmeticFunction R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
* An arithmetic function `f` `IsMultiplicative` when `x.Coprime y → f (x * y) = f x * f y`.
* Multiplication and power instances on `ArithmeticFunction R`, are defined using Dirichlet
  convolution.

Further examples of arithmetic functions, such as the Möbius function `μ`, are available in
other files in the `Mathlib.NumberTheory.ArithmeticFunction` directory.

## Tags

arithmetic functions, dirichlet convolution, divisors
-/

@[expose] public section

open Finset

open Nat

variable (R : Type*)

/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `ArithmeticFunctions` is by
  Dirichlet convolution. -/
/-
**ArithmeticFunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ArithmeticFunction [Zero R]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literatur
e, they are
  often instead defined as functions from `ℕ+`. Multiplication on `ArithmeticFun
ctions` is by
  Dirichlet convolution.
-/
def ArithmeticFunction [Zero R] :=
  ZeroHom ℕ R
/-
**ArithmeticFunction.zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ArithmeticFunction.zero [Zero R] : Zero (ArithmeticFunction R) :=
  inferInstanceAs (Zero (ZeroHom ℕ R))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] : Inhabited (ArithmeticFunction R) := inferInstanceAs (Inhabited (ZeroHom ℕ R))

variable {R}

namespace ArithmeticFunction

section Zero

variable [Zero R]

/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (ArithmeticFunction R) ℕ R :=
  inferInstanceAs (FunLike (ZeroHom ℕ R) ℕ R)

@[simp]
/-
**ArithmeticFunction.toFun_eq** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：toFun_eq (f : ArithmeticFunction R) : f.toFun = f
参数：f : ArithmeticFunction R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq (f : ArithmeticFunction R) : f.toFun = f := rfl

@[simp]
/-
**ArithmeticFunction.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：coe_mk (f : Nat -> R) (hf) : @DFunLike.coe (ArithmeticFunction R) _ _ _ (Z
eroHom.mk f hf) = f
参数：f : Nat -> R；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : ℕ → R) (hf) : @DFunLike.coe (ArithmeticFunction R) _ _ _
    (ZeroHom.mk f hf) = f := rfl

@[simp]
/-
**ArithmeticFunction.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：map_zero {f : ArithmeticFunction R} : f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
-/
theorem map_zero {f : ArithmeticFunction R} : f 0 = 0 :=
  ZeroHom.map_zero' f
/-
**ArithmeticFunction.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：coe_inj {f g : ArithmeticFunction R} : (f : Nat -> R) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
-/
theorem coe_inj {f g : ArithmeticFunction R} : (f : ℕ → R) = g ↔ f = g :=
  DFunLike.coe_fn_eq
/-
**ArithmeticFunction.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：range_coe : Set.range ((↑) : ArithmeticFunction R -> (Nat -> R)) = {f | f 
0 = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_coe : Set.range ((↑) : ArithmeticFunction R → (ℕ → R)) = {f | f 0 = 0} := by
  ext f
  exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

@[simp]
/-
**ArithmeticFunction.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：zero_apply {x : Nat} : (0 : ArithmeticFunction R) x = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply {x : ℕ} : (0 : ArithmeticFunction R) x = 0 :=
  rfl

@[ext]
/-
**ArithmeticFunction.ext** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [inst_1 : Z
ero N] ⦃f g : ZeroHom M N⦄, (∀ (x : M), f x = g x) → f = g
-/
theorem ext ⦃f g : ArithmeticFunction R⦄ (h : ∀ x, f x = g x) : f = g :=
  ZeroHom.ext h

section One

variable [One R]

/-
**ArithmeticFunction.one** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
形式化陈述：one : One (ArithmeticFunction R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (ArithmeticFunction R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩
/-
**ArithmeticFunction.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：one_apply {x : Nat} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply {x : ℕ} : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0 :=
  rfl

@[simp]
/-
**ArithmeticFunction.one_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：one_one : (1 : ArithmeticFunction R) 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_one : (1 : ArithmeticFunction R) 1 = 1 :=
  rfl

@[simp]
/-
**ArithmeticFunction.one_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：one_apply_ne {x : Nat} (h : x != 1) : (1 : ArithmeticFunction R) x = 0
参数：h : x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : ArithmeticFunction R) x = 0 :=
  if_neg h

end One

end Zero

/-- Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We cannot inline
this in `natCoe` because it gets unfolded too much. -/
@[coe]
/-
**ArithmeticFunction.natToArithmeticFunction** 是 Mathlib 中的一个定义，位于命名空间 `Arithmet
icFunction`。
形式化陈述：natToArithmeticFunction [AddMonoidWithOne R] : (ArithmeticFunction Nat) ->
 (ArithmeticFunction R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce an arithmetic function with values in `ℕ` to one with values in `R`. We c
annot inline
this in `natCoe` because it gets unfolded too much.
-/
def natToArithmeticFunction [AddMonoidWithOne R] :
    (ArithmeticFunction ℕ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩
/-
**ArithmeticFunction.natCoe** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
形式化陈述：natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction Nat) (ArithmeticFunc
tion R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance natCoe [AddMonoidWithOne R] : Coe (ArithmeticFunction ℕ) (ArithmeticFunction R) :=
  ⟨natToArithmeticFunction⟩

@[simp]
/-
**ArithmeticFunction.natCoe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：natCoe_nat (f : ArithmeticFunction Nat) : natToArithmeticFunction f = f
参数：f : ArithmeticFunction Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
-/
theorem natCoe_nat (f : ArithmeticFunction ℕ) : natToArithmeticFunction f = f :=
  ext fun _ => cast_id _

@[simp]
/-
**ArithmeticFunction.natCoe_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction Nat} {x : Nat} :
 (f : ArithmeticFunction R) x = f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCoe_apply [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x :=
  rfl

/-- Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We cannot inline
this in `intCoe` because it gets unfolded too much. -/
@[coe]
/-
**ArithmeticFunction.ofInt** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction`。
形式化陈述：ofInt [AddGroupWithOne R] : (ArithmeticFunction Int) -> (ArithmeticFunctio
n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce an arithmetic function with values in `ℤ` to one with values in `R`. We c
annot inline
this in `intCoe` because it gets unfolded too much.
-/
def ofInt [AddGroupWithOne R] :
    (ArithmeticFunction ℤ) → (ArithmeticFunction R) :=
  fun f => ⟨fun n => ↑(f n), by simp⟩
/-
**ArithmeticFunction.intCoe** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
形式化陈述：intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction Int) (ArithmeticFunct
ion R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance intCoe [AddGroupWithOne R] : Coe (ArithmeticFunction ℤ) (ArithmeticFunction R) :=
  ⟨ofInt⟩

@[simp]
/-
**ArithmeticFunction.intCoe_int** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：intCoe_int (f : ArithmeticFunction Int) : ofInt f = f
参数：f : ArithmeticFunction Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `Int.cast_id`：∀ {n : ℤ}, ↑n = n
-/
theorem intCoe_int (f : ArithmeticFunction ℤ) : ofInt f = f :=
  ext fun _ => Int.cast_id

@[simp]
/-
**ArithmeticFunction.intCoe_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`
。
形式化陈述：intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction Int} {x : Nat} : 
(f : ArithmeticFunction R) x = f x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCoe_apply [AddGroupWithOne R] {f : ArithmeticFunction ℤ} {x : ℕ} :
    (f : ArithmeticFunction R) x = f x := rfl

@[simp]
/-
**ArithmeticFunction.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：coe_coe [AddGroupWithOne R] {f : ArithmeticFunction Nat} : ((f : Arithmeti
cFunction Int) : ArithmeticFunction R) = (f : ArithmeticFunction R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_coe [AddGroupWithOne R] {f : ArithmeticFunction ℕ} :
    ((f : ArithmeticFunction ℤ) : ArithmeticFunction R) = (f : ArithmeticFunction R) := by
  ext
  simp

@[simp]
/-
**ArithmeticFunction.natCoe_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：natCoe_one [AddMonoidWithOne R] : ((1 : ArithmeticFunction Nat) : Arithmet
icFunction R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCoe_one [AddMonoidWithOne R] :
    ((1 : ArithmeticFunction ℕ) : ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

@[simp]
/-
**ArithmeticFunction.intCoe_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction Int) : Arithmeti
cFunction R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_ite`：cast_ite [IntCast R] (P : Prop) [Decidable P] (m n : Int) 
: ((ite P m n : Int) : R) = ite P (m : R) (n : R)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCoe_one [AddGroupWithOne R] : ((1 : ArithmeticFunction ℤ) :
    ArithmeticFunction R) = 1 := by
  ext n
  simp [one_apply]

section AddMonoid

variable [AddMonoid R]

/-
**ArithmeticFunction.add** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
形式化陈述：add : Add (ArithmeticFunction R) where add f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add (ArithmeticFunction R) where
  add f g := ⟨f + g, by simp⟩

@[simp]
/-
**ArithmeticFunction.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：add_apply {f g : ArithmeticFunction R} {n : Nat} : (f + g) n = f n + g n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply {f g : ArithmeticFunction R} {n : ℕ} : (f + g) n = f n + g n :=
  rfl
/-
**ArithmeticFunction.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction
`。
形式化陈述：instAddMonoid : AddMonoid (ArithmeticFunction R) where add_assoc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid : AddMonoid (ArithmeticFunction R) where
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _
  nsmul := nsmulRec

end AddMonoid

set_option backward.isDefEq.respectTransparency false in
/-
**ArithmeticFunction.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticF
unction`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFu
nction R) where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ArithmeticFunction R) where
  natCast n := ⟨fun x ↦ if x = 1 then (n : R) else 0, by simp⟩
  natCast_zero := by ext; simp
  natCast_succ n := by ext x; by_cases h : x = 1 <;> simp [h]
/-
**ArithmeticFunction.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunc
tion`。
形式化陈述：instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R)
 where add_comm _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid R] : AddCommMonoid (ArithmeticFunction R) where
  add_comm _ _ := ext fun _ ↦ add_comm _ _
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NegZeroClass R] : Neg (ArithmeticFunction R) where
  neg f := ⟨-f, by simp⟩

@[simp]
/-
**ArithmeticFunction.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：neg_apply [NegZeroClass R] {f : ArithmeticFunction R} {n : Nat} : (-f) n =
 -f n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply [NegZeroClass R] {f : ArithmeticFunction R} {n : ℕ} : (-f) n = -f n := by
  rfl
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] : AddGroup (ArithmeticFunction R) where
  neg_add_cancel _ := ext fun _ ↦ neg_add_cancel _
  zsmul := zsmulRec
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] : AddCommGroup (ArithmeticFunction R) where
  add_comm := fun _ _ ↦ add_comm _ _

section SMul

variable {M : Type*} [Zero R] [AddCommMonoid M] [SMul R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirichlet convolution of two arithmetic functions `f` and `g` is another ari
thmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x 
* y = n`.
-/
instance : SMul (ArithmeticFunction R) (ArithmeticFunction M) where
  smul f g := ⟨fun n ↦ ∑ x ∈ divisorsAntidiagonal n, f x.fst • g x.snd, by simp⟩

@[simp]
/-
**ArithmeticFunction.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : Nat}
 : (f • g) n = ∑ x in divisorsAntidiagonal n, f x.fst • g x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply {f : ArithmeticFunction R} {g : ArithmeticFunction M} {n : ℕ} :
    (f • g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst • g x.snd :=
  rfl

end SMul

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dirichlet convolution of two arithmetic functions `f` and `g` is another ari
thmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x 
* y = n`.
-/
instance [Semiring R] : Mul (ArithmeticFunction R) where
  mul f g := f • g

@[simp]
/-
**ArithmeticFunction.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : Nat} : (f * g) n 
= ∑ x in divisorsAntidiagonal n, f x.fst * g x.snd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply [Semiring R] {f g : ArithmeticFunction R} {n : ℕ} :
    (f * g) n = ∑ x ∈ divisorsAntidiagonal n, f x.fst * g x.snd :=
  rfl
/-
**ArithmeticFunction.mul_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction
`。
形式化陈述：mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 
* g 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisorsAntidiagonal_one`：divisorsAntidiagonal_one : divisorsAntidia
gonal 1 = {(1, 1)}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_apply_one [Semiring R] {f g : ArithmeticFunction R} : (f * g) 1 = f 1 * g 1 := by simp

@[simp, norm_cast]
/-
**ArithmeticFunction.natCoe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：natCoe_mul [Semiring R] {f g : ArithmeticFunction Nat} : (↑(f * g) : Arith
meticFunction R) = f * g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCoe_mul [Semiring R] {f g : ArithmeticFunction ℕ} :
    (↑(f * g) : ArithmeticFunction R) = f * g := by
  ext n
  simp

@[simp, norm_cast]
/-
**ArithmeticFunction.intCoe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：intCoe_mul [Ring R] {f g : ArithmeticFunction Int} : (↑(f * g) : Arithmeti
cFunction R) = ↑f * g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCoe_mul [Ring R] {f g : ArithmeticFunction ℤ} :
    (↑(f * g) : ArithmeticFunction R) = ↑f * g := by
  ext n
  simp

section Module

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-
**ArithmeticFunction.mul_smul'** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) : (f * g
) • h = f • g • h
参数：f g : ArithmeticFunction R；h : ArithmeticFunction M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
-/
theorem mul_smul' (f g : ArithmeticFunction R) (h : ArithmeticFunction M) :
    (f * g) • h = f • g • h := by
  ext n
  simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, sum_sigma']
  apply sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l * j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i * k, l), (i, k)⟩) <;> aesop (add simp mul_assoc)

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArithmeticFunction.one_smul'** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b
参数：b : ArithmeticFunction M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ArithmeticFunction.one_apply_ne`：one_apply_ne {x : Nat} (h : x != 1) : (
1 : ArithmeticFunction R) x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem one_smul' (b : ArithmeticFunction M) : (1 : ArithmeticFunction R) • b = b := by
  ext x
  simp_all [← map_div_right_divisors, sum_eq_single 1]

end Module

section Semiring

variable [Semiring R]

set_option backward.isDefEq.respectTransparency.types false in
/-
**ArithmeticFunction.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
形式化陈述：instMonoid : Monoid (ArithmeticFunction R) where one_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (ArithmeticFunction R) where
  one_mul := one_smul'
  mul_one f := by
    ext x
    simp_all [← map_div_left_divisors, sum_eq_single 1]
  mul_assoc := mul_smul'
/-
**ArithmeticFunction.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`
。
形式化陈述：instSemiring : Semiring (ArithmeticFunction R) where zero_mul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring : Semiring (ArithmeticFunction R) where
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  left_distrib a b c := by ext; simp [← sum_add_distrib, mul_add]
  right_distrib a b c := by ext; simp [← sum_add_distrib, add_mul]

end Semiring

/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] : CommSemiring (ArithmeticFunction R) where
  mul_comm f g := by
    ext
    rw [mul_apply, ← map_swap_divisorsAntidiagonal, sum_map]
    simp [mul_comm]
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] : CommRing (ArithmeticFunction R) where
  neg_add_cancel := neg_add_cancel
  mul_comm := mul_comm
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S] :
    Module R (ArithmeticFunction S) where
  smul x f := ⟨x • f, by simp⟩
  smul_zero x := ext fun n ↦ smul_zero x
  smul_add x f g := ext fun n ↦ smul_add x (f n) (g n)
  zero_smul f := ext fun n ↦ zero_smul R (f n)
  one_smul f := ext fun n ↦ one_smul R (f n)
  add_smul x y f := ext fun n ↦ add_smul x y (f n)
  mul_smul x y f := ext fun n ↦ mul_smul x y (f n)

-- note that `smul_apply` would be a more suitable name, but is already in use for the action of
-- `ArithmeticFunction R` on `ArithmeticFunction S`
@[simp]
/-
**ArithmeticFunction.smul_map** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticFunction`。
形式化陈述：smul_map {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S] (x : R) (
f : ArithmeticFunction S) (n : Nat) : (x • f) n = x • f n
参数：x : R；f : ArithmeticFunction S；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_map {S : Type*} [Semiring R] [AddCommMonoid S] [Module R S]
    (x : R) (f : ArithmeticFunction S) (n : ℕ) : (x • f) n = x • f n := by
  rfl

-- We can deduce the `Algebra` structure from the `Module` structure here due to the lack of
-- a more natural definition of `algebraMap`.
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] :
    Algebra R (ArithmeticFunction S) :=
  .ofModule (fun x f g ↦ ext fun n ↦ by simp [Finset.smul_sum])
    fun x f g ↦ ext fun n ↦ by simp [Finset.smul_sum]

@[simp]
/-
**ArithmeticFunction.algebraMap_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：algebraMap_apply_one {S : Type*} [CommSemiring R] [Semiring S] [Algebra R 
S] (x : R) : algebraMap R (ArithmeticFunction S) x 1 = algebraMap R S x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `ArithmeticFunction.smul_map`：smul_map {S : Type*} [Semiring R] [AddCommM
onoid S] [Module R S] (x : R) (f : ArithmeticFunction S) (n : Nat) : (x • f) n =
 x • f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_apply_one {S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (x : R) :
    algebraMap R (ArithmeticFunction S) x 1 = algebraMap R S x := by
  simp [Algebra.algebraMap_eq_smul_one]
/-
**ArithmeticFunction.** 是 Mathlib 中的一个实例，位于命名空间 `ArithmeticFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (ArithmeticFunction R) (ArithmeticFunction M) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_add r x y := by
    ext
    simp only [sum_add_distrib, smul_add, smul_apply, add_apply]
  smul_zero r := by
    ext
    simp only [smul_apply, sum_const_zero, smul_zero, zero_apply]
  add_smul r s x := by
    ext
    simp only [add_smul, sum_add_distrib, smul_apply, add_apply]
  zero_smul r := by
    ext
    simp only [smul_apply, sum_const_zero, zero_smul, zero_apply]

section DirichletInverse

section Ring

/- We use `(hf : Invertible (f 1))` instead of `[hf : Invertible (f 1)]` because in practice such
an instance is unlikely to be automatically synthesized due to the presence of `f`. -/
variable [Ring R] (f : ℕ → R) (hf : Invertible (f 1))

/-- Given an inverse of `f 1`, construct the Dirichlet inverse of `f`. We use `Invertible` to make
this definition computable when `f` is computable. -/
/-
**ArithmeticFunction.dirichletInverseFun** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFu
nction`。
形式化陈述：dirichletInverseFun (n : Nat) : R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an inverse of `f 1`, construct the Dirichlet inverse of `f`. We use `Inver
tible` to make
this definition computable when `f` is computable.
-/
def dirichletInverseFun (n : ℕ) : R :=
  if n = 0 then 0
  else if n = 1 then ⅟(f 1)
  else - ⅟(f 1) * ∑ d : n.properDivisors,
    have : d < n := (Nat.mem_properDivisors.mp d.2).2
    f (n / d) * dirichletInverseFun d

@[simp]
/-
**ArithmeticFunction.dirichletInverseFun_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `A
rithmeticFunction`。
形式化陈述：dirichletInverseFun_apply_zero : dirichletInverseFun f hf 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.dirichletInverseFun.eq_1`：∀ {R : Type u_1} [inst : Ri
ng R] (f : ℕ → R) (hf : Invertible (f 1)) (n : ℕ),   ArithmeticFunction.dirichle
tInverseFun f hf n =     if n = 0…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem dirichletInverseFun_apply_zero : dirichletInverseFun f hf 0 = 0 := by
  rw [dirichletInverseFun, if_pos rfl]

@[simp]
/-
**ArithmeticFunction.dirichletInverseFun_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Ar
ithmeticFunction`。
形式化陈述：dirichletInverseFun_apply_one : dirichletInverseFun f hf 1 = ⅟(f 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.dirichletInverseFun.eq_1`：∀ {R : Type u_1} [inst : Ri
ng R] (f : ℕ → R) (hf : Invertible (f 1)) (n : ℕ),   ArithmeticFunction.dirichle
tInverseFun f hf n =     if n = 0…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem dirichletInverseFun_apply_one : dirichletInverseFun f hf 1 = ⅟(f 1) := by
  rw [dirichletInverseFun, if_neg one_ne_zero, if_pos rfl]

@[simp]
/-
**ArithmeticFunction.dirichletInverseFun_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Ari
thmeticFunction`。
形式化陈述：dirichletInverseFun_apply_ne {n : Nat} (hn0 : n != 0) (hn1 : n != 1) : dir
ichletInverseFun f hf n = - ⅟(f 1) * ∑ d in n.properDivisors, f (n / d) * dirich
letInverseFun f hf d
参数：hn0 : n != 0；hn1 : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.dirichletInverseFun.eq_1`：∀ {R : Type u_1} [inst : Ri
ng R] (f : ℕ → R) (hf : Invertible (f 1)) (n : ℕ),   ArithmeticFunction.dirichle
tInverseFun f hf n =     if n = 0…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
-/
theorem dirichletInverseFun_apply_ne {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    dirichletInverseFun f hf n =
      - ⅟(f 1) * ∑ d ∈ n.properDivisors, f (n / d) * dirichletInverseFun f hf d := by
  rw [dirichletInverseFun, if_neg hn0, if_neg hn1]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- Given an inverse of `f 1`, construct the Dirichlet inverse of `f`. -/
@[simp]
/-
**ArithmeticFunction.dirichletInverse** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：dirichletInverse : ArithmeticFunction R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.dirichletInverseFun_apply_zero`：dirichletInverseFun_a
pply_zero : dirichletInverseFun f hf 0 = 0

--- 原说明 ---
Given an inverse of `f 1`, construct the Dirichlet inverse of `f`.
-/
def dirichletInverse : ArithmeticFunction R :=
  ⟨dirichletInverseFun f hf, dirichletInverseFun_apply_zero f hf⟩

set_option backward.isDefEq.respectTransparency false in
/-
**ArithmeticFunction.self_mul_dirichletInverse** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：self_mul_dirichletInverse (f : ArithmeticFunction R) (hf : Invertible (f 1
)) : f * dirichletInverse f hf = 1
参数：f : ArithmeticFunction R；hf : Invertible (f 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.dirichletInverseFun_apply_zero`：dirichletInverseFun_a
pply_zero : dirichletInverseFun f hf 0 = 0
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisorsAntidiagonal_one`：divisorsAntidiagonal_one : divisorsAntidia
gonal 1 = {(1, 1)}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ArithmeticFunction.dirichletInverseFun_apply_one`：dirichletInverseFun_ap
ply_one : dirichletInverseFun f hf 1 = ⅟(f 1)
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `ArithmeticFunction.dirichletInverse.eq_1`：∀ {R : Type u_1} [inst : Ring 
R] (f : ℕ → R) (hf : Invertible (f 1)),   ArithmeticFunction.dirichletInverse f 
hf = { toFun := ArithmeticFunc…
· 使用定理 `ArithmeticFunction.mul_apply`：mul_apply [Semiring R] {f g : ArithmeticFu
nction R} {n : Nat} : (f * g) n = ∑ x in divisorsAntidiagonal n, f x.fst * g x.s
nd
· 使用定理 `ArithmeticFunction.coe_mk`：coe_mk (f : Nat -> R) (hf) : @DFunLike.coe (A
rithmeticFunction R) _ _ _ (ZeroHom.mk f hf) = f
· 使用定理 `Nat.sum_divisorsAntidiagonal'`：∀ {M : Type u_1} [inst : AddCommMonoid M]
 (f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.di
visors, f (n / i) i
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ArithmeticFunction.dirichletInverseFun_apply_ne`：dirichletInverseFun_app
ly_ne {n : Nat} (hn0 : n != 0) (hn1 : n != 1) : dirichletInverseFun f hf n = - ⅟
(f 1) * ∑ d in n.properDivisors, f (n…
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
（共 34 条，此处仅展示前 30 条）
-/
theorem self_mul_dirichletInverse (f : ArithmeticFunction R) (hf : Invertible (f 1)) :
    f * dirichletInverse f hf = 1 := by
  ext n
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  rw [dirichletInverse, mul_apply, coe_mk,
    Nat.sum_divisorsAntidiagonal' fun x y ↦ f x * dirichletInverseFun f hf y,
    ← Nat.cons_self_properDivisors hn0]
  simp [hn0, hn1, pos_of_ne_zero]

end Ring

section CommRing

variable [CommRing R] (f : ArithmeticFunction R)

/-
**ArithmeticFunction.dirichletInverse_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction`。
形式化陈述：dirichletInverse_mul_self (hf : Invertible (f 1)) : dirichletInverse f hf 
* f = 1
参数：hf : Invertible (f 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ArithmeticFunction.self_mul_dirichletInverse`：self_mul_dirichletInverse 
(f : ArithmeticFunction R) (hf : Invertible (f 1)) : f * dirichletInverse f hf =
 1
-/
theorem dirichletInverse_mul_self (hf : Invertible (f 1)) : dirichletInverse f hf * f = 1 := by
  rw [mul_comm, self_mul_dirichletInverse]

variable {f} in
/-
**ArithmeticFunction.isUnit_iff_isUnit_apply_one** 是 Mathlib 中的一个定理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：isUnit_iff_isUnit_apply_one : IsUnit f ↔ IsUnit (f 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.mul_apply_one`：mul_apply_one [Semiring R] {f g : Arit
hmeticFunction R} : (f * g) 1 = f 1 * g 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `ArithmeticFunction.one_one`：one_one : (1 : ArithmeticFunction R) 1 = 1
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `ArithmeticFunction.dirichletInverse_mul_self`：dirichletInverse_mul_self 
(hf : Invertible (f 1)) : dirichletInverse f hf * f = 1
· 使用定理 `ArithmeticFunction.self_mul_dirichletInverse`：self_mul_dirichletInverse 
(f : ArithmeticFunction R) (hf : Invertible (f 1)) : f * dirichletInverse f hf =
 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem isUnit_iff_isUnit_apply_one : IsUnit f ↔ IsUnit (f 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.val 1, f⁻¹.val 1, ?_, ?_⟩, rfl⟩
    · rw [← ArithmeticFunction.mul_apply_one, Units.mul_inv, one_one]
    · rw [← ArithmeticFunction.mul_apply_one, Units.inv_mul, one_one]
  · suffices Invertible (f 1) → Invertible f by simpa using Nonempty.map this
    exact fun hf ↦ ⟨_, dirichletInverse_mul_self f hf, self_mul_dirichletInverse f hf⟩

end CommRing

end DirichletInverse

/-- Multiplicative functions -/
/-
**ArithmeticFunction.IsMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunct
ion`。
形式化陈述：IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop
参数：f : ArithmeticFunction R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative functions
-/
def IsMultiplicative [MonoidWithZero R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n

namespace IsMultiplicative

section MonoidWithZero

variable [MonoidWithZero R]

@[simp, arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction.IsMultiplicative`。
形式化陈述：map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1
参数：h : f.IsMultiplicative。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem map_one {f : ArithmeticFunction R} (h : f.IsMultiplicative) : f 1 = 1 :=
  h.1

@[simp]
/-
**ArithmeticFunction.IsMultiplicative.map_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名
空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m
 n : Nat} (h : m.gcd n = 1) : f (m * n) = f m * f n
参数：hf : f.IsMultiplicative；h : m.gcd n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_mul_of_coprime {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : ℕ}
    (h : m.gcd n = 1) : f (m * n) = f m * f n :=
  hf.2 h

end MonoidWithZero

open scoped Function in -- required for scoped `on` notation
/-
**ArithmeticFunction.IsMultiplicative.map_prod** 是 Mathlib 中的一个定理，位于命名空间 `Arithm
eticFunction.IsMultiplicative`。
形式化陈述：map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι -> Nat) {f : Arithmetic
Function R} (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise 
(Coprime on g)) : f (∏ i in s, g i) = ∏ i in s, f (g i)
参数：g : ι -> Nat；hf : f.IsMultiplicative；s : Finset ι；hs : (s : Set ι).Pairwise (
Coprime on g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `Nat.Coprime.prod_right`：∀ {ι : Type u_1} {x : ℕ} {t : Finset ι} {s : ι →
 ℕ}, (∀ i ∈ t, x.Coprime (s i)) → x.Coprime (∏ i ∈ t, s i)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.pairwise_insert_of_symm`：pairwise_insert_of_symm [Std.Symm r] : (ins
ert a s).Pairwise r ↔ s.Pairwise r ∧ forall b in s, a != b -> r a b
· 使用定理 `Nat.Coprime.stdSymm`：Std.Symm Nat.Coprime
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Membership.mem.ne_of_notMem`：∀ {α : Type u_1} {β : Type u_2} [inst : Mem
bership α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem map_prod {ι : Type*} [CommMonoidWithZero R] (g : ι → ℕ) {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (s : Finset ι) (hs : (s : Set ι).Pairwise (Coprime on g)) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  classical
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert _ _ has ih =>
      rw [coe_insert, Set.pairwise_insert_of_symm] at hs
      rw [prod_insert has, prod_insert has, hf.map_mul_of_coprime, ih hs.1]
      exact Coprime.prod_right fun i hi => hs.2 _ hi (hi.ne_of_notMem has).symm
/-
**ArithmeticFunction.IsMultiplicative.map_prod_of_prime** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：map_prod_of_prime [CommMonoidWithZero R] {f : ArithmeticFunction R} (h_mul
t : ArithmeticFunction.IsMultiplicative f) (t : Finset Nat) (ht : forall p in t,
 p.Prime) : f (∏ a in t, a) = ∏ a in t, f a
参数：h_mult : ArithmeticFunction.IsMultiplicative f；t : Finset Nat；ht : forall p i
n t, p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_prod`：map_prod {ι : Type*} [Comm
MonoidWithZero R] (g : ι -> Nat) {f : ArithmeticFunction R} (hf : f.IsMultiplica
tive) (s : Finset ι) (hs : (s : Se…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
-/
theorem map_prod_of_prime [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f)
    (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod _ h_mult t fun x hx y hy hxy => (coprime_primes (ht x hx) (ht y hy)).mpr hxy
/-
**ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors** 是 Mathli
b 中的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：map_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunc
tion R} (h_mult : ArithmeticFunction.IsMultiplicative f) (l : Nat) (t : Finset N
at) (ht : t subseteq l.primeFactors) : f (∏ a in t, a) = ∏ a in t, f a
参数：h_mult : ArithmeticFunction.IsMultiplicative f；l : Nat；t : Finset Nat；ht : t 
subseteq l.primeFactors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_prod_of_prime`：map_prod_of_prime
 [CommMonoidWithZero R] {f : ArithmeticFunction R} (h_mult : ArithmeticFunction.
IsMultiplicative f) (t : Finset Nat) (ht : …
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
-/
theorem map_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : ArithmeticFunction.IsMultiplicative f) (l : ℕ)
    (t : Finset ℕ) (ht : t ⊆ l.primeFactors) :
    f (∏ a ∈ t, a) = ∏ a ∈ t, f a :=
  map_prod_of_prime h_mult t fun _ a => prime_of_mem_primeFactors (ht a)
/-
**ArithmeticFunction.IsMultiplicative.prod_primeFactors** 是 Mathlib 中的一个定理，位于命名空
间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：prod_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R} (h_mul
t : f.IsMultiplicative) {l : Nat} (hl : Squarefree l) : ∏ a in l.primeFactors, f
 a = f l
参数：h_mult : f.IsMultiplicative；hl : Squarefree l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors`：map
_prod_of_subset_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R} (
h_mult : ArithmeticFunction.IsMultiplicative f) (l : Nat)…
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
-/
theorem prod_primeFactors [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (h_mult : f.IsMultiplicative) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [← h_mult.map_prod_of_subset_primeFactors l _ Subset.rfl,
    prod_primeFactors_of_squarefree hl]
/-
**ArithmeticFunction.IsMultiplicative.map_div_of_coprime** 是 Mathlib 中的一个定理，位于命名
空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：map_div_of_coprime [GroupWithZero R] {f : ArithmeticFunction R} (hf : IsMu
ltiplicative f) {l d : Nat} (hdl : d ∣ l) (hl : (l / d).Coprime d) (hd : f d != 
0) : f (l / d) = f l / f d
参数：hf : IsMultiplicative f；hdl : d ∣ l；hl : (l / d).Coprime d；hd : f d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_of_eq_mul`：div_eq_of_eq_mul (hb : b != 0) : a = c * b -> a / b = 
c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
-/
theorem map_div_of_coprime [GroupWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {l d : ℕ} (hdl : d ∣ l) (hl : (l / d).Coprime d) (hd : f d ≠ 0) :
    f (l / d) = f l / f d := by
  apply (div_eq_of_eq_mul hd ..).symm
  rw [← hf.right hl, Nat.div_mul_cancel hdl]

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.natCast** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction.IsMultiplicative`。
形式化陈述：natCast {f : ArithmeticFunction Nat} [Semiring R] (h : f.IsMultiplicative)
 : IsMultiplicative (f : ArithmeticFunction R)
参数：h : f.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
-/
theorem natCast {f : ArithmeticFunction ℕ} [Semiring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.intCast** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction.IsMultiplicative`。
形式化陈述：intCast {f : ArithmeticFunction Int} [Ring R] (h : f.IsMultiplicative) : I
sMultiplicative (f : ArithmeticFunction R)
参数：h : f.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_one`：map_one {f : ArithmeticFunc
tion R} (h : f.IsMultiplicative) : f 1 = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
-/
theorem intCast {f : ArithmeticFunction ℤ} [Ring R] (h : f.IsMultiplicative) :
    IsMultiplicative (f : ArithmeticFunction R) :=
  ⟨by simp [h], fun cop => by simp [h.2 cop]⟩

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.mul** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction.IsMultiplicative`。
形式化陈述：mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative
) (hg : g.IsMultiplicative) : IsMultiplicative (f * g)
参数：hf : f.IsMultiplicative；hg : g.IsMultiplicative。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisorsAntidiagonal_one`：divisorsAntidiagonal_one : divisorsAntidia
gonal 1 = {(1, 1)}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [ins
t : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x ∈ s ×ˢ
 t, f x.1…
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `Nat.mul_eq_zero`：∀ {m n : ℕ}, n * m = 0 ↔ n = 0 ∨ m = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
（共 56 条，此处仅展示前 30 条）
-/
theorem mul [CommSemiring R] {f g : ArithmeticFunction R} (hf : f.IsMultiplicative)
    (hg : g.IsMultiplicative) : IsMultiplicative (f * g) := by
  refine ⟨by simp [hf.1, hg.1], ?_⟩
  simp only [mul_apply]
  intro m n cop
  rw [sum_mul_sum, ← sum_product']
  symm
  apply sum_nbij fun ((i, j), k, l) ↦ (i * k, j * l)
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h
    simp only [mem_divisorsAntidiagonal, Ne, mem_product] at h
    rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    simp only [mem_divisorsAntidiagonal, mul_eq_zero, Ne]
    constructor
    · ring
    rw [mul_eq_zero] at *
    exact not_or_intro ha hb
  · simp only [Set.InjOn, mem_coe, mem_divisorsAntidiagonal, mem_product, Prod.mk_inj]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hcd h
    ext
    · trans gcd (a1 * a2) (a1 * b1)
      · rw [gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.1, gcd_mul_left, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one,
          mul_one]
    · trans gcd (a1 * a2) (a2 * b2)
      · rw [mul_comm, gcd_mul_left, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
          mul_one]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.1.1, h.2, mul_comm, gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_one]
    · trans gcd (b1 * b2) (a1 * b1)
      · rw [mul_comm, gcd_mul_right, cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one,
          one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.1, mul_comm c1 d1, gcd_mul_left,
          cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_one]
    · trans gcd (b1 * b2) (a2 * b2)
      · rw [gcd_mul_right, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
      · rw [← hcd.1.1, ← hcd.2.1] at cop
        rw [← hcd.2.1, h.2, gcd_mul_right,
          cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mul]
  · simp only [Set.SurjOn, Set.subset_def, mem_coe, mem_divisorsAntidiagonal, mem_product,
      Set.mem_image]
    rintro ⟨b1, b2⟩ h
    use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
    rw [← cop.gcd_mul _, ← cop.gcd_mul _, ← h.1, gcd_mul_gcd_of_coprime_of_mul_eq_mul cop h.1,
      gcd_mul_gcd_of_coprime_of_mul_eq_mul cop.symm _]
    · rw [Ne, mul_eq_zero, not_or] at h
      simp [h.2.1, h.2.2]
    rw [mul_comm n m, h.1]
  · simp only [mem_divisorsAntidiagonal, mem_product]
    rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
    rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
      hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
    ring

/-- For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
/-
**ArithmeticFunction.IsMultiplicative.multiplicative_factorization** 是 Mathlib 中
的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunctio
n R) (hf : f.IsMultiplicative) {n : Nat} (hn : n != 0) : f n = n.factorization.p
rod fun p k => f (p ^ k)
参数：f : ArithmeticFunction R；hf : f.IsMultiplicative；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.multiplicative_factorization`：multiplicative_factorization {β : Type
*} [CommMonoid β] (f : Nat -> β) (h_mult : forall x y : Nat, Coprime x y -> f (x
 * y) = f x * f y) (hf…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
For any multiplicative function `f` and any `n > 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n`
-/
theorem multiplicative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    f n = n.factorization.prod fun p k => f (p ^ k) :=
  Nat.multiplicative_factorization f (fun _ _ => hf.2) hf.1 hn

/-- A recapitulation of the definition of multiplicative that is simpler for proofs -/
/-
**ArithmeticFunction.IsMultiplicative.iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ari
thmeticFunction.IsMultiplicative`。
形式化陈述：iff_ne_zero [MonoidWithZero R] {f : ArithmeticFunction R} : IsMultiplicati
ve f ↔ f 1 = 1 ∧ forall {m n : Nat}, m != 0 -> n != 0 -> m.Coprime n -> f (m * n
) = f m * f n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
A recapitulation of the definition of multiplicative that is simpler for proofs
-/
theorem iff_ne_zero [MonoidWithZero R] {f : ArithmeticFunction R} :
    IsMultiplicative f ↔
      f 1 = 1 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n := by
  refine and_congr_right' (forall₂_congr fun m n => ⟨fun h _ _ => h, fun h hmn => ?_⟩)
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  exact h hm hn hmn

/-- Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers -/
/-
**ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers** 是 Mathlib 中的一个
定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R
) (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative)
 : f = g ↔ forall p i : Nat, Nat.Prime p -> f (p ^ i) = g (p ^ i)
参数：f : ArithmeticFunction R；hf : f.IsMultiplicative；g : ArithmeticFunction R；hg 
: g.IsMultiplicative。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ArithmeticFunction.ext`：ext ⦃f g : ArithmeticFunction R⦄ (h : forall x, 
f x = g x) : f = g
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`：multip
licative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R) (hf : f
.IsMultiplicative) {n : Nat} (hn : n != 0) : f n = n.f…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime

--- 原说明 ---
Two multiplicative functions `f` and `g` are equal if and only if
they agree on prime powers
-/
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : ℕ, Nat.Prime p → f (p ^ i) = g (p ^ i) := by
  constructor <;> intro h
  · simp [h]
  ext n
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  rw [multiplicative_factorization f hf hn, multiplicative_factorization g hg hn]
  exact prod_congr rfl fun p hp ↦ h p _ (prime_of_mem_primeFactors hp)
/-
**ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply** 是 Mathlib 中的一个定理
，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R} 
(hf : f.IsMultiplicative) {x y : Nat} : f (x.lcm y) * f (x.gcd y) = f x * f y
参数：hf : f.IsMultiplicative。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.lcm_zero_left`：∀ (m : ℕ), Nat.lcm 0 m = 0
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lcm_zero_right`：∀ (m : ℕ), m.lcm 0 = 0
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.gcd_ne_zero_left`：∀ {m n : ℕ}, m ≠ 0 → m.gcd n ≠ 0
· 使用定理 `Nat.lcm_ne_zero`：∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.lcm n ≠ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`：multip
licative_factorization [CommMonoidWithZero R] (f : ArithmeticFunction R) (hf : f
.IsMultiplicative) {n : Nat} (hn : n != 0) : f n = n.f…
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `Nat.factorization_lcm`：factorization_lcm {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a.lcm b).factorization = a.factorization ⊔ b.factorization
· 使用定理 `Finsupp.support_sup`：support_sup [DecidableEq ι] (f g : ι ->₀ α) : (f ⊔ 
g).support = f.support union g.support
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.factorization_gcd`：factorization_gcd {a b : Nat} (ha_pos : a != 0) (
hb_pos : b != 0) : (gcd a b).factorization = a.factorization ⊓ b.factorization
· 使用定理 `Finsupp.support_inf`：support_inf [DecidableEq ι] (f g : ι ->₀ α) : (f ⊓ 
g).support = f.support inter g.support
· 使用定理 `Finset.inter_subset_union`：inter_subset_union : s inter t subseteq s uni
on t
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
（共 35 条，此处仅展示前 30 条）
-/
theorem lcm_apply_mul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} :
    f (x.lcm y) * f (x.gcd y) = f x * f y := by
  by_cases hx : x = 0
  · simp only [hx, f.map_zero, zero_mul, lcm_zero_left, gcd_zero_left]
  by_cases hy : y = 0
  · simp only [hy, f.map_zero, mul_zero, lcm_zero_right, gcd_zero_right, zero_mul]
  have hgcd_ne_zero : x.gcd y ≠ 0 := gcd_ne_zero_left hx
  have hlcm_ne_zero : x.lcm y ≠ 0 := lcm_ne_zero hx hy
  have hfi_zero : ∀ {i}, f (i ^ 0) = 1 := by
    intro i; rw [pow_zero, hf.1]
  iterate 4 rw [hf.multiplicative_factorization f (by assumption),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ => hfi_zero)
      (s := (x.primeFactors ∪ y.primeFactors))]
  · rw [← prod_mul_distrib, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p _
    rcases Nat.le_or_le (x.factorization p) (y.factorization p) with h | h <;>
      simp only [factorization_lcm hx hy, Finsupp.sup_apply, h, sup_of_le_right,
        sup_of_le_left, inf_of_le_right, factorization_gcd hx hy, Finsupp.inf_apply,
        inf_of_le_left, mul_comm]
  · apply subset_union_right
  · apply subset_union_left
  · rw [factorization_gcd hx hy, Finsupp.support_inf]
    apply inter_subset_union
  · simp [factorization_lcm hx hy]
/-
**ArithmeticFunction.IsMultiplicative.map_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction.IsMultiplicative`。
形式化陈述：map_gcd [CommGroupWithZero R] {f : ArithmeticFunction R} (hf : f.IsMultipl
icative) {x y : Nat} (hf_lcm : f (x.lcm y) != 0) : f (x.gcd y) = f x * f y / f (
x.lcm y)
参数：hf : f.IsMultiplicative；hf_lcm : f (x.lcm y) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply`：lcm_apply_m
ul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R} (hf : f.IsMultipl
icative) {x y : Nat} : f (x.lcm y) * f (x.gcd y) …
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
theorem map_gcd [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} (hf_lcm : f (x.lcm y) ≠ 0) :
    f (x.gcd y) = f x * f y / f (x.lcm y) := by
  rw [← hf.lcm_apply_mul_gcd_apply, mul_div_cancel_left₀ _ hf_lcm]
/-
**ArithmeticFunction.IsMultiplicative.map_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Arithme
ticFunction.IsMultiplicative`。
形式化陈述：map_lcm [CommGroupWithZero R] {f : ArithmeticFunction R} (hf : f.IsMultipl
icative) {x y : Nat} (hf_gcd : f (x.gcd y) != 0) : f (x.lcm y) = f x * f y / f (
x.gcd y)
参数：hf : f.IsMultiplicative；hf_gcd : f (x.gcd y) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply`：lcm_apply_m
ul_gcd_apply [CommMonoidWithZero R] {f : ArithmeticFunction R} (hf : f.IsMultipl
icative) {x y : Nat} : f (x.lcm y) * f (x.gcd y) …
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
theorem map_lcm [CommGroupWithZero R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {x y : ℕ} (hf_gcd : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [← hf.lcm_apply_mul_gcd_apply, mul_div_cancel_right₀ _ hf_gcd]
/-
**ArithmeticFunction.IsMultiplicative.eq_zero_of_squarefree_of_dvd_eq_zero** 是 M
athlib 中的一个定理，位于命名空间 `ArithmeticFunction.IsMultiplicative`。
形式化陈述：eq_zero_of_squarefree_of_dvd_eq_zero [MonoidWithZero R] {f : ArithmeticFun
ction R} (hf : IsMultiplicative f) {m n : Nat} (hn : Squarefree n) (hmn : m ∣ n)
 (h_zero : f m = 0) : f n = 0
参数：hf : IsMultiplicative f；hn : Squarefree n；hmn : m ∣ n；h_zero : f m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime`：map_mul_of_copri
me {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {m n : Nat} (h : m.gcd n
 = 1) : f (m * n) = f m * f n
· 使用定理 `Nat.coprime_of_squarefree_mul`：coprime_of_squarefree_mul {m n : Nat} (h 
: Squarefree (m * n)) : m.Coprime n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_zero_of_squarefree_of_dvd_eq_zero [MonoidWithZero R] {f : ArithmeticFunction R}
    (hf : IsMultiplicative f) {m n : ℕ} (hn : Squarefree n) (hmn : m ∣ n)
    (h_zero : f m = 0) :
    f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [zero_mul, hf.map_mul_of_coprime (coprime_of_squarefree_mul hn), h_zero]

end IsMultiplicative

@[simp, arith_mult]
/-
**ArithmeticFunction.isMultiplicative_one** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction`。
形式化陈述：isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : Arithmetic
Function R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.IsMultiplicative.iff_ne_zero`：iff_ne_zero [MonoidWith
Zero R] {f : ArithmeticFunction R} : IsMultiplicative f ↔ f 1 = 1 ∧ forall {m n 
: Nat}, m != 0 -> n != 0 -> m.Coprime…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArithmeticFunction.one_apply_ne`：one_apply_ne {x : Nat} (h : x != 1) : (
1 : ArithmeticFunction R) x = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem isMultiplicative_one [MonoidWithZero R] : IsMultiplicative (1 : ArithmeticFunction R) :=
  IsMultiplicative.iff_ne_zero.2 ⟨by simp, by
    intro m n hm hn hmn
    by_cases h : m = 1 <;> aesop⟩

@[arith_mult]
/-
**ArithmeticFunction.isMultiplicative_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Arit
hmeticFunction`。
形式化陈述：isMultiplicative_finsetProd [CommSemiring R] {ι : Type*} (f : ι -> Arithme
ticFunction R) (s : Finset ι) (hf : forall i in s, IsMultiplicative (f i)) : IsM
ultiplicative (∏ i in s, f i)
参数：f : ι -> ArithmeticFunction R；s : Finset ι；hf : forall i in s, IsMultiplicati
ve (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `ArithmeticFunction.IsMultiplicative.mul`：mul [CommSemiring R] {f g : Ari
thmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMulti
plicative (f * g)
-/
theorem isMultiplicative_finsetProd [CommSemiring R] {ι : Type*}
    (f : ι → ArithmeticFunction R) (s : Finset ι) (hf : ∀ i ∈ s, IsMultiplicative (f i)) :
    IsMultiplicative (∏ i ∈ s, f i) := by
  induction s using Finset.cons_induction
  case empty => simp
  case cons a s ha ih =>
    rw [Finset.prod_cons]
    exact (hf a (by grind)).mul (by grind)

@[arith_mult]
/-
**ArithmeticFunction.IsMultiplicative.pow** 是 Mathlib 中的一个定理，位于命名空间 `ArithmeticF
unction.IsMultiplicative`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : ArithmeticFunction R},   f.I
sMultiplicative → ∀ {k : ℕ}, (f ^ k).IsMultiplicative
参数：f ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `ArithmeticFunction.IsMultiplicative.mul`：mul [CommSemiring R] {f g : Ari
thmeticFunction R} (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) : IsMulti
plicative (f * g)
-/
theorem IsMultiplicative.pow [CommSemiring R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) {k : ℕ} : IsMultiplicative (f ^ k) := by
  induction k
  case zero => simp
  case succ k hk =>
    rw [pow_succ]
    exact hk.mul hf

end ArithmeticFunction

