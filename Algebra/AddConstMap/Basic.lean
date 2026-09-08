/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Basic

/-!
# Maps (semi)conjugating a shift to a shift

Denote by $S^1$ the unit circle `UnitAddCircle`.
A common way to study a self-map $f\colon S^1\to S^1$ of degree `1`
is to lift it to a map $\tilde f\colon \mathbb R\to \mathbb R$
such that $\tilde f(x + 1) = \tilde f(x)+1$ for all `x`.

In this file we define a structure and a typeclass
for bundled maps satisfying `f (x + a) = f x + b`.

We use parameters `a` and `b` instead of `1` to accommodate for two use cases:

- maps between circles of different lengths;
- self-maps $f\colon S^1\to S^1$ of degree other than one,
  including orientation-reversing maps.
-/

@[expose] public section

assert_not_exists Finset

open Function Set

/-- A bundled map `f : G → H` such that `f (x + a) = f x + b` for all `x`,
denoted as `f : G →+c[a, b] H`.

One can think about `f` as a lift to `G` of a map between two `AddCircle`s. -/
/-
**AddConstMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u_1) → (H : Type u_2) → [Add G] → [Add H] → G → H → Type (max u_
1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled map `f : G → H` such that `f (x + a) = f x + b` for all `x`,
denoted as `f : G →+c[a, b] H`.

One can think about `f` as a lift to `G` of a map between two `AddCircle`s.
-/
structure AddConstMap (G H : Type*) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G → H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead. -/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b

@[inherit_doc]
scoped[AddConstMap] notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b

/-- Typeclass for maps satisfying `f (x + a) = f x + b`.

Note that `a` and `b` are `outParam`s,
so one should not add instances like
`[AddConstMapClass F G H a b] : AddConstMapClass F G H (-a) (-b)`. -/
/-
**AddConstMapClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (G : outParam (Type u_2)) →     (H : outParam (Type u_3
)) → [Add G] → [Add H] → outParam G → outParam H → [FunLike F G H] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for maps satisfying `f (x + a) = f x + b`.

Note that `a` and `b` are `outParam`s,
so one should not add instances like
`[AddConstMapClass F G H a b] : AddConstMapClass F G H (-a) (-b)`.
-/
class AddConstMapClass (F : Type*) (G H : outParam Type*) [Add G] [Add H]
    (a : outParam G) (b : outParam H) [FunLike F G H] : Prop where
  /-- A map of `AddConstMapClass` class semiconjugates shift by `a` to the shift by `b`:
  `∀ x, f (x + a) = f x + b`. -/
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

namespace AddConstMapClass

/-!
### Properties of `AddConstMapClass` maps

In this section we prove properties like `f (x + n • a) = f x + n • b`.
-/

scoped[AddConstMapClass] attribute [simp] map_add_const

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

/-
**AddConstMapClass.semiconj** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：∀ {F : Type u_1} {G : Type u_2} {H : Type u_3} [inst : FunLike F G H] {a :
 G} {b : H} [inst_1 : Add G] [inst_2 : Add H]   [AddConstMapClass F G H a b] (f 
: F), Function.Semiconj (⇑f) (fun x => x + a) fun x => x + b
参数：f : F；⇑f；fun x => x + a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_add_const`：∀ {F : Type u_1} {G : outParam (Type u_2
)} {H : outParam (Type u_3)} {inst : Add G} {inst_1 : Add H} {a : outParam G}   
{b : outParam H} {in…
-/
protected theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) :=
  map_add_const f

@[scoped simp]
/-
**AddConstMapClass.map_add_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b] (f 
: F) (x : G) (n : Nat) : f (x + n • a) = f x + n • b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `Function.Semiconj.iterate_right`：iterate_right {f : α -> β} {ga : α -> α
} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
· 使用定理 `AddConstMapClass.semiconj`：∀ {F : Type u_1} {G : Type u_2} {H : Type u_3
} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : Add G] [inst_2 : Add H]   [Ad
dConstMapClass …
-/
theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

@[scoped simp]
/-
**AddConstMapClass.map_add_nat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 
b] (f : F) (x : G) (n : Nat) : f (x + n) = f x + n • b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by simp [← map_add_nsmul]
/-
**AddConstMapClass.map_add_one** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b] (f :
 F) (x : G) : f (x + 1) = f x + b
参数：f : F；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_add_const`：∀ {F : Type u_1} {G : outParam (Type u_2
)} {H : outParam (Type u_3)} {inst : Add G} {inst_1 : Add H} {a : outParam G}   
{b : outParam H} {in…
-/
theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := map_add_const f x

@[scoped simp]
/-
**AddConstMapClass.map_add_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 
1 b] (f : F) (x : G) (n : Nat) [n.AtLeastTwo] : f (x + ofNat(n)) = f x + (ofNat(
n) : Nat) • b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_add_nat'`：map_add_nat' [AddMonoidWithOne G] [AddMon
oid H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Nat) : f (x + n) = f x 
+ n • b
-/
theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : ℕ) • b :=
  map_add_nat' f x n
/-
**AddConstMapClass.map_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F 
G H 1 1] (f : F) (x : G) (n : Nat) : f (x + n) = f x + n
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_add_nat'`：map_add_nat' [AddMonoidWithOne G] [AddMon
oid H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Nat) : f (x + n) = f x 
+ n • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n := by simp
/-
**AddConstMapClass.map_add_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass 
F G H 1 1] (f : F) (x : G) (n : Nat) [n.AtLeastTwo] : f (x + ofNat(n)) = f x + o
fNat(n)
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_add_nat`：map_add_nat [AddMonoidWithOne G] [AddMonoi
dWithOne H] [AddConstMapClass F G H 1 1] (f : F) (x : G) (n : Nat) : f (x + n) =
 f x + n
-/
theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + ofNat(n) := map_add_nat f x n

@[scoped simp]
/-
**AddConstMapClass.map_const** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) : 
f a = f 0 + b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddConstMapClass.map_add_const`：∀ {F : Type u_1} {G : outParam (Type u_2
)} {H : outParam (Type u_3)} {inst : Add G} {inst_1 : Add H} {a : outParam G}   
{b : outParam H} {in…
-/
theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  simpa using map_add_const f 0
/-
**AddConstMapClass.map_one** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f :
 F) : f 1 = f 0 + b
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_const`：map_const [AddZeroClass G] [Add H] [AddConst
MapClass F G H a b] (f : F) : f a = f 0 + b
-/
theorem map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F) :
    f 1 = f 0 + b :=
  map_const f

@[scoped simp]
/-
**AddConstMapClass.map_nsmul_const** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b] (
f : F) (n : Nat) : f (n • a) = f 0 + n • b
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddConstMapClass.map_add_nsmul`：map_add_nsmul [AddMonoid G] [AddMonoid H
] [AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x + n • a) = f x +
 n • b
-/
theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_nsmul f 0 n

@[scoped simp]
/-
**AddConstMapClass.map_nat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b] (
f : F) (n : Nat) : f n = f 0 + n • b
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddConstMapClass.map_add_nat'`：map_add_nat' [AddMonoidWithOne G] [AddMon
oid H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Nat) : f (x + n) = f x 
+ n • b
-/
theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) : f n = f 0 + n • b := by
  simpa using map_add_nat' f 0 n
/-
**AddConstMapClass.map_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
 (f : F) (n : Nat) [n.AtLeastTwo] : f (ofNat(n)) = f 0 + (ofNat(n) : Nat) • b
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_nat'`：map_nat' [AddMonoidWithOne G] [AddMonoid H] [
AddConstMapClass F G H 1 b] (f : F) (n : Nat) : f n = f 0 + n • b
-/
theorem map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f (ofNat(n)) = f 0 + (ofNat(n) : ℕ) • b :=
  map_nat' f n
/-
**AddConstMapClass.map_nat** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 
1 1] (f : F) (n : Nat) : f n = f 0 + n
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_nat'`：map_nat' [AddMonoidWithOne G] [AddMonoid H] [
AddConstMapClass F G H 1 b] (f : F) (n : Nat) : f n = f 0 + n • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by simp
/-
**AddConstMapClass.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G 
H 1 1] (f : F) (n : Nat) [n.AtLeastTwo] : f ofNat(n) = f 0 + ofNat(n)
参数：f : F；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_nat`：map_nat [AddMonoidWithOne G] [AddMonoidWithOne
 H] [AddConstMapClass F G H 1 1] (f : F) (n : Nat) : f n = f 0 + n
-/
theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := map_nat f n

@[scoped simp]
/-
**AddConstMapClass.map_const_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_const_add [AddCommMagma G] [Add H] [AddConstMapClass F G H a b] (f : F
) (x : G) : f (a + x) = f x + b
参数：f : F；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddConstMapClass.map_add_const`：∀ {F : Type u_1} {G : outParam (Type u_2
)} {H : outParam (Type u_3)} {inst : Add G} {inst_1 : Add H} {a : outParam G}   
{b : outParam H} {in…
-/
theorem map_const_add [AddCommMagma G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  rw [add_comm, map_add_const]
/-
**AddConstMapClass.map_one_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b] 
(f : F) (x : G) : f (1 + x) = f x + b
参数：f : F；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_const_add`：map_const_add [AddCommMagma G] [Add H] [
AddConstMapClass F G H a b] (f : F) (x : G) : f (a + x) = f x + b
-/
theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := map_const_add f x

@[scoped simp]
/-
**AddConstMapClass.map_nsmul_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
 (f : F) (n : Nat) (x : G) : f (n • a + x) = f x + n • b
参数：f : F；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddConstMapClass.map_add_nsmul`：map_add_nsmul [AddMonoid G] [AddMonoid H
] [AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x + n • a) = f x +
 n • b
-/
theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_nsmul]

@[scoped simp]
/-
**AddConstMapClass.map_nat_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G 
H 1 b] (f : F) (n : Nat) (x : G) : f (↑n + x) = f x + n • b
参数：f : F；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `AddConstMapClass.map_nsmul_add`：map_nsmul_add [AddCommMonoid G] [AddMono
id H] [AddConstMapClass F G H a b] (f : F) (n : Nat) (x : G) : f (n • a + x) = f
 x + n • b
-/
theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using map_nsmul_add f n x
/-
**AddConstMapClass.map_ofNat_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F 
G H 1 b] (f : F) (n : Nat) [n.AtLeastTwo] (x : G) : f (ofNat(n) + x) = f x + ofN
at(n) • b
参数：f : F；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_nat_add'`：map_nat_add' [AddCommMonoidWithOne G] [Ad
dMonoid H] [AddConstMapClass F G H 1 b] (f : F) (n : Nat) (x : G) : f (↑n + x) =
 f x + n • b
-/
theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b :=
  map_nat_add' f n x
/-
**AddConstMapClass.map_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClas
s F G H 1 1] (f : F) (n : Nat) (x : G) : f (↑n + x) = f x + n
参数：f : F；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_nat_add'`：map_nat_add' [AddCommMonoidWithOne G] [Ad
dMonoid H] [AddConstMapClass F G H 1 b] (f : F) (n : Nat) (x : G) : f (↑n + x) =
 f x + n • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by simp
/-
**AddConstMapClass.map_ofNat_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapCl
ass F G H 1 1] (f : F) (n : Nat) [n.AtLeastTwo] (x : G) : f (ofNat(n) + x) = f x
 + ofNat(n)
参数：f : F；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_nat_add`：map_nat_add [AddCommMonoidWithOne G] [AddM
onoidWithOne H] [AddConstMapClass F G H 1 1] (f : F) (n : Nat) (x : G) : f (↑n +
 x) = f x + n
-/
theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) :=
  map_nat_add f n x

@[scoped simp]
/-
**AddConstMapClass.map_sub_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b] (f : 
F) (x : G) (n : Nat) : f (x - n • a) = f x - n • b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `AddConstMapClass.map_add_nsmul`：map_add_nsmul [AddMonoid G] [AddMonoid H
] [AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x + n • a) = f x +
 n • b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]

@[scoped simp]
/-
**AddConstMapClass.map_sub_const** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b] (f : 
F) (x : G) : f (x - a) = f x - b
参数：f : F；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddConstMapClass.map_sub_nsmul`：map_sub_nsmul [AddGroup G] [AddGroup H] 
[AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x - n • a) = f x - n
 • b
-/
theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using map_sub_nsmul f x 1
/-
**AddConstMapClass.map_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
 (f : F) (x : G) : f (x - 1) = f x - b
参数：f : F；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_sub_const`：map_sub_const [AddGroup G] [AddGroup H] 
[AddConstMapClass F G H a b] (f : F) (x : G) : f (x - a) = f x - b
-/
theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b :=
  map_sub_const f x

@[scoped simp]
/-
**AddConstMapClass.map_sub_nat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
 (f : F) (x : G) (n : Nat) : f (x - n) = f x - n • b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `AddConstMapClass.map_sub_nsmul`：map_sub_nsmul [AddGroup G] [AddGroup H] 
[AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x - n • a) = f x - n
 • b
-/
theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using map_sub_nsmul f x n

@[scoped simp]
/-
**AddConstMapClass.map_sub_ofNat'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 
b] (f : F) (x : G) (n : Nat) [n.AtLeastTwo] : f (x - ofNat(n)) = f x - ofNat(n) 
• b
参数：f : F；x : G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_sub_nat'`：map_sub_nat' [AddGroupWithOne G] [AddGrou
p H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Nat) : f (x - n) = f x - 
n • b
-/
theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b :=
  map_sub_nat' f x n

@[scoped simp]
/-
**AddConstMapClass.map_add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：∀ {F : Type u_1} {G : Type u_2} {H : Type u_3} [inst : FunLike F G H] {a :
 G} {b : H} [inst_1 : AddGroup G]   [inst_2 : AddGroup H] [AddConstMapClass F G 
H a b] (f : F) (x : G) (n : ℤ), f (x + n • a) = f x + n • b
参数：f : F；x : G；n : ℤ；x + n • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `AddConstMapClass.map_add_nsmul`：map_add_nsmul [AddMonoid G] [AddMonoid H
] [AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x + n • a) = f x +
 n • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
· 使用定理 `AddConstMapClass.map_sub_nsmul`：map_sub_nsmul [AddGroup G] [AddGroup H] 
[AddConstMapClass F G H a b] (f : F) (x : G) (n : Nat) : f (x - n • a) = f x - n
 • b
-/
theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : ∀ n : ℤ, f (x + n • a) = f x + n • b
  | (n : ℕ) => by simp
  | .negSucc n => by simp [← sub_eq_add_neg]

@[scoped simp]
/-
**AddConstMapClass.map_zsmul_const** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b] (f 
: F) (n : Int) : f (n • a) = f 0 + n • b
参数：f : F；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddConstMapClass.map_add_zsmul`：∀ {F : Type u_1} {G : Type u_2} {H : Typ
e u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddGroup G]   [inst_2 : 
AddGroup H] [AddCons…
-/
theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_zsmul f 0 n

@[scoped simp]
/-
**AddConstMapClass.map_add_int'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
 (f : F) (x : G) (n : Int) : f (x + n) = f x + n • b
参数：f : F；x : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddConstMapClass.map_add_zsmul`：∀ {F : Type u_1} {G : Type u_2} {H : Typ
e u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddGroup G]   [inst_2 : 
AddGroup H] [AddCons…
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
-/
theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  rw [← map_add_zsmul f x n, zsmul_one]
/-
**AddConstMapClass.map_add_int** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G 
H 1 1] (f : F) (x : G) (n : Int) : f (x + n) = f x + n
参数：f : F；x : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_add_int'`：map_add_int' [AddGroupWithOne G] [AddGrou
p H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Int) : f (x + n) = f x + 
n • b
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp

@[scoped simp]
/-
**AddConstMapClass.map_sub_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b] (f : 
F) (x : G) (n : Int) : f (x - n • a) = f x - n • b
参数：f : F；x : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `AddConstMapClass.map_add_zsmul`：∀ {F : Type u_1} {G : Type u_2} {H : Typ
e u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddGroup G]   [inst_2 : 
AddGroup H] [AddCons…
-/
theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

@[scoped simp]
/-
**AddConstMapClass.map_sub_int'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
 (f : F) (x : G) (n : Int) : f (x - n) = f x - n • b
参数：f : F；x : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddConstMapClass.map_sub_zsmul`：map_sub_zsmul [AddGroup G] [AddGroup H] 
[AddConstMapClass F G H a b] (f : F) (x : G) (n : Int) : f (x - n • a) = f x - n
 • b
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
-/
theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  rw [← map_sub_zsmul, zsmul_one]
/-
**AddConstMapClass.map_sub_int** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G 
H 1 1] (f : F) (x : G) (n : Int) : f (x - n) = f x - n
参数：f : F；x : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_sub_int'`：map_sub_int' [AddGroupWithOne G] [AddGrou
p H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Int) : f (x - n) = f x - 
n • b
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by simp

@[scoped simp]
/-
**AddConstMapClass.map_zsmul_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b] (
f : F) (n : Int) (x : G) : f (n • a + x) = f x + n • b
参数：f : F；n : Int；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddConstMapClass.map_add_zsmul`：∀ {F : Type u_1} {G : Type u_2} {H : Typ
e u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddGroup G]   [inst_2 : 
AddGroup H] [AddCons…
-/
theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_zsmul]

@[scoped simp]
/-
**AddConstMapClass.map_int_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 
1 b] (f : F) (n : Int) (x : G) : f (↑n + x) = f x + n • b
参数：f : F；n : Int；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddConstMapClass.map_zsmul_add`：map_zsmul_add [AddCommGroup G] [AddGroup
 H] [AddConstMapClass F G H a b] (f : F) (n : Int) (x : G) : f (n • a + x) = f x
 + n • b
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
-/
theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← map_zsmul_add, zsmul_one]
/-
**AddConstMapClass.map_int_add** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass 
F G H 1 1] (f : F) (n : Int) (x : G) : f (↑n + x) = f x + n
参数：f : F；n : Int；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddConstMapClass.map_int_add'`：map_int_add' [AddCommGroupWithOne G] [Add
Group H] [AddConstMapClass F G H 1 b] (f : F) (n : Int) (x : G) : f (↑n + x) = f
 x + n • b
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by simp
/-
**AddConstMapClass.map_fract** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：map_fract {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H] 
[FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) : f (Int.fract x) =
 f x - ⌊x⌋ • b
参数：f : F；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.map_sub_int'`：map_sub_int' [AddGroupWithOne G] [AddGrou
p H] [AddConstMapClass F G H 1 b] (f : F) (x : G) (n : Int) : f (x - n) = f x - 
n • b
-/
theorem map_fract {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H]
    [FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) :
    f (Int.fract x) = f x - ⌊x⌋ • b :=
  map_sub_int' ..

open scoped Relator in
/-- Auxiliary lemmas for the "monotonicity on a fundamental interval implies monotonicity" lemmas.
We formulate it for any relation so that the proof works both for `Monotone` and `StrictMono`. -/
/-
**AddConstMapClass.rel_map_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`。
形式化陈述：∀ {F : Type u_1} {G : Type u_2} {H : Type u_3} [inst : FunLike F G H] {a :
 G} {b : H} [inst_1 : AddCommGroup G]   [inst_2 : LinearOrder G] [IsOrderedAddMo
noid G] [Archimedean G] [inst_5 : AddGroup H] [AddConstMapClass F G H a b]   {f 
: F} {R : H → H → Prop} [IsTrans H R] [hR : CovariantClass H H (fun x y => y + x
) R],   0 < a →     ∀ {l : G},       (∀ x ∈ Set.Icc l (l + a), ∀ y ∈ Set.Icc l (
l + a), x < y → R (f x) (f y)) →         Relator.LiftFun (fun x1 x2 => x1 < x2) 
R ⇑f ⇑f
参数：fun x y => y + x；∀ x ∈ Set.Icc l (l + a), ∀ y ∈ Set.Icc l (l + a), x < y → R 
(f x) (f y)；fun x1 x2 => x1 < x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `existsUnique_sub_zsmul_mem_Ioc`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `zsmul_le_zsmul_left`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
PartialOrder α] [IsOrderedAddMonoid α] {m n : ℤ} {a : α},   0 ≤ a → m ≤ n → m • 
a ≤ n • a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemmas for the "monotonicity on a fundamental interval implies monoton
icity" lemmas.
We formulate it for any relation so that the proof works both for `Monotone` and
 `StrictMono`.
-/
protected theorem rel_map_of_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Archimedean G] [AddGroup H]
    [AddConstMapClass F G H a b] {f : F} {R : H → H → Prop} [IsTrans H R]
    [hR : CovariantClass H H (fun x y ↦ y + x) R] (ha : 0 < a) {l : G}
    (hf : ∀ x ∈ Icc l (l + a), ∀ y ∈ Icc l (l + a), x < y → R (f x) (f y)) :
    ((· < ·) ⇒ R) f f := fun x y hxy ↦ by
  replace hR := hR.elim
  have ha' : 0 ≤ a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x ∈ Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa using hR (m • b) this
    exact this _ _ (by simpa) hm
  · -- Now find `n` such that `l + n • a < y ≤ l + (n + 1) • a`
    rcases existsUnique_sub_zsmul_mem_Ioc ha y l with ⟨n, hny, -⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · -- Since `l ≤ x ≤ y`, the case `n < 0` is impossible
      refine absurd ?_ hxy.not_ge
      calc
        y ≤ l + a + n • a := sub_le_iff_le_add.1 hny.2
        _ = l + (n + 1) • a := by rw [add_comm n, add_smul, one_smul, add_assoc]
        _ ≤ l + (0 : ℤ) • a := by gcongr; lia
        _ ≤ x := by simpa using hx.1
    · -- If `n = 0`, then `l < y ≤ l + a`, hence we can apply the assumption
      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
    · -- In the remaining case `0 < n` we use transitivity.
      -- If `R = (· < ·)`, then the proof looks like
      -- `f x < f (l + a) ≤ f (l + n • a) < f y`
      trans f (l + (1 : ℤ) • a)
      · grind
      have hy : R (f (l + n • a)) (f y) := by
        rw [← sub_add_cancel y (n • a), map_add_zsmul, map_add_zsmul]
        refine hR _ <| hf _ ?_ _ (Ioc_subset_Icc_self hny) hny.1; simpa
      rw [← Int.add_one_le_iff, zero_add] at hn
      rcases hn.eq_or_lt with rfl | hn; · assumption
      trans f (l + n • a)
      · refine Int.rel_of_forall_rel_succ_of_lt R (f := (f <| l + · • a)) (fun k ↦ ?_) hn
        simp_rw [add_comm k 1, add_zsmul, ← add_assoc, one_zsmul, map_add_zsmul]
        refine hR (k • b) (hf _ ?_ _ ?_ ?_) <;> simpa
      · assumption
/-
**AddConstMapClass.monotone_iff_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`
。
形式化陈述：monotone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [
Archimedean G] [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H] [AddCons
tMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) : Monotone f ↔ MonotoneOn f (I
cc l (l + a))
参数：ha : 0 < a；l : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.monotoneOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Monotone f → ∀ (s : Set α), MonotoneOn f s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_iff_forall_lt`：monotone_iff_forall_lt : Monotone f ↔ forall ⦃a 
b⦄, a < b -> f a <= f b
· 使用定理 `AddConstMapClass.rel_map_of_Icc`：∀ {F : Type u_1} {G : Type u_2} {H : Ty
pe u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddCommGroup G]   [inst
_2 : LinearOrder G] […
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem monotone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Monotone f ↔ MonotoneOn f (Icc l (l + a)) :=
  ⟨(Monotone.monotoneOn · _), fun hf ↦ monotone_iff_forall_lt.2 <|
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy ↦ hf hx hy hxy.le⟩
/-
**AddConstMapClass.antitone_iff_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClass`
。
形式化陈述：antitone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [
Archimedean G] [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H] [AddCons
tMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) : Antitone f ↔ AntitoneOn f (I
cc l (l + a))
参数：ha : 0 < a；l : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.monotone_iff_Icc`：monotone_iff_Icc [AddCommGroup G] [Li
nearOrder G] [IsOrderedAddMonoid G] [Archimedean G] [AddCommGroup H] [PartialOrd
er H] [IsOrderedAddMono…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem antitone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Antitone f ↔ AntitoneOn f (Icc l (l + a)) :=
  monotone_iff_Icc (H := Hᵒᵈ) ha l
/-
**AddConstMapClass.strictMono_iff_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClas
s`。
形式化陈述：strictMono_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
 [Archimedean G] [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H] [AddCo
nstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) : StrictMono f ↔ StrictMonoO
n f (Icc l (l + a))
参数：ha : 0 < a；l : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `AddConstMapClass.rel_map_of_Icc`：∀ {F : Type u_1} {G : Type u_2} {H : Ty
pe u_3} [inst : FunLike F G H] {a : G} {b : H} [inst_1 : AddCommGroup G]   [inst
_2 : LinearOrder G] […
· 使用定理 `instIsTransLt`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 < x2
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem strictMono_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictMono f ↔ StrictMonoOn f (Icc l (l + a)) :=
  ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩
/-
**AddConstMapClass.strictAnti_iff_Icc** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMapClas
s`。
形式化陈述：strictAnti_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
 [Archimedean G] [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H] [AddCo
nstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) : StrictAnti f ↔ StrictAntiO
n f (Icc l (l + a))
参数：ha : 0 < a；l : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMapClass.strictMono_iff_Icc`：strictMono_iff_Icc [AddCommGroup G]
 [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] [AddCommGroup H] [Partia
lOrder H] [IsOrderedAddMo…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
-/
theorem strictAnti_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictAnti f ↔ StrictAntiOn f (Icc l (l + a)) :=
  strictMono_iff_Icc (H := Hᵒᵈ) ha l

end AddConstMapClass

open AddConstMapClass

namespace AddConstMap

section Add

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

/-!
### Coercion to function
-/

/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Coercion to function
-/
instance : FunLike (G →+c[a, b] H) G H where
  coe := AddConstMap.toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**AddConstMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (f : G → H)   (hf : ∀ (x : G), f (x + a) = f x + b), ⇑{ toFun := f, map_ad
d_const' := hf } = f
参数：f : G → H；hf : ∀ (x : G), f (x + a) = f x + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, push_cast] theorem coe_mk (f : G → H) (hf) : ⇑(mk f hf : G →+c[a, b] H) = f := rfl
/-
**AddConstMap.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (f : AddConstMap G H a b),   { toFun := ⇑f, map_add_const' := ⋯ } = f
参数：f : AddConstMap G H a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddConstMap.map_add_const'`：∀ {G : Type u_1} {H : Type u_2} [inst : Add 
G] [inst_1 : Add H] {a : G} {b : H} (self : AddConstMap G H a b) (x : G),   self
.toFun (x + a) =…
-/
@[simp] theorem mk_coe (f : G →+c[a, b] H) : mk f f.2 = f := rfl
/-
**AddConstMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (f : AddConstMap G H a b), f.toFun = ⇑f
参数：f : AddConstMap G H a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toFun_eq_coe (f : G →+c[a, b] H) : f.toFun = f := rfl
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddConstMapClass (G →+c[a, b] H) G H a b where
  map_add_const f := f.map_add_const'
/-
**AddConstMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} {f g : AddConstMap G H a b},   (∀ (x : G), f x = g x) → f = g
参数：∀ (x : G), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] protected theorem ext {f g : G →+c[a, b] H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun → coe, as_prefix coe)

/-!
### Constructions about `G →+c[a, b] H`
-/

/-- The identity map as `G →+c[a, a] G`. -/
@[simps -fullyApplied]
/-
**AddConstMap.id** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：{G : Type u_1} → [inst : Add G] → {a : G} → AddConstMap G G a a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as `G →+c[a, a] G`.
-/
protected def id : G →+c[a, a] G := ⟨id, fun _ ↦ rfl⟩
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (G →+c[a, a] G) := ⟨.id⟩

/-- Composition of two `AddConstMap`s. -/
@[simps -fullyApplied]
/-
**AddConstMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：comp {K : Type*} [Add K] {c : K} (g : H ->+c[b, c] K) (f : G ->+c[a, b] H)
 : G ->+c[a, c] K
参数：g : H ->+c[b, c] K；f : G ->+c[a, b] H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two `AddConstMap`s.
-/
def comp {K : Type*} [Add K] {c : K} (g : H →+c[b, c] K) (f : G →+c[a, b] H) :
    G →+c[a, c] K :=
  ⟨g ∘ f, by simp⟩
/-
**AddConstMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (f : AddConstMap G H a b),   f.comp AddConstMap.id = f
参数：f : AddConstMap G H a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem comp_id (f : G →+c[a, b] H) : f.comp .id = f := rfl
/-
**AddConstMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Add G] [inst_1 : Add H] {a : G} {b
 : H} (f : AddConstMap G H a b),   AddConstMap.id.comp f = f
参数：f : AddConstMap G H a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem id_comp (f : G →+c[a, b] H) : .comp .id f = f := rfl

/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
@[simps -fullyApplied]
/-
**AddConstMap.replaceConsts** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：replaceConsts (f : G ->+c[a, b] H) (a' b') (ha : a = a') (hb : b = b') : G
 ->+c[a', b'] H where toFun
参数：f : G ->+c[a, b] H；a' b'；ha : a = a'；hb : b = b'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional eq
ualities.
-/
def replaceConsts (f : G →+c[a, b] H) (a' b') (ha : a = a') (hb : b = b') :
    G →+c[a', b'] H where
  toFun := f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'

/-!
### Additive action on `G →+c[a, b] H`
-/

/-- If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`. -/
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`.
-/
instance {K : Type*} [VAdd K H] [VAddAssocClass K H H] : VAdd K (G →+c[a, b] H) :=
  ⟨fun c f ↦ ⟨c +ᵥ ⇑f, fun x ↦ by simp [vadd_add_assoc]⟩⟩

@[simp, norm_cast]
/-
**AddConstMap.coe_vadd** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G ->+c
[a, b] H) : ⇑(c +ᵥ f) = c +ᵥ ⇑f
参数：c : K；f : G ->+c[a, b] H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G →+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f :=
  rfl
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Type*} [AddMonoid K] [AddAction K H] [VAddAssocClass K H H] :
    AddAction K (G →+c[a, b] H) :=
  DFunLike.coe_injective.addAction _ coe_vadd

/-!
### Monoid structure on endomorphisms `G →+c[a, a] G`
-/

/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Monoid structure on endomorphisms `G →+c[a, a] G`
-/
instance : Mul (G →+c[a, a] G) := ⟨comp⟩
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (G →+c[a, a] G) := ⟨.id⟩
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (G →+c[a, a] G) ℕ where
  pow f n := ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩
/-
**AddConstMap.** 是 Mathlib 中的一个实例，位于命名空间 `AddConstMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (G →+c[a, a] G) :=
  DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**AddConstMap.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：mul_def (f g : G ->+c[a, a] G) : f * g = f.comp g
参数：f g : G ->+c[a, a] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : G →+c[a, a] G) : f * g = f.comp g := rfl
/-
**AddConstMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} [inst : Add G] {a : G} (f g : AddConstMap G G a a), ⇑(f *
 g) = ⇑f ∘ ⇑g
参数：f g : AddConstMap G G a a；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, push_cast] theorem coe_mul (f g : G →+c[a, a] G) : ⇑(f * g) = f ∘ g := rfl
/-
**AddConstMap.one_def** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：one_def : (1 : G ->+c[a, a] G) = .id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : G →+c[a, a] G) = .id := rfl
/-
**AddConstMap.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} [inst : Add G] {a : G}, ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, push_cast] theorem coe_one : ⇑(1 : G →+c[a, a] G) = id := rfl
/-
**AddConstMap.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} [inst : Add G] {a : G} (f : AddConstMap G G a a) (n : ℕ),
 ⇑(f ^ n) = (⇑f)^[n]
参数：f : AddConstMap G G a a；n : ℕ；f ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, push_cast] theorem coe_pow (f : G →+c[a, a] G) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl
/-
**AddConstMap.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：pow_apply (f : G ->+c[a, a] G) (n : Nat) (x : G) : (f ^ n) x = f^[n] x
参数：f : G ->+c[a, a] G；n : Nat；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply (f : G →+c[a, a] G) (n : ℕ) (x : G) : (f ^ n) x = f^[n] x := rfl

/-- Coercion to functions as a monoid homomorphism to `Function.End G`. -/
@[simps -fullyApplied]
/-
**AddConstMap.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：toEnd : (G ->+c[a, a] G) ->* Function.End G where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion to functions as a monoid homomorphism to `Function.End G`.
-/
def toEnd : (G →+c[a, a] G) →* Function.End G where
  toFun := DFunLike.coe
  map_mul' _ _ := rfl
  map_one' := rfl

end Add

section AddZeroClass

variable {G H K : Type*} [Add G] [AddZeroClass H] {a : G} {b : H}

/-!
### Multiplicative action on `(b : H) × (G →+c[a, b] H)`

If `K` acts distributively on `H`, then for each `f : G →+c[a, b] H`
we define `(AddConstMap.smul c f : G →+c[a, c • b] H)`.

One can show that this defines a multiplicative action of `K` on `(b : H) × (G →+c[a, b] H)`
but we don't do this at the moment because we don't need this.
-/

/-- Pointwise scalar multiplication of `f : G →+c[a, b] H` as a map `G →+c[a, c • b] H`. -/
@[simps -fullyApplied]
/-
**AddConstMap.smul** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：smul [DistribSMul K H] (c : K) (f : G ->+c[a, b] H) : G ->+c[a, c • b] H w
here toFun
参数：c : K；f : G ->+c[a, b] H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pointwise scalar multiplication of `f : G →+c[a, b] H` as a map `G →+c[a, c • b]
 H`.
-/
def smul [DistribSMul K H] (c : K) (f : G →+c[a, b] H) : G →+c[a, c • b] H where
  toFun := c • ⇑f
  map_add_const' x := by simp [smul_add]

end AddZeroClass

section AddMonoid

variable {G : Type*} [AddMonoid G] {a : G}

/-- The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`. -/
@[simps! -fullyApplied]
/-
**AddConstMap.addLeftHom** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：addLeftHom : Multiplicative G ->* (G ->+c[a, a] G) where toFun c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`.
-/
def addLeftHom : Multiplicative G →* (G →+c[a, a] G) where
  toFun c := c.toAdd +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

end AddMonoid

section AddCommGroup

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {a : G} {b : H}

/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
@[simps! apply_coe]
/-
**AddConstMap.conjNeg** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：conjNeg : (G ->+c[a, b] H) ≃ (G ->+c[a, b] H)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`.
-/
def conjNeg : (G →+c[a, b] H) ≃ (G →+c[a, b] H) :=
  Involutive.toPerm (fun f ↦ ⟨fun x ↦ - f (-x), fun _ ↦ by simp [neg_add_eq_sub]⟩) fun _ ↦
    AddConstMap.ext fun _ ↦ by simp
/-
**AddConstMap.conjNeg_symm** 是 Mathlib 中的一个定理，位于命名空间 `AddConstMap`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : AddCommGroup G] [inst_1 : AddCommG
roup H] {a : G} {b : H},   AddConstMap.conjNeg.symm = AddConstMap.conjNeg
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem conjNeg_symm : (conjNeg (a := a) (b := b)).symm = conjNeg := rfl

end AddCommGroup

section FloorRing

variable {R G : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [AddGroup G]
  (a : G)

/-- A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`. -/
/-
**AddConstMap.mkFract** 是 Mathlib 中的一个定义，位于命名空间 `AddConstMap`。
形式化陈述：mkFract : (Ico (0 : R) 1 -> G) ≃ (R ->+c[1, a] G) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`.
-/
def mkFract : (Ico (0 : R) 1 → G) ≃ (R →+c[1, a] G) where
  toFun f := ⟨fun x ↦ f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x ↦ by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

end FloorRing

end AddConstMap

