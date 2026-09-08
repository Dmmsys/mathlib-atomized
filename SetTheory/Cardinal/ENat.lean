/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.Data.ENat.Basic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Conversion between `Cardinal` and `ℕ∞`

In this file we define a coercion `Cardinal.ofENat : ℕ∞ → Cardinal`
and a projection `Cardinal.toENat : Cardinal →+*o ℕ∞`.
We also prove basic theorems about these definitions.

## Implementation notes

We define `Cardinal.ofENat` as a function instead of a bundled homomorphism
so that we can use it as a coercion and delaborate its application to `↑n`.

We define `Cardinal.toENat` as a bundled homomorphism
so that we can use all the theorems about homomorphisms without specializing them to this function.
Since it is not registered as a coercion, the argument about delaboration does not apply.

## Keywords

set theory, cardinals, extended natural numbers
-/

@[expose] public section

assert_not_exists Field

open Function Set
universe u v

namespace Cardinal

/-- Coercion `ℕ∞ → Cardinal`. It sends natural numbers to natural numbers and `⊤` to `ℵ₀`.

See also `Cardinal.ofENatHom` for a bundled homomorphism version. -/
/-
**Cardinal.ofENat** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：ℕ∞ → Cardinal.{u_1}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `ℕ∞ → Cardinal`. It sends natural numbers to natural numbers and `⊤` to
 `ℵ₀`.

See also `Cardinal.ofENatHom` for a bundled homomorphism version.
-/
@[coe] def ofENat : ℕ∞ → Cardinal
  | (n : ℕ) => n
  | ⊤ => ℵ₀
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ENat Cardinal := ⟨Cardinal.ofENat⟩
/-
**Cardinal.ofENat_top** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：↑⊤ = Cardinal.aleph0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofENat_top : ofENat ⊤ = ℵ₀ := rfl
/-
**Cardinal.ofENat_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ), ↑↑n = ↑n
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofENat_nat (n : ℕ) : ofENat n = n := rfl
/-
**Cardinal.ofENat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofENat_zero : ofENat 0 = 0 := rfl
/-
**Cardinal.ofENat_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofENat_one : ofENat 1 = 1 := rfl
/-
**Cardinal.ofENat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofENat_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℕ∞) : Cardinal) = OfNat.ofNat n :=
  rfl
/-
**Cardinal.ofENat_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_strictMono : StrictMono ofENat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.strictMono_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder
 α] [inst_1 : Preorder β] {f : WithTop α → β},   StrictMono f ↔ (StrictMono fun 
a => f ↑a) ∧…
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
lemma ofENat_strictMono : StrictMono ofENat :=
  WithTop.strictMono_iff.2 ⟨Nat.strictMono_cast, fun _ ↦ natCast_lt_aleph0⟩

@[simp, norm_cast]
/-
**Cardinal.ofENat_lt_ofENat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_lt_ofENat {m n : Nat∞} : (m : Cardinal) < n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Cardinal.ofENat_strictMono`：ofENat_strictMono : StrictMono ofENat
-/
lemma ofENat_lt_ofENat {m n : ℕ∞} : (m : Cardinal) < n ↔ m < n :=
  ofENat_strictMono.lt_iff_lt

@[gcongr, mono] alias ⟨_, ofENat_lt_ofENat_of_lt⟩ := ofENat_lt_ofENat

@[simp, norm_cast]
/-
**Cardinal.ofENat_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_lt_aleph0 {m : Nat∞} : (m : Cardinal) < ℵ₀ ↔ m < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.ofENat_lt_ofENat`：ofENat_lt_ofENat {m n : Nat∞} : (m : Cardinal
) < n ↔ m < n
-/
lemma ofENat_lt_aleph0 {m : ℕ∞} : (m : Cardinal) < ℵ₀ ↔ m < ⊤ :=
  ofENat_lt_ofENat (n := ⊤)
/-
**Cardinal.ofENat_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ}, ↑m < ↑n ↔ m < ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_lt_nat {m : ℕ∞} {n : ℕ} : ofENat m < n ↔ m < n := by norm_cast
/-
**Cardinal.ofENat_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ} [inst : n.AtLeastTwo], ↑m < OfNat.ofNat n ↔ m < OfNat.o
fNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ofENat_lt_nat`：∀ {m : ℕ∞} {n : ℕ}, ↑m < ↑n ↔ m < ↑n
-/
@[simp] lemma ofENat_lt_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m < ofNat(n) ↔ m < OfNat.ofNat n := ofENat_lt_nat
/-
**Cardinal.nat_lt_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ} {n : ℕ∞}, ↑m < ↑n ↔ ↑m < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma nat_lt_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) < n ↔ m < n := by norm_cast
/-
**Cardinal.ofENat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, 0 < ↑m ↔ 0 < m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_pos {m : ℕ∞} : 0 < (m : Cardinal) ↔ 0 < m := by norm_cast
/-
**Cardinal.one_lt_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, 1 < ↑m ↔ 1 < m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_lt_ofENat {m : ℕ∞} : 1 < (m : Cardinal) ↔ 1 < m := by norm_cast
/-
**Cardinal.ofNat_lt_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ} [inst : m.AtLeastTwo] {n : ℕ∞}, OfNat.ofNat m < ↑n ↔ OfNat.ofNat
 m < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_lt_ofENat`：∀ {m : ℕ} {n : ℕ∞}, ↑m < ↑n ↔ ↑m < n
-/
@[simp, norm_cast] lemma ofNat_lt_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
    (ofNat(m) : Cardinal) < n ↔ OfNat.ofNat m < n := nat_lt_ofENat
/-
**Cardinal.ofENat_mono** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_mono : Monotone ofENat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Cardinal.ofENat_strictMono`：ofENat_strictMono : StrictMono ofENat
-/
lemma ofENat_mono : Monotone ofENat := ofENat_strictMono.monotone

@[simp, norm_cast]
/-
**Cardinal.ofENat_le_ofENat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_le_ofENat {m n : Nat∞} : (m : Cardinal) <= n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Cardinal.ofENat_strictMono`：ofENat_strictMono : StrictMono ofENat
-/
lemma ofENat_le_ofENat {m n : ℕ∞} : (m : Cardinal) ≤ n ↔ m ≤ n := ofENat_strictMono.le_iff_le

@[gcongr, mono] alias ⟨_, ofENat_le_ofENat_of_le⟩ := ofENat_le_ofENat
/-
**Cardinal.ofENat_le_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ∞), ↑n ≤ Cardinal.aleph0
参数：n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.ofENat_le_ofENat`：ofENat_le_ofENat {m n : Nat∞} : (m : Cardinal
) <= n ↔ m <= n
· 使用定理 `le_top`：le_top : a <= ⊤
-/
@[simp] lemma ofENat_le_aleph0 (n : ℕ∞) : ↑n ≤ ℵ₀ := ofENat_le_ofENat.2 le_top
/-
**Cardinal.ofENat_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ}, ↑m ≤ ↑n ↔ m ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_le_nat {m : ℕ∞} {n : ℕ} : ofENat m ≤ n ↔ m ≤ n := by norm_cast
/-
**Cardinal.ofENat_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, ↑m ≤ 1 ↔ m ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_le_one {m : ℕ∞} : ofENat m ≤ 1 ↔ m ≤ 1 := by norm_cast
/-
**Cardinal.ofENat_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ} [inst : n.AtLeastTwo], ↑m ≤ OfNat.ofNat n ↔ m ≤ OfNat.o
fNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ofENat_le_nat`：∀ {m : ℕ∞} {n : ℕ}, ↑m ≤ ↑n ↔ m ≤ ↑n
-/
@[simp] lemma ofENat_le_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    ofENat m ≤ ofNat(n) ↔ m ≤ OfNat.ofNat n := ofENat_le_nat
/-
**Cardinal.nat_le_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ} {n : ℕ∞}, ↑m ≤ ↑n ↔ ↑m ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma nat_le_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) ≤ n ↔ m ≤ n := by norm_cast
/-
**Cardinal.one_le_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {n : ℕ∞}, 1 ≤ ↑n ↔ 1 ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma one_le_ofENat {n : ℕ∞} : 1 ≤ (n : Cardinal) ↔ 1 ≤ n := by norm_cast

@[simp]
/-
**Cardinal.ofNat_le_ofENat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofNat_le_ofENat {m : Nat} [m.AtLeastTwo] {n : Nat∞} : (ofNat(m) : Cardinal
) <= n ↔ OfNat.ofNat m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_le_ofENat`：∀ {m : ℕ} {n : ℕ∞}, ↑m ≤ ↑n ↔ ↑m ≤ n
-/
lemma ofNat_le_ofENat {m : ℕ} [m.AtLeastTwo] {n : ℕ∞} :
    (ofNat(m) : Cardinal) ≤ n ↔ OfNat.ofNat m ≤ n := nat_le_ofENat
/-
**Cardinal.ofENat_injective** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_injective : Injective ofENat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Cardinal.ofENat_strictMono`：ofENat_strictMono : StrictMono ofENat
-/
lemma ofENat_injective : Injective ofENat := ofENat_strictMono.injective

@[simp, norm_cast]
/-
**Cardinal.ofENat_inj** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_inj {m n : Nat∞} : (m : Cardinal) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Cardinal.ofENat_injective`：ofENat_injective : Injective ofENat
-/
lemma ofENat_inj {m n : ℕ∞} : (m : Cardinal) = n ↔ m = n := ofENat_injective.eq_iff
/-
**Cardinal.ofENat_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ}, ↑m = ↑n ↔ m = ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_eq_nat {m : ℕ∞} {n : ℕ} : (m : Cardinal) = n ↔ m = n := by norm_cast
/-
**Cardinal.nat_eq_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ} {n : ℕ∞}, ↑m = ↑n ↔ ↑m = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma nat_eq_ofENat {m : ℕ} {n : ℕ∞} : (m : Cardinal) = n ↔ m = n := by norm_cast
/-
**Cardinal.ofENat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, ↑m = 0 ↔ m = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_eq_zero {m : ℕ∞} : (m : Cardinal) = 0 ↔ m = 0 := by norm_cast
/-
**Cardinal.zero_eq_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, 0 = ↑m ↔ m = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
@[simp] lemma zero_eq_ofENat {m : ℕ∞} : 0 = (m : Cardinal) ↔ m = 0 := by norm_cast; apply eq_comm
/-
**Cardinal.ofENat_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, ↑m = 1 ↔ m = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_eq_one {m : ℕ∞} : (m : Cardinal) = 1 ↔ m = 1 := by norm_cast
/-
**Cardinal.one_eq_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, 1 = ↑m ↔ m = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
@[simp] lemma one_eq_ofENat {m : ℕ∞} : 1 = (m : Cardinal) ↔ m = 1 := by norm_cast; apply eq_comm
/-
**Cardinal.ofENat_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞} {n : ℕ} [inst : n.AtLeastTwo], ↑m = OfNat.ofNat n ↔ m = OfNat.o
fNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ofENat_eq_nat`：∀ {m : ℕ∞} {n : ℕ}, ↑m = ↑n ↔ m = ↑n
-/
@[simp] lemma ofENat_eq_ofNat {m : ℕ∞} {n : ℕ} [n.AtLeastTwo] :
    (m : Cardinal) = ofNat(n) ↔ m = OfNat.ofNat n := ofENat_eq_nat
/-
**Cardinal.ofNat_eq_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ} {n : ℕ∞} [inst : m.AtLeastTwo], OfNat.ofNat m = ↑n ↔ OfNat.ofNat
 m = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nat_eq_ofENat`：∀ {m : ℕ} {n : ℕ∞}, ↑m = ↑n ↔ ↑m = n
-/
@[simp] lemma ofNat_eq_ofENat {m : ℕ} {n : ℕ∞} [m.AtLeastTwo] :
    ofNat(m) = (n : Cardinal) ↔ OfNat.ofNat m = n := nat_eq_ofENat
/-
**Cardinal.lift_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
参数：m : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
-/
@[simp, norm_cast] lemma lift_ofENat : ∀ m : ℕ∞, lift.{u, v} m = m
  | (m : ℕ) => lift_natCast m
  | ⊤ => lift_aleph0
/-
**Cardinal.lift_lt_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, Cardinal.lift.{u, v} x < ↑m ↔ x < ↑m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma lift_lt_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x < m ↔ x < m := by
  rw [← lift_ofENat.{u, v}, lift_lt]
/-
**Cardinal.lift_le_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, Cardinal.lift.{u, v} x ≤ ↑m ↔ x ≤ ↑m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma lift_le_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x ≤ m ↔ x ≤ m := by
  rw [← lift_ofENat.{u, v}, lift_le]
/-
**Cardinal.lift_eq_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, Cardinal.lift.{u, v} x = ↑m ↔ x = ↑m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma lift_eq_ofENat {x : Cardinal.{v}} {m : ℕ∞} : lift.{u} x = m ↔ x = m := by
  rw [← lift_ofENat.{u, v}, lift_inj]
/-
**Cardinal.ofENat_lt_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, ↑m < Cardinal.lift.{u, v} x ↔ ↑m < x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_lt_lift {x : Cardinal.{v}} {m : ℕ∞} : m < lift.{u} x ↔ m < x := by
  rw [← lift_ofENat.{u, v}, lift_lt]
/-
**Cardinal.ofENat_le_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, ↑m ≤ Cardinal.lift.{u, v} x ↔ ↑m ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_le_lift {x : Cardinal.{v}} {m : ℕ∞} : m ≤ lift.{u} x ↔ m ≤ x := by
  rw [← lift_ofENat.{u, v}, lift_le]
/-
**Cardinal.ofENat_eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {x : Cardinal.{v}} {m : ℕ∞}, ↑m = Cardinal.lift.{u, v} x ↔ ↑m = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofENat_eq_lift {x : Cardinal.{v}} {m : ℕ∞} : m = lift.{u} x ↔ m = x := by
  rw [← lift_ofENat.{u, v}, lift_inj]

@[simp]
/-
**Cardinal.range_ofENat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：range_ofENat : range ofENat = Iic ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Cardinal.ofENat_le_aleph0`：∀ (n : ℕ∞), ↑n ≤ Cardinal.aleph0
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma range_ofENat : range ofENat = Iic ℵ₀ := by
  refine (range_subset_iff.2 ofENat_le_aleph0).antisymm fun x (hx : x ≤ ℵ₀) ↦ ?_
  rcases hx.lt_or_eq with hlt | rfl
  · lift x to ℕ using hlt
    exact mem_range_self (x : ℕ∞)
  · exact mem_range_self (⊤ : ℕ∞)
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift Cardinal ℕ∞ (↑) (· ≤ ℵ₀) where
  prf x := (Set.ext_iff.1 range_ofENat x).2

/-- Unbundled version of `Cardinal.toENat`. -/
/-
**Cardinal.toENatAux** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：toENatAux : Cardinal.{u} -> Nat∞
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unbundled version of `Cardinal.toENat`.
-/
noncomputable def toENatAux : Cardinal.{u} → ℕ∞ := extend Nat.cast Nat.cast fun _ ↦ ⊤
/-
**Cardinal.toENatAux_nat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_nat (n : Nat) : toENatAux n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
lemma toENatAux_nat (n : ℕ) : toENatAux n = n := Nat.cast_injective.extend_apply ..
/-
**Cardinal.toENatAux_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_zero : toENatAux 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_nat`：toENatAux_nat (n : Nat) : toENatAux n = n
-/
lemma toENatAux_zero : toENatAux 0 = 0 := toENatAux_nat 0
/-
**Cardinal.toENatAux_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ <= a) : toENatAux a = ⊤
参数：ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
lemma toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ ≤ a) : toENatAux a = ⊤ :=
  extend_apply' _ _ _ fun ⟨_n, hn⟩ ↦ ha.not_gt <| hn ▸ natCast_lt_aleph0
/-
**Cardinal.toENatAux_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ∞), (↑n).toENatAux = n
参数：n : ℕ∞；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_nat`：toENatAux_nat (n : Nat) : toENatAux n = n
· 使用引理 `Cardinal.toENatAux_eq_top`：toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ <= a
) : toENatAux a = ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma toENatAux_ofENat : ∀ n : ℕ∞, toENatAux n = n
  | (n : ℕ) => toENatAux_nat n
  | ⊤ => toENatAux_eq_top le_rfl

attribute [local simp] toENatAux_nat toENatAux_zero toENatAux_ofENat
/-
**Cardinal.toENatAux_gc** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_gc : GaloisConnection (↑) toENatAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.toENatAux_nat`：toENatAux_nat (n : Nat) : toENatAux n = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.ofENat_le_aleph0`：∀ (n : ℕ∞), ↑n ≤ Cardinal.aleph0
· 使用引理 `Cardinal.toENatAux_eq_top`：toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ <= a
) : toENatAux a = ⊤
-/
lemma toENatAux_gc : GaloisConnection (↑) toENatAux := fun n x ↦ by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, (ofENat_le_aleph0 n).trans hx]
/-
**Cardinal.toENatAux_le_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_le_nat {x : Cardinal} {n : Nat} : toENatAux x <= n ↔ x <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Cardinal.toENatAux_nat`：toENatAux_nat (n : Nat) : toENatAux n = n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Cardinal.toENatAux_eq_top`：toENatAux_eq_top {a : Cardinal} (ha : ℵ₀ <= a
) : toENatAux a = ⊤
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem toENatAux_le_nat {x : Cardinal} {n : ℕ} : toENatAux x ≤ n ↔ x ≤ n := by
  cases lt_or_ge x ℵ₀ with
  | inl hx => lift x to ℕ using hx; simp
  | inr hx => simp [toENatAux_eq_top hx, natCast_lt_aleph0.trans_le hx]
/-
**Cardinal.toENatAux_eq_nat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_eq_nat {x : Cardinal} {n : Nat} : toENatAux x = n ↔ x = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.toENatAux_gc`：toENatAux_gc : GaloisConnection (↑) toENatAux
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENatAux_eq_nat {x : Cardinal} {n : ℕ} : toENatAux x = n ↔ x = n := by
  simp only [le_antisymm_iff, toENatAux_le_nat, ← toENatAux_gc _, ofENat_nat]
/-
**Cardinal.toENatAux_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENatAux_eq_zero {x : Cardinal} : toENatAux x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_eq_nat`：toENatAux_eq_nat {x : Cardinal} {n : Nat} : t
oENatAux x = n ↔ x = n
-/
lemma toENatAux_eq_zero {x : Cardinal} : toENatAux x = 0 ↔ x = 0 := toENatAux_eq_nat

/-- Projection from cardinals to `ℕ∞`. Sends all infinite cardinals to `⊤`.

We define this function as a bundled monotone ring homomorphism. -/
/-
**Cardinal.toENat** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：toENat : Cardinal.{u} ->+*o Nat∞ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_zero`：toENatAux_zero : toENatAux 0 = 0

--- 原说明 ---
Projection from cardinals to `ℕ∞`. Sends all infinite cardinals to `⊤`.

We define this function as a bundled monotone ring homomorphism.
-/
noncomputable def toENat : Cardinal.{u} →+*o ℕ∞ where
  toFun := toENatAux
  map_one' := toENatAux_nat 1
  map_mul' x y := by
    wlog hle : x ≤ y; · rw [mul_comm, this y x (le_of_not_ge hle), mul_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to ℕ using hle.trans_lt hy; lift y to ℕ using hy
      simp only [← Nat.cast_mul, toENatAux_nat]
    | inr hy =>
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · simp only [toENatAux_eq_top hy]
        rw [toENatAux_eq_top, ENat.mul_top]
        · rwa [Ne, toENatAux_eq_zero]
        · exact le_mul_of_one_le_of_le (Cardinal.one_le_iff_ne_zero.2 hx) hy
  map_add' x y := by
    wlog hle : x ≤ y; · rw [add_comm, this y x (le_of_not_ge hle), add_comm]
    cases lt_or_ge y ℵ₀ with
    | inl hy =>
      lift x to ℕ using hle.trans_lt hy; lift y to ℕ using hy
      simp only [← Nat.cast_add, toENatAux_nat]
    | inr hy =>
      simp only [toENatAux_eq_top hy, add_top]
      exact toENatAux_eq_top <| le_add_left hy
  map_zero' := toENatAux_zero
  monotone' := toENatAux_gc.monotone_u

/-- The coercion `Cardinal.ofENat` and the projection `Cardinal.toENat` form a Galois connection.
See also `Cardinal.gciENat`. -/
/-
**Cardinal.enat_gc** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：enat_gc : GaloisConnection (↑) toENat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_gc`：toENatAux_gc : GaloisConnection (↑) toENatAux

--- 原说明 ---
The coercion `Cardinal.ofENat` and the projection `Cardinal.toENat` form a Galoi
s connection.
See also `Cardinal.gciENat`.
-/
lemma enat_gc : GaloisConnection (↑) toENat := toENatAux_gc
/-
**Cardinal.toENat_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
参数：n : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENatAux_ofENat`：∀ (n : ℕ∞), (↑n).toENatAux = n
-/
@[simp] lemma toENat_ofENat (n : ℕ∞) : toENat n = n := toENatAux_ofENat n
/-
**Cardinal.toENat_comp_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：⇑Cardinal.toENat ∘ Cardinal.ofENat = id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
-/
@[simp] lemma toENat_comp_ofENat : toENat ∘ (↑) = id := funext toENat_ofENat

/-- The coercion `Cardinal.ofENat` and the projection `Cardinal.toENat`
form a Galois coinsertion. -/
/-
**Cardinal.gciENat** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：gciENat : GaloisCoinsertion (↑) toENat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.enat_gc`：enat_gc : GaloisConnection (↑) toENat

--- 原说明 ---
The coercion `Cardinal.ofENat` and the projection `Cardinal.toENat`
form a Galois coinsertion.
-/
noncomputable def gciENat : GaloisCoinsertion (↑) toENat :=
  enat_gc.toGaloisCoinsertion fun n ↦ (toENat_ofENat n).le
/-
**Cardinal.toENat_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_strictMonoOn : StrictMonoOn toENat (Iic ℵ₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
-/
lemma toENat_strictMonoOn : StrictMonoOn toENat (Iic ℵ₀) := by
  simp only [← range_ofENat, StrictMonoOn, forall_mem_range, toENat_ofENat, ofENat_lt_ofENat]
  exact fun _ _ ↦ id
/-
**Cardinal.toENat_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_injOn : InjOn toENat (Iic ℵ₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用引理 `Cardinal.toENat_strictMonoOn`：toENat_strictMonoOn : StrictMonoOn toENat 
(Iic ℵ₀)
-/
lemma toENat_injOn : InjOn toENat (Iic ℵ₀) := toENat_strictMonoOn.injOn
/-
**Cardinal.ofENat_toENat_le** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_toENat_le (a : Cardinal) : ↑(toENat a) <= a
参数：a : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_le`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀ (a : 
α), l (u a) ≤…
· 使用引理 `Cardinal.enat_gc`：enat_gc : GaloisConnection (↑) toENat
-/
lemma ofENat_toENat_le (a : Cardinal) : ↑(toENat a) ≤ a := enat_gc.l_u_le _

@[simp]
/-
**Cardinal.ofENat_toENat_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_toENat_eq_self {a : Cardinal} : toENat a = a ↔ a <= ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.exists_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u 
→ ∀ (a : α), (∃ b,…
· 使用引理 `Cardinal.enat_gc`：enat_gc : GaloisConnection (↑) toENat
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用引理 `Cardinal.range_ofENat`：range_ofENat : range ofENat = Iic ℵ₀
-/
lemma ofENat_toENat_eq_self {a : Cardinal} : toENat a = a ↔ a ≤ ℵ₀ := by
  rw [eq_comm, ← enat_gc.exists_eq_l]
  simpa only [mem_range, eq_comm] using! Set.ext_iff.1 range_ofENat a

@[simp] alias ⟨_, ofENat_toENat⟩ := ofENat_toENat_eq_self
/-
**Cardinal.toENat_nat** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_nat (n : Nat) : toENat n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
-/
lemma toENat_nat (n : ℕ) : toENat n = n := map_natCast _ n
/-
**Cardinal.toENat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], Cardinal.toENat (OfNat.ofNat n) = OfNat.o
fNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENat_nat`：toENat_nat (n : Nat) : toENat n = n
-/
@[simp] lemma toENat_ofNat (n : ℕ) [n.AtLeastTwo] : toENat ofNat(n) = ofNat(n) := toENat_nat _

variable {c c' : Cardinal.{u}} {n : ℕ}
/-
**Cardinal.toENat_le_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENat c ≤ ↑n ↔ c ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENatAux_le_nat`：toENatAux_le_nat {x : Cardinal} {n : Nat} : t
oENatAux x <= n ↔ x <= n
-/
@[simp] lemma toENat_le_natCast : toENat c ≤ n ↔ c ≤ n := toENatAux_le_nat
/-
**Cardinal.toENat_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, Cardinal.toENat c ≤ 1 ↔ c ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_le_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c ≤ ↑n ↔ c ≤ ↑n
-/
@[simp] lemma toENat_le_one : toENat c ≤ 1 ↔ c ≤ 1 := toENat_le_natCast
/-
**Cardinal.toENat_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], Cardinal.toENat c ≤ Of
Nat.ofNat n ↔ c ≤ OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_le_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c ≤ ↑n ↔ c ≤ ↑n
-/
@[simp] lemma toENat_le_ofNat [n.AtLeastTwo] : toENat c ≤ ofNat(n) ↔ c ≤ ofNat(n) :=
  toENat_le_natCast

@[deprecated (since := "2026-01-13")] alias toENat_le_nat := toENat_le_natCast
/-
**Cardinal.toENat_le_iff_of_le_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_le_iff_of_le_aleph0 (hc : c <= ℵ₀) : toENat c <= toENat c' ↔ c <= c
'
参数：hc : c <= ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Cardinal.instCanLiftENatOfENatLeAleph0`：CanLift Cardinal.{u_1} ℕ∞ Cardin
al.ofENat fun x => x ≤ Cardinal.aleph0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Cardinal.enat_gc`：enat_gc : GaloisConnection (↑) toENat
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENat_le_iff_of_le_aleph0 (hc : c ≤ ℵ₀) : toENat c ≤ toENat c' ↔ c ≤ c' := by
  lift c to ℕ∞ using hc; simp_rw [toENat_ofENat, enat_gc _]
/-
**Cardinal.toENat_le_iff_of_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_le_iff_of_lt_aleph0 (hc' : c' < ℵ₀) : toENat c <= toENat c' ↔ c <= 
c'
参数：hc' : c' < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Cardinal.toENat_nat`：toENat_nat (n : Nat) : toENat n = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENat_le_iff_of_lt_aleph0 (hc' : c' < ℵ₀) : toENat c ≤ toENat c' ↔ c ≤ c' := by
  lift c' to ℕ using hc'; simp_rw [toENat_nat, ← toENat_le_natCast]
/-
**Cardinal.toENat_eq_iff_of_le_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_eq_iff_of_le_aleph0 (hc : c <= ℵ₀) (hc' : c' <= ℵ₀) : toENat c = to
ENat c' ↔ c = c'
参数：hc : c <= ℵ₀；hc' : c' <= ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用引理 `Cardinal.toENat_strictMonoOn`：toENat_strictMonoOn : StrictMonoOn toENat 
(Iic ℵ₀)
-/
lemma toENat_eq_iff_of_le_aleph0 (hc : c ≤ ℵ₀) (hc' : c' ≤ ℵ₀) : toENat c = toENat c' ↔ c = c' :=
  toENat_strictMonoOn.injOn.eq_iff hc hc'
/-
**Cardinal.natCast_le_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n ≤ Cardinal.toENat c ↔ ↑n ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.toENat_nat`：toENat_nat (n : Nat) : toENat n = n
· 使用引理 `Cardinal.toENat_le_iff_of_le_aleph0`：toENat_le_iff_of_le_aleph0 (hc : c 
<= ℵ₀) : toENat c <= toENat c' ↔ c <= c'
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma natCast_le_toENat : n ≤ toENat c ↔ n ≤ c := by
  rw [← toENat_nat n, toENat_le_iff_of_le_aleph0 natCast_le_aleph0]
/-
**Cardinal.one_le_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, 1 ≤ Cardinal.toENat c ↔ 1 ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_le_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n ≤ Cardinal.
toENat c ↔ ↑n ≤ c
-/
@[simp] lemma one_le_toENat : 1 ≤ toENat c ↔ 1 ≤ c := natCast_le_toENat
/-
**Cardinal.ofNat_le_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], OfNat.ofNat n ≤ Cardin
al.toENat c ↔ OfNat.ofNat n ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_le_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n ≤ Cardinal.
toENat c ↔ ↑n ≤ c
-/
@[simp] lemma ofNat_le_toENat [n.AtLeastTwo] : ofNat(n) ≤ toENat c ↔ ofNat(n) ≤ c :=
  natCast_le_toENat
/-
**Cardinal.toENat_lt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENat c < ↑n ↔ c < ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toENat_lt_natCast : toENat c < n ↔ c < n := by simp [← not_le]
/-
**Cardinal.toENat_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], Cardinal.toENat c < Of
Nat.ofNat n ↔ c < OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_lt_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c < ↑n ↔ c < ↑n
-/
@[simp] lemma toENat_lt_ofNat [n.AtLeastTwo] : toENat c < ofNat(n) ↔ c < ofNat(n) :=
  toENat_lt_natCast
/-
**Cardinal.natCast_lt_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n < Cardinal.toENat c ↔ ↑n < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma natCast_lt_toENat : n < toENat c ↔ n < c := by simp [← not_le]
/-
**Cardinal.one_lt_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, 1 < Cardinal.toENat c ↔ 1 < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_lt_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n < Cardinal.
toENat c ↔ ↑n < c
-/
@[simp] lemma one_lt_toENat : 1 < toENat c ↔ 1 < c := natCast_lt_toENat
/-
**Cardinal.ofNat_lt_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], OfNat.ofNat n < Cardin
al.toENat c ↔ OfNat.ofNat n < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_lt_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n < Cardinal.
toENat c ↔ ↑n < c
-/
@[simp] lemma ofNat_lt_toENat [n.AtLeastTwo] : ofNat(n) < toENat c ↔ ofNat(n) < c :=
  natCast_lt_toENat
/-
**Cardinal.toENat_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENat c = ↑n ↔ c = ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENatAux_eq_nat`：toENatAux_eq_nat {x : Cardinal} {n : Nat} : t
oENatAux x = n ↔ x = n
-/
@[simp] lemma toENat_eq_natCast : toENat c = n ↔ c = n := toENatAux_eq_nat
/-
**Cardinal.toENat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, Cardinal.toENat c = 0 ↔ c = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_eq_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c = ↑n ↔ c = ↑n
-/
@[simp] lemma toENat_eq_zero : toENat c = 0 ↔ c = 0 := toENat_eq_natCast
/-
**Cardinal.toENat_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, Cardinal.toENat c = 1 ↔ c = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_eq_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c = ↑n ↔ c = ↑n
-/
@[simp] lemma toENat_eq_one : toENat c = 1 ↔ c = 1 := toENat_eq_natCast
/-
**Cardinal.toENat_eq_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], Cardinal.toENat c = Of
Nat.ofNat n ↔ c = OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toENat_eq_natCast`：∀ {c : Cardinal.{u}} {n : ℕ}, Cardinal.toENa
t c = ↑n ↔ c = ↑n
-/
@[simp] lemma toENat_eq_ofNat [n.AtLeastTwo] : toENat c = ofNat(n) ↔ c = ofNat(n) :=
  toENat_eq_natCast

@[deprecated toENat_eq_zero (since := "2026-05-25")]
/-
**Cardinal.toENat_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_lt_one : toENat c < 1 ↔ c < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toENat_lt_one : toENat c < 1 ↔ c < 1 := by simp

@[deprecated (since := "2026-01-13")] alias toENat_eq_nat := toENat_eq_natCast
/-
**Cardinal.natCast_eq_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n = Cardinal.toENat c ↔ ↑n = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma natCast_eq_toENat : n = toENat c ↔ n = c := by simp [eq_comm (a := Nat.cast _)]
/-
**Cardinal.ofNat_eq_toENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}} {n : ℕ} [inst : n.AtLeastTwo], OfNat.ofNat n = Cardin
al.toENat c ↔ OfNat.ofNat n = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.natCast_eq_toENat`：∀ {c : Cardinal.{u}} {n : ℕ}, ↑n = Cardinal.
toENat c ↔ ↑n = c
-/
@[simp] lemma ofNat_eq_toENat [n.AtLeastTwo] : ofNat(n) = toENat c ↔ ofNat(n) = c :=
  natCast_eq_toENat
/-
**Cardinal.toENat_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, Cardinal.toENat c = ⊤ ↔ Cardinal.aleph0 ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.u_eq_top`：u_eq_top {l : α -> β} {u : β -> α} (gc : Galo
isConnection l u) {x} : u x = ⊤ ↔ l ⊤ <= x
· 使用引理 `Cardinal.enat_gc`：enat_gc : GaloisConnection (↑) toENat
-/
@[simp] lemma toENat_eq_top : toENat c = ⊤ ↔ ℵ₀ ≤ c := enat_gc.u_eq_top
/-
**Cardinal.toENat_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：toENat_ne_top : toENat c != ⊤ ↔ c < ℵ₀
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
lemma toENat_ne_top : toENat c ≠ ⊤ ↔ c < ℵ₀ := by simp
/-
**Cardinal.toENat_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {c : Cardinal.{u}}, Cardinal.toENat c < ⊤ ↔ c < Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toENat_lt_top : toENat c < ⊤ ↔ c < ℵ₀ := by simp [lt_top_iff_ne_top]

@[simp]
/-
**Cardinal.toENat_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toENat_lift : toENat (lift.{v} c) = toENat c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Cardinal.instCanLiftENatOfENatLeAleph0`：CanLift Cardinal.{u_1} ℕ∞ Cardin
al.ofENat fun x => x ≤ Cardinal.aleph0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_ofENat`：∀ (m : ℕ∞), Cardinal.lift.{u, v} ↑m = ↑m
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.toENat_eq_top`：∀ {c : Cardinal.{u}}, Cardinal.toENat c = ⊤ ↔ Ca
rdinal.aleph0 ≤ c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem toENat_lift : toENat (lift.{v} c) = toENat c := by
  cases le_total c ℵ₀ with
  | inl ha => lift c to ℕ∞ using ha; simp
  | inr ha => simp [toENat_eq_top.2, ha]
/-
**Cardinal.toENat_congr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：toENat_congr {α : Type u} {β : Type v} (e : α ≃ β) : toENat #α = toENat #β
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toENat_lift`：toENat_lift : toENat (lift.{v} c) = toENat c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
-/
theorem toENat_congr {α : Type u} {β : Type v} (e : α ≃ β) : toENat #α = toENat #β := by
  rw [← toENat_lift, lift_mk_eq.{_, _, v}.mpr ⟨e⟩, toENat_lift]

@[simp, norm_cast]
/-
**Cardinal.ofENat_add** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：ofENat_add (m n : Nat∞) : ofENat (m + n) = m + n
参数：m n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENat_injOn`：toENat_injOn : InjOn toENat (Iic ℵ₀)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofENat_add (m n : ℕ∞) : ofENat (m + n) = m + n := by apply toENat_injOn <;> simp
/-
**Cardinal.aleph0_add_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (m : ℕ∞), Cardinal.aleph0 + ↑m = Cardinal.aleph0
参数：m : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.ofENat_add`：ofENat_add (m n : Nat∞) : ofENat (m + n) = m + n
-/
@[simp] lemma aleph0_add_ofENat (m : ℕ∞) : ℵ₀ + m = ℵ₀ := (ofENat_add ⊤ m).symm
/-
**Cardinal.ofENat_add_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (m : ℕ∞), ↑m + Cardinal.aleph0 = Cardinal.aleph0
参数：m : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.aleph0_add_ofENat`：∀ (m : ℕ∞), Cardinal.aleph0 + ↑m = Cardinal.
aleph0
-/
@[simp] lemma ofENat_add_aleph0 (m : ℕ∞) : m + ℵ₀ = ℵ₀ := by rw [add_comm, aleph0_add_ofENat]
/-
**Cardinal.ofENat_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, m ≠ 0 → ↑m * Cardinal.aleph0 = Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_mul_aleph0`：aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ofENat_nat`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Cardinal.nat_mul_aleph0`：nat_mul_aleph0 {n : Nat} (hn : n != 0) : ↑n * ℵ
₀ = ℵ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
@[simp] lemma ofENat_mul_aleph0 {m : ℕ∞} (hm : m ≠ 0) : ↑m * ℵ₀ = ℵ₀ := by
  induction m with
  | top => exact aleph0_mul_aleph0
  | coe m => rw [ofENat_nat, nat_mul_aleph0 (mod_cast hm)]
/-
**Cardinal.aleph0_mul_ofENat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {m : ℕ∞}, m ≠ 0 → Cardinal.aleph0 * ↑m = Cardinal.aleph0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.ofENat_mul_aleph0`：∀ {m : ℕ∞}, m ≠ 0 → ↑m * Cardinal.aleph0 = C
ardinal.aleph0
-/
@[simp] lemma aleph0_mul_ofENat {m : ℕ∞} (hm : m ≠ 0) : ℵ₀ * m = ℵ₀ := by
  rw [mul_comm, ofENat_mul_aleph0 hm]
/-
**Cardinal.ofENat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ (m n : ℕ∞), ↑(m * n) = ↑m * ↑n
参数：m n : ℕ∞；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.toENat_injOn`：toENat_injOn : InjOn toENat (Iic ℵ₀)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `Cardinal.ofENat_le_aleph0`：∀ (n : ℕ∞), ↑n ≤ Cardinal.aleph0
· 使用定理 `Cardinal.aleph0_mul_aleph0`：aleph0_mul_aleph0 : ℵ₀ * ℵ₀ = ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toENat_ofENat`：∀ (n : ℕ∞), Cardinal.toENat ↑n = n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma ofENat_mul (m n : ℕ∞) : ofENat (m * n) = m * n :=
  toENat_injOn (by simp)
    (aleph0_mul_aleph0 ▸ mul_le_mul' (ofENat_le_aleph0 _) (ofENat_le_aleph0 _)) (by simp)

/-- The coercion `Cardinal.ofENat` as a bundled homomorphism. -/
/-
**Cardinal.ofENatHom** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：ofENatHom : Nat∞ ->+*o Cardinal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.ofENat_one`：↑1 = 1
· 使用定理 `Cardinal.ofENat_mul`：∀ (m n : ℕ∞), ↑(m * n) = ↑m * ↑n
· 使用定理 `Cardinal.ofENat_zero`：↑0 = 0
· 使用引理 `Cardinal.ofENat_add`：ofENat_add (m n : Nat∞) : ofENat (m + n) = m + n
· 使用引理 `Cardinal.ofENat_mono`：ofENat_mono : Monotone ofENat

--- 原说明 ---
The coercion `Cardinal.ofENat` as a bundled homomorphism.
-/
def ofENatHom : ℕ∞ →+*o Cardinal where
  toFun := (↑)
  map_one' := ofENat_one
  map_mul' := ofENat_mul
  map_zero' := ofENat_zero
  map_add' := ofENat_add
  monotone' := ofENat_mono

end Cardinal

