/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.PNat.Equiv

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `PNat`, the subtype of natural numbers that are positive.
It is defined in `Data.PNat.Defs`, but most of the development is deferred to here so
that `Data.PNat.Defs` can have very few imports.
-/

@[expose] public section

deriving instance Add, Mul, Distrib, AddLeftCancelSemigroup, AddRightCancelSemigroup,
  AddCommSemigroup, CommMonoid, IsOrderedCancelMonoid, WellFoundedLT, AddLeftMono,
  AddLeftStrictMono, AddLeftReflectLE, AddLeftReflectLT for PNat

namespace PNat

/-
**PNat.instCancelCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：CancelCommMonoid ℕ+
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCancelCommMonoid : CancelCommMonoid ℕ+ where

@[simp]
/-
**PNat.one_add_natPred** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_add_natPred (n : Nat+) : 1 + n.natPred = n
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.natPred.eq_1`：∀ (i : ℕ+), i.natPred = ↑i - 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `add_tsub_cancel_iff_le`：add_tsub_cancel_iff_le : a + (b - a) = b ↔ a <= 
b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem one_add_natPred (n : ℕ+) : 1 + n.natPred = n := by
  rw [natPred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]

@[simp]
/-
**PNat.natPred_add_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_add_one (n : Nat+) : n.natPred + 1 = n
参数：n : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `PNat.one_add_natPred`：one_add_natPred (n : Nat+) : 1 + n.natPred = n
-/
theorem natPred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_natPred

@[gcongr, mono]
/-
**PNat.natPred_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_strictMono : StrictMono natPred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pred_lt_pred`：∀ {n m : ℕ}, n ≠ 0 → n < m → n.pred < m.pred
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem natPred_strictMono : StrictMono natPred := fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[gcongr, mono]
/-
**PNat.natPred_monotone** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_monotone : Monotone natPred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `PNat.natPred_strictMono`：natPred_strictMono : StrictMono natPred
-/
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.monotone
/-
**PNat.natPred_injective** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_injective : Function.Injective natPred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `PNat.natPred_strictMono`：natPred_strictMono : StrictMono natPred
-/
theorem natPred_injective : Function.Injective natPred :=
  natPred_strictMono.injective

@[simp]
/-
**PNat.natPred_lt_natPred** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_lt_natPred {m n : Nat+} : m.natPred < n.natPred ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `PNat.natPred_strictMono`：natPred_strictMono : StrictMono natPred
-/
theorem natPred_lt_natPred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  natPred_strictMono.lt_iff_lt

@[simp]
/-
**PNat.natPred_le_natPred** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_le_natPred {m n : Nat+} : m.natPred <= n.natPred ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `PNat.natPred_strictMono`：natPred_strictMono : StrictMono natPred
-/
theorem natPred_le_natPred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  natPred_strictMono.le_iff_le

@[simp]
/-
**PNat.natPred_inj** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：natPred_inj {m n : Nat+} : m.natPred = n.natPred ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `PNat.natPred_injective`：natPred_injective : Function.Injective natPred
-/
theorem natPred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  natPred_injective.eq_iff

@[simp, norm_cast]
/-
**PNat.val_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `PNat`。
形式化陈述：val_ofNat (n : Nat) [NeZero n] : ((ofNat(n) : Nat+) : Nat) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_ofNat (n : ℕ) [NeZero n] :
    ((ofNat(n) : ℕ+) : ℕ) = OfNat.ofNat n :=
  rfl

@[simp]
/-
**PNat.mk_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `PNat`。
形式化陈述：mk_ofNat (n : Nat) (h : 0 < n) : @Eq Nat+ (⟨ofNat(n), h⟩ : Nat+) (haveI : 
NeZero n
参数：n : Nat；h : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_ofNat (n : ℕ) (h : 0 < n) :
    @Eq ℕ+ (⟨ofNat(n), h⟩ : ℕ+) (haveI : NeZero n := ⟨h.ne'⟩; OfNat.ofNat n) :=
  rfl

end PNat

namespace Nat

@[gcongr, mono]
/-
**Nat.succPNat_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_strictMono : StrictMono succPNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
-/
theorem succPNat_strictMono : StrictMono succPNat := fun _ _ => Nat.succ_lt_succ

@[gcongr, mono]
/-
**Nat.succPNat_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_mono : Monotone succPNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.succPNat_strictMono`：succPNat_strictMono : StrictMono succPNat
-/
theorem succPNat_mono : Monotone succPNat :=
  succPNat_strictMono.monotone

@[simp]
/-
**Nat.succPNat_lt_succPNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_lt_succPNat {m n : Nat} : m.succPNat < n.succPNat ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Nat.succPNat_strictMono`：succPNat_strictMono : StrictMono succPNat
-/
theorem succPNat_lt_succPNat {m n : ℕ} : m.succPNat < n.succPNat ↔ m < n :=
  succPNat_strictMono.lt_iff_lt

@[simp]
/-
**Nat.succPNat_le_succPNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_le_succPNat {m n : Nat} : m.succPNat <= n.succPNat ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Nat.succPNat_strictMono`：succPNat_strictMono : StrictMono succPNat
-/
theorem succPNat_le_succPNat {m n : ℕ} : m.succPNat ≤ n.succPNat ↔ m ≤ n :=
  succPNat_strictMono.le_iff_le
/-
**Nat.succPNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_injective : Function.Injective succPNat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Nat.succPNat_strictMono`：succPNat_strictMono : StrictMono succPNat
-/
theorem succPNat_injective : Function.Injective succPNat :=
  succPNat_strictMono.injective

@[simp]
/-
**Nat.succPNat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succPNat_inj {n m : Nat} : succPNat n = succPNat m ↔ n = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Nat.succPNat_injective`：succPNat_injective : Function.Injective succPNat
-/
theorem succPNat_inj {n m : ℕ} : succPNat n = succPNat m ↔ n = m :=
  succPNat_injective.eq_iff

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on `ℕ+` induced by
similar structures on `ℕ`. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
@[simp, norm_cast]
/-
**PNat.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2

--- 原说明 ---
We now define a long list of structures on `ℕ+` induced by
similar structures on `ℕ`. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  Subtype.ext_iff.symm

@[simp, norm_cast]
/-
**PNat.add_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：add_coe (m n : Nat+) : ((m + n : Nat+) : Nat) = m + n
参数：m n : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl

/-- `coe` promoted to an `AddHom`, that is, a morphism which preserves addition. -/
@[simps]
/-
**PNat.coeAddHom** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：coeAddHom : AddHom Nat+ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.add_coe`：add_coe (m n : Nat+) : ((m + n : Nat+) : Nat) = m + n

--- 原说明 ---
`coe` promoted to an `AddHom`, that is, a morphism which preserves addition.
-/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := (↑)
  map_add' := add_coe

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps! -fullyApplied apply]
/-
**PNat._root_.OrderIso.pnatIsoNat** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism between ℕ and ℕ+ given by `succ`.
-/
def _root_.OrderIso.pnatIsoNat : ℕ+ ≃o ℕ where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred

@[simp]
/-
**PNat._root_.OrderIso.pnatIsoNat_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.pnatIsoNat_symm_apply : OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl
/-
**PNat.lt_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lt_add_one_iff : forall {a b : Nat+}, a < b + 1 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
-/
theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := Nat.lt_add_one_iff
/-
**PNat.add_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：add_one_le_iff : forall {a b : Nat+}, a + 1 <= b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
-/
theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := Nat.add_one_le_iff
/-
**PNat.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instOrderBot : OrderBot Nat+ where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property
/-
**PNat.** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsBotOneClass ℕ+ where
  isBot_one a := a.2

@[simp]
/-
**PNat.bot_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：bot_eq_one : (⊥ : Nat+) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
/-
**PNat.caseStrongInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：caseStrongInductionOn {p : Nat+ -> Sort*} (a : Nat+) (hz : p 1) (hi : fora
ll n, (forall m, m <= n -> p m) -> p (n + 1)) : p a
参数：a : Nat+；hz : p 1；hi : forall n, (forall m, m <= n -> p m) -> p (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
Strong induction on `ℕ+`, with `n = 1` treated separately.
-/
def caseStrongInductionOn {p : ℕ+ → Sort*} (a : ℕ+) (hz : p 1)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  rcases k with - | k
  · exact (lt_irrefl 0 kprop).elim
  rcases k with - | k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim, induction_eliminator]
/-
**PNat.recOn** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：recOn (n : Nat+) {p : Nat+ -> Sort*} (one : p 1) (succ : forall n, p n -> 
p (n + 1)) : p n
参数：n : Nat+；one : p 1；succ : forall n, p n -> p (n + 1)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also 
to Types,
not only to `Prop`.
-/
def recOn (n : ℕ+) {p : ℕ+ → Sort*} (one : p 1) (succ : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction n with
  | zero => exact absurd h (by decide)
  | succ n IH =>
    rcases n with - | n
    · exact one
    · exact succ _ (IH n.succ_pos)

@[simp]
/-
**PNat.recOn_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：recOn_one {p} (one succ) : @PNat.recOn 1 p one succ = one
参数：one succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem recOn_one {p} (one succ) : @PNat.recOn 1 p one succ = one :=
  rfl

@[simp]
/-
**PNat.recOn_succ** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：recOn_succ (n : Nat+) {p : Nat+ -> Sort*} (one succ) : @PNat.recOn (n + 1)
 p one succ = succ n (@PNat.recOn n p one succ)
参数：n : Nat+；one succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem recOn_succ (n : ℕ+) {p : ℕ+ → Sort*} (one succ) :
    @PNat.recOn (n + 1) p one succ = succ n (@PNat.recOn n p one succ) := by
  obtain ⟨n, h⟩ := n
  cases n <;> [exact absurd h (by decide); rfl]

@[simp]
/-
**PNat.ofNat_le_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：ofNat_le_ofNat {m n : Nat} [NeZero m] [NeZero n] : (ofNat(m) : Nat+) <= of
Nat(n) ↔ OfNat.ofNat m <= OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofNat_le_ofNat {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) ≤ ofNat(n) ↔ OfNat.ofNat m ≤ OfNat.ofNat n :=
  .rfl

@[simp]
/-
**PNat.ofNat_lt_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：ofNat_lt_ofNat {m n : Nat} [NeZero m] [NeZero n] : (ofNat(m) : Nat+) < ofN
at(n) ↔ OfNat.ofNat m < OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofNat_lt_ofNat {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) < ofNat(n) ↔ OfNat.ofNat m < OfNat.ofNat n :=
  .rfl

@[simp]
/-
**PNat.ofNat_inj** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：ofNat_inj {m n : Nat} [NeZero m] [NeZero n] : (ofNat(m) : Nat+) = ofNat(n)
 ↔ OfNat.ofNat m = OfNat.ofNat n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
-/
theorem ofNat_inj {m n : ℕ} [NeZero m] [NeZero n] :
    (ofNat(m) : ℕ+) = ofNat(n) ↔ OfNat.ofNat m = OfNat.ofNat n :=
  Subtype.mk_eq_mk

@[simp, norm_cast]
/-
**PNat.mul_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
参数：m n : Nat+。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl

/-- `PNat.coe` promoted to a `MonoidHom`. -/
/-
**PNat.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `PNat`。
形式化陈述：coeMonoidHom : Nat+ ->* Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.one_coe`：one_coe : ((1 : Nat+) : Nat) = 1
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n

--- 原说明 ---
`PNat.coe` promoted to a `MonoidHom`.
-/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
/-
**PNat.coe_coeMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：coe_coeMonoidHom : (coeMonoidHom : Nat+ -> Nat) = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeMonoidHom : (coeMonoidHom : ℕ+ → ℕ) = (↑) :=
  rfl

@[deprecated le_one_iff_eq_one (since := "2026-05-07")]
/-
**PNat.le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：le_one_iff {n : Nat+} : n <= 1 ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.instIsBotOneClass`：IsBotOneClass ℕ+
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 := by
  simp
/-
**PNat.lt_add_left** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lt_add_left (n m : Nat+) : n < m + n
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_add_of_pos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, 0 < b → a < b + a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2
/-
**PNat.lt_add_right** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lt_add_right (n m : Nat+) : n < n + m
参数：n m : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `PNat.lt_add_left`：lt_add_left (n m : Nat+) : n < m + n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]
/-
**PNat.pow_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：pow_coe (m : Nat+) (n : Nat) : ↑(m ^ n) = (m : Nat) ^ n
参数：m : Nat+；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_coe (m : ℕ+) (n : ℕ) : ↑(m ^ n) = (m : ℕ) ^ n :=
  rfl

@[deprecated one_lt_of_gt (since := "2026-05-07")]
/-
**PNat.one_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：one_lt_of_lt {a b : Nat+} (hab : a < b) : 1 < b
参数：hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.one_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : O
ne α] [IsBotOneClass α], a < b → 1 < b
· 使用定理 `PNat.instIsBotOneClass`：IsBotOneClass ℕ+
-/
theorem one_lt_of_lt {a b : ℕ+} (hab : a < b) : 1 < b := hab.one_lt
/-
**PNat.add_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：add_one (a : Nat+) : a + 1 = succPNat a
参数：a : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem add_one (a : ℕ+) : a + 1 = succPNat a := rfl
/-
**PNat.lt_succ_self** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：lt_succ_self (a : Nat+) : a < succPNat a
参数：a : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
-/
theorem lt_succ_self (a : ℕ+) : a < succPNat a := Nat.lt_add_one a

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
/-
**PNat.instSub** 是 Mathlib 中的一个实例，位于命名空间 `PNat`。
形式化陈述：instSub : Sub Nat+
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance instSub : Sub ℕ+ :=
  ⟨fun a b => toPNat' (a - b : ℕ)⟩
/-
**PNat.sub_coe** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a) (a - b : Nat) 
1
参数：a b : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PNat.toPNat'_coe`：∀ {n : ℕ}, 0 < n → ↑n.toPNat' = n
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (toPNat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl
/-
**PNat.sub_le** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：sub_le (a b : Nat+) : a - b <= a
参数：a b : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coe_le_coe`：coe_le_coe (n k : Nat+) : (n : Nat) <= k ↔ n <= k
· 使用定理 `PNat.sub_coe`：sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a
) (a - b : Nat) 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sub_le (a b : ℕ+) : a - b ≤ a := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2
/-
**PNat.le_sub_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：le_sub_one_of_lt {a b : Nat+} (hab : a < b) : a <= b - (1 : Nat+)
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.coe_le_coe`：coe_le_coe (n k : Nat+) : (n : Nat) <= k ↔ n <= k
· 使用定理 `PNat.sub_coe`：sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a
) (a - b : Nat) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
theorem le_sub_one_of_lt {a b : ℕ+} (hab : a < b) : a ≤ b - (1 : ℕ+) := by
  rw [← coe_le_coe, sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)
/-
**PNat.add_sub_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：add_sub_of_lt {a b : Nat+} : a < b -> a + (b - a) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.add_coe`：add_coe (m n : Nat+) : ((m + n : Nat+) : Nat) = m + n
· 使用定理 `PNat.sub_coe`：sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a
) (a - b : Nat) 1
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
  fun h =>
    PNat.eq <| by
      rw [add_coe, sub_coe, if_pos h]
      exact add_tsub_cancel_of_le h.le
/-
**PNat.sub_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：sub_add_of_lt {a b : Nat+} (h : b < a) : a - b + b = a
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `PNat.add_sub_of_lt`：add_sub_of_lt {a b : Nat+} : a < b -> a + (b - a) = 
b
-/
theorem sub_add_of_lt {a b : ℕ+} (h : b < a) : a - b + b = a := by
  rw [add_comm, add_sub_of_lt h]

@[simp]
/-
**PNat.add_sub** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：add_sub {a b : Nat+} : a + b - b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `instAddLeftReflectLEPNat`：AddLeftReflectLE ℕ+
· 使用定理 `PNat.sub_add_of_lt`：sub_add_of_lt {a b : Nat+} (h : b < a) : a - b + b =
 a
· 使用定理 `PNat.lt_add_left`：lt_add_left (n m : Nat+) : n < m + n
-/
theorem add_sub {a b : ℕ+} : a + b - b = a :=
  add_right_cancel (sub_add_of_lt (lt_add_left _ _))

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
/-
**PNat.exists_eq_succ_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ {n : ℕ+}, n ≠ 1 → ∃ k, n = k + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`.
-/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (_ : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h₁ => False.elim <| h₁ rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩

/-- Lemmas with div, dvd and mod operations -/
/-
**PNat.modDivAux_spec** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：∀ (k : ℕ+) (r q : ℕ), ¬(r = 0 ∧ q = 0) → ↑(k.modDivAux r q).1 + ↑k * (k.mo
dDivAux r q).2 = r + ↑k * q
参数：k : ℕ+；r q : ℕ；r = 0 ∧ q = 0；k.modDivAux r q；k.modDivAux r q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pred_succ`：∀ (n : ℕ), n.succ.pred = n
· 使用定理 `Nat.mul_succ`：∀ (n m : ℕ), n * m.succ = n * m + n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
Lemmas with div, dvd and mod operations
-/
theorem modDivAux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (_ : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | _, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, _ => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | _, _ + 1, _, _ => rfl
/-
**PNat.mod_add_div** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mod_add_div (m k : Nat+) : (mod m k + k * div m k : Nat) = m
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `PNat.ne_zero`：ne_zero (n : Nat+) : (n : Nat) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PNat.modDivAux_spec`：∀ (k : ℕ+) (r q : ℕ), ¬(r = 0 ∧ q = 0) → ↑(k.modDiv
Aux r q).1 + ↑k * (k.modDivAux r q).2 = r + ↑k * q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀
/-
**PNat.div_add_mod** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：div_add_mod (m k : Nat+) : (k * div m k + mod m k : Nat) = m
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `PNat.mod_add_div`：mod_add_div (m k : Nat+) : (mod m k + k * div m k : Na
t) = m
-/
theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)
/-
**PNat.mod_add_div'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mod_add_div' (m k : Nat+) : (mod m k + div m k * k : Nat) = m
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PNat.mod_add_div`：mod_add_div (m k : Nat+) : (mod m k + k * div m k : Na
t) = m
-/
theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _
/-
**PNat.div_add_mod'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：div_add_mod' (m k : Nat+) : (div m k * k + mod m k : Nat) = m
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PNat.div_add_mod`：div_add_mod (m k : Nat+) : (k * div m k + mod m k : Na
t) = m
-/
theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _
/-
**PNat.mod_le** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mod_le (m k : Nat+) : mod m k <= m ∧ mod m k <= k
参数：m k : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.mod_coe`：mod_coe (m k : Nat+) : (mod m k : Nat) = ite ((m : Nat) % 
(k : Nat) = 0) (k : Nat) ((m : Nat) % (k : Nat))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.mod_le`：∀ (x y : ℕ), x % y ≤ x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
-/
theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm ⊢
    simp
    lia
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩

set_option backward.isDefEq.respectTransparency false in
/-
**PNat.dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `PNat.coe_inj`：coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
· 使用定理 `PNat.mk_coe`：mk_coe (n h) : (PNat.val (⟨n, h⟩ : Nat+) : Nat) = n
-/
theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) <| by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj, h, mul_coe, mk_coe]
/-
**PNat.dvd_iff'** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_iff' {k m : Nat+} : k ∣ m ↔ mod m k = k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff`：dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat)
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `PNat.mod_coe`：mod_coe (m k : Nat+) : (mod m k : Nat) = ite ((m : Nat) % 
(k : Nat) = 0) (k : Nat) ((m : Nat) % (k : Nat))
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe, if_pos h]
  · intro h
    by_cases h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).ne h).elim
/-
**PNat.le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：le_of_dvd {m n : Nat+} : m ∣ n -> m <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.dvd_iff'`：dvd_iff' {k m : Nat+} : k ∣ m ↔ mod m k = k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PNat.mod_le`：mod_le (m k : Nat+) : mod m k <= m ∧ mod m k <= k
-/
theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left
/-
**PNat.mul_div_exact** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：mul_div_exact {m k : Nat+} (h : k ∣ m) : k * divExact m k = m
参数：h : k ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PNat.eq`：eq {m n : Nat+} : (m : Nat) = n -> m = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.mul_coe`：mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PNat.div_add_mod`：div_add_mod (m k : Nat+) : (k * div m k + mod m k : Na
t) = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PNat.dvd_iff'`：dvd_iff' {k m : Nat+} : k ∣ m ↔ mod m k = k
· 使用定理 `Nat.mul_succ`：∀ (n m : ℕ), n * m.succ = n * m + n
-/
theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply PNat.eq; rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]
/-
**PNat.dvd_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_antisymm {m n : Nat+} : m ∣ n -> n ∣ m -> m = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `PNat.le_of_dvd`：le_of_dvd {m n : Nat+} : m ∣ n -> m <= n
-/
theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)
/-
**PNat.dvd_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：dvd_one_iff (n : Nat+) : n ∣ 1 ↔ n = 1
参数：n : Nat+。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `PNat.dvd_antisymm`：dvd_antisymm {m n : Nat+} : m ∣ n -> n ∣ m -> m = n
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩
/-
**PNat.pos_of_div_pos** 是 Mathlib 中的一个定理，位于命名空间 `PNat`。
形式化陈述：pos_of_div_pos {n : Nat+} {a : Nat} (h : a ∣ n) : 0 < a
参数：h : a ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `PNat.ne_zero`：ne_zero (n : Nat+) : (n : Nat) != 0
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

end PNat

