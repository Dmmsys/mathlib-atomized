/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Tactic.ApplyFun

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `Data.Sym.Sym2`.

TODO: This was created as supporting material for `Sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

@[expose] public section

assert_not_exists MonoidWithZero
open List (Vector)
open Function

/-- The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `Multiset` since these are well developed in the
library.  We also give a definition `Sym.sym'` in terms of vectors, and we
show these are equivalent in `Sym.symEquivSym'`.
-/
/-
**Sym** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Sym (α : Type*) (n : Nat)
参数：α : Type*；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `Multiset` since these are well developed in the
library.  We also give a definition `Sym.sym'` in terms of vectors, and we
show these are equivalent in `Sym.symEquivSym'`.
-/
def Sym (α : Type*) (n : ℕ) :=
  { s : Multiset α // Multiset.card s = n }
deriving [DecidableEq α] → DecidableEq _

/-- The canonical map to `Multiset α` that forgets that `s` has length `n` -/
/-
**Sym.toMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：{α : Type u_1} → {n : ℕ} → Sym α n → Multiset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map to `Multiset α` that forgets that `s` has length `n`
-/
@[coe] def Sym.toMultiset {α : Type*} {n : ℕ} (s : Sym α n) : Multiset α :=
  s.1
/-
**Sym.hasCoe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sym.hasCoe (α : Type*) (n : Nat) : CoeOut (Sym α n) (Multiset α)
参数：α : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sym.hasCoe (α : Type*) (n : ℕ) : CoeOut (Sym α n) (Multiset α) :=
  ⟨Sym.toMultiset⟩

/-- This is the `List.Perm` setoid lifted to `Vector`.

See note [reducible non-instances].
-/
/-
**List.Vector.Perm.isSetoid** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：List.Vector.Perm.isSetoid (α : Type*) (n : Nat) : Setoid (Vector α n)
参数：α : Type*；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `List.Perm` setoid lifted to `Vector`.

See note [reducible non-instances].
-/
abbrev List.Vector.Perm.isSetoid (α : Type*) (n : ℕ) : Setoid (Vector α n) :=
  (List.isSetoid α).comap Subtype.val

attribute [local instance] Vector.Perm.isSetoid

-- Copy over the `DecidableRel` instance across the definition.
-- (Although `List.Vector.Perm.isSetoid` is an `abbrev`, `List.isSetoid` is not.)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} {n : ℕ} [DecidableEq α] :
    DecidableRel (· ≈ · : List.Vector α n → List.Vector α n → Prop) :=
  fun _ _ => List.decidablePerm _ _

namespace Sym

variable {α β : Type*} {n n' m : ℕ} {s : Sym α n} {a b : α}

/-
**Sym.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_injective : Injective ((↑) : Sym α n -> Multiset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_injective : Injective ((↑) : Sym α n → Multiset α) :=
  Subtype.coe_injective

@[simp, norm_cast]
/-
**Sym.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
-/
theorem coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s₂ :=
  coe_injective.eq_iff
/-
**Sym.ext** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {s₁ s₂ : Sym α n}, ↑s₁ = ↑s₂ → s₁ = s₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
-/
@[ext] theorem ext {s₁ s₂ : Sym α n} (h : (s₁ : Multiset α) = ↑s₂) : s₁ = s₂ :=
  coe_injective h

@[simp]
/-
**Sym.val_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：val_eq_coe (s : Sym α n) : s.1 = ↑s
参数：s : Sym α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_coe (s : Sym α n) : s.1 = ↑s :=
  rfl

/-- Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[match_pattern]
/-
**Sym.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Sym`。
形式化陈述：mk (m : Multiset α) (h : Multiset.card m = n) : Sym α n
参数：m : Multiset α；h : Multiset.card m = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an element of the `n`th symmetric power from a multiset of cardinality
 `n`.
-/
abbrev mk (m : Multiset α) (h : Multiset.card m = n) : Sym α n :=
  ⟨m, h⟩

/-- The unique element in `Sym α 0`. -/
@[match_pattern]
/-
**Sym.nil** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：nil : Sym α 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_zero`：card_zero : @card α 0 = 0

--- 原说明 ---
The unique element in `Sym α 0`.
-/
def nil : Sym α 0 :=
  ⟨0, Multiset.card_zero⟩

@[simp]
/-
**Sym.coe_nil** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_nil : ↑(@Sym.nil α) = (0 : Multiset α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nil : ↑(@Sym.nil α) = (0 : Multiset α) :=
  rfl

/-- Inserts an element into the term of `Sym α n`, increasing the length by one.
-/
@[match_pattern]
/-
**Sym.cons** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：cons (a : α) (s : Sym α n) : Sym α n.succ
参数：a : α；s : Sym α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inserts an element into the term of `Sym α n`, increasing the length by one.
-/
def cons (a : α) (s : Sym α n) : Sym α n.succ :=
  ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩

@[inherit_doc]
infixr:67 " ::ₛ " => cons

@[simp]
/-
**Sym.cons_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_inj_right (a : α) (s s' : Sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s'
参数：a : α；s s' : Sym α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Multiset.cons_inj_right`：cons_inj_right (a : α) : forall {s t : Multiset
 α}, a ::ₘ s = a ::ₘ t ↔ s = t
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem cons_inj_right (a : α) (s s' : Sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s' :=
  Subtype.ext_iff.trans <| (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]
/-
**Sym.cons_inj_left** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_inj_left (a a' : α) (s : Sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a'
参数：a a' : α；s : Sym α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Multiset.cons_inj_left`：cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ
 s = b ::ₘ s ↔ a = b
-/
theorem cons_inj_left (a a' : α) (s : Sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a' :=
  Subtype.ext_iff.trans <| Multiset.cons_inj_left _
/-
**Sym.cons_swap** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_swap (a b : α) (s : Sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s
参数：a b : α；s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
-/
theorem cons_swap (a b : α) (s : Sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s :=
  Subtype.ext <| Multiset.cons_swap a b s.1
/-
**Sym.coe_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_cons (s : Sym α n) (a : α) : (a ::ₛ s : Multiset α) = a ::ₘ s
参数：s : Sym α n；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_cons (s : Sym α n) (a : α) : (a ::ₛ s : Multiset α) = a ::ₘ s :=
  rfl

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
/-
**Sym.ofVector** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：ofVector : List.Vector α n -> Sym α n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the quotient map that takes a list of n elements as an n-tuple and produ
ces an nth
symmetric power.
-/
def ofVector : List.Vector α n → Sym α n :=
  fun x => ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the quotient map that takes a list of n elements as an n-tuple and produ
ces an nth
symmetric power.
-/
instance : Coe (List.Vector α n) (Sym α n) where coe x := ofVector x

@[simp]
/-
**Sym.ofVector_nil** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：ofVector_nil : ↑(Vector.nil : List.Vector α 0) = (Sym.nil : Sym α 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofVector_nil : ↑(Vector.nil : List.Vector α 0) = (Sym.nil : Sym α 0) :=
  rfl

@[simp]
/-
**Sym.ofVector_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：ofVector_cons (a : α) (v : List.Vector α n) : ↑(Vector.cons a v) = a ::ₛ (
↑v : Sym α n)
参数：a : α；v : List.Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ofVector_cons (a : α) (v : List.Vector α n) :
    ↑(Vector.cons a v) = a ::ₛ (↑v : Sym α n) := by
  cases v
  rfl

@[simp]
/-
**Sym.card_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：card_coe : Multiset.card (s : Multiset α) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem card_coe : Multiset.card (s : Multiset α) = n := s.prop

/-- `α ∈ s` means that `a` appears as one of the factors in `s`.
-/
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : Membership α (Sym α n) :=
  ⟨fun s a => a ∈ s.1⟩
/-
**Sym.decidableMem** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a in s)
参数：a : α；s : Sym α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a ∈ s) :=
  s.1.decidableMem _
/-
**Sym.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} (s : Multiset α) (h : s.card = n), ↑(Sym.mk s h) 
= s
参数：s : Multiset α；h : s.card = n；Sym.mk s h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (s : Multiset α) (h : Multiset.card s = n) : mk s h = s := rfl

@[simp]
/-
**Sym.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_mk (a : α) (s : Multiset α) (h : Multiset.card s = n) : a in mk s h ↔ 
a in s
参数：a : α；s : Multiset α；h : Multiset.card s = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (a : α) (s : Multiset α) (h : Multiset.card s = n) : a ∈ mk s h ↔ a ∈ s :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Sym.** 是 Mathlib 中的一个引理，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «forall» {p : Sym α n → Prop} :
    (∀ s : Sym α n, p s) ↔ ∀ (s : Multiset α) (hs : Multiset.card s = n), p (Sym.mk s hs) := by
  simp [Sym]

set_option backward.isDefEq.respectTransparency false in
/-
**Sym.** 是 Mathlib 中的一个引理，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma «exists» {p : Sym α n → Prop} :
    (∃ s : Sym α n, p s) ↔ ∃ (s : Multiset α) (hs : Multiset.card s = n), p (Sym.mk s hs) := by
  simp [Sym]

@[simp]
/-
**Sym.notMem_nil** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：notMem_nil (a : α) : a ∉ (nil : Sym α 0)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
-/
theorem notMem_nil (a : α) : a ∉ (nil : Sym α 0) :=
  Multiset.notMem_zero a

@[simp]
/-
**Sym.mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_cons : a in b ::ₛ s ↔ a = b ∨ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
-/
theorem mem_cons : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s :=
  Multiset.mem_cons

@[simp]
/-
**Sym.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_coe : a in (s : Multiset α) ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe : a ∈ (s : Multiset α) ↔ a ∈ s :=
  Iff.rfl
/-
**Sym.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_cons_of_mem (h : a in s) : a in b ::ₛ s
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
-/
theorem mem_cons_of_mem (h : a ∈ s) : a ∈ b ::ₛ s :=
  Multiset.mem_cons_of_mem h
/-
**Sym.mem_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_cons_self (a : α) (s : Sym α n) : a in a ::ₛ s
参数：a : α；s : Sym α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
theorem mem_cons_self (a : α) (s : Sym α n) : a ∈ a ::ₛ s :=
  Multiset.mem_cons_self a s.1
/-
**Sym.cons_of_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_of_coe_eq (a : α) (v : List.Vector α n) : a ::ₛ (↑v : Sym α n) = ↑(a 
::ᵥ v)
参数：a : α；v : List.Vector α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_of_coe_eq (a : α) (v : List.Vector α n) : a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v) :=
  Subtype.ext <| by
    cases v
    rfl

open scoped List in
/-
**Sym.sound** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：sound {a b : List.Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b
参数：h : a.val ~ b.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem sound {a b : List.Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b :=
  Subtype.ext <| Quotient.sound h

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if `a` is present in the sym. -/
/-
**Sym.erase** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a in s) : Sym α n
参数：s : Sym α (n + 1)；a : α；h : a in s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if `a` is present in the sym.
-/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : Sym α n :=
  ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans <| s.property.symm ▸ n.pred_succ⟩

@[simp]
/-
**Sym.erase_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：erase_mk [DecidableEq α] (m : Multiset α) (hc : Multiset.card m = n + 1) (
a : α) (h : a in m) : (mk m hc).erase a h = mk (m.erase a) (by rw [Multiset.card
_erase_of_mem h, hc, Nat.add_one, Nat.pred_succ])
参数：m : Multiset α；hc : Multiset.card m = n + 1；a : α；h : a in m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_mk [DecidableEq α] (m : Multiset α)
    (hc : Multiset.card m = n + 1) (a : α) (h : a ∈ m) :
    (mk m hc).erase a h = mk (m.erase a)
        (by rw [Multiset.card_erase_of_mem h, hc, Nat.add_one, Nat.pred_succ]) :=
  rfl

@[simp]
/-
**Sym.coe_erase** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s) : (s.era
se a h : Multiset α) = Multiset.erase s a
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) :
    (s.erase a h : Multiset α) = Multiset.erase s a :=
  rfl

@[simp]
/-
**Sym.cons_erase** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a in s) : a ::ₛ
 s.erase a h = s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
-/
theorem cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) : a ::ₛ s.erase a h = s :=
  coe_injective <| Multiset.cons_erase h

@[simp]
/-
**Sym.erase_cons_head** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：erase_cons_head [DecidableEq α] (s : Sym α n) (a : α) (h : a in a ::ₛ s
参数：s : Sym α n；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
-/
theorem erase_cons_head [DecidableEq α] (s : Sym α n) (a : α)
    (h : a ∈ a ::ₛ s := mem_cons_self a s) : (a ::ₛ s).erase a h = s :=
  coe_injective <| Multiset.erase_cons_head a s.1

/-- Another definition of the nth symmetric power, using vectors modulo permutations. (See `Sym`.)
-/
/-
**Sym.Sym'** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：Sym' (α : Type*) (n : Nat)
参数：α : Type*；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another definition of the nth symmetric power, using vectors modulo permutations
. (See `Sym`.)
-/
def Sym' (α : Type*) (n : ℕ) :=
  Quotient (Vector.Perm.isSetoid α n)

/-- This is `cons` but for the alternative `Sym'` definition.
-/
/-
**Sym.cons'** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：cons' {α : Type*} {n : Nat} : α -> Sym' α n -> Sym' α (Nat.succ n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `cons` but for the alternative `Sym'` definition.
-/
def cons' {α : Type*} {n : ℕ} : α → Sym' α n → Sym' α (Nat.succ n) := fun a =>
  Quotient.map (Vector.cons a) fun ⟨_, _⟩ ⟨_, _⟩ h => List.Perm.cons _ h

@[inherit_doc]
scoped notation a " :: " b => cons' a b

/-- Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
/-
**Sym.symEquivSym'** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：symEquivSym' {α : Type*} {n : Nat} : Sym α n ≃ Sym' α n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multisets of cardinality n are equivalent to length-n vectors up to permutations
.
-/
def symEquivSym' {α : Type*} {n : ℕ} : Sym α n ≃ Sym' α n :=
  Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl
/-
**Sym.cons_equiv_eq_equiv_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cons_equiv_eq_equiv_cons (α : Type*) (n : Nat) (a : α) (s : Sym α n) : (a 
:: symEquivSym' s) = symEquivSym' (a ::ₛ s)
参数：α : Type*；n : Nat；a : α；s : Sym α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_equiv_eq_equiv_cons (α : Type*) (n : ℕ) (a : α) (s : Sym α n) :
    (a :: symEquivSym' s) = symEquivSym' (a ::ₛ s) := by
  rcases s with ⟨⟨l⟩, _⟩
  rfl
/-
**Sym.instZeroSym** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：instZeroSym : Zero (Sym α 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZeroSym : Zero (Sym α 0) :=
  ⟨⟨0, rfl⟩⟩
/-
**Sym.toMultiset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：∀ {α : Type u_1}, ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toMultiset_zero : toMultiset (0 : Sym α 0) = 0 := rfl
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmptyCollection (Sym α 0) :=
  ⟨0⟩
/-
**Sym.eq_nil_of_card_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：eq_nil_of_card_zero (s : Sym α 0) : s = nil
参数：s : Sym α 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem eq_nil_of_card_zero (s : Sym α 0) : s = nil :=
  Subtype.ext <| Multiset.card_eq_zero.1 s.2
/-
**Sym.uniqueZero** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：uniqueZero : Unique (Sym α 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.eq_nil_of_card_zero`：eq_nil_of_card_zero (s : Sym α 0) : s = nil
-/
instance uniqueZero : Unique (Sym α 0) :=
  ⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `replicate n a` is the sym containing only `a` with multiplicity `n`. -/
/-
**Sym.replicate** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：replicate (n : Nat) (a : α) : Sym α n
参数：n : Nat；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n

--- 原说明 ---
`replicate n a` is the sym containing only `a` with multiplicity `n`.
-/
def replicate (n : ℕ) (a : α) : Sym α n :=
  ⟨Multiset.replicate n a, Multiset.card_replicate _ _⟩
/-
**Sym.replicate_succ** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：replicate_succ {a : α} {n : Nat} : replicate n.succ a = a ::ₛ replicate n 
a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicate_succ {a : α} {n : ℕ} : replicate n.succ a = a ::ₛ replicate n a :=
  rfl
/-
**Sym.coe_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_replicate : (replicate n a : Multiset α) = Multiset.replicate n a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_replicate : (replicate n a : Multiset α) = Multiset.replicate n a :=
  rfl
/-
**Sym.val_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：val_replicate : (replicate n a).val = Multiset.replicate n a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.val_eq_coe`：val_eq_coe (s : Sym α n) : s.1 = ↑s
· 使用定理 `Sym.coe_replicate`：coe_replicate : (replicate n a : Multiset α) = Multis
et.replicate n a
-/
theorem val_replicate : (replicate n a).val = Multiset.replicate n a := by
  rw [val_eq_coe, coe_replicate]

@[simp]
/-
**Sym.mem_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_replicate : b in replicate n a ↔ n != 0 ∧ b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_replicate`：mem_replicate {a b : α} {n : Nat} : b in replica
te n a ↔ n != 0 ∧ b = a
-/
theorem mem_replicate : b ∈ replicate n a ↔ n ≠ 0 ∧ b = a :=
  Multiset.mem_replicate

set_option backward.isDefEq.respectTransparency false in
/-
**Sym.eq_replicate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：eq_replicate_iff : s = replicate n a ↔ forall b in s, b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Sym.val_replicate`：val_replicate : (replicate n a).val = Multiset.replic
ate n a
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem eq_replicate_iff : s = replicate n a ↔ ∀ b ∈ s, b = a := by
  rw [Subtype.ext_iff, val_replicate, Multiset.eq_replicate]
  exact and_iff_right s.2
/-
**Sym.exists_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：exists_mem (s : Sym α n.succ) : exists a, a in s
参数：s : Sym α n.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_pos_iff_exists_mem`：card_pos_iff_exists_mem {s : Multiset 
α} : 0 < card s ↔ exists a, a in s
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem exists_mem (s : Sym α n.succ) : ∃ a, a ∈ s :=
  Multiset.card_pos_iff_exists_mem.1 <| s.2.symm ▸ n.succ_pos
/-
**Sym.exists_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：exists_cons_of_mem {s : Sym α (n + 1)} {a : α} (h : a in s) : exists t, s 
= a ::ₛ t
参数：n + 1；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem exists_cons_of_mem {s : Sym α (n + 1)} {a : α} (h : a ∈ s) : ∃ t, s = a ::ₛ t := by
  obtain ⟨m, h⟩ := Multiset.exists_cons_of_mem h
  have : Multiset.card m = n := by
    apply_fun Multiset.card at h
    rw [s.2, Multiset.card_cons, add_left_inj] at h
    exact h.symm
  use ⟨m, this⟩
  apply Subtype.ext
  exact h
/-
**Sym.exists_eq_cons_of_succ** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：exists_eq_cons_of_succ (s : Sym α n.succ) : exists (a : α) (s' : Sym α n),
 s = a ::ₛ s'
参数：s : Sym α n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.exists_mem`：exists_mem (s : Sym α n.succ) : exists a, a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.cons_erase`：cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h
 : a in s) : a ::ₛ s.erase a h = s
-/
theorem exists_eq_cons_of_succ (s : Sym α n.succ) : ∃ (a : α) (s' : Sym α n), s = a ::ₛ s' := by
  obtain ⟨a, ha⟩ := exists_mem s
  classical exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩
/-
**Sym.eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：eq_replicate {a : α} {n : Nat} {s : Sym α n} : s = replicate n a ↔ forall 
b in s, b = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem eq_replicate {a : α} {n : ℕ} {s : Sym α n} : s = replicate n a ↔ ∀ b ∈ s, b = a :=
  Subtype.ext_iff.trans <| Multiset.eq_replicate.trans <| and_iff_right s.prop
/-
**Sym.eq_replicate_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：eq_replicate_of_subsingleton [Subsingleton α] (a : α) {n : Nat} (s : Sym α
 n) : s = replicate n a
参数：a : α；s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym.eq_replicate`：eq_replicate {a : α} {n : Nat} {s : Sym α n} : s = rep
licate n a ↔ forall b in s, b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_replicate_of_subsingleton [Subsingleton α] (a : α) {n : ℕ} (s : Sym α n) :
    s = replicate n a :=
  eq_replicate.2 fun _ _ => Subsingleton.elim _ _
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] (n : ℕ) : Subsingleton (Sym α n) :=
  ⟨by
    cases n
    · simp [eq_iff_true_of_subsingleton]
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_replicate_of_subsingleton b s', eq_replicate_of_subsingleton b s]⟩
/-
**Sym.inhabitedSym** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：inhabitedSym [Inhabited α] (n : Nat) : Inhabited (Sym α n)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedSym [Inhabited α] (n : ℕ) : Inhabited (Sym α n) :=
  ⟨replicate n default⟩
/-
**Sym.inhabitedSym'** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
形式化陈述：inhabitedSym' [Inhabited α] (n : Nat) : Inhabited (Sym' α n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance inhabitedSym' [Inhabited α] (n : ℕ) : Inhabited (Sym' α n) :=
  ⟨Quotient.mk' (List.Vector.replicate n default)⟩
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [IsEmpty α] : IsEmpty (Sym α n.succ) :=
  ⟨fun s => by
    obtain ⟨a, -⟩ := exists_mem s
    exact isEmptyElim a⟩
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [Unique α] : Unique (Sym α n) :=
  Unique.mk' _
/-
**Sym.replicate_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：replicate_right_inj {a b : α} {n : Nat} (h : n != 0) : replicate n a = rep
licate n b ↔ a = b
参数：h : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Multiset.replicate_right_inj`：∀ {α : Type u_1} {a b : α} {n : ℕ}, n ≠ 0 
→ (Multiset.replicate n a = Multiset.replicate n b ↔ a = b)
-/
theorem replicate_right_inj {a b : α} {n : ℕ} (h : n ≠ 0) : replicate n a = replicate n b ↔ a = b :=
  Subtype.ext_iff.trans (Multiset.replicate_right_inj h)
/-
**Sym.replicate_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：replicate_right_injective {n : Nat} (h : n != 0) : Function.Injective (rep
licate n : α -> Sym α n)
参数：h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym.replicate_right_inj`：replicate_right_inj {a b : α} {n : Nat} (h : n 
!= 0) : replicate n a = replicate n b ↔ a = b
-/
theorem replicate_right_injective {n : ℕ} (h : n ≠ 0) :
    Function.Injective (replicate n : α → Sym α n) := fun _ _ => (replicate_right_inj h).1
/-
**Sym.** 是 Mathlib 中的一个实例，位于命名空间 `Sym`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) [Nontrivial α] : Nontrivial (Sym α (n + 1)) :=
  (replicate_right_injective n.succ_ne_zero).nontrivial

/-- A function `α → β` induces a function `Sym α n → Sym β n` by applying it to every element of
the underlying `n`-tuple. -/
/-
**Sym.map** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：map {n : Nat} (f : α -> β) (x : Sym α n) : Sym β n
参数：f : α -> β；x : Sym α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `α → β` induces a function `Sym α n → Sym β n` by applying it to ever
y element of
the underlying `n`-tuple.
-/
def map {n : ℕ} (f : α → β) (x : Sym α n) : Sym β n :=
  ⟨x.val.map f, by simp⟩

@[simp]
/-
**Sym.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_map {n : Nat} {f : α -> β} {b : β} {l : Sym α n} : b in Sym.map f l ↔ 
exists a, a in l ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem mem_map {n : ℕ} {f : α → β} {b : β} {l : Sym α n} :
    b ∈ Sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  Multiset.mem_map

set_option backward.isDefEq.respectTransparency false in
/-- Note: `Sym.map_id` is not simp-normal, as simp ends up unfolding `id` with `Sym.map_congr` -/
@[simp]
/-
**Sym.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_id' {α : Type*} {n : Nat} (s : Sym α n) : Sym.map (fun x : α => x) s =
 s
参数：s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.ext`：∀ {α : Type u_1} {n : ℕ} {s₁ s₂ : Sym α n}, ↑s₁ = ↑s₂ → s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note: `Sym.map_id` is not simp-normal, as simp ends up unfolding `id` with `Sym.
map_congr`
-/
theorem map_id' {α : Type*} {n : ℕ} (s : Sym α n) : Sym.map (fun x : α => x) s = s := by
  ext; simp only [map, Multiset.map_id', ← val_eq_coe]

set_option backward.isDefEq.respectTransparency false in
/-
**Sym.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_id {α : Type*} {n : Nat} (s : Sym α n) : Sym.map id s = s
参数：s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.ext`：∀ {α : Type u_1} {n : ℕ} {s₁ s₂ : Sym α n}, ↑s₁ = ↑s₂ → s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id {α : Type*} {n : ℕ} (s : Sym α n) : Sym.map id s = s := by
  ext; simp only [map, id_eq, Multiset.map_id', ← val_eq_coe]

@[simp]
/-
**Sym.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_map {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β) (s : Sym α n) 
: Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s
参数：g : β -> γ；f : α -> β；s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : Sym α n) :
    Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s :=
  Subtype.ext <| by dsimp only [Sym.map]; simp

@[simp]
/-
**Sym.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_zero (f : α -> β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_zero (f : α → β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
  rfl

@[simp]
/-
**Sym.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_cons {n : Nat} (f : α -> β) (a : α) (s : Sym α n) : (a ::ₛ s).map f = 
f a ::ₛ s.map f
参数：f : α -> β；a : α；s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.ext`：∀ {α : Type u_1} {n : ℕ} {s₁ s₂ : Sym α n}, ↑s₁ = ↑s₂ → s₁ = s₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem map_cons {n : ℕ} (f : α → β) (a : α) (s : Sym α n) : (a ::ₛ s).map f = f a ::ₛ s.map f :=
  ext <| Multiset.map_cons _ _ _

@[congr]
/-
**Sym.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_congr {f g : α -> β} {s : Sym α n} (h : forall x in s, f x = g x) : ma
p f s = map g s
参数：h : forall x in s, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
-/
theorem map_congr {f g : α → β} {s : Sym α n} (h : ∀ x ∈ s, f x = g x) : map f s = map g s :=
  Subtype.ext <| Multiset.map_congr rfl h

@[simp]
/-
**Sym.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_mk {f : α -> β} {m : Multiset α} {hc : Multiset.card m = n} : map f (m
k m hc) = mk (m.map f) (by simp [hc])
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk {f : α → β} {m : Multiset α} {hc : Multiset.card m = n} :
    map f (mk m hc) = mk (m.map f) (by simp [hc]) :=
  rfl

@[simp]
/-
**Sym.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_map (s : Sym α n) (f : α -> β) : ↑(s.map f) = Multiset.map f s
参数：s : Sym α n；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (s : Sym α n) (f : α → β) : ↑(s.map f) = Multiset.map f s :=
  rfl
/-
**Sym.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：map_injective {f : α -> β} (hf : Injective f) (n : Nat) : Injective (map f
 : Sym α n -> Sym β n)
参数：hf : Injective f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym.coe_inj`：coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s
₂
-/
theorem map_injective {f : α → β} (hf : Injective f) (n : ℕ) :
    Injective (map f : Sym α n → Sym β n) := fun _ _ h =>
  coe_injective <| Multiset.map_injective hf <| coe_inj.2 h

/-- Mapping an equivalence `α ≃ β` using `Sym.map` gives an equivalence between `Sym α n` and
`Sym β n`. -/
@[simps]
/-
**Sym.equivCongr** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：equivCongr (e : α ≃ β) : Sym α n ≃ Sym β n where toFun
参数：e : α ≃ β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Mapping an equivalence `α ≃ β` using `Sym.map` gives an equivalence between `Sym
 α n` and
`Sym β n`.
-/
def equivCongr (e : α ≃ β) : Sym α n ≃ Sym β n where
  toFun := map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
an element of the symmetric power on `{x // x ∈ s}`. -/
/-
**Sym.attach** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：attach (s : Sym α n) : Sym { x // x in s } n
参数：s : Sym α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
an element of the symmetric power on `{x // x ∈ s}`.
-/
def attach (s : Sym α n) : Sym { x // x ∈ s } n :=
  ⟨s.val.attach, by (conv_rhs => rw [← s.2, ← Multiset.card_attach])⟩

@[simp]
/-
**Sym.attach_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：attach_mk {m : Multiset α} {hc : Multiset.card m = n} : attach (mk m hc) =
 mk m.attach (Multiset.card_attach.trans hc)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem attach_mk {m : Multiset α} {hc : Multiset.card m = n} :
    attach (mk m hc) = mk m.attach (Multiset.card_attach.trans hc) :=
  rfl

@[simp]
/-
**Sym.coe_attach** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_attach (s : Sym α n) : (s.attach : Multiset { a // a in s }) = Multise
t.attach (s : Multiset α)
参数：s : Sym α n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_attach (s : Sym α n) : (s.attach : Multiset { a // a ∈ s }) =
    Multiset.attach (s : Multiset α) :=
  rfl
/-
**Sym.attach_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：attach_map_coe (s : Sym α n) : s.attach.map (↑) = s
参数：s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
-/
theorem attach_map_coe (s : Sym α n) : s.attach.map (↑) = s :=
  coe_injective <| Multiset.attach_map_val _

@[simp]
/-
**Sym.mem_attach** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_attach (s : Sym α n) (x : { x // x in s }) : x in s.attach
参数：s : Sym α n；x : { x // x in s }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_attach`：mem_attach (s : Multiset α) : forall x, x in s.atta
ch
-/
theorem mem_attach (s : Sym α n) (x : { x // x ∈ s }) : x ∈ s.attach :=
  Multiset.mem_attach _ _

@[simp]
/-
**Sym.attach_nil** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：attach_nil : (nil : Sym α 0).attach = nil
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem attach_nil : (nil : Sym α 0).attach = nil :=
  rfl

@[simp]
/-
**Sym.attach_cons** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：attach_cons (x : α) (s : Sym α n) : (cons x s).attach = cons ⟨x, mem_cons_
self _ _⟩ (s.attach.map fun x => ⟨x, mem_cons_of_mem x.prop⟩)
参数：x : α；s : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.coe_injective`：coe_injective : Injective ((↑) : Sym α n -> Multiset 
α)
· 使用定理 `Sym.mem_cons_self`：mem_cons_self (a : α) (s : Sym α n) : a in a ::ₛ s
· 使用定理 `Sym.mem_cons_of_mem`：mem_cons_of_mem (h : a in s) : a in b ::ₛ s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Multiset.attach_cons`：attach_cons (a : α) (m : Multiset α) : (a ::ₘ m).a
ttach = ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p
.2⟩
-/
theorem attach_cons (x : α) (s : Sym α n) :
    (cons x s).attach =
      cons ⟨x, mem_cons_self _ _⟩ (s.attach.map fun x => ⟨x, mem_cons_of_mem x.prop⟩) :=
  coe_injective <| Multiset.attach_cons _ _

/-- Change the length of a `Sym` using an equality.
The simp-normal form is for the `cast` to be pushed outward. -/
/-
**Sym.cast** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：{α : Type u_1} → {n m : ℕ} → n = m → Sym α n ≃ Sym α m
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Change the length of a `Sym` using an equality.
The simp-normal form is for the `cast` to be pushed outward.
-/
protected def cast {n m : ℕ} (h : n = m) : Sym α n ≃ Sym α m where
  toFun s := ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩

@[simp]
/-
**Sym.cast_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cast_rfl : Sym.cast rfl s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem cast_rfl : Sym.cast rfl s = s :=
  Subtype.ext rfl

@[simp]
/-
**Sym.cast_cast** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：cast_cast {n'' : Nat} (h : n = n') (h' : n' = n'') : Sym.cast h' (Sym.cast
 h s) = Sym.cast (h.trans h') s
参数：h : n = n'；h' : n' = n''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_cast {n'' : ℕ} (h : n = n') (h' : n' = n'') :
    Sym.cast h' (Sym.cast h s) = Sym.cast (h.trans h') s :=
  rfl

@[simp]
/-
**Sym.coe_cast** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_cast (h : n = m) : (Sym.cast h s : Multiset α) = s
参数：h : n = m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_cast (h : n = m) : (Sym.cast h s : Multiset α) = s :=
  rfl

@[simp]
/-
**Sym.mem_cast** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_cast (h : n = m) : a in Sym.cast h s ↔ a in s
参数：h : n = m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cast (h : n = m) : a ∈ Sym.cast h s ↔ a ∈ s :=
  Iff.rfl

/-- Append a pair of `Sym` terms. -/
/-
**Sym.append** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：append (s : Sym α n) (s' : Sym α n') : Sym α (n + n')
参数：s : Sym α n；s' : Sym α n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append a pair of `Sym` terms.
-/
def append (s : Sym α n) (s' : Sym α n') : Sym α (n + n') :=
  ⟨s.1 + s'.1, by rw [Multiset.card_add, s.2, s'.2]⟩

@[simp]
/-
**Sym.append_inj_right** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：append_inj_right (s : Sym α n) {t t' : Sym α n'} : s.append t = s.append t
' ↔ t = t'
参数：s : Sym α n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem append_inj_right (s : Sym α n) {t t' : Sym α n'} : s.append t = s.append t' ↔ t = t' :=
  Subtype.ext_iff.trans <| (add_right_inj _).trans Subtype.ext_iff.symm

@[simp]
/-
**Sym.append_inj_left** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：append_inj_left {s s' : Sym α n} (t : Sym α n') : s.append t = s'.append t
 ↔ s = s'
参数：t : Sym α n'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem append_inj_left {s s' : Sym α n} (t : Sym α n') : s.append t = s'.append t ↔ s = s' :=
  Subtype.ext_iff.trans <| (add_left_inj _).trans Subtype.ext_iff.symm

set_option backward.isDefEq.respectTransparency false in
/-
**Sym.append_comm** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：append_comm (s : Sym α n') (s' : Sym α n') : s.append s' = Sym.cast (add_c
omm _ _) (s'.append s)
参数：s : Sym α n'；s' : Sym α n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Sym.cast_rfl`：cast_rfl : Sym.cast rfl s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem append_comm (s : Sym α n') (s' : Sym α n') :
    s.append s' = Sym.cast (add_comm _ _) (s'.append s) := by
  simp [append, add_comm]

@[simp, norm_cast]
/-
**Sym.coe_append** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_append (s : Sym α n) (s' : Sym α n') : (s.append s' : Multiset α) = s 
+ s'
参数：s : Sym α n；s' : Sym α n'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_append (s : Sym α n) (s' : Sym α n') : (s.append s' : Multiset α) = s + s' :=
  rfl
/-
**Sym.mem_append_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_append_iff {s' : Sym α m} : a in s.append s' ↔ a in s ∨ a in s'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
-/
theorem mem_append_iff {s' : Sym α m} : a ∈ s.append s' ↔ a ∈ s ∨ a ∈ s' :=
  Multiset.mem_add

set_option backward.isDefEq.respectTransparency false in
/-- `a ↦ {a}` as an equivalence between `α` and `Sym α 1`. -/
@[simps apply]
/-
**Sym.oneEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：oneEquiv : α ≃ Sym α 1 where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?

--- 原说明 ---
`a ↦ {a}` as an equivalence between `α` and `Sym α 1`.
-/
def oneEquiv : α ≃ Sym α 1 where
  toFun a := ⟨{a}, by simp⟩
  invFun s := (Equiv.subtypeQuotientEquivQuotientSubtype
      (·.length = 1) _ (fun _ ↦ Iff.rfl) (fun l l' ↦ by rfl) s).liftOn
    (fun l ↦ l.1.head <| List.length_pos_iff.mp <| by simp)
    fun ⟨_, _⟩ ⟨_, h⟩ ↦ fun perm ↦ by
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
      exact List.eq_of_mem_singleton (List.Perm.mem_iff perm |>.mp <| List.head_mem _)
  right_inv := by rintro ⟨⟨l⟩, h⟩; obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h; rfl

/-- Fill a term `m : Sym α (n - i)` with `i` copies of `a` to obtain a term of `Sym α n`.
This is a convenience wrapper for `m.append (replicate i a)` that adjusts the term using
`Sym.cast`. -/
/-
**Sym.fill** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：fill (a : α) (i : Fin (n + 1)) (m : Sym α (n - i)) : Sym α n
参数：a : α；i : Fin (n + 1)；m : Sym α (n - i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fill a term `m : Sym α (n - i)` with `i` copies of `a` to obtain a term of `Sym 
α n`.
This is a convenience wrapper for `m.append (replicate i a)` that adjusts the te
rm using
`Sym.cast`.
-/
def fill (a : α) (i : Fin (n + 1)) (m : Sym α (n - i)) : Sym α n :=
  Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (replicate i a))
/-
**Sym.coe_fill** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} : (fill a i m : Mul
tiset α) = m + replicate i a
参数：n + 1；n - i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} :
    (fill a i m : Multiset α) = m + replicate i a :=
  rfl
/-
**Sym.mem_fill_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)} : a in Sym.fi
ll b i s ↔ (i : Nat) != 0 ∧ a = b ∨ a in s
参数：n + 1；n - i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.fill.eq_1`：∀ {α : Type u_1} {n : ℕ} (a : α) (i : Fin (n + 1)) (m : S
ym α (n - ↑i)),   Sym.fill a i m = (Sym.cast ⋯) (m.append (Sym.replicate (↑i) a)
)
· 使用定理 `Sym.mem_cast`：mem_cast (h : n = m) : a in Sym.cast h s ↔ a in s
· 使用定理 `Sym.mem_append_iff`：mem_append_iff {s' : Sym α m} : a in s.append s' ↔ a
 in s ∨ a in s'
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Sym.mem_replicate`：mem_replicate : b in replicate n a ↔ n != 0 ∧ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)} :
    a ∈ Sym.fill b i s ↔ (i : ℕ) ≠ 0 ∧ a = b ∨ a ∈ s := by
  rw [fill, mem_cast, mem_append_iff, or_comm, mem_replicate]

open Multiset

/-- Remove every `a` from a given `Sym α n`.
Yields the number of copies `i` and a term of `Sym α (n - i)`. -/
/-
**Sym.filterNe** 是 Mathlib 中的一个定义，位于命名空间 `Sym`。
形式化陈述：filterNe [DecidableEq α] (a : α) (m : Sym α n) : Σ i : Fin (n + 1), Sym α 
(n - i)
参数：a : α；m : Sym α n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove every `a` from a given `Sym α n`.
Yields the number of copies `i` and a term of `Sym α (n - i)`.
-/
def filterNe [DecidableEq α] (a : α) (m : Sym α n) : Σ i : Fin (n + 1), Sym α (n - i) :=
  ⟨⟨m.1.count a, (count_le_card _ _).trans_lt <| by rw [m.2, Nat.lt_succ_iff]⟩,
    m.1.filter (a ≠ ·),
    Nat.eq_sub_of_add_eq <|
      Eq.trans
        (by
          rw [← countP_eq_card_filter, add_comm]
          simp only [eq_comm, Ne, count]
          rw [← card_eq_countP_add_countP _ _])
        m.2⟩
/-
**Sym.sigma_sub_ext** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：sigma_sub_ext {m₁ m₂ : Σ i : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Mult
iset α) = m₂.2) : m₁ = m₂
参数：n + 1；n - i；h : (m₁.2 : Multiset α) = m₂.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.subtype_ext`：∀ {α : Type u_1} {β : Type u_7} {p : α → β → Prop} {x
₀ x₁ : (a : α) × Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Sym.val_eq_coe`：val_eq_coe (s : Sym α n) : s.1 = ↑s
-/
theorem sigma_sub_ext {m₁ m₂ : Σ i : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2) :
    m₁ = m₂ :=
  Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self (Nat.le_of_lt_succ m₁.1.is_lt), ← m₁.2.2, val_eq_coe, h,
        ← val_eq_coe, m₂.2.2, Nat.sub_sub_self (Nat.le_of_lt_succ m₂.1.is_lt)])
    h
/-
**Sym.fill_filterNe** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：fill_filterNe [DecidableEq α] (a : α) (m : Sym α n) : (m.filterNe a).2.fil
l a (m.filterNe a).1 = m
参数：a : α；m : Sym α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.ext`：∀ {α : Type u_1} {n : ℕ} {s₁ s₂ : Sym α n}, ↑s₁ = ↑s₂ → s₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.coe_fill`：coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} : (
fill a i m : Multiset α) = m + replicate i a
· 使用定理 `Sym.filterNe.eq_1`：∀ {α : Type u_1} {n : ℕ} [inst : DecidableEq α] (a : 
α) (m : Sym α n),   Sym.filterNe a m = ⟨⟨Multiset.count a ↑m, ⋯⟩, ⟨Multiset.filt
er (fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.val_eq_coe`：val_eq_coe (s : Sym α n) : s.1 = ↑s
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Multiset.count_filter`：count_filter {p} [DecidablePred p] {a} {s : Multi
set α} : count a (filter p s) = if p a then count a s else 0
· 使用定理 `Sym.coe_replicate`：coe_replicate : (replicate n a : Multiset α) = Multis
et.replicate n a
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem fill_filterNe [DecidableEq α] (a : α) (m : Sym α n) :
    (m.filterNe a).2.fill a (m.filterNe a).1 = m :=
  Sym.ext
    (by
      rw [coe_fill, filterNe, ← val_eq_coe, Subtype.coe_mk, Fin.val_mk]
      ext b; dsimp
      rw [count_add, count_filter, Sym.coe_replicate, count_replicate]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
      · rw [if_pos h, if_neg h, add_zero])
/-
**Sym.filter_ne_fill** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：filter_ne_fill [DecidableEq α] (a : α) (m : Σ i : Fin (n + 1), Sym α (n - 
i)) (h : a ∉ m.2) : (m.2.fill a m.1).filterNe a = m
参数：a : α；m : Σ i : Fin (n + 1), Sym α (n - i)；h : a ∉ m.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym.sigma_sub_ext`：sigma_sub_ext {m₁ m₂ : Σ i : Fin (n + 1), Sym α (n - 
i)} (h : (m₁.2 : Multiset α) = m₂.2) : m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym.filterNe.eq_1`：∀ {α : Type u_1} {n : ℕ} [inst : DecidableEq α] (a : 
α) (m : Sym α n),   Sym.filterNe a m = ⟨⟨Multiset.count a ↑m, ⋯⟩, ⟨Multiset.filt
er (fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.val_eq_coe`：val_eq_coe (s : Sym α n) : s.1 = ↑s
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Sym.coe_fill`：coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} : (
fill a i m : Multiset α) = m + replicate i a
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Sym.mem_replicate`：mem_replicate : b in replicate n a ↔ n != 0 ∧ b = a
· 使用定理 `Sym.mem_coe`：mem_coe : a in (s : Multiset α) ↔ a in s
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem filter_ne_fill
    [DecidableEq α] (a : α) (m : Σ i : Fin (n + 1), Sym α (n - i)) (h : a ∉ m.2) :
    (m.2.fill a m.1).filterNe a = m :=
  sigma_sub_ext
    (by
      rw [filterNe, ← val_eq_coe, Subtype.coe_mk, val_eq_coe, coe_fill]
      rw [filter_add, filter_eq_self.2, add_eq_left, eq_zero_iff_forall_notMem]
      · intro b hb
        rw [mem_filter, Sym.mem_coe, mem_replicate] at hb
        exact hb.2 hb.1.2.symm
      · exact fun a ha ha' => h <| ha'.symm ▸ ha)
/-
**Sym.count_coe_fill_self_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：count_coe_fill_self_of_notMem [DecidableEq α] {a : α} {i : Fin (n + 1)} {s
 : Sym α (n - i)} (hx : a ∉ s) : count a (fill a i s : Multiset α) = i
参数：n + 1；n - i；hx : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.count_replicate_self`：count_replicate_self (a : α) (n : Nat) : 
count a (replicate n a) = n
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_coe_fill_self_of_notMem [DecidableEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : a ∉ s) :
    count a (fill a i s : Multiset α) = i := by
  simp [coe_fill, coe_replicate, hx]
/-
**Sym.count_coe_fill_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：count_coe_fill_of_ne [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym 
α (n - i)} (hx : x != a) : count x (fill a i s : Multiset α) = count x s
参数：n + 1；n - i；hx : x != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_coe_fill_of_ne [DecidableEq α] {a x : α} {i : Fin (n + 1)} {s : Sym α (n - i)}
    (hx : x ≠ a) :
    count x (fill a i s : Multiset α) = count x s := by
  suffices x ∉ Multiset.replicate i a by simp [coe_fill, coe_replicate, this]
  simp [Multiset.mem_replicate, hx]

end Sym

section Equiv

/-! ### Combinatorial equivalences -/


variable {α : Type*} {n : ℕ}

open Sym

namespace SymOptionSuccEquiv

/-- Function from the symmetric product over `Option` splitting on whether or not
it contains a `none`. -/
/-
**SymOptionSuccEquiv.encode** 是 Mathlib 中的一个定义，位于命名空间 `SymOptionSuccEquiv`。
形式化陈述：encode [DecidableEq α] (s : Sym (Option α) n.succ) : Sym (Option α) n oplu
s Sym α n.succ
参数：s : Sym (Option α) n.succ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function from the symmetric product over `Option` splitting on whether or not
it contains a `none`.
-/
def encode [DecidableEq α] (s : Sym (Option α) n.succ) : Sym (Option α) n ⊕ Sym α n.succ :=
  if h : none ∈ s then Sum.inl (s.erase none h)
  else
    Sum.inr
      (s.attach.map fun o =>
        o.1.get <| Option.ne_none_iff_isSome.1 <| ne_of_mem_of_not_mem o.2 h)

@[simp]
/-
**SymOptionSuccEquiv.encode_of_none_mem** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionSucc
Equiv`。
形式化陈述：encode_of_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none i
n s) : encode s = Sum.inl (s.erase none h)
参数：s : Sym (Option α) n.succ；h : none in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem encode_of_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∈ s) :
    encode s = Sum.inl (s.erase none h) :=
  dif_pos h

@[simp]
/-
**SymOptionSuccEquiv.encode_of_none_notMem** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionS
uccEquiv`。
形式化陈述：encode_of_none_notMem [DecidableEq α] (s : Sym (Option α) n.succ) (h : non
e ∉ s) : encode s = Sum.inr (s.attach.map fun o => o.1.get Option.ne_none_iff_is
Some.1 ne_of_mem_of_not_mem o.2 h)
参数：s : Sym (Option α) n.succ；h : none ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem encode_of_none_notMem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∉ s) :
    encode s =
      Sum.inr
        (s.attach.map fun o =>
          o.1.get <| Option.ne_none_iff_isSome.1 <| ne_of_mem_of_not_mem o.2 h) :=
  dif_neg h

/-- Inverse of `Sym_option_succ_equiv.decode`. -/
/-
**SymOptionSuccEquiv.decode** 是 Mathlib 中的一个定义，位于命名空间 `SymOptionSuccEquiv`。
形式化陈述：{α : Type u_1} → {n : ℕ} → Sym (Option α) n ⊕ Sym α n.succ → Sym (Option α
) n.succ
参数：Option α；Option α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of `Sym_option_succ_equiv.decode`.
-/
def decode : Sym (Option α) n ⊕ Sym α n.succ → Sym (Option α) n.succ
  | Sum.inl s => none ::ₛ s
  | Sum.inr s => s.map Embedding.some

@[simp]
/-
**SymOptionSuccEquiv.decode_inl** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionSuccEquiv`。
形式化陈述：decode_inl (s : Sym (Option α) n) : decode (Sum.inl s) = none ::ₛ s
参数：s : Sym (Option α) n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_inl (s : Sym (Option α) n) : decode (Sum.inl s) = none ::ₛ s :=
  rfl

@[simp]
/-
**SymOptionSuccEquiv.decode_inr** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionSuccEquiv`。
形式化陈述：decode_inr (s : Sym α n.succ) : decode (Sum.inr s) = s.map Embedding.some
参数：s : Sym α n.succ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decode_inr (s : Sym α n.succ) : decode (Sum.inr s) = s.map Embedding.some :=
  rfl

@[simp]
/-
**SymOptionSuccEquiv.decode_encode** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionSuccEquiv
`。
形式化陈述：decode_encode [DecidableEq α] (s : Sym (Option α) n.succ) : decode (encode
 s) = s
参数：s : Sym (Option α) n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymOptionSuccEquiv.encode_of_none_mem`：encode_of_none_mem [DecidableEq α
] (s : Sym (Option α) n.succ) (h : none in s) : encode s = Sum.inl (s.erase none
 h)
· 使用定理 `Sym.cons_erase`：cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h
 : a in s) : a ::ₛ s.erase a h = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_isSome`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ o
.isSome = true
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SymOptionSuccEquiv.encode_of_none_notMem`：encode_of_none_notMem [Decidab
leEq α] (s : Sym (Option α) n.succ) (h : none ∉ s) : encode s = Sum.inr (s.attac
h.map fun o => o.1.get Option.…
· 使用定理 `Sym.map_congr`：map_congr {f g : α -> β} {s : Sym α n} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `Sym.map_map`：map_map {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β)
 (s : Sym α n) : Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
· 使用定理 `Sym.attach_map_coe`：attach_map_coe (s : Sym α n) : s.attach.map (↑) = s
-/
theorem decode_encode [DecidableEq α] (s : Sym (Option α) n.succ) : decode (encode s) = s := by
  by_cases h : none ∈ s
  · simp [h]
  · simp only [decode, h, not_false_iff, encode_of_none_notMem, Embedding.some_apply, map_map,
      comp_apply, Option.some_get]
    convert! s.attach_map_coe

@[simp]
/-
**SymOptionSuccEquiv.encode_decode** 是 Mathlib 中的一个定理，位于命名空间 `SymOptionSuccEquiv
`。
形式化陈述：encode_decode [DecidableEq α] (s : Sym (Option α) n oplus Sym α n.succ) : 
encode (decode s) = s
参数：s : Sym (Option α) n oplus Sym α n.succ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `SymOptionSuccEquiv.encode_of_none_mem`：encode_of_none_mem [DecidableEq α
] (s : Sym (Option α) n.succ) (h : none in s) : encode s = Sum.inl (s.erase none
 h)
· 使用定理 `Sym.erase_cons_head`：erase_cons_head [DecidableEq α] (s : Sym α n) (a : 
α) (h : a in a ::ₛ s
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Sym.map_injective`：map_injective {f : α -> β} (hf : Injective f) (n : Na
t) : Injective (map f : Sym α n -> Sym β n)
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Sym.map_congr`：map_congr {f g : α -> β} {s : Sym α n} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `Sym.map_map`：map_map {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β)
 (s : Sym α n) : Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
· 使用定理 `Sym.attach_map_coe`：attach_map_coe (s : Sym α n) : s.attach.map (↑) = s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
-/
theorem encode_decode [DecidableEq α] (s : Sym (Option α) n ⊕ Sym α n.succ) :
    encode (decode s) = s := by
  obtain s | s := s
  · simp
  · unfold SymOptionSuccEquiv.encode
    split_ifs with h
    · obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
    · refine congr_arg Sum.inr ?_
      refine map_injective (Option.some_injective _) _ ?_
      refine Eq.trans ?_ (.trans (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe ?_) <;> simp

end SymOptionSuccEquiv

/-- The symmetric product over `Option` is a disjoint union over simpler symmetric products. -/
--@[simps]
/-
**symOptionSuccEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：symOptionSuccEquiv [DecidableEq α] : Sym (Option α) n.succ ≃ Sym (Option α
) n oplus Sym α n.succ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SymOptionSuccEquiv.decode_encode`：decode_encode [DecidableEq α] (s : Sym
 (Option α) n.succ) : decode (encode s) = s
· 使用定理 `SymOptionSuccEquiv.encode_decode`：encode_decode [DecidableEq α] (s : Sym
 (Option α) n oplus Sym α n.succ) : encode (decode s) = s
-/
def symOptionSuccEquiv [DecidableEq α] :
    Sym (Option α) n.succ ≃ Sym (Option α) n ⊕ Sym α n.succ where
  toFun := SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode

end Equiv

