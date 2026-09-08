/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Multiset.Fold

/-!
# GCD and LCM operations on multisets

## Main definitions

- `Multiset.gcd` - the greatest common denominator of a `Multiset` of elements of a `GCDMonoid`
- `Multiset.lcm` - the least common multiple of a `Multiset` of elements of a `GCDMonoid`

## Implementation notes

TODO: simplify with a tactic and `Data.Multiset.Lattice`

## Tags

multiset, gcd
-/

@[expose] public section

namespace Multiset

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### LCM -/


section lcm

/-- Least common multiple of a multiset -/
/-
**Multiset.lcm** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：lcm (s : Multiset α) : α
参数：s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm

--- 原说明 ---
Least common multiple of a multiset
-/
def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1

@[simp]
/-
**Multiset.lcm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_zero : (0 : Multiset α).lcm = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_zero`：fold_zero (b : α) : (0 : Multiset α).fold op b = b
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
-/
theorem lcm_zero : (0 : Multiset α).lcm = 1 :=
  fold_zero _ _

@[simp]
/-
**Multiset.lcm_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
-/
theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm :=
  fold_cons_left _ _ _ _

@[simp]
/-
**Multiset.lcm_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
· 使用定理 `Multiset.fold_singleton`：fold_singleton (b a : α) : ({a} : Multiset α).f
old op b = a * b
· 使用定理 `lcm_one_right`：lcm_one_right [NormalizedGCDMonoid α] (a : α) : lcm a 1 =
 normalize a
-/
theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a :=
  (fold_singleton _ _ _).trans <| lcm_one_right _

@[simp]
/-
**Multiset.lcm_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `lcm_same`：lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize
 a
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
-/
theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)
/-
**Multiset.lcm_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall b in s, b ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.lcm_zero`：lcm_zero : (0 : Multiset α).lcm = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.lcm_cons`：lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = G
CDMonoid.lcm a s.lcm
-/
theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ ∀ b ∈ s, b ∣ a :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, lcm_dvd_iff])
/-
**Multiset.dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dvd_lcm {s : Multiset α} {a : α} (h : a in s) : a ∣ s.lcm
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.lcm_dvd`：lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall 
b in s, b ∣ a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h
/-
**Multiset.lcm_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₁.lcm ∣ s₂.lcm
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.lcm_dvd`：lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall 
b in s, b ∣ a
· 使用定理 `Multiset.dvd_lcm`：dvd_lcm {s : Multiset α} {a : α} (h : a in s) : a ∣ s.
lcm
-/
theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
  lcm_dvd.2 fun _ hb ↦ dvd_lcm (h hb)

@[simp]
/-
**Multiset.normalize_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lcm_zero`：lcm_zero : (0 : Multiset α).lcm = 1
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.lcm_cons`：lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = G
CDMonoid.lcm a s.lcm
· 使用定理 `normalize_lcm`：normalize_lcm [NormalizedGCDMonoid α] (a b : α) : normali
ze (lcm a b) = lcm a b
-/
theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s _ ↦ by simp

@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ 0 ∈ s := by
  induction s using Multiset.induction_on with
  | empty => simp only [lcm_zero, one_ne_zero, notMem_zero]
  | cons a s ihs => simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a]
/-
**Multiset.lcm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_ne_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm != 0 ↔ 0 ∉ s
参数：s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Multiset.lcm_eq_zero_iff`：∀ {α : Type u_1} [inst : CommMonoidWithZero α]
 [inst_1 : NormalizedGCDMonoid α] [Nontrivial α] (s : Multiset α),   s.lcm = 0 ↔
 0 ∈ s
-/
theorem lcm_ne_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm ≠ 0 ↔ 0 ∉ s :=
  not_congr (lcm_eq_zero_iff s)

variable [DecidableEq α]

@[simp]
/-
**Multiset.lcm_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lcm_zero`：lcm_zero : (0 : Multiset α).lcm = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {s : Multiset α} :
 a in s -> dedup (a ::ₘ s) = dedup s
· 使用定理 `Multiset.lcm_cons`：lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = G
CDMonoid.lcm a s.lcm
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `lcm_assoc`：lcm_assoc [NormalizedGCDMonoid α] (m n k : α) : lcm (lcm m n)
 k = lcm m (lcm n k)
· 使用定理 `lcm_same`：lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize
 a
· 使用定理 `lcm_eq_of_associated_left`：lcm_eq_of_associated_left [NormalizedGCDMonoi
d α] {m n : α} (h : Associated m n) (k : α) : lcm m k = lcm n k
· 使用定理 `associated_normalize`：associated_normalize (x : α) : Associated x (norma
lize x)
· 使用定理 `Multiset.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {s : Multise
t α} : a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, lcm_cons]
    unfold lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)

@[simp]
/-
**Multiset.lcm_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.
lcm s₂.lcm
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.lcm_dedup`：lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.lcm_add`：lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMono
id.lcm s₁.lcm s₂.lcm
-/
theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp

@[simp]
/-
**Multiset.lcm_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_union (s₁ s₂ : Multiset α) : (s₁ union s₂).lcm = GCDMonoid.lcm s₁.lcm 
s₂.lcm
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.lcm_dedup`：lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.lcm_add`：lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMono
id.lcm s₁.lcm s₂.lcm
-/
theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add]
  simp

@[simp]
/-
**Multiset.lcm_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm
 a s.lcm
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.lcm_dedup`：lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.lcm_cons`：lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = G
CDMonoid.lcm a s.lcm
-/
theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm := by
  rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_cons]
  simp

end lcm

/-! ### GCD -/


section gcd

/-- Greatest common divisor of a multiset -/
/-
**Multiset.gcd** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：gcd (s : Multiset α) : α
参数：s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd

--- 原说明 ---
Greatest common divisor of a multiset
-/
def gcd (s : Multiset α) : α :=
  s.fold GCDMonoid.gcd 0

@[simp]
/-
**Multiset.gcd_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_zero : (0 : Multiset α).gcd = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_zero`：fold_zero (b : α) : (0 : Multiset α).fold op b = b
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
-/
theorem gcd_zero : (0 : Multiset α).gcd = 0 :=
  fold_zero _ _

@[simp]
/-
**Multiset.gcd_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
-/
theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd :=
  fold_cons_left _ _ _ _

@[simp]
/-
**Multiset.gcd_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
· 使用定理 `Multiset.fold_singleton`：fold_singleton (b a : α) : ({a} : Multiset α).f
old op b = a * b
· 使用定理 `gcd_zero_right`：gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0
 = normalize a
-/
theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a :=
  (fold_singleton _ _ _).trans <| gcd_zero_right _

@[simp]
/-
**Multiset.gcd_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
-/
theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)
/-
**Multiset.dvd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ forall b in s, a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])
/-
**Multiset.gcd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_dvd {s : Multiset α} {a : α} (h : a in s) : s.gcd ∣ a
参数：h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.dvd_gcd`：dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ forall 
b in s, a ∣ b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h
/-
**Multiset.gcd_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₂.gcd ∣ s₁.gcd
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dvd_gcd`：dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ forall 
b in s, a ∣ b
· 使用定理 `Multiset.gcd_dvd`：gcd_dvd {s : Multiset α} {a : α} (h : a in s) : s.gcd 
∣ a
-/
theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun _ hb ↦ gcd_dvd (h hb)

@[simp]
/-
**Multiset.normalize_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `normalize_gcd`：normalize_gcd [NormalizedGCDMonoid α] : forall a b : α, n
ormalize (gcd a b) = gcd a b
-/
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s _ ↦ by simp
/-
**Multiset.gcd_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ forall x in s, x = 0
参数：s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.gcd_dvd`：gcd_dvd {s : Multiset α} {a : α} (h : a in s) : s.gcd 
∣ a
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
-/
theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x ∈ s, x = 0 := by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx ↦ h x (mem_cons_of_mem hx)]
/-
**Multiset.gcd_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_ne_zero_iff (s : Multiset α) : s.gcd != 0 ↔ exists x in s, x != 0
参数：s : Multiset α。
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
theorem gcd_ne_zero_iff (s : Multiset α) : s.gcd ≠ 0 ↔ ∃ x ∈ s, x ≠ 0 := by
  simp [gcd_eq_zero_iff]
/-
**Multiset.gcd_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_map_mul {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α] (a : 
α) (s : Multiset α) : (s.map (a * ·)).gcd = normalize a * s.gcd
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `Associated.gcd_eq_right`：Associated.gcd_eq_right [NormalizedGCDMonoid α]
 {m n : α} (h : Associated m n) (k : α) : gcd k m = gcd k n
· 使用定理 `Associated.mul_right`：Associated.mul_right [CommMonoid M] {a b : M} (h :
 a ~ᵤ b) (c : M) : a * c ~ᵤ b * c
· 使用定理 `normalize_associated`：normalize_associated (x : α) : Associated (normali
ze x) x
-/
theorem gcd_map_mul {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    (a : α) (s : Multiset α) : (s.map (a * ·)).gcd = normalize a * s.gcd := by
  refine s.induction_on ?_ fun b s ih ↦ ?_
  · simp_rw [map_zero, gcd_zero, mul_zero]
  · simp_rw [map_cons, gcd_cons, ← gcd_mul_left]
    rw [ih]
    apply ((normalize_associated a).mul_right _).gcd_eq_right
/-
**Multiset.associated_gcd_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：associated_gcd_map_mul (a : α) (s : Multiset α) : Associated (s.map (a * ·
)).gcd (a * s.gcd)
参数：a : α；s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Associated.gcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst_1 :
 GCDMonoid α] {a₁ a₂ b₁ b₂ : α},   Associated a₁ a₂ → Associated b₁ b₂ → Associa
ted …
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
· 使用定理 `gcd_mul_left'`：gcd_mul_left' [GCDMonoid α] (a b c : α) : Associated (gcd
 (a * b) (a * c)) (a * gcd b c)
-/
theorem associated_gcd_map_mul (a : α) (s : Multiset α) :
    Associated (s.map (a * ·)).gcd (a * s.gcd) := by
  refine s.induction_on ?_ fun b s ih ↦ ?_
  · simp_rw [map_zero, gcd_zero, mul_zero, Associated.of_eq]
  · simp_rw [map_cons, gcd_cons]
    exact .trans (.gcd .rfl ih) (gcd_mul_left' ..)

section

variable [DecidableEq α]

@[simp]
/-
**Multiset.gcd_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.gcd_zero`：gcd_zero : (0 : Multiset α).gcd = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {s : Multiset α} :
 a in s -> dedup (a ::ₘ s) = dedup s
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `gcd_assoc`：gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n)
 k = gcd m (gcd n k)
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `Associated.gcd_eq_left`：Associated.gcd_eq_left [NormalizedGCDMonoid α] {
m n : α} (h : Associated m n) (k : α) : gcd m k = gcd n k
· 使用定理 `associated_normalize`：associated_normalize (x : α) : Associated x (norma
lize x)
· 使用定理 `Multiset.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {s : Multise
t α} : a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, gcd_cons]
    unfold gcd
    rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same]
    apply (associated_normalize _).gcd_eq_left

@[simp]
/-
**Multiset.gcd_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.
gcd s₂.gcd
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.gcd_dedup`：gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.gcd_add`：gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMono
id.gcd s₁.gcd s₂.gcd
-/
theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp

@[simp]
/-
**Multiset.gcd_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_union (s₁ s₂ : Multiset α) : (s₁ union s₂).gcd = GCDMonoid.gcd s₁.gcd 
s₂.gcd
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.gcd_dedup`：gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.gcd_add`：gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMono
id.gcd s₁.gcd s₂.gcd
-/
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp

@[simp]
/-
**Multiset.gcd_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd
 a s.gcd
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.gcd_dedup`：gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.gcd_cons`：gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = G
CDMonoid.gcd a s.gcd
-/
theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_cons]
  simp

end

/-
**Multiset.extract_gcd'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：extract_gcd' (s t : Multiset α) (hs : exists x, x in s ∧ x != (0 : α)) (ht
 : s = t.map (s.gcd * ·)) : t.gcd = 1
参数：s t : Multiset α；hs : exists x, x in s ∧ x != (0 : α)；ht : s = t.map (s.gcd *
 ·)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.normalize_gcd`：normalize_gcd (s : Multiset α) : normalize s.gcd
 = s.gcd
· 使用定理 `normalize_eq_one`：normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x 
where mp hx
· 使用定理 `associated_one_iff_isUnit`：associated_one_iff_isUnit [Monoid M] {a : M} 
: (a : M) ~ᵤ 1 ↔ IsUnit a
· 使用定理 `Associated.of_mul_left`：Associated.of_mul_left [CommMonoidWithZero M] [I
sCancelMulZero M] {a b c d : M} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c) (ha : a != 0)
 : b ~ᵤ d
· 使用定理 `GCDMonoid.toIsCancelMulZero`：∀ {α : Type u_2} {inst : CommMonoidWithZero
 α} [self : GCDMonoid α], IsCancelMulZero α
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `Associated.of_eq`：Associated.of_eq [Monoid M] {a b : M} (h : a = b) : a 
~ᵤ b
· 使用定理 `Multiset.associated_gcd_map_mul`：associated_gcd_map_mul (a : α) (s : Mul
tiset α) : Associated (s.map (a * ·)).gcd (a * s.gcd)
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.gcd_eq_zero_iff`：gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔
 forall x in s, x = 0
-/
theorem extract_gcd' (s t : Multiset α) (hs : ∃ x, x ∈ s ∧ x ≠ (0 : α))
    (ht : s = t.map (s.gcd * ·)) : t.gcd = 1 := by
  rw [← normalize_gcd, normalize_eq_one, ← associated_one_iff_isUnit]
  refine .of_mul_left (.symm ?_) .rfl (a := s.gcd) ?_
  · simpa using (Associated.of_eq <| congr(gcd $ht)).trans (associated_gcd_map_mul ..)
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs
/-
**Multiset.extract_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：extract_gcd (s : Multiset α) (hs : s != 0) : exists t : Multiset α, s = t.
map (s.gcd * ·) ∧ t.gcd = 1
参数：s : Multiset α；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_replicate`：map_replicate (f : α -> β) (k : Nat) (a : α) : (
replicate k a).map f = replicate k (f a)
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.gcd_eq_zero_iff`：gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔
 forall x in s, x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
· 使用定理 `Multiset.gcd_dedup`：gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd
· 使用定理 `Multiset.dedup_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α} {n : ℕ}, n ≠ 0 → (n • s).dedup = s.dedup
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Multiset.card_pos`：card_pos {s : Multiset α} : 0 < card s ↔ s != 0
· 使用定理 `Multiset.dedup_singleton`：dedup_singleton {a : α} : dedup ({a} : Multise
t α) = {a}
· 使用定理 `Multiset.gcd_singleton`：gcd_singleton {a : α} : ({a} : Multiset α).gcd =
 normalize a
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Multiset.extract_gcd'`：extract_gcd' (s t : Multiset α) (hs : exists x, x
 in s ∧ x != (0 : α)) (ht : s = t.map (s.gcd * ·)) : t.gcd = 1
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Multiset.gcd_dvd`：gcd_dvd {s : Multiset α} {a : α} (h : a in s) : s.gcd 
∣ a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  classical
    by_cases! h : ∀ x ∈ s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate, eq_replicate, mul_one, s.gcd_eq_zero_iff.2 h, ← nsmul_singleton,
    ← gcd_dedup, dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @gcd_dvd _ _ _ s
      refine ⟨s.pmap @f fun _ ↦ id, ?_, extract_gcd' s _ h ?_⟩ <;>
      · rw [map_pmap]
        conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ ↦ id]
        congr with (x hx)
        rw [id, ← hf hx]

end gcd

end Multiset

