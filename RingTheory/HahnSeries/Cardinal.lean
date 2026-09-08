/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.SetTheory.Cardinal.Arithmetic

import Mathlib.Algebra.Group.Pointwise.Set.Card

/-!
# Cardinality of Hahn series

We define `HahnSeries.cardSupp` as the cardinality of the support of a Hahn series, and find bounds
for the cardinalities of different operations. We also build the subgroups, subrings, etc. of Hahn
series bounded by a given infinite cardinal.
-/

@[expose] public section

open Cardinal

namespace HahnSeries

variable {Γ R S α : Type*}

/-! ### Cardinality function -/

section PartialOrder
variable [PartialOrder Γ]

section Zero
variable [Zero R]

/-- The cardinality of the support of a Hahn series. -/
/-
**HahnSeries.cardSupp** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp (x : R⟦Γ⟧) : Cardinal
参数：x : R⟦Γ⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinality of the support of a Hahn series.
-/
def cardSupp (x : R⟦Γ⟧) : Cardinal :=
  #x.support
/-
**HahnSeries.cardSupp_congr** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support) 
: x.cardSupp = y.cardSupp
参数：h : x.support = y.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support = y.support) :
    x.cardSupp = y.cardSupp := by
  simp_rw [cardSupp, h]
/-
**HahnSeries.cardSupp_mono** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support subseteq y.sup
port) : x.cardSupp <= y.cardSupp
参数：h : x.support subseteq y.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
-/
theorem cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (h : x.support ⊆ y.support) :
    x.cardSupp ≤ y.cardSupp :=
  mk_le_mk_of_subset h

@[simp]
/-
**HahnSeries.cardSupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.support_zero`：support_zero : support (0 : R⟦Γ⟧) = ∅
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0 := by
  simp [cardSupp]
/-
**HahnSeries.cardSupp_single_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_single_of_ne (a : Γ) {r : R} (h : r != 0) : cardSupp (single a r)
 = 1
参数：a : Γ；h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.cardSupp.eq_1`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Partia
lOrder Γ] [inst_1 : Zero R] (x : HahnSeries Γ R),   x.cardSupp = Cardinal.mk ↑x.
support
· 使用定理 `HahnSeries.support_single_of_ne`：support_single_of_ne (h : r != 0) : sup
port (single a r) = {a}
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
-/
theorem cardSupp_single_of_ne (a : Γ) {r : R} (h : r ≠ 0) : cardSupp (single a r) = 1 := by
  rw [cardSupp, support_single_of_ne h, mk_singleton]
/-
**HahnSeries.cardSupp_single_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_single_le (a : Γ) (r : R) : cardSupp (single a r) <= 1
参数：a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `HahnSeries.support_single_subset`：support_single_subset : support (singl
e a r) subseteq {a}
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
-/
theorem cardSupp_single_le (a : Γ) (r : R) : cardSupp (single a r) ≤ 1 :=
  (mk_le_mk_of_subset support_single_subset).trans_eq (mk_singleton a)

@[simp]
/-
**HahnSeries.cardSupp_one_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_one_le [Zero Γ] [One R] : cardSupp (1 : R⟦Γ⟧) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_single_le`：cardSupp_single_le (a : Γ) (r : R) : card
Supp (single a r) <= 1
-/
theorem cardSupp_one_le [Zero Γ] [One R] : cardSupp (1 : R⟦Γ⟧) ≤ 1 :=
  cardSupp_single_le ..

@[simp]
/-
**HahnSeries.cardSupp_one** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_one [Zero Γ] [One R] [NeZero (1 : R)] : cardSupp (1 : R⟦Γ⟧) = 1
参数：1 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_single_of_ne`：cardSupp_single_of_ne (a : Γ) {r : R} 
(h : r != 0) : cardSupp (single a r) = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem cardSupp_one [Zero Γ] [One R] [NeZero (1 : R)] : cardSupp (1 : R⟦Γ⟧) = 1 :=
  cardSupp_single_of_ne _ one_ne_zero
/-
**HahnSeries.cardSupp_map_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_map_le [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) : (x.map f).cardSupp
 <= x.cardSupp
参数：x : R⟦Γ⟧；f : ZeroHom R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_mono`：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (
h : x.support subseteq y.support) : x.cardSupp <= y.cardSupp
· 使用定理 `ZeroHom.zeroHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Zero M] [i
nst_1 : Zero N], ZeroHomClass (ZeroHom M N) M N
· 使用定理 `HahnSeries.support_map_subset`：support_map_subset [Zero S] (x : R⟦Γ⟧) (f
 : ZeroHom R S) : (x.map f).support subseteq x.support
-/
theorem cardSupp_map_le [Zero S] (x : R⟦Γ⟧) (f : ZeroHom R S) : (x.map f).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_map_subset ..
/-
**HahnSeries.cardSupp_truncLT_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_truncLT_le [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ) : (truncLT c x).car
dSupp <= x.cardSupp
参数：x : R⟦Γ⟧；c : Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_mono`：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (
h : x.support subseteq y.support) : x.cardSupp <= y.cardSupp
· 使用定理 `HahnSeries.support_truncLT_subset`：support_truncLT_subset [PartialOrder 
Γ] [DecidableLT Γ] (c : Γ) (x : R⟦Γ⟧) : (truncLT c x).support subseteq x.support
-/
theorem cardSupp_truncLT_le [DecidableLT Γ] (x : R⟦Γ⟧) (c : Γ) :
    (truncLT c x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_truncLT_subset ..
/-
**HahnSeries.cardSupp_smul_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_smul_le (s : S) (x : R⟦Γ⟧) [SMulZeroClass S R] : (s • x).cardSupp
 <= x.cardSupp
参数：s : S；x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_mono`：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (
h : x.support subseteq y.support) : x.cardSupp <= y.cardSupp
· 使用定理 `HahnSeries.support_smul_subset`：support_smul_subset (r : R) (x : HahnSer
ies Γ V) : (r • x).support subseteq x.support
-/
theorem cardSupp_smul_le (s : S) (x : R⟦Γ⟧) [SMulZeroClass S R] : (s • x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_smul_subset ..

end Zero

/-
**HahnSeries.cardSupp_neg_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_neg_le [NegZeroClass R] (x : R⟦Γ⟧) : (-x).cardSupp <= x.cardSupp
参数：x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_mono`：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (
h : x.support subseteq y.support) : x.cardSupp <= y.cardSupp
· 使用定理 `HahnSeries.support_neg_subset`：support_neg_subset (x : R⟦Γ⟧) : (-x).supp
ort subseteq x.support
-/
theorem cardSupp_neg_le [NegZeroClass R] (x : R⟦Γ⟧) : (-x).cardSupp ≤ x.cardSupp :=
  cardSupp_mono <| support_neg_subset ..
/-
**HahnSeries.cardSupp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_add_le [AddMonoid R] (x y : R⟦Γ⟧) : (x + y).cardSupp <= x.cardSup
p + y.cardSupp
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `HahnSeries.support_add_subset`：support_add_subset (x y : R⟦Γ⟧) : (x + y)
.support subseteq x.support union y.support
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
-/
theorem cardSupp_add_le [AddMonoid R] (x y : R⟦Γ⟧) : (x + y).cardSupp ≤ x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_add_subset ..)).trans (mk_union_le ..)

@[simp]
/-
**HahnSeries.cardSupp_neg** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_neg [AddGroup R] (x : R⟦Γ⟧) : (-x).cardSupp = x.cardSupp
参数：x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.cardSupp_congr`：cardSupp_congr [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧}
 (h : x.support = y.support) : x.cardSupp = y.cardSupp
· 使用定理 `HahnSeries.support_neg`：support_neg {x : R⟦Γ⟧} : (-x).support = x.suppor
t
-/
theorem cardSupp_neg [AddGroup R] (x : R⟦Γ⟧) : (-x).cardSupp = x.cardSupp :=
  cardSupp_congr support_neg
/-
**HahnSeries.cardSupp_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_sub_le [AddGroup R] (x y : R⟦Γ⟧) : (x - y).cardSupp <= x.cardSupp
 + y.cardSupp
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `HahnSeries.support_sub_subset`：support_sub_subset (x y : R⟦Γ⟧) : (x - y)
.support subseteq x.support union y.support
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
-/
theorem cardSupp_sub_le [AddGroup R] (x y : R⟦Γ⟧) : (x - y).cardSupp ≤ x.cardSupp + y.cardSupp :=
  (mk_le_mk_of_subset (support_sub_subset ..)).trans (mk_union_le ..)
/-
**HahnSeries.cardSupp_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalN
onAssocSemiring R] (x y : R⟦Γ⟧) : (x * y).cardSupp <= x.cardSupp * y.cardSupp
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `HahnSeries.support_mul_subset`：support_mul_subset [NonUnitalNonAssocSemi
ring R] {x y : R⟦Γ⟧} : support (x * y) subseteq support x + support y
· 使用定理 `Cardinal.mk_add_le`：∀ {M : Type u_2} [inst : Add M] {s t : Set M}, Cardi
nal.mk ↑(s + t) ≤ Cardinal.mk ↑s * Cardinal.mk ↑t
-/
theorem cardSupp_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R]
    (x y : R⟦Γ⟧) : (x * y).cardSupp ≤ x.cardSupp * y.cardSupp :=
  (mk_le_mk_of_subset (support_mul_subset ..)).trans mk_add_le
/-
**HahnSeries.cardSupp_single_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_single_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Non
UnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) : (single a r * x).cardSupp
 <= x.cardSupp
参数：x : R⟦Γ⟧；a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HahnSeries.cardSupp_mul_le`：cardSupp_mul_le [AddCommMonoid Γ] [IsOrdered
CancelAddMonoid Γ] [NonUnitalNonAssocSemiring R] (x y : R⟦Γ⟧) : (x * y).cardSupp
 <= x.cardSupp *…
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `HahnSeries.cardSupp_single_le`：cardSupp_single_le (a : Γ) (r : R) : card
Supp (single a r) <= 1
-/
theorem cardSupp_single_mul_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (single a r * x).cardSupp ≤ x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_left (cardSupp_single_le ..) _)
/-
**HahnSeries.cardSupp_mul_single_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_mul_single_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Non
UnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) : (x * single a r).cardSupp
 <= x.cardSupp
参数：x : R⟦Γ⟧；a : Γ；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HahnSeries.cardSupp_mul_le`：cardSupp_mul_le [AddCommMonoid Γ] [IsOrdered
CancelAddMonoid Γ] [NonUnitalNonAssocSemiring R] (x y : R⟦Γ⟧) : (x * y).cardSupp
 <= x.cardSupp *…
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `HahnSeries.cardSupp_single_le`：cardSupp_single_le (a : Γ) (r : R) : card
Supp (single a r) <= 1
-/
theorem cardSupp_mul_single_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ) (r : R) :
    (x * single a r).cardSupp ≤ x.cardSupp := by
  simpa using (cardSupp_mul_le ..).trans (mul_le_mul_right (cardSupp_single_le ..) _)
/-
**HahnSeries.cardSupp_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_pow_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R
] (x : R⟦Γ⟧) (n : Nat) : (x ^ n).cardSupp <= x.cardSupp ^ n
参数：x : R⟦Γ⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HahnSeries.cardSupp_mul_le`：cardSupp_mul_le [AddCommMonoid Γ] [IsOrdered
CancelAddMonoid Γ] [NonUnitalNonAssocSemiring R] (x y : R⟦Γ⟧) : (x * y).cardSupp
 <= x.cardSupp *…
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
-/
theorem cardSupp_pow_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Semiring R]
    (x : R⟦Γ⟧) (n : ℕ) : (x ^ n).cardSupp ≤ x.cardSupp ^ n := by
  induction n with
  | zero => simp
  | succ n IH =>
    simpa [pow_succ] using (cardSupp_mul_le ..).trans <| mul_le_mul_left IH _
/-
**HahnSeries.cardSupp_hsum_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_hsum_le [AddCommMonoid R] (s : SummableFamily Γ R α) : lift s.hsu
m.cardSupp <= sum fun a => (s a).cardSupp
参数：s : SummableFamily Γ R α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `HahnSeries.SummableFamily.support_hsum_subset`：support_hsum_subset {s : 
SummableFamily Γ R α} : s.hsum.support subseteq ⋃ a : α, (s a).support
· 使用定理 `Cardinal.mk_iUnion_le_sum_mk_lift`：mk_iUnion_le_sum_mk_lift {α : Type u}
 {ι : Type v} {f : ι -> Set α} : lift.{v} #(⋃ i, f i) <= sum fun i => #(f i)
-/
theorem cardSupp_hsum_le [AddCommMonoid R] (s : SummableFamily Γ R α) :
    lift s.hsum.cardSupp ≤ sum fun a ↦ (s a).cardSupp :=
  (lift_le.2 <| mk_le_mk_of_subset (SummableFamily.support_hsum_subset ..)).trans
    mk_iUnion_le_sum_mk_lift

end PartialOrder

section LinearOrder
variable [LinearOrder Γ]

/-
**HahnSeries.cardSupp_hsum_powers_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_hsum_powers_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Co
mmRing R] (x : R⟦Γ⟧) : (SummableFamily.powers x).hsum.cardSupp <= max ℵ₀ x.cardS
upp
参数：x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.sum_pow_le_max_aleph0`：sum_pow_le_max_aleph0 (x : Cardinal) : s
um (fun n => x ^ n) <= max ℵ₀ x
· 使用定理 `HahnSeries.cardSupp_hsum_le`：cardSupp_hsum_le [AddCommMonoid R] (s : Sum
mableFamily Γ R α) : lift s.hsum.cardSupp <= sum fun a => (s a).cardSupp
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `HahnSeries.cardSupp_pow_le`：cardSupp_pow_le [AddCommMonoid Γ] [IsOrdered
CancelAddMonoid Γ] [Semiring R] (x : R⟦Γ⟧) (n : Nat) : (x ^ n).cardSupp <= x.car
dSupp ^ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.cardSupp_zero`：cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem cardSupp_hsum_powers_le [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
    (x : R⟦Γ⟧) : (SummableFamily.powers x).hsum.cardSupp ≤ max ℵ₀ x.cardSupp := by
  grw [← lift_uzero (cardSupp _), ← sum_pow_le_max_aleph0, cardSupp_hsum_le, sum_le_sum]
  intro i
  rw [SummableFamily.powers_toFun]
  split_ifs
  · exact cardSupp_pow_le ..
  · cases i <;> simp
/-
**HahnSeries.cardSupp_inv_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_inv_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : R⟦Γ
⟧) : x⁻¹.cardSupp <= max ℵ₀ x.cardSupp
参数：x : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `HahnSeries.cardSupp_zero`：cardSupp_zero : cardSupp (0 : R⟦Γ⟧) = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HahnSeries.cardSupp_single_mul_le`：cardSupp_single_mul_le [AddCommMonoid
 Γ] [IsOrderedCancelAddMonoid Γ] [NonUnitalNonAssocSemiring R] (x : R⟦Γ⟧) (a : Γ
) (r : R) : (single a r…
· 使用定理 `HahnSeries.cardSupp_hsum_powers_le`：cardSupp_hsum_powers_le [AddCommMono
id Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] (x : R⟦Γ⟧) : (SummableFamily.pow
ers x).hsum.cardSupp <= …
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `HahnSeries.cardSupp_mono`：cardSupp_mono [Zero S] {x : R⟦Γ⟧} {y : S⟦Γ⟧} (
h : x.support subseteq y.support) : x.cardSupp <= y.cardSupp
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.coeff_single_mul`：coeff_single_mul [NonUnitalNonAssocSemiring
 R] [PartialOrder Γ'] [AddCommGroup Γ'] [IsOrderedAddMonoid Γ'] {r : R} {x : R⟦Γ
'⟧} {a b : Γ'} : …
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
（共 32 条，此处仅展示前 30 条）
-/
theorem cardSupp_inv_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x : R⟦Γ⟧) :
    x⁻¹.cardSupp ≤ max ℵ₀ x.cardSupp := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  apply (cardSupp_single_mul_le ..).trans (cardSupp_hsum_powers_le ..) |>.trans
  gcongr
  refine (cardSupp_single_mul_le _ (-x.order) x.leadingCoeff⁻¹).trans' <| cardSupp_mono fun _ ↦ ?_
  aesop (add simp [coeff_single_mul])
/-
**HahnSeries.cardSupp_div_le** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：cardSupp_div_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : R
⟦Γ⟧) : (x / y).cardSupp <= x.cardSupp * max ℵ₀ y.cardSupp
参数：x y : R⟦Γ⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `HahnSeries.cardSupp_mul_le`：cardSupp_mul_le [AddCommMonoid Γ] [IsOrdered
CancelAddMonoid Γ] [NonUnitalNonAssocSemiring R] (x y : R⟦Γ⟧) : (x * y).cardSupp
 <= x.cardSupp *…
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `HahnSeries.cardSupp_inv_le`：cardSupp_inv_le [AddCommGroup Γ] [IsOrderedA
ddMonoid Γ] [Field R] (x : R⟦Γ⟧) : x⁻¹.cardSupp <= max ℵ₀ x.cardSupp
-/
theorem cardSupp_div_le [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] (x y : R⟦Γ⟧) :
    (x / y).cardSupp ≤ x.cardSupp * max ℵ₀ y.cardSupp :=
  (cardSupp_mul_le ..).trans <| mul_le_mul_right (cardSupp_inv_le y) _

end LinearOrder

/-! ### Substructures -/

variable (κ : Cardinal)

section AddMonoid
variable [PartialOrder Γ] [AddMonoid R] [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded submonoid of Hahn series with less than `κ` terms. -/
@[simps!]
/-
**HahnSeries.cardSuppLTAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：cardSuppLTAddSubmonoid : AddSubmonoid R⟦Γ⟧ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `κ`-bounded submonoid of Hahn series with less than `κ` terms.
-/
def cardSuppLTAddSubmonoid : AddSubmonoid R⟦Γ⟧ where
  carrier := {x | x.cardSupp < κ}
  zero_mem' := by simpa using aleph0_pos.trans_le hκ.out
  add_mem' hx hy := (cardSupp_add_le ..).trans_lt <| add_lt_of_lt hκ.out hx hy

@[simp]
/-
**HahnSeries.mem_cardSuppLTAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_cardSuppLTAddSubmonoid {x : R⟦Γ⟧} : x in cardSuppLTAddSubmonoid Γ R κ 
↔ x.cardSupp < κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cardSuppLTAddSubmonoid {x : R⟦Γ⟧} : x ∈ cardSuppLTAddSubmonoid Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddMonoid

section AddGroup
variable [PartialOrder Γ] [AddGroup R] [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded subgroup of Hahn series with less than `κ` terms. -/
@[simps!]
/-
**HahnSeries.cardSuppLTAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：cardSuppLTAddSubgroup : AddSubgroup R⟦Γ⟧ where neg_mem'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `κ`-bounded subgroup of Hahn series with less than `κ` terms.
-/
def cardSuppLTAddSubgroup : AddSubgroup R⟦Γ⟧ where
  neg_mem' := by simp
  __ := cardSuppLTAddSubmonoid Γ R κ

@[simp]
/-
**HahnSeries.mem_cardSuppLTAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_cardSuppLTAddSubgroup {x : R⟦Γ⟧} : x in cardSuppLTAddSubgroup Γ R κ ↔ 
x.cardSupp < κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cardSuppLTAddSubgroup {x : R⟦Γ⟧} : x ∈ cardSuppLTAddSubgroup Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end AddGroup

section Subring
variable [PartialOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [Ring R]
  [hκ : Fact (ℵ₀ ≤ κ)]

variable (Γ R) in
/-- The `κ`-bounded subring of Hahn series with less than `κ` terms. -/
/-
**HahnSeries.cardSuppLTSubring** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：cardSuppLTSubring : Subring R⟦Γ⟧ where one_mem'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `κ`-bounded subring of Hahn series with less than `κ` terms.
-/
def cardSuppLTSubring : Subring R⟦Γ⟧ where
  one_mem' := cardSupp_one_le.trans_lt <| one_lt_aleph0.trans_le hκ.out
  mul_mem' hx hy := (cardSupp_mul_le ..).trans_lt <| mul_lt_of_lt hκ.out hx hy
  __ := cardSuppLTAddSubgroup Γ R κ

@[simp]
/-
**HahnSeries.mem_cardSuppLTSubring** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_cardSuppLTSubring {x : R⟦Γ⟧} : x in cardSuppLTSubring Γ R κ ↔ x.cardSu
pp < κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cardSuppLTSubring {x : R⟦Γ⟧} : x ∈ cardSuppLTSubring Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subring

section Subfield
variable [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [Field R] [hκ : Fact (ℵ₀ < κ)]

variable (Γ R) in
/-- The `κ`-bounded subfield of Hahn series with less than `κ` terms. -/
@[simps!]
/-
**HahnSeries.cardSuppLTSubfield** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：cardSuppLTSubfield : Subfield R⟦Γ⟧ where inv_mem' _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `κ`-bounded subfield of Hahn series with less than `κ` terms.
-/
def cardSuppLTSubfield : Subfield R⟦Γ⟧ where
  inv_mem' _ _ := (cardSupp_inv_le _).trans_lt <| by simpa [hκ.out]
  __ := have : Fact (ℵ₀ ≤ κ) := ⟨hκ.out.le⟩; cardSuppLTSubring Γ R κ

@[simp]
/-
**HahnSeries.mem_cardSuppLTSubfield** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：mem_cardSuppLTSubfield {x : R⟦Γ⟧} : x in cardSuppLTSubfield Γ R κ ↔ x.card
Supp < κ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cardSuppLTSubfield {x : R⟦Γ⟧} : x ∈ cardSuppLTSubfield Γ R κ ↔ x.cardSupp < κ :=
  .rfl

end Subfield
end HahnSeries

