/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Algebra.Order.Module.Rat
public import Mathlib.Tactic.GCongr

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Order properties of the average over a finset
-/

public section

open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

namespace Finset
section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

/-
**Finset.expect_eq_zero_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_eq_zero_iff_of_nonneg (hf : forall i in s, 0 <= f i) : 𝔼 i in s, f 
i = 0 ↔ forall i in s, f i = 0
参数：hf : forall i in s, 0 <= f i。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma expect_eq_zero_iff_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonneg hf]
/-
**Finset.expect_eq_zero_iff_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_eq_zero_iff_of_nonpos (hf : forall i in s, f i <= 0) : 𝔼 i in s, f 
i = 0 ↔ forall i in s, f i = 0
参数：hf : forall i in s, f i <= 0。
该定理/引理刻画了左右两侧的等价关系。
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
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_eq_zero_iff_of_nonpos`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma expect_eq_zero_iff_of_nonpos (hf : ∀ i ∈ s, f i ≤ 0) :
    𝔼 i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  simp +contextual [expect, sum_eq_zero_iff_of_nonpos hf]

section PosSMulMono
variable [PosSMulMono ℚ≥0 α] {a : α}

@[gcongr]
/-
**Finset.expect_le_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_le_expect (hfg : forall i in s, f i <= g i) : 𝔼 i in s, f i <= 𝔼 i 
in s, g i
参数：hfg : forall i in s, f i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0
-/
lemma expect_le_expect (hfg : ∀ i ∈ s, f i ≤ g i) : 𝔼 i ∈ s, f i ≤ 𝔼 i ∈ s, g i :=
  smul_le_smul_of_nonneg_left (sum_le_sum hfg) <| by positivity
/-
**Finset.expect_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_le (hs : s.Nonempty) (h : forall x in s, f x <= a) : 𝔼 i in s, f i 
<= a
参数：hs : s.Nonempty；h : forall x in s, f x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_smul_le_iff_of_pos`：inv_smul_le_iff_of_pos [PosSMulMono α β] [PosSMu
lReflectLE α β] (ha : 0 < a) : a⁻¹ • b₁ <= b₂ ↔ b₁ <= a • b₂
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
-/
lemma expect_le (hs : s.Nonempty) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a :=
  (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h
/-
**Finset.le_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_expect (hs : s.Nonempty) (h : forall x in s, a <= f x) : a <= 𝔼 i in s,
 f i
参数：hs : s.Nonempty；h : forall x in s, a <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_inv_smul_iff_of_pos`：le_inv_smul_iff_of_pos [PosSMulMono α β] [PosSMu
lReflectLE α β] (ha : 0 < a) : b₁ <= a⁻¹ • b₂ ↔ a • b₁ <= b₂
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Finset.card_nsmul_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
-/
lemma le_expect (hs : s.Nonempty) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i :=
  (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h
/-
**Finset.expect_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_nonneg (hf : forall i in s, 0 <= f i) : 0 <= 𝔼 i in s, f i
参数：hf : forall i in s, 0 <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i :=
  smul_nonneg (by positivity) <| sum_nonneg hf

end PosSMulMono

section PosSMulMono
variable {M N : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N] [Module ℚ≥0 N]
  [PosSMulMono ℚ≥0 N] {m : M → N} {p : M → Prop} {f : ι → M} {s : Finset ι}

/-- Let `{a | p a}` be an additive subsemigroup of an additive commutative monoid `M`. If `m` is a
subadditive function (`m (a + b) ≤ m a + m b`) preserved under division by a natural, `f` is a
function valued in that subsemigroup and `s` is a nonempty set, then
`m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
/-
**Finset.le_expect_nonempty_of_subadditive_on_pred** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
形式化陈述：le_expect_nonempty_of_subadditive_on_pred (h_add : forall a b, p a -> p b 
-> m (a + b) <= m a + m b) (hp_add : forall a b, p a -> p b -> p (a + b)) (h_div
 : forall (n : Nat) a, p a -> m (a /Rat n) = m a /Rat n) (hs_nonempty : s.Nonemp
ty) (hs : forall i in s, p (f i)) : m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i)
参数：h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b；hp_add : forall a b,
 p a -> p b -> p (a + b)；h_div : forall (n : Nat) a, p a -> m (a /Rat n) = m a /
Rat n；hs_nonempty : s.Nonempty；hs : forall i in s, p (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_induction_nonempty`：∀ {ι : Type u_1} {s : Finset ι} {M : Type
 u_7} [inst : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a →
 p b → p (a + b)) →…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `Finset.le_sum_nonempty_of_subadditive_on_pred`：∀ {ι : Type u_1} {M : Typ
e u_4} {N : Type u_5} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] [inst_
2 : Preorder N]   [IsOrderedAddMono…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0

--- 原说明 ---
Let `{a | p a}` be an additive subsemigroup of an additive commutative monoid `M
`. If `m` is a
subadditive function (`m (a + b) ≤ m a + m b`) preserved under division by a nat
ural, `f` is a
function valued in that subsemigroup and `s` is a nonempty set, then
`m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`.
-/
lemma le_expect_nonempty_of_subadditive_on_pred (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b)
    (hp_add : ∀ a b, p a → p b → p (a + b)) (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (f i)) :
    m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  simp only [expect, h_div _ _ (sum_induction_nonempty _ _ hp_add hs_nonempty hs)]
  exact smul_le_smul_of_nonneg_left
    (le_sum_nonempty_of_subadditive_on_pred _ _ h_add hp_add _ _ hs_nonempty hs) <| by positivity

/-- If `m : M → N` is a subadditive function (`m (a + b) ≤ m a + m b`) and `s` is a nonempty set,
then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
/-
**Finset.le_expect_nonempty_of_subadditive** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_expect_nonempty_of_subadditive (m : M -> N) (h_mul : forall a b, m (a +
 b) <= m a + m b) (h_div : forall (n : Nat) a, m (a /Rat n) = m a /Rat n) (hs : 
s.Nonempty) : m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i)
参数：m : M -> N；h_mul : forall a b, m (a + b) <= m a + m b；h_div : forall (n : Nat
) a, m (a /Rat n) = m a /Rat n；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_expect_nonempty_of_subadditive_on_pred`：le_expect_nonempty_of_
subadditive_on_pred (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b) (
hp_add : forall a b, p a -> p b -> p (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `m : M → N` is a subadditive function (`m (a + b) ≤ m a + m b`) and `s` is a 
nonempty set,
then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`.
-/
lemma le_expect_nonempty_of_subadditive (m : M → N) (h_mul : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) (hs : s.Nonempty) :
    m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) :=
  le_expect_nonempty_of_subadditive_on_pred (p := fun _ ↦ True) (by simpa) (by simp) (by simpa) hs
    (by simp)

/-- Let `{a | p a}` be a subsemigroup of a commutative monoid `M`. If `m` is a subadditive function
(`m (x + y) ≤ m x + m y`, `m 0 = 0`) preserved under division by a natural and `f` is a function
valued in that subsemigroup, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
/-
**Finset.le_expect_of_subadditive_on_pred** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_expect_of_subadditive_on_pred (h_zero : m 0 = 0) (h_add : forall a b, p
 a -> p b -> m (a + b) <= m a + m b) (hp_add : forall a b, p a -> p b -> p (a + 
b)) (h_div : forall (n : Nat) a, p a -> m (a /Rat n) = m a /Rat n) (hs : forall 
i in s, p (f i)) : m (𝔼 i in s, f i) <= 𝔼 i in s, m (f i)
参数：h_zero : m 0 = 0；h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b；hp_
add : forall a b, p a -> p b -> p (a + b)；h_div : forall (n : Nat) a, p a -> m (
a /Rat n) = m a /Rat n；hs : forall i in s, p (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_empty`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] (f : ι → M),   (∅.expect fun i => f i) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.le_expect_nonempty_of_subadditive_on_pred`：le_expect_nonempty_of_
subadditive_on_pred (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b) (
hp_add : forall a b, p a -> p b -> p (…

--- 原说明 ---
Let `{a | p a}` be a subsemigroup of a commutative monoid `M`. If `m` is a subad
ditive function
(`m (x + y) ≤ m x + m y`, `m 0 = 0`) preserved under division by a natural and `
f` is a function
valued in that subsemigroup, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`.
-/
lemma le_expect_of_subadditive_on_pred (h_zero : m 0 = 0)
    (h_add : ∀ a b, p a → p b → m (a + b) ≤ m a + m b) (hp_add : ∀ a b, p a → p b → p (a + b))
    (h_div : ∀ (n : ℕ) a, p a → m (a /ℚ n) = m a /ℚ n)
    (hs : ∀ i ∈ s, p (f i)) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := by
  obtain rfl | hs_nonempty := s.eq_empty_or_nonempty
  · simp [h_zero]
  · exact le_expect_nonempty_of_subadditive_on_pred h_add hp_add h_div hs_nonempty hs

-- TODO: Contribute back better docstring to `le_prod_of_submultiplicative`
/-- If `m` is a subadditive function (`m (x + y) ≤ m x + m y`, `m 0 = 0`) preserved under division
by a natural, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`. -/
/-
**Finset.le_expect_of_subadditive** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_expect_of_subadditive (h_zero : m 0 = 0) (h_add : forall a b, m (a + b)
 <= m a + m b) (h_div : forall (n : Nat) a, m (a /Rat n) = m a /Rat n) : m (𝔼 i 
in s, f i) <= 𝔼 i in s, m (f i)
参数：h_zero : m 0 = 0；h_add : forall a b, m (a + b) <= m a + m b；h_div : forall (n
 : Nat) a, m (a /Rat n) = m a /Rat n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_expect_of_subadditive_on_pred`：le_expect_of_subadditive_on_pre
d (h_zero : m 0 = 0) (h_add : forall a b, p a -> p b -> m (a + b) <= m a + m b) 
(hp_add : forall a b, p a -> …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `m` is a subadditive function (`m (x + y) ≤ m x + m y`, `m 0 = 0`) preserved 
under division
by a natural, then `m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i)`.
-/
lemma le_expect_of_subadditive (h_zero : m 0 = 0) (h_add : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) :=
  le_expect_of_subadditive_on_pred (p := fun _ ↦ True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)

end PosSMulMono
end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [Module ℚ≥0 α]
  [PosSMulStrictMono ℚ≥0 α] {s : Finset ι} {f g : ι → α} {a : α}

/-
**Finset.expect_lt_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_lt_expect (hfg : forall i in s, f i <= g i) (hfg' : exists i in s, 
f i < g i) : 𝔼 i in s, f i < 𝔼 i in s, g i
参数：hfg : forall i in s, f i <= g i；hfg' : exists i in s, f i < g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
· 使用定理 `Finset.sum_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → M} {s : Fins
et ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
-/
lemma expect_lt_expect (hfg : ∀ i ∈ s, f i ≤ g i) (hfg' : ∃ i ∈ s, f i < g i) :
    𝔼 i ∈ s, f i < 𝔼 i ∈ s, g i :=
  smul_lt_smul_of_pos_left (sum_lt_sum hfg hfg')
    (by obtain ⟨i, hi, -⟩ := hfg'; have : s.Nonempty := ⟨i, hi⟩; simpa)
/-
**Finset.expect_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_lt (hle : forall x in s, f x <= a) (hlt : exists x in s, f x < a) :
 𝔼 i in s, f i < a
参数：hle : forall x in s, f x <= a；hlt : exists x in s, f x < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finset.expect_lt_expect`：expect_lt_expect (hfg : forall i in s, f i <= g
 i) (hfg' : exists i in s, f i < g i) : 𝔼 i in s, f i < 𝔼 i in s, g i
-/
lemma expect_lt (hle : ∀ x ∈ s, f x ≤ a) (hlt : ∃ x ∈ s, f x < a) :
    𝔼 i ∈ s, f i < a := by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt
/-
**Finset.lt_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：lt_expect (hle : forall x in s, a <= f x) (hlt : exists x in s, a < f x) :
 a < 𝔼 i in s, f i
参数：hle : forall x in s, a <= f x；hlt : exists x in s, a < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Finset.expect_lt_expect`：expect_lt_expect (hfg : forall i in s, f i <= g
 i) (hfg' : exists i in s, f i < g i) : 𝔼 i in s, f i < 𝔼 i in s, g i
-/
lemma lt_expect (hle : ∀ x ∈ s, a ≤ f x) (hlt : ∃ x ∈ s, a < f x) :
    a < 𝔼 i ∈ s, f i := by
  rw [← expect_const (hlt.imp (fun _ => And.left)) a]
  exact expect_lt_expect hle hlt
/-
**Finset.expect_pos'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_pos' (h : forall i in s, 0 <= f i) (hs : exists i in s, 0 < f i) : 
0 < 𝔼 i in s, f i
参数：h : forall i in s, 0 <= f i；hs : exists i in s, 0 < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.expect_const_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCom
mMonoid M] [inst_1 : _root_.Module ℚ≥0 M] (s : Finset ι),   (s.expect fun _i => 
0) = 0
· 使用引理 `Finset.expect_lt_expect`：expect_lt_expect (hfg : forall i in s, f i <= g
 i) (hfg' : exists i in s, f i < g i) : 𝔼 i in s, f i < 𝔼 i in s, g i
-/
lemma expect_pos' (h : ∀ i ∈ s, 0 ≤ f i) (hs : ∃ i ∈ s, 0 < f i) : 0 < 𝔼 i ∈ s, f i :=
  (expect_const_zero _).symm.trans_lt <| expect_lt_expect h hs
/-
**Finset.expect_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_pos (hf : forall i in s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i in s,
 f i
参数：hf : forall i in s, 0 < f i；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finset.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M]
 [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι}
 [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
-/
lemma expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i :=
  smul_pos (inv_pos.2 <| mod_cast hs.card_pos) <| sum_pos hf hs

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι}
  {f g : ι → α} {a : α}

/-
**Finset.exists_lt_of_expect_lt_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_lt_of_expect_lt_expect (h : 𝔼 i in s, g i < 𝔼 i in s, f i) : exists
 x in s, g x < f x
参数：h : 𝔼 i in s, g i < 𝔼 i in s, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Finset.expect_le_expect`：expect_le_expect (hfg : forall i in s, f i <= g
 i) : 𝔼 i in s, f i <= 𝔼 i in s, g i
-/
lemma exists_lt_of_expect_lt_expect (h : 𝔼 i ∈ s, g i < 𝔼 i ∈ s, f i) :
    ∃ x ∈ s, g x < f x := by
  contrapose! h; exact expect_le_expect h
/-
**Finset.exists_lt_of_lt_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i in s, f i) : exists 
x in s, a < f x
参数：hs : s.Nonempty；h : a < 𝔼 i in s, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Finset.expect_le`：expect_le (hs : s.Nonempty) (h : forall x in s, f x <=
 a) : 𝔼 i in s, f i <= a
-/
lemma exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i ∈ s, f i) : ∃ x ∈ s, a < f x := by
  contrapose! h; exact expect_le hs h
/-
**Finset.exists_lt_of_expect_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i in s, f i < a) : exists 
x in s, f x < a
参数：hs : s.Nonempty；h : 𝔼 i in s, f i < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Finset.le_expect`：le_expect (hs : s.Nonempty) (h : forall x in s, a <= f
 x) : a <= 𝔼 i in s, f i
-/
lemma exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i < a) : ∃ x ∈ s, f x < a := by
  contrapose! h; exact le_expect hs h

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddMonoid
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedCancelAddMonoid α] [Module ℚ≥0 α]
  [PosSMulStrictMono ℚ≥0 α] {a : α} {s : Finset ι} {f g : ι → α}

/-
**Finset.exists_le_of_expect_le_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_le_of_expect_le_expect (hs : s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i 
in s, f i) : exists x in s, g x <= f x
参数：hs : s.Nonempty；h : 𝔼 i in s, g i <= 𝔼 i in s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `Finset.expect_lt_expect`：expect_lt_expect (hfg : forall i in s, f i <= g
 i) (hfg' : exists i in s, f i < g i) : 𝔼 i in s, f i < 𝔼 i in s, g i
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma exists_le_of_expect_le_expect (hs : s.Nonempty) (h : 𝔼 i ∈ s, g i ≤ 𝔼 i ∈ s, f i) :
    ∃ x ∈ s, g x ≤ f x := by
  obtain ⟨_, hx⟩ := hs
  contrapose! h
  exact expect_lt_expect (fun _ hx ↦ le_of_lt (h _ hx)) ⟨_, ⟨hx, h _ hx⟩⟩
/-
**Finset.exists_le_of_le_expect** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_le_of_le_expect (hs : s.Nonempty) (h : a <= 𝔼 i in s, f i) : exists
 x in s, a <= f x
参数：hs : s.Nonempty；h : a <= 𝔼 i in s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_le_of_expect_le_expect`：exists_le_of_expect_le_expect (hs 
: s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i in s, f i) : exists x in s, g x <= f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
-/
lemma exists_le_of_le_expect (hs : s.Nonempty) (h : a ≤ 𝔼 i ∈ s, f i) : ∃ x ∈ s, a ≤ f x :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])
/-
**Finset.exists_le_of_expect_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_le_of_expect_le (hs : s.Nonempty) (h : 𝔼 i in s, f i <= a) : exists
 x in s, f x <= a
参数：hs : s.Nonempty；h : 𝔼 i in s, f i <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_le_of_expect_le_expect`：exists_le_of_expect_le_expect (hs 
: s.Nonempty) (h : 𝔼 i in s, g i <= 𝔼 i in s, f i) : exists x in s, g x <= f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.expect_const`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMono
id M] [inst_1 : _root_.Module ℚ≥0 M] {s : Finset ι},   s.Nonempty → ∀ (a : M), (
s.expect …
-/
lemma exists_le_of_expect_le (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i ≤ a) : ∃ x ∈ s, f x ≤ a :=
  exists_le_of_expect_le_expect hs (by rwa [expect_const hs _])

end LinearOrderedCancelAddMonoid

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] [PosSMulMono ℚ≥0 α]

/-
**Finset.abs_expect_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：abs_expect_le (s : Finset ι) (f : ι -> α) : |𝔼 i in s, f i| <= 𝔼 i in s, |
f i|
参数：s : Finset ι；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_expect_of_subadditive`：le_expect_of_subadditive (h_zero : m 0 
= 0) (h_add : forall a b, m (a + b) <= m a + m b) (h_div : forall (n : Nat) a, m
 (a /Rat n) = m a /Ra…
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_add_le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddCommGroup α
] [AddLeftMono α] (a b : α), |a + b| ≤ |a| + |b|
· 使用定理 `abs_nnqsmul`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOr
der α] [IsOrderedAddMonoid α]   [inst_3 : DistribMulAction ℚ≥0 α] [PosSMulMono ℚ
≥…
-/
lemma abs_expect_le (s : Finset ι) (f : ι → α) : |𝔼 i ∈ s, f i| ≤ 𝔼 i ∈ s, |f i| :=
  le_expect_of_subadditive abs_zero abs_add_le (fun _ ↦ abs_nnqsmul _)

end LinearOrderedAddCommGroup

section LinearOrderedCommSemiring
variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] [Module ℚ≥0 R]
  [PosSMulMono ℚ≥0 R]

/-- **Cauchy-Schwarz inequality** in terms of `Finset.expect`. -/
/-
**Finset.expect_mul_sq_le_sq_mul_sq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι -> R) : (𝔼 i in s, f i 
* g i) ^ 2 <= (𝔼 i in s, f i ^ 2) * 𝔼 i in s, g i ^ 2
参数：s : Finset ι；f g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用引理 `Finset.sum_mul_sq_le_sq_mul_sq`：sum_mul_sq_le_sq_mul_sq [CommSemiring R]
 [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] (s : Finset ι) (f g :
 ι -> R) : (∑ i in s…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNRat.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ℚ≥0

--- 原说明 ---
**Cauchy-Schwarz inequality** in terms of `Finset.expect`.
-/
lemma expect_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (𝔼 i ∈ s, f i * g i) ^ 2 ≤ (𝔼 i ∈ s, f i ^ 2) * 𝔼 i ∈ s, g i ^ 2 := by
  simp only [expect, smul_pow, inv_pow, smul_mul_smul_comm, ← sq]
  gcongr
  exact sum_mul_sq_le_sq_mul_sq ..

end LinearOrderedCommSemiring
end Finset

open Finset

namespace Fintype
variable [Fintype ι]

section OrderedAddCommMonoid
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] {f : ι → α}

/-
**Fintype.expect_eq_zero_iff_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_eq_zero_iff_of_nonneg (hf : 0 <= f) : 𝔼 i, f i = 0 ↔ f = 0
参数：hf : 0 <= f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_eq_zero_iff_of_nonneg`：expect_eq_zero_iff_of_nonneg (hf : 
forall i in s, 0 <= f i) : 𝔼 i in s, f i = 0 ↔ forall i in s, f i = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma expect_eq_zero_iff_of_nonneg (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop
/-
**Fintype.expect_eq_zero_iff_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：expect_eq_zero_iff_of_nonpos (hf : f <= 0) : 𝔼 i, f i = 0 ↔ f = 0
参数：hf : f <= 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.expect_eq_zero_iff_of_nonpos`：expect_eq_zero_iff_of_nonpos (hf : 
forall i in s, f i <= 0) : 𝔼 i in s, f i = 0 ↔ forall i in s, f i = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma expect_eq_zero_iff_of_nonpos (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

end OrderedAddCommMonoid
end Fintype

open Finset

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset
open scoped BigOperators

attribute [local instance] monadLiftOptionMetaM in
/-- Positivity extension for `Finset.expect`. -/
@[positivity Finset.expect _ _]
meta def evalFinsetExpect : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match e with
  | ~q(@Finset.expect $ι _ $instα $instmod $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := .betaRev f #[i]
    let rbody ← core zα pα body
    let p_pos : Option Q(0 < $e) ← do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      let some ps ← proveFinsetNonempty s | pure none
      let .some pα' ← trySynthInstanceQ q(IsOrderedCancelAddMonoid $α) | pure none
      let .some instαordsmul ← trySynthInstanceQ q(PosSMulStrictMono ℚ≥0 $α) | pure none
      assumeInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody
      pure <| some
        q(@expect_pos $ι $α $instα $pα $pα' $instmod $instαordsmul $s $f (fun i _ ↦ $pr i) $ps)
    -- Try to show that the sum is positive
    if let some p_pos := p_pos then
      return .positive p_pos
    -- Fall back to showing that the sum is nonnegative
    else
      let pbody ← rbody.toNonneg
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody
      let instαordmon ← synthInstanceQ q(IsOrderedAddMonoid $α)
      let instαordsmul ← synthInstanceQ q(PosSMulMono ℚ≥0 $α)
      assumeInstancesCommute
      return .nonnegative
        q(@expect_nonneg $ι $α $instα $pα $instαordmon $instmod $s $f $instαordsmul fun i _ ↦ $pr i)
  | _ => throwError "not Finset.expect"

/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j ∈ range n, a j ^ 2 := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a : ULift.{2} ℕ → ℚ) (s : Finset (ULift.{2} ℕ)) : 0 ≤ 𝔼 j ∈ s, a j ^ 2 := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n : ℕ) (a : ℕ → ℚ) : 0 ≤ 𝔼 j : Fin 8, 𝔼 i ∈ range n, (a j ^ 2 + i ^ 2) := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n : ℕ) (a : ℕ → ℚ) : 0 < 𝔼 j : Fin (n + 1), (a j ^ 2 + 1) := by positivity
/-
**Mathlib.Meta.Positivity.** 是 Mathlib 中的一个示例，位于命名空间 `Mathlib.Meta.Positivity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (a : ℕ → ℚ) : 0 < 𝔼 j ∈ ({1} : Finset ℕ), (a j ^ 2 + 1) := by positivity

end Mathlib.Meta.Positivity

