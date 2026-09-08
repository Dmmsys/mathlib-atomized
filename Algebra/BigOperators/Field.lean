/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finset.Density

/-!
# Results about big operators with values in a field
-/

public section

open Fintype

variable {ι K : Type*} [DivisionSemiring K]

/-
**Multiset.sum_map_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multiset.sum_map_div (s : Multiset ι) (f : ι -> K) (a : K) : (s.map (fun x
 => f x / a)).sum = (s.map f).sum / a
参数：s : Multiset ι；f : ι -> K；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Multiset.sum_map_mul_right`：sum_map_mul_right : sum (s.map fun i => f i 
* a) = sum (s.map f) * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]
/-
**Finset.sum_div** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ i in s, f i) / a =
 ∑ i in s, f i / a
参数：s : Finset ι；f : ι -> K；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.sum_div (s : Finset ι) (f : ι → K) (a : K) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv, sum_mul]

-- TODO: Move these to `Algebra.BigOperators.Group.Finset.Basic`, next to the corresponding `card`
-- lemmas, once `Finset.dens` doesn't depend on `Field` anymore.
namespace Finset
variable {α β : Type*} [Fintype β]

@[simp]
/-
**Finset.dens_disjiUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_disjiUnion (s : Finset α) (t : α -> Finset β) (h) : (s.disjiUnion t h
).dens = ∑ a in s, (t a).dens
参数：s : Finset α；t : α -> Finset β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_disjiUnion`：card_disjiUnion (s : Finset ι) (t : ι -> Finset 
M) (h) : #(s.disjiUnion t h) = ∑ a in s, #(t a)
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a ∈ s, (t a).dens := by
  simp [dens, sum_div]

variable {s : Finset α} {t : α → Finset β}
/-
**Finset.dens_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) : (s.biU
nion t).dens = ∑ u in s, (t u).dens
参数：h : (s : Set α).PairwiseDisjoint t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]
/-
**Finset.dens_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens <= ∑ a in s, (t a).de
ns
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
-/
lemma dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le
/-
**Finset.dens_eq_sum_dens_fiberwise** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β -> α} {t : Finset β} (h 
: (t : Set β).MapsTo f s) : t.dens = ∑ a in s, {b in t | f b = a}.dens
参数：h : (t : Set β).MapsTo f s。
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
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]
/-
**Finset.dens_eq_sum_dens_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dens_eq_sum_dens_image [DecidableEq α] (f : β -> α) (t : Finset β) : t.den
s = ∑ a in t.image f, {b in t | f b = a}.dens
参数：f : β -> α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.dens_eq_sum_dens_fiberwise`：dens_eq_sum_dens_fiberwise [Decidable
Eq α] {f : β -> α} {t : Finset β} (h : (t : Set β).MapsTo f s) : t.dens = ∑ a in
 s, {b in t | f b = a}.…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
lemma dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens :=
  dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

end Finset

