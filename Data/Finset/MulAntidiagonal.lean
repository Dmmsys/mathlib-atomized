/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Multiplication antidiagonal as a `Finset`.

We construct the `Finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered. -/

@[expose] public section


namespace Set

open scoped Pointwise

variable {α : Type*} {s t : Set α}

@[to_additive]
/-
**Set.IsPWO.mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsPWO`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [inst_1 : PartialOrde
r α] [IsOrderedCancelMonoid α],   s.IsPWO → t.IsPWO → (s * t).IsPWO
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_mul_prod`：image_mul_prod : (fun x : α × α => x.fst * x.snd) ''
 s ×ˢ t = s * t
· 使用定理 `Set.IsPWO.image_of_monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Pre
order α] [inst_1 : Preorder β] {s : Set α},   s.IsPWO → ∀ {f : α → β}, Monotone 
f → (f '' s).IsPW…
· 使用定理 `Set.IsPWO.prod`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [ins
t_1 : Preorder β] {s : Set α} {t : Set β},   s.IsPWO → t.IsPWO → (s ×ˢ t).IsPWO
· 使用定理 `Monotone.mul'`：Monotone.mul' [MulLeftMono α] [MulRightMono α] (hf : Mono
tone f) (hg : Monotone g) : Monotone fun x => f x * g x
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `monotone_fst`：monotone_fst : Monotone (@Prod.fst α β)
· 使用定理 `monotone_snd`：monotone_snd : Monotone (@Prod.snd α β)
-/
theorem IsPWO.mul [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

variable [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]

@[to_additive]
/-
**Set.IsWF.mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [inst_1 : LinearOrder
 α] [IsOrderedCancelMonoid α],   s.IsWF → t.IsWF → (s * t).IsWF
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.isWF`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α}, s.IsPW
O → s.IsWF
· 使用定理 `Set.IsPWO.mul`：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [ins
t_1 : PartialOrder α] [IsOrderedCancelMonoid α],   s.IsPWO → t.IsPWO → (s * t).I
sPW…
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
-/
theorem IsWF.mul (hs : s.IsWF) (ht : t.IsWF) : IsWF (s * t) :=
  (hs.isPWO.mul ht.isPWO).isWF

@[to_additive]
/-
**Set.IsWF.min_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.IsWF`。
形式化陈述：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [inst_1 : LinearOrder
 α] [inst_2 : IsOrderedCancelMonoid α]   (hs : s.IsWF) (ht : t.IsWF) (hsn : s.No
nempty) (htn : t.Nonempty), ⋯.min ⋯ = hs.min hsn * ht.min htn
参数：hs : s.IsWF；ht : t.IsWF；hsn : s.Nonempty；htn : t.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.IsWF.mul`：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [inst
_1 : LinearOrder α] [IsOrderedCancelMonoid α],   s.IsWF → t.IsWF → (s * t).IsWF
· 使用定理 `Set.Nonempty.mul`：∀ {α : Type u_2} [inst : Mul α] {s t : Set α}, s.Nonem
pty → t.Nonempty → (s * t).Nonempty
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.IsWF.le_min_iff`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}
 {a : α} (hs : s.IsWF) (hn : s.Nonempty),   a ≤ hs.min hn ↔ ∀ b ∈ s, a ≤ b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
-/
theorem IsWF.min_mul (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_mul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

open scoped Pointwise

variable {α : Type*}
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
  {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO) (a : α)

/-- `Finset.mulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive /-- `Finset.antidiagonal hs ht a` is the set of all pairs of an element in
`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/]
/-
**Finset.mulAntidiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulAntidiagonal : Finset (α × α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulAntidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_isPWO hs ht a).toFinset

variable {hs ht a} {u : Set α} {hu : u.IsPWO} {x : α × α}

@[to_additive (attr := simp)]
/-
**Finset.mem_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_mulAntidiagonal : x in mulAntidiagonal hs ht a ↔ x.1 in s ∧ x.2 in t ∧
 x.1 * x.2 = a
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
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a := by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive]
/-
**Finset.mulAntidiagonal_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulAntidiagonal_mono_left (h : u subseteq s) : mulAntidiagonal hu ht a sub
seteq mulAntidiagonal hs ht a
参数：h : u subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `Set.mulAntidiagonal_mono_left`：mulAntidiagonal_mono_left (h : s₁ subsete
q s₂) : mulAntidiagonal s₁ t a subseteq mulAntidiagonal s₂ t a
-/
theorem mulAntidiagonal_mono_left (h : u ⊆ s) : mulAntidiagonal hu ht a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_left h

@[to_additive]
/-
**Finset.mulAntidiagonal_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulAntidiagonal_mono_right (h : u subseteq t) : mulAntidiagonal hs hu a su
bseteq mulAntidiagonal hs ht a
参数：h : u subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `Set.mulAntidiagonal_mono_right`：mulAntidiagonal_mono_right (h : t₁ subse
teq t₂) : mulAntidiagonal s t₁ a subseteq mulAntidiagonal s t₂ a
-/
theorem mulAntidiagonal_mono_right (h : u ⊆ t) :
    mulAntidiagonal hs hu a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_right h

@[to_additive]
/-
**Finset.swap_mem_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：swap_mem_mulAntidiagonal : x.swap in Finset.mulAntidiagonal hs ht a ↔ x in
 Finset.mulAntidiagonal ht hs a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem swap_mem_mulAntidiagonal :
    x.swap ∈ Finset.mulAntidiagonal hs ht a ↔ x ∈ Finset.mulAntidiagonal ht hs a := by
  simp

@[to_additive]
/-
**Finset.support_mulAntidiagonal_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonem
pty } subseteq s * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_mulAntidiagonal`：mem_mulAntidiagonal : x in mulAntidiagonal h
s ht a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  exact ⟨b.1, hb.1, b.2, hb.2⟩

@[to_additive]
/-
**Finset.isPWO_support_mulAntidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isPWO_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }
.IsPWO
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.IsPWO.mono`：∀ {α : Type u_2} [inst : Preorder α] {s t : Set α}, t.Is
PWO → s ⊆ t → s.IsPWO
· 使用定理 `Set.IsPWO.mul`：∀ {α : Type u_1} {s t : Set α} [inst : CommMonoid α] [ins
t_1 : PartialOrder α] [IsOrderedCancelMonoid α],   s.IsPWO → t.IsPWO → (s * t).I
sPW…
· 使用定理 `Finset.support_mulAntidiagonal_subset_mul`：support_mulAntidiagonal_subse
t_mul : { a | (mulAntidiagonal hs ht a).Nonempty } subseteq s * t
-/
theorem isPWO_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.mul ht).mono support_mulAntidiagonal_subset_mul

@[to_additive]
/-
**Finset.mulAntidiagonal_min_mul_min** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulAntidiagonal_min_mul_min {α} [CommMonoid α] [LinearOrder α] [IsOrderedC
ancelMonoid α] {s t : Set α} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty) (hnt
 : t.Nonempty) : mulAntidiagonal hs.isPWO ht.isPWO (hs.min hns * ht.min hnt) = {
(hs.min hns, ht.min hnt)}
参数：hs : s.IsWF；ht : t.IsWF；hns : s.Nonempty；hnt : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Set.IsWF.isPWO`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.I
sWF → s.IsPWO
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `Set.IsWF.min_le`：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α} {a 
: α} (hs : s.IsWF) (hn : s.Nonempty), a ∈ s → hs.min hn ≤ a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_lt_mul_of_lt_of_le`：mul_lt_mul_of_lt_of_le [MulLeftMono α] [MulRight
StrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c <= d) : a * c < b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `Set.IsWF.min_mem`：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} (hs :
 s.IsWF) (hn : s.Nonempty), hs.min hn ∈ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mulAntidiagonal_min_mul_min {α} [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]
    {s t : Set α} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty) (hnt : t.Nonempty) :
    mulAntidiagonal hs.isPWO ht.isPWO (hs.min hns * ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

@[deprecated (since := "2026-06-08")] alias addAntidiagonal := antidiagonal
@[deprecated (since := "2026-06-08")] alias mem_addAntidiagonal := mem_antidiagonal
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_mono_left := antidiagonal_mono_left
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_mono_right := antidiagonal_mono_right
@[deprecated (since := "2026-06-08")] alias swap_mem_addAntidiagonal := swap_mem_antidiagonal
@[deprecated (since := "2026-06-08")]
alias support_addAntidiagonal_subset_add := support_antidiagonal_subset_add
@[deprecated (since := "2026-06-08")]
alias isPWO_support_addAntidiagonal := isPWO_support_antidiagonal
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_min_mul_min := antidiagonal_min_add_min

end Finset

