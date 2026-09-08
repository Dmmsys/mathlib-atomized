/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# GCD and LCM operations on finsets

## Main definitions

- `Finset.gcd` - the greatest common denominator of a `Finset` of elements of a `GCDMonoid`
- `Finset.lcm` - the least common multiple of a `Finset` of elements of a `GCDMonoid`

## Implementation notes

Many of the proofs use the lemmas `gcd_def` and `lcm_def`, which relate `Finset.gcd`
and `Finset.lcm` to `Multiset.gcd` and `Multiset.lcm`.

TODO: simplify with a tactic and `Data.Finset.Lattice`

## Tags

finset, gcd
-/

@[expose] public section

variable {ι α β γ : Type*}

namespace Finset

open Multiset

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/


section lcm

/-- Least common multiple of a finite set -/
/-
**Finset.lcm** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：lcm (s : Finset β) (f : β -> α) : α
参数：s : Finset β；f : β -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm

--- 原说明 ---
Least common multiple of a finite set
-/
def lcm (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.lcm 1 f

variable {s s₁ s₂ : Finset β} {f : β → α}
/-
**Finset.lcm_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_def : s.lcm f = (s.1.map f).lcm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_def : s.lcm f = (s.1.map f).lcm :=
  rfl

@[simp]
/-
**Finset.lcm_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_empty : (∅ : Finset β).lcm f = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_empty : (∅ : Finset β).lcm f = 1 :=
  rfl

@[simp]
/-
**Finset.lcm_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ forall b in s, f b ∣ a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.lcm_dvd`：lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ forall 
b in s, b ∣ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a := by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩
/-
**Finset.lcm_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.lcm_dvd_iff`：lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ forall b in s, f
 b ∣ a
-/
theorem lcm_dvd {a : α} : (∀ b ∈ s, f b ∣ a) → s.lcm f ∣ a :=
  lcm_dvd_iff.2
/-
**Finset.dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
参数：hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.lcm_dvd_iff`：lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ forall b in s, f
 b ∣ a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem dvd_lcm {b : β} (hb : b ∈ s) : f b ∣ s.lcm f :=
  lcm_dvd_iff.1 dvd_rfl _ hb

@[simp]
/-
**Finset.lcm_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_insert [DecidableEq β] {b : β} : (insert b s : Finset β).lcm f = GCDMo
noid.lcm (f b) (s.lcm f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lcm_eq_right_iff`：lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h 
: normalize b = b) : lcm a b = b ↔ a ∣ b
· 使用定理 `Multiset.normalize_lcm`：normalize_lcm (s : Multiset α) : normalize s.lcm
 = s.lcm
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
-/
theorem lcm_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f) := by
  by_cases h : b ∈ s
  · rw [insert_eq_of_mem h,
      (lcm_eq_right_iff (f b) (s.lcm f) (Multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)]
  apply fold_insert h

@[simp]
/-
**Finset.lcm_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.lcm_singleton`：lcm_singleton {a : α} : ({a} : Multiset α).lcm =
 normalize a
-/
theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) :=
  Multiset.lcm_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.
/-
**Finset.normalize_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：normalize_lcm : normalize (s.lcm f) = s.lcm f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.normalize_lcm`：normalize_lcm (s : Multiset α) : normalize s.lcm
 = s.lcm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalize_lcm : normalize (s.lcm f) = s.lcm f := by simp [lcm_def]
/-
**Finset.lcm_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_union [DecidableEq β] : (s₁ union s₂).lcm f = GCDMonoid.lcm (s₁.lcm f)
 (s₂.lcm f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `Finset.lcm_empty`：lcm_empty : (∅ : Finset β).lcm f = 1
· 使用定理 `lcm_one_left`：lcm_one_left [NormalizedGCDMonoid α] (a : α) : lcm 1 a = n
ormalize a
· 使用定理 `Finset.normalize_lcm`：normalize_lcm : normalize (s.lcm f) = s.lcm f
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.lcm_insert`：lcm_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
· 使用定理 `lcm_assoc`：lcm_assoc [NormalizedGCDMonoid α] (m n k : α) : lcm (lcm m n)
 k = lcm m (lcm n k)
-/
theorem lcm_union [DecidableEq β] : (s₁ ∪ s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f) :=
  Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s _ ih ↦ by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]
/-
**Finset.lcm_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) 
: s₁.lcm f = s₂.lcm g
参数：hs : s₁ = s₂；hfg : forall a in s₂, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `instCommutativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative lcm
· 使用定理 `instAssociativeLcm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative lcm
-/
theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by
  subst hs
  exact Finset.fold_congr hfg
/-
**Finset.lcm_mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_mono_fun {g : β -> α} (h : forall b in s, f b ∣ g b) : s.lcm f ∣ s.lcm
 g
参数：h : forall b in s, f b ∣ g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.lcm_dvd`：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ 
a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
-/
theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g :=
  lcm_dvd fun b hb ↦ (h b hb).trans (dvd_lcm hb)
/-
**Finset.lcm_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_mono (h : s₁ subseteq s₂) : s₁.lcm f ∣ s₂.lcm f
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.lcm_dvd`：lcm_dvd {a : α} : (forall b in s, f b ∣ a) -> s.lcm f ∣ 
a
· 使用定理 `Finset.dvd_lcm`：dvd_lcm {b : β} (hb : b in s) : f b ∣ s.lcm f
-/
theorem lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f :=
  lcm_dvd fun _ hb ↦ dvd_lcm (h hb)
/-
**Finset.lcm_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_image [DecidableEq β] {g : γ -> β} (s : Finset γ) : (s.image g).lcm f 
= s.lcm (f ∘ g)
参数：s : Finset γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Finset.lcm_insert`：lcm_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
-/
theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]
/-
**Finset.lcm_eq_lcm_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.lcm_image`：lcm_image [DecidableEq β] {g : γ -> β} (s : Finset γ) 
: (s.image g).lcm f = s.lcm (f ∘ g)
-/
theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id :=
  Eq.symm <| lcm_image _

@[simp]
/-
**Finset.lcm_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ exists x in s, f x = 0
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
theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ ∃ x ∈ s, f x = 0 := by
  simp only [lcm_def, Multiset.lcm_eq_zero_iff, Multiset.mem_map, mem_val]
/-
**Finset.lcm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lcm_ne_zero_iff [Nontrivial α] : s.lcm f != 0 ↔ forall x in s, f x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lcm_ne_zero_iff [Nontrivial α] : s.lcm f ≠ 0 ↔ ∀ x ∈ s, f x ≠ 0 := by
  simp [lcm_eq_zero_iff]

end lcm

/-! ### gcd -/


section gcd

/-- Greatest common divisor of a finite set -/
/-
**Finset.gcd** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：gcd (s : Finset β) (f : β -> α) : α
参数：s : Finset β；f : β -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd

--- 原说明 ---
Greatest common divisor of a finite set
-/
def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f

variable {s s₁ s₂ : Finset β} {f : β → α}
/-
**Finset.gcd_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_def : s.gcd f = (s.1.map f).gcd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_def : s.gcd f = (s.1.map f).gcd :=
  rfl

@[simp]
/-
**Finset.gcd_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_empty : (∅ : Finset β).gcd f = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_empty : (∅ : Finset β).gcd f = 0 :=
  rfl
/-
**Finset.dvd_gcd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a ∣ f b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.dvd_gcd`：dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ forall 
b in s, a ∣ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b := by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩
/-
**Finset.gcd_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
参数：hb : b in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem gcd_dvd {b : β} (hb : b ∈ s) : s.gcd f ∣ f b :=
  dvd_gcd_iff.1 dvd_rfl _ hb
/-
**Finset.dvd_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：dvd_gcd {a : α} : (forall b in s, a ∣ f b) -> a ∣ s.gcd f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
-/
theorem dvd_gcd {a : α} : (∀ b ∈ s, a ∣ f b) → a ∣ s.gcd f :=
  dvd_gcd_iff.2
/-
**Finset.gcd_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_cons {b : β} (h : b ∉ s) : (cons b s h : Finset β).gcd f = GCDMonoid.g
cd (f b) (s.gcd f)
参数：h : b ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_cons`：fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a
 * s.fold op b f
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
-/
theorem gcd_cons {b : β} (h : b ∉ s) :
    (cons b s h : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) :=
  fold_cons h

@[simp]
/-
**Finset.gcd_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_insert [DecidableEq β] {b : β} : (insert b s : Finset β).gcd f = GCDMo
noid.gcd (f b) (s.gcd f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `gcd_eq_right_iff`：gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h 
: normalize b = b) : gcd a b = b ↔ b ∣ a
· 使用定理 `Multiset.normalize_gcd`：normalize_gcd (s : Multiset α) : normalize s.gcd
 = s.gcd
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
-/
theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := by
  by_cases h : b ∈ s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h

@[simp]
/-
**Finset.gcd_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.gcd_singleton`：gcd_singleton {a : α} : ({a} : Multiset α).gcd =
 normalize a
-/
theorem gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b) :=
  Multiset.gcd_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.
/-
**Finset.normalize_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：normalize_gcd : normalize (s.gcd f) = s.gcd f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.normalize_gcd`：normalize_gcd (s : Multiset α) : normalize s.gcd
 = s.gcd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [gcd_def]
/-
**Finset.gcd_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_union [DecidableEq β] : (s₁ union s₂).gcd f = GCDMonoid.gcd (s₁.gcd f)
 (s₂.gcd f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `Finset.gcd_empty`：gcd_empty : (∅ : Finset β).gcd f = 0
· 使用定理 `gcd_zero_left`：gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a =
 normalize a
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `gcd_assoc`：gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n)
 k = gcd m (gcd n k)
-/
theorem gcd_union [DecidableEq β] : (s₁ ∪ s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f) :=
  Finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd])
    fun a s _ ih ↦ by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]
/-
**Finset.gcd_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) 
: s₁.gcd f = s₂.gcd g
参数：hs : s₁ = s₂；hfg : forall a in s₂, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `instCommutativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Commutative gcd
· 使用定理 `instAssociativeGcd`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [inst
_1 : NormalizedGCDMonoid α], Std.Associative gcd
-/
theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  exact Finset.fold_congr hfg
/-
**Finset.gcd_mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_mono_fun {g : β -> α} (h : forall b in s, f b ∣ g b) : s.gcd f ∣ s.gcd
 g
参数：h : forall b in s, f b ∣ g b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.dvd_gcd`：dvd_gcd {a : α} : (forall b in s, a ∣ f b) -> a ∣ s.gcd 
f
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
-/
theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g :=
  dvd_gcd fun b hb ↦ (gcd_dvd hb).trans (h b hb)
/-
**Finset.gcd_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_mono (h : s₁ subseteq s₂) : s₂.gcd f ∣ s₁.gcd f
参数：h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.dvd_gcd`：dvd_gcd {a : α} : (forall b in s, a ∣ f b) -> a ∣ s.gcd 
f
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
-/
theorem gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f :=
  dvd_gcd fun _ hb ↦ gcd_dvd (h hb)
/-
**Finset.gcd_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_image [DecidableEq β] {g : γ -> β} (s : Finset γ) : (s.image g).gcd f 
= s.gcd (f ∘ g)
参数：s : Finset γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
-/
theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]
/-
**Finset.gcd_eq_gcd_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.gcd_image`：gcd_image [DecidableEq β] {g : γ -> β} (s : Finset γ) 
: (s.image g).gcd f = s.gcd (f ∘ g)
-/
theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id :=
  Eq.symm <| gcd_image _
/-
**Finset.gcd_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem gcd_eq_zero_iff : s.gcd f = 0 ↔ ∀ x ∈ s, f x = 0 := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s h ih => grind [gcd_cons, _root_.gcd_eq_zero_iff]
/-
**Finset.gcd_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_ne_zero_iff : s.gcd f != 0 ↔ exists x in s, f x != 0
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
theorem gcd_ne_zero_iff : s.gcd f ≠ 0 ↔ ∃ x ∈ s, f x ≠ 0 := by
  simp [gcd_eq_zero_iff]
/-
**Finset.gcd_eq_gcd_filter_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β => f x = 0] : s.gcd f =
 {x in s | f x != 0}.gcd f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
· 使用定理 `Finset.gcd_union`：gcd_union [DecidableEq β] : (s₁ union s₂).gcd f = GCDM
onoid.gcd (s₁.gcd f) (s₂.gcd f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `gcd_same`：gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize
 a
· 使用定理 `normalize_zero`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Nor
malizationMonoid α], normalize 0 = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `gcd_zero_left`：gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a =
 normalize a
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
-/
theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β ↦ f x = 0] :
    s.gcd f = {x ∈ s | f x ≠ 0}.gcd f := by
  classical
    trans ({x ∈ s | f x = 0} ∪ {x ∈ s | f x ≠ 0}).gcd f
    · rw [filter_union_filter_not_eq]
    rw [gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact gcd {x ∈ s | f x ≠ 0} f
    · refine congr (congr rfl <| s.induction_on ?_ ?_) (by simp)
      · simp
      · intro a s _ h
        rw [filter_insert]
        split_ifs with h1 <;> simp [h, h1]
    simp only [gcd_zero_left, normalize_gcd]

nonrec theorem gcd_mul_left {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    {s : Finset β} {f : β → α} {a : α} :
    (s.gcd fun x ↦ a * f x) = normalize a * s.gcd f := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [gcd_insert, gcd_insert, h, ← gcd_mul_left]
      apply ((normalize_associated a).mul_right _).gcd_eq_right

nonrec theorem gcd_mul_right {α} [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α]
    {s : Finset β} {f : β → α} {a : α} :
    (s.gcd fun x ↦ f x * a) = s.gcd f * normalize a := by
  simp_rw [mul_comm]; exact gcd_mul_left

variable (s f) in
nonrec theorem gcd_mul_left' (a : α) : Associated (s.gcd fun x ↦ a * f x) (a * s.gcd f) := by
  classical exact s.induction_on (by simp) fun b s hbs h ↦ by
             simpa using .trans (.gcd .rfl h) (gcd_mul_left' ..)

variable (s f) in
nonrec theorem gcd_mul_right' (a : α) : Associated (s.gcd fun x ↦ f x * a) (s.gcd f * a) := by
  simp_rw [mul_comm]; apply gcd_mul_left'
/-
**Finset.extract_gcd'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：extract_gcd' (f g : β -> α) (hs : exists x, x in s ∧ f x != 0) (hg : foral
l b in s, f b = s.gcd f * g b) : s.gcd g = 1
参数：f g : β -> α；hs : exists x, x in s ∧ f x != 0；hg : forall b in s, f b = s.gcd
 f * g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.normalize_gcd`：normalize_gcd : normalize (s.gcd f) = s.gcd f
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
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.gcd_congr`：gcd_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.gcd f = s₂.gcd g
· 使用定理 `Finset.gcd_mul_left'`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid
WithZero α] [inst_1 : NormalizedGCDMonoid α] (s : Finset β)   (f : β → α) (a : α
), Associa…
· 使用定理 `Associated.rfl`：∀ {M : Type u_1} [inst : Monoid M] {x : M}, Associated x
 x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.gcd_eq_zero_iff`：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f
 x = 0
-/
theorem extract_gcd' (f g : β → α) (hs : ∃ x, x ∈ s ∧ f x ≠ 0)
    (hg : ∀ b ∈ s, f b = s.gcd f * g b) : s.gcd g = 1 := by
  rw [← normalize_gcd, normalize_eq_one, ← associated_one_iff_isUnit]
  refine .of_mul_left (.symm <| .trans ?_ (gcd_mul_left' ..)) .rfl (a := s.gcd f) ?_
  · simp [← gcd_congr rfl hg]
  contrapose! hs
  exact s.gcd_eq_zero_iff.1 hs
/-
**Finset.extract_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：extract_gcd (f : β -> α) (hs : s.Nonempty) : exists g : β -> α, (forall b 
in s, f b = s.gcd f * g b) ∧ s.gcd g = 1
参数：f : β -> α；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.gcd_eq_zero_iff`：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f
 x = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.gcd_eq_gcd_image`：gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s
.image f).gcd id
· 使用定理 `Finset.image_const`：image_const {s : Finset α} (h : s.Nonempty) (b : β) 
: (s.image fun _ => b) = singleton b
· 使用定理 `Finset.gcd_singleton`：gcd_singleton {b : β} : ({b} : Finset β).gcd f = n
ormalize (f b)
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `normalize_one`：∀ {α : Type u_1} [inst : MonoidWithZero α] [inst_1 : Norm
alizationMonoid α], normalize 1 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.extract_gcd'`：extract_gcd' (f g : β -> α) (hs : exists x, x in s 
∧ f x != 0) (hg : forall b in s, f b = s.gcd f * g b) : s.gcd g = 1
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem extract_gcd (f : β → α) (hs : s.Nonempty) :
    ∃ g : β → α, (∀ b ∈ s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by
  classical
    by_cases! h : ∀ x ∈ s, f x = (0 : α)
    · refine ⟨fun _ ↦ 1, fun b hb ↦ by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [gcd_eq_gcd_image, image_const hs, gcd_singleton, id, normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      refine ⟨fun b ↦ if hb : b ∈ s then g' hb else 0, fun b hb ↦ ?_,
          extract_gcd' f _ h fun b hb ↦ ?_⟩
      · simp only [hb, hg, dite_true]
      rw [dif_pos hb, hg hb]

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
/-
**Finset.gcd_div_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：gcd_div_eq_one (his : i in s) (hfi : f i != 0) : s.gcd (fun j => f j / s.g
cd f) = 1
参数：his : i in s；hfi : f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.extract_gcd`：extract_gcd (f : β -> α) (hs : s.Nonempty) : exists 
g : β -> α, (forall b in s, f b = s.gcd f * g b) ∧ s.gcd g = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.gcd_congr`：gcd_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.gcd f = s₂.gcd g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.gcd_eq_zero_iff`：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f
 x = 0

--- 原说明 ---
Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`.
-/
lemma gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha ↦ ?_).trans hg
  rw [he a ha, mul_div_cancel_left₀]
  exact mt Finset.gcd_eq_zero_iff.1 fun h ↦ hfi <| h i his
/-
**Finset.gcd_div_id_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：gcd_div_id_eq_one {s : Finset α} {a : α} (has : a in s) (ha : a != 0) : s.
gcd (fun b => b / s.gcd id) = 1
参数：has : a in s；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.gcd_div_eq_one`：gcd_div_eq_one (his : i in s) (hfi : f i != 0) : 
s.gcd (fun j => f j / s.gcd f) = 1
-/
lemma gcd_div_id_eq_one {s : Finset α} {a : α} (has : a ∈ s) (ha : a ≠ 0) :
    s.gcd (fun b ↦ b / s.gcd id) = 1 := gcd_div_eq_one has ha

end gcd

end Finset

namespace Finset

section IsDomain

variable [CommRing α] [NormalizedGCDMonoid α]

/-
**Finset.gcd_eq_of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：gcd_eq_of_dvd_sub {s : Finset β} {f g : β -> α} {a : α} (h : forall x : β,
 x in s -> a ∣ f x - g x) : GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g
)
参数：h : forall x : β, x in s -> a ∣ f x - g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gcd_zero_right`：gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0
 = normalize a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.gcd_insert`：gcd_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `gcd_comm`：gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `gcd_assoc`：gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n)
 k = gcd m (gcd n k)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `gcd_eq_of_dvd_sub_right`：gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b 
- c) : gcd a b = gcd a c
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β → α} {a : α}
    (h : ∀ x : β, x ∈ s → a ∣ f x - g x) :
    GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) := by
  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [gcd_insert, gcd_insert, gcd_comm (f b), ← gcd_assoc,
      hi fun x hx ↦ h _ (mem_insert_of_mem hx), gcd_comm a, gcd_assoc,
      gcd_comm a (GCDMonoid.gcd _ _), gcd_comm (g b), gcd_assoc _ _ a, gcd_comm _ a]
    exact congr_arg _ (gcd_eq_of_dvd_sub_right (h _ (mem_insert_self _ _)))

end IsDomain

variable {s : Finset ι}

/-- The gcd of a finset of integers is nonnegative. -/
@[grind .]
/-
**Finset.Int.finsetGcd_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Int`。
形式化陈述：∀ {ι : Type u_1} {s : Finset ι} {f : ι → ℤ}, 0 ≤ s.gcd f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.gcd_cons`：gcd_cons {b : β} (h : b ∉ s) : (cons b s h : Finset β).
gcd f = GCDMonoid.gcd (f b) (s.gcd f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.coe_gcd`：coe_gcd (i j : Int) : ↑(Int.gcd i j) = GCDMonoid.gcd i j

--- 原说明 ---
The gcd of a finset of integers is nonnegative.
-/
theorem Int.finsetGcd_nonneg {f : ι → ℤ} : 0 ≤ s.gcd f := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [gcd_cons, ← Int.coe_gcd]
    grind

end Finset

