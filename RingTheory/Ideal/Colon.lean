/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

@[expose] public section

namespace Submodule

open scoped Pointwise

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {N N₁ N₂ : Submodule R M} {S S₁ S₂ : Set M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`.
We treat it as an infix in lemma names. -/
/-
**Submodule.colon** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：colon (N : Submodule R M) (S : Set M) : Ideal R where carrier
参数：N : Submodule R M；S : Set M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`.
We treat it as an infix in lemma names.
-/
def colon (N : Submodule R M) (S : Set M) : Ideal R where
  carrier := {r : R | (r • S : Set M) ⊆ N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_iff]
    intro x hx y hy
    exact N.smul_mem _ (hx hy)
/-
**Submodule.mem_colon** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_colon {r} : r in N.colon S ↔ forall s in S, r • s in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
-/
theorem mem_colon {r} : r ∈ N.colon S ↔ ∀ s ∈ S, r • s ∈ N := Set.smul_set_subset_iff

@[simp]
/-
**Submodule.mem_colon_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_colon_singleton {x : M} {r : R} : r in N.colon {x} ↔ r • x in N
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_colon_singleton {x : M} {r : R} : r ∈ N.colon {x} ↔ r • x ∈ N := by
  simp [mem_colon, forall_eq]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) (P : Submodule R M) : (N.colon (P : Set M)).IsTwoSided where
  mul_mem_of_left {r} s hr p hp := by
    obtain ⟨p, hp, rfl⟩ := hp
    exact hr ⟨_, P.smul_mem _ hp, (mul_smul ..).symm⟩

@[simp]
/-
**Submodule.colon_univ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon Set.univ = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial`：True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
-/
theorem colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon Set.univ = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x ↦ ⟨fun h ↦ mul_one x ▸ h 1 trivial, fun h _ _ ↦ I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]
/-
**Submodule.bot_colon** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_colon : colon (⊥ : Submodule R M) (N : Set M) = N.annihilator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bot_colon : colon (⊥ : Submodule R M) (N : Set M) = N.annihilator := by
  ext x
  simp [mem_colon, mem_annihilator]
/-
**Submodule.colon_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：colon_mono (hn : N₁ <= N₂) (hs : S₁ subseteq S₂) : N₁.colon S₂ <= N₂.colon
 S₁
参数：hn : N₁ <= N₂；hs : S₁ subseteq S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_colon`：mem_colon {r} : r in N.colon S ↔ forall s in S, r •
 s in N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem colon_mono (hn : N₁ ≤ N₂) (hs : S₁ ⊆ S₂) : N₁.colon S₂ ≤ N₂.colon S₁ :=
  fun _ hrns ↦ mem_colon.mpr fun s₁ hs₁ ↦ hn <| mem_colon.mp hrns s₁ <| hs hs₁
/-
**Submodule._root_.Ideal.le_colon** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.le_colon {I : Ideal R} {S : Set R} [I.IsTwoSided] : I ≤ I.colon S :=
  colon_univ.symm.trans_le (colon_mono le_rfl S.subset_univ)
/-
**Submodule.iInf_colon_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iInf_colon_iUnion (ι₁ : Sort*) (f : ι₁ -> Submodule R M) (ι₂ : Sort*) (g :
 ι₂ -> Set M) : (⨅ i, f i).colon (⋃ j, g j) = ⨅ (i) (j), (f i).colon (g j)
参数：ι₁ : Sort*；f : ι₁ -> Submodule R M；ι₂ : Sort*；g : ι₂ -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
theorem iInf_colon_iUnion (ι₁ : Sort*) (f : ι₁ → Submodule R M) (ι₂ : Sort*) (g : ι₂ → Set M) :
    (⨅ i, f i).colon (⋃ j, g j) = ⨅ (i) (j), (f i).colon (g j) := by
  aesop (add simp mem_colon)

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

/-- If `S ⊆ N₂`, then intersecting with `N₂` does not change the colon ideal. -/
/-
**Submodule.colon_inf_eq_left_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_inf_eq_left_of_subset (h : S subseteq (N₂ : Set M)) : (N₁ ⊓ N₂).colo
n S = N₁.colon S
参数：h : S subseteq (N₂ : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …

--- 原说明 ---
If `S ⊆ N₂`, then intersecting with `N₂` does not change the colon ideal.
-/
lemma colon_inf_eq_left_of_subset (h : S ⊆ (N₂ : Set M)) : (N₁ ⊓ N₂).colon S = N₁.colon S := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.colon_eq_top_iff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_eq_top_iff_subset (S : Set M) : N.colon S = ⊤ ↔ S subseteq N
参数：S : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma colon_eq_top_iff_subset (S : Set M) : N.colon S = ⊤ ↔ S ⊆ N := by
  aesop (add simp [mem_colon, Ideal.eq_top_iff_one])

@[simp]
/-
**Submodule.inf_colon** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.iInf_colon** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：iInf_colon {ι : Sort*} (f : ι -> Submodule R M) : (⨅ i, f i).colon S = ⨅ i
, (f i).colon S
参数：f : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma iInf_colon {ι : Sort*} (f : ι → Submodule R M) : (⨅ i, f i).colon S = ⨅ i, (f i).colon S := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.colon_finsetInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_finsetInf {ι : Type*} (s : Finset ι) (f : ι -> Submodule R M) : (s.i
nf f).colon S = s.inf (fun i => (f i).colon S)
参数：s : Finset ι；f : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma colon_finsetInf {ι : Type*} (s : Finset ι) (f : ι → Submodule R M) :
    (s.inf f).colon S = s.inf (fun i ↦ (f i).colon S) := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.top_colon** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：top_colon : (⊤ : Submodule R M).colon S = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma top_colon : (⊤ : Submodule R M).colon S = ⊤ := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.colon_union** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_union : N.colon (S₁ union S₂) = N.colon S₁ ⊓ N.colon S₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma colon_union : N.colon (S₁ ∪ S₂) = N.colon S₁ ⊓ N.colon S₂ := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.colon_iUnion** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_iUnion {ι : Sort*} (f : ι -> Set M) : N.colon (⋃ i, f i) = ⨅ i, N.co
lon (f i)
参数：f : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma colon_iUnion {ι : Sort*} (f : ι → Set M) : N.colon (⋃ i, f i) = ⨅ i, N.colon (f i) := by
  aesop (add simp mem_colon)

@[simp]
/-
**Submodule.colon_empty** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_empty : N.colon (∅ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma colon_empty : N.colon (∅ : Set M) = ⊤ := by
  aesop (add simp mem_colon)
/-
**Submodule.colon_singleton_zero** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_singleton_zero : N.colon {0} = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma colon_singleton_zero : N.colon {0} = ⊤ := by
  simp
/-
**Submodule.colon_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：colon_bot : N.colon ((⊥ : Submodule R M) : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma colon_bot : N.colon ((⊥ : Submodule R M) : Set M) = ⊤ := by
  simp

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N N' : Submodule R M} {S : Set M}

@[deprecated mem_colon (since := "2026-01-15")]
/-
**Submodule.mem_colon'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_colon' {r} : r in N.colon S ↔ S <= comap (r • (LinearMap.id : M ->ₗ[R]
 M)) N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_colon`：mem_colon {r} : r in N.colon S ↔ forall s in S, r •
 s in N
-/
theorem mem_colon' {r} : r ∈ N.colon S ↔ S ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) N :=
  mem_colon
/-
**Submodule.mem_colon_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_colon_iff_le {r} : r in N.colon N' ↔ r • N' <= N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_colon_iff_le {r} : r ∈ N.colon N' ↔ r • N' ≤ N := by
  aesop (add simp SetLike.coe_subset_coe)

/-- A variant for arbitrary sets in commutative semirings -/
/-
**Submodule.bot_colon'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_colon' : (⊥ : Submodule R M).colon S = (span R S).annihilator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant for arbitrary sets in commutative semirings
-/
theorem bot_colon' : (⊥ : Submodule R M).colon S = (span R S).annihilator := by
  aesop (add simp [mem_colon, mem_annihilator_span])

@[simp]
/-
**Submodule.colon_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：colon_span : N.colon (span R S) = N.colon S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.colon_mono`：colon_mono (hn : N₁ <= N₂) (hs : S₁ subseteq S₂) :
 N₁.colon S₂ <= N₂.colon S₁
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_colon`：mem_colon {r} : r in N.colon S ↔ forall s in S, r •
 s in N
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem colon_span : N.colon (span R S) = N.colon S := by
  refine (colon_mono le_rfl subset_span).antisymm fun r h ↦ mem_colon.mpr fun s hs ↦ ?_
  induction hs using Submodule.span_induction with
  | mem => aesop (add simp mem_colon)
  | zero => simp
  | add => aesop
  | smul => simp_all [smul_mem, smul_comm r]
/-
**Submodule._root_.Ideal.colon_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.colon_span {I : Ideal R} {S : Set R} : I.colon (Ideal.span S) = I.colon S := by
  simp
/-
**Submodule.mem_colon_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_colon_span_singleton {x : M} {r : R} : r in N.colon (span R {x}) ↔ r •
 x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.colon_span`：colon_span : N.colon (span R S) = N.colon S
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_colon_span_singleton {x : M} {r : R} : r ∈ N.colon (span R {x}) ↔ r • x ∈ N := by
  simp
/-
**Submodule._root_.Ideal.mem_colon_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.mem_colon_span_singleton {I : Ideal R} {x r : R} :
    r ∈ I.colon (Ideal.span {x}) ↔ r * x ∈ I := by
  simp

end CommSemiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
variable {N P : Submodule R M}

@[simp]
/-
**Submodule.annihilator_map_mkQ_eq_colon** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon (P : Se
t M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_annihilator`：mem_annihilator {r} : r in N.annihilator ↔ fo
rall n in N, r • n = (0 : M)
· 使用定理 `Submodule.mem_colon`：mem_colon {r} : r in N.colon S ↔ forall s in S, r •
 s in N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon (P : Set M) := by
  ext
  rw [mem_annihilator, mem_colon]
  exact ⟨fun H p hp ↦ (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ ↦ hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩
/-
**Submodule.annihilator_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Submodule.annihilator_top`：annihilator_top : (⊤ : Submodule R M).annihil
ator = Module.annihilator R M
· 使用引理 `Submodule.annihilator_map_mkQ_eq_colon`：annihilator_map_mkQ_eq_colon : a
nnihilator (P.map N.mkQ) = N.colon (P : Set M)
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon Set.univ := by
  ext r
  have htop : (⊤ : Submodule R (M ⧸ N)) = (⊤ : Submodule R M).map N.mkQ := by
    simpa [map_top] using (LinearMap.range_eq_top.mpr (mkQ_surjective N)).symm
  rw [← annihilator_top (R := R) (M := M ⧸ N), htop,
    annihilator_map_mkQ_eq_colon (N := N) (P := ⊤), Submodule.top_coe]
/-
**Submodule._root_.Ideal.annihilator_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.annihilator_quotient {I : Ideal R} [I.IsTwoSided] :
    Module.annihilator R (R ⧸ I) = I := by
  rw [Submodule.annihilator_quotient, colon_univ]

end Ring

end Submodule

