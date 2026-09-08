/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Unbundled
public import Batteries.Logic

/-!
# Lexicographic order on a sigma type

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `PSigma.Lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `Combinatorics.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i` per say.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `Sigma.Lex` where all summands are the same
-/

public section


namespace Sigma

variable {ι : Type*} {α : ι → Type*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}
  {a b : Σ i, α i}

/-- The lexicographical order on a sigma type. It takes in a relation on the index type and a
relation for each summand. `a` is related to `b` iff their summands are related or they are in the
same summand and are related through the summand's relation. -/
/-
**Sigma.Lex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Sigma`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} → (ι → ι → Prop) → ((i : ι) → α i → 
α i → Prop) → (i : ι) × α i → (i : ι) × α i → Prop
参数：ι → ι → Prop；(i : ι) → α i → α i → Prop；i : ι；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographical order on a sigma type. It takes in a relation on the index t
ype and a
relation for each summand. `a` is related to `b` iff their summands are related 
or they are in the
same summand and are related through the summand's relation.
-/
inductive Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) : ∀ _ _ : Σ i, α i, Prop
  | left {i j : ι} (a : α i) (b : α j) : r i j → Lex r s ⟨i, a⟩ ⟨j, b⟩
  | right {i : ι} (a b : α i) : s i a b → Lex r s ⟨i, a⟩ ⟨i, b⟩
/-
**Sigma.lex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1, s b.1 (h.rec a.2
) b.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ _ h
/-
**Sigma.Lex.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Sigma.Lex`。
形式化陈述：{ι : Type u_1} →   {α : ι → Type u_2} →     (r : ι → ι → Prop) →       (s 
: (i : ι) → α i → α i → Prop) →         [DecidableEq ι] → [DecidableRel r] → [(i
 : ι) → DecidableRel (s i)] → DecidableRel (Sigma.Lex r s)
参数：r : ι → ι → Prop；s : (i : ι) → α i → α i → Prop；i : ι；s i；Sigma.Lex r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
/-
**Sigma.Lex.mono** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : (i : ι
) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →     (∀ (i : ι) (a b : 
α i), s₁ i a b → s₂ i a b) → ∀ {a b : (i : ι) × α i}, Sigma.Lex r₁ s₁ a b → Sigm
a.Lex r₂ s₂ a b
参数：i : ι；∀ (a b : ι), r₁ a b → r₂ a b；∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b
；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ _ (hs _ _ _ hab)
/-
**Sigma.Lex.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {r₁ r₂ : ι → ι → Prop} {s : (i : ι) → 
α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) → ∀ {a b : (i : ι) × α i}, S
igma.Lex r₁ s a b → Sigma.Lex r₂ s a b
参数：i : ι；∀ (a b : ι), r₁ a b → r₂ a b；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.Lex.mono`：∀ {ι : Type u_1} {α : ι → Type u_2} {r₁ r₂ : ι → ι → Pro
p} {s₁ s₂ : (i : ι) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →     
(∀ (…
-/
theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ i, α i} (h : Lex r₁ s a b) :
    Lex r₂ s a b :=
  h.mono hr fun _ _ _ => id
/-
**Sigma.Lex.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Sigma.Lex`。
形式化陈述：∀ {ι : Type u_1} {α : ι → Type u_2} {r : ι → ι → Prop} {s₁ s₂ : (i : ι) → 
α i → α i → Prop},   (∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b) → ∀ {a b : (i 
: ι) × α i}, Sigma.Lex r s₁ a b → Sigma.Lex r s₂ a b
参数：i : ι；∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sigma.Lex.mono`：∀ {ι : Type u_1} {α : ι → Type u_2} {r₁ r₂ : ι → ι → Pro
p} {s₁ s₂ : (i : ι) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →     
(∀ (…
-/
theorem Lex.mono_right (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i} (h : Lex r s₁ a b) :
    Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs
/-
**Sigma.lex_swap** 是 Mathlib 中的一个定理，位于命名空间 `Sigma`。
形式化陈述：lex_swap : Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s 
i)) b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lex_swap : Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a := by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      · exact Lex.left _ _ h
      · exact Lex.right _ _ h
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Std.Refl (s i)] : Std.Refl (Lex r s) :=
  ⟨fun ⟨_, _⟩ => Lex.right _ _ <| refl _⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] [∀ i, Std.Irrefl (s i)] : Std.Irrefl (Lex r s) :=
  ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    · exact irrefl _ hi
    · exact irrefl _ ha
      ⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans ι r] [∀ i, IsTrans (α i) (s i)] : IsTrans _ (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact Lex.left _ _ (_root_.trans hij hk)
    · exact Lex.left _ _ hij
    · exact Lex.left _ _ hk
    · exact Lex.right _ _ (_root_.trans hab hc)⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Symm r] [∀ i, Std.Symm (s i)] : Std.Symm (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Lex.left _ _ (symm hij)
    · exact Lex.right _ _ (symm hab)
      ⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Asymm r] [∀ i, Std.Antisymm (s i)] : Std.Antisymm (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
    · exact (irrefl _ hij).elim
    · exact (irrefl _ hji).elim
    · exact congr_arg (Sigma.mk _ ·) <| antisymm hab hba⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Trichotomous r] [∀ i, Std.Total (s i)] : Std.Total (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | hba := total_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Lex.right _ _ hba)
    · exact Or.inr (Lex.left _ _ hji)⟩
/-
**Sigma.** 是 Mathlib 中的一个实例，位于命名空间 `Sigma`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Trichotomous r] [∀ i, Std.Trichotomous (s i)] : Std.Trichotomous (Lex r s) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap <| by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr <| Lex.right _ _ hba)
    · exact Or.inr (Or.inr <| Lex.left _ _ hji)

end Sigma

/-! ### `PSigma` -/


namespace PSigma

variable {ι : Sort*} {α : ι → Sort*} {r : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}

/-
**PSigma.lex_iff** 是 Mathlib 中的一个定理，位于命名空间 `PSigma`。
形式化陈述：lex_iff {a b : Σ' i, α i} : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1
, s b.1 (h.rec a.2) b.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lex_iff {a b : Σ' i, α i} :
    Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ h
/-
**PSigma.Lex.decidable** 是 Mathlib 中的一个定义，位于命名空间 `PSigma.Lex`。
形式化陈述：{ι : Sort u_1} →   {α : ι → Sort u_2} →     (r : ι → ι → Prop) →       (s 
: (i : ι) → α i → α i → Prop) →         [DecidableEq ι] → [DecidableRel r] → [(i
 : ι) → DecidableRel (s i)] → DecidableRel (PSigma.Lex r s)
参数：r : ι → ι → Prop；s : (i : ι) → α i → α i → Prop；i : ι；s i；PSigma.Lex r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
/-
**PSigma.Lex.mono** 是 Mathlib 中的一个定理，位于命名空间 `PSigma.Lex`。
形式化陈述：∀ {ι : Sort u_1} {α : ι → Sort u_2} {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : (i : ι
) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →     (∀ (i : ι) (a b : 
α i), s₁ i a b → s₂ i a b) → ∀ {a b : (i : ι) ×' α i}, PSigma.Lex r₁ s₁ a b → PS
igma.Lex r₂ s₂ a b
参数：i : ι；∀ (a b : ι), r₁ a b → r₂ a b；∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b
；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Lex.mono {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
    (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ (hs _ _ _ hab)
/-
**PSigma.Lex.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `PSigma.Lex`。
形式化陈述：∀ {ι : Sort u_1} {α : ι → Sort u_2} {r₁ r₂ : ι → ι → Prop} {s : (i : ι) → 
α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) → ∀ {a b : (i : ι) ×' α i}, 
PSigma.Lex r₁ s a b → PSigma.Lex r₂ s a b
参数：i : ι；∀ (a b : ι), r₁ a b → r₂ a b；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSigma.Lex.mono`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {r₁ r₂ : ι → ι → Pr
op} {s₁ s₂ : (i : ι) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →    
 (∀ (…
-/
theorem Lex.mono_left {r₁ r₂ : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}
    (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ' i, α i} (h : Lex r₁ s a b) : Lex r₂ s a b :=
  h.mono hr fun _ _ _ => id
/-
**PSigma.Lex.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `PSigma.Lex`。
形式化陈述：∀ {ι : Sort u_1} {α : ι → Sort u_2} {r : ι → ι → Prop} {s₁ s₂ : (i : ι) → 
α i → α i → Prop},   (∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b) → ∀ {a b : (i 
: ι) ×' α i}, PSigma.Lex r s₁ a b → PSigma.Lex r s₂ a b
参数：i : ι；∀ (i : ι) (a b : α i), s₁ i a b → s₂ i a b；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSigma.Lex.mono`：∀ {ι : Sort u_1} {α : ι → Sort u_2} {r₁ r₂ : ι → ι → Pr
op} {s₁ s₂ : (i : ι) → α i → α i → Prop},   (∀ (a b : ι), r₁ a b → r₂ a b) →    
 (∀ (…
-/
theorem Lex.mono_right {r : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
    (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i} (h : Lex r s₁ a b) : Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs

end PSigma

