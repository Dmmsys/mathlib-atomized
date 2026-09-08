/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Fintype instances for pi types
-/

@[expose] public section

assert_not_exists IsOrderedRing MonoidWithZero

open Finset Function

variable {α β : Type*}

namespace Fintype

variable [DecidableEq α] [Fintype α] {γ δ : α → Type*} {s : ∀ a, Finset (γ a)}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition). -/
/-
**Fintype.piFinset** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：piFinset (t : forall a, Finset (δ a)) : Finset (forall a, δ a)
参数：t : forall a, Finset (δ a)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `Fintype.piFinset t` of all functions taking values in `t a` for all `a`.
 This is the
analogue of `Finset.pi` where the base finset is `univ` (but formally they are n
ot the same, as
there is an additional condition `i ∈ Finset.univ` in the `Finset.pi` definition
).
-/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ =>
    by simp +contextual [funext_iff]⟩

@[simp, grind =]
/-
**Fintype.mem_piFinset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：mem_piFinset {t : forall a, Finset (δ a)} {f : forall a, δ a} : f in piFin
set t ↔ forall a, f a in t a
参数：δ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a := by
  constructor
  · simp only [piFinset, mem_map, and_imp, forall_prop_of_true, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [piFinset, mem_map, forall_prop_of_true, mem_univ, mem_pi]
    exact fun hf => ⟨fun a _ => f a, hf, rfl⟩

@[simp]
/-
**Fintype.coe_piFinset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：coe_piFinset (t : forall a, Finset (δ a)) : (piFinset t : Set (forall a, δ
 a)) = Set.pi Set.univ fun a => t a
参数：t : forall a, Finset (δ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
-/
theorem coe_piFinset (t : ∀ a, Finset (δ a)) :
    (piFinset t : Set (∀ a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset
/-
**Fintype.piFinset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_subset (t₁ t₂ : forall a, Finset (δ a)) (h : forall a, t₁ a subse
teq t₂ a) : piFinset t₁ subseteq piFinset t₂
参数：t₁ t₂ : forall a, Finset (δ a)；h : forall a, t₁ a subseteq t₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem piFinset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
    piFinset t₁ ⊆ piFinset t₂ := fun _ hg => mem_piFinset.2 fun a => h a <| mem_piFinset.1 hg a

@[simp]
/-
**Fintype.piFinset_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_eq_empty : piFinset s = ∅ ↔ exists i, s i = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem piFinset_eq_empty : piFinset s = ∅ ↔ ∃ i, s i = ∅ := by simp [piFinset]

@[simp]
/-
**Fintype.piFinset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : forall i, Finset (δ i
)) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ := by simp

@[simp]
/-
**Fintype.piFinset_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_nonempty : (piFinset s).Nonempty ↔ forall a, (s a).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma piFinset_nonempty : (piFinset s).Nonempty ↔ ∀ a, (s a).Nonempty := by simp [piFinset]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, Aesop.piFinset_nonempty_of_forall_nonempty⟩ := piFinset_nonempty
/-
**Fintype._root_.Finset.Nonempty.piFinset_const** 是 Mathlib 中的一个引理，位于命名空间 `Finty
pe`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finset.Nonempty.piFinset_const {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Finset β}
    (hs : s.Nonempty) : (piFinset fun _ : ι ↦ s).Nonempty := piFinset_nonempty.2 fun _ ↦ hs

@[simp]
/-
**Fintype.piFinset_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_of_isEmpty [IsEmpty α] (s : forall a, Finset (γ a)) : piFinset s 
= univ
参数：s : forall a, Finset (γ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_univ_of_forall`：eq_univ_of_forall : (forall x, x in s) -> s = 
univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma piFinset_of_isEmpty [IsEmpty α] (s : ∀ a, Finset (γ a)) : piFinset s = univ :=
  eq_univ_of_forall fun _ ↦ by simp

@[simp]
/-
**Fintype.piFinset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_singleton (f : forall i, δ i) : piFinset (fun i => {f i} : forall
 i, Finset (δ i)) = {f}
参数：f : forall i, δ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
-/
theorem piFinset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by grind
/-
**Fintype.piFinset_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_subsingleton {f : forall i, Finset (δ i)} (hf : forall i, (f i : 
Set (δ i)).Subsingleton) : (Fintype.piFinset f : Set (forall i, δ i)).Subsinglet
on
参数：δ i；hf : forall i, (f i : Set (δ i)).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
-/
theorem piFinset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun _ ha _ hb =>
  funext fun _ => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)
/-
**Fintype.piFinset_disjoint_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：piFinset_disjoint_of_disjoint (t₁ t₂ : forall a, Finset (δ a)) {a : α} (h 
: Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂)
参数：t₁ t₂ : forall a, Finset (δ a)；h : Disjoint (t₁ a) (t₂ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem piFinset_disjoint_of_disjoint (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)
/-
**Fintype.piFinset_image** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_image [forall a, DecidableEq (δ a)] (f : forall a, γ a -> δ a) (s
 : forall a, Finset (γ a)) : piFinset (fun a => (s a).image (f a)) = (piFinset s
).image fun b a => f _ (b a)
参数：δ a；f : forall a, γ a -> δ a；s : forall a, Finset (γ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma piFinset_image [∀ a, DecidableEq (δ a)] (f : ∀ a, γ a → δ a) (s : ∀ a, Finset (γ a)) :
    piFinset (fun a ↦ (s a).image (f a)) = (piFinset s).image fun b a ↦ f _ (b a) := by
  ext; simp only [mem_piFinset, mem_image, Classical.skolem, forall_and, funext_iff]
/-
**Fintype.eval_image_piFinset_subset** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：eval_image_piFinset_subset (t : forall a, Finset (δ a)) (a : α) [Decidable
Eq (δ a)] : ((piFinset t).image fun f => f a) subseteq t a
参数：t : forall a, Finset (δ a)；a : α；δ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.mem_piFinset`：mem_piFinset {t : forall a, Finset (δ a)} {f : for
all a, δ a} : f in piFinset t ↔ forall a, f a in t a
-/
lemma eval_image_piFinset_subset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)] :
    ((piFinset t).image fun f ↦ f a) ⊆ t a := image_subset_iff.2 fun _x hx ↦ mem_piFinset.1 hx _
/-
**Fintype.eval_image_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：eval_image_piFinset (t : forall a, Finset (δ a)) (a : α) [DecidableEq (δ a
)] (ht : forall b, a != b -> (t b).Nonempty) : ((piFinset t).image fun f => f a)
 = t a
参数：t : forall a, Finset (δ a)；a : α；δ a；ht : forall b, a != b -> (t b).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Fintype.eval_image_piFinset_subset`：eval_image_piFinset_subset (t : fora
ll a, Finset (δ a)) (a : α) [DecidableEq (δ a)] : ((piFinset t).image fun f => f
 a) subseteq t a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma eval_image_piFinset (t : ∀ a, Finset (δ a)) (a : α) [DecidableEq (δ a)]
    (ht : ∀ b, a ≠ b → (t b).Nonempty) : ((piFinset t).image fun f ↦ f a) = t a := by
  refine (eval_image_piFinset_subset _ _).antisymm fun x h ↦ mem_image.2 ?_
  choose f hf using ht
  exact ⟨fun b ↦ if h : a = b then h ▸ x else f _ h, by aesop, by simp⟩
/-
**Fintype.eval_image_piFinset_const** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：eval_image_piFinset_const {β} [DecidableEq β] (t : Finset β) (a : α) : ((p
iFinset fun _i : α => t).image fun f => f a) = t
参数：t : Finset β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.piFinset_empty`：piFinset_empty [Nonempty α] : piFinset (fun _ =>
 ∅ : forall i, Finset (δ i)) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fintype.eval_image_piFinset`：eval_image_piFinset (t : forall a, Finset (
δ a)) (a : α) [DecidableEq (δ a)] (ht : forall b, a != b -> (t b).Nonempty) : ((
piFinset t).image…
-/
lemma eval_image_piFinset_const {β} [DecidableEq β] (t : Finset β) (a : α) :
    ((piFinset fun _i : α ↦ t).image fun f ↦ f a) = t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · have : Nonempty α := ⟨a⟩
    simp
  · exact eval_image_piFinset (fun _ ↦ t) a fun _ _ ↦ ht

variable [∀ a, DecidableEq (δ a)]
/-
**Fintype.piFinset_inter** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_inter (s t : forall a, Finset (δ a)) : piFinset (fun i => s i int
er t i) = piFinset s inter piFinset t
参数：s t : forall a, Finset (δ a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piFinset_inter (s t : ∀ a, Finset (δ a)) :
    piFinset (fun i ↦ s i ∩ t i) = piFinset s ∩ piFinset t := by
  grind
/-
**Fintype.filter_piFinset_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：filter_piFinset_of_notMem (t : forall a, Finset (δ a)) (a : α) (x : δ a) (
hx : x ∉ t a) : {f in piFinset t | f a = x} = ∅
参数：t : forall a, Finset (δ a)；a : α；x : δ a；hx : x ∉ t a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filter_piFinset_of_notMem (t : ∀ a, Finset (δ a)) (a : α) (x : δ a) (hx : x ∉ t a) :
    {f ∈ piFinset t | f a = x} = ∅ := by
  grind
/-
**Fintype.piFinset_update_eq_filter_piFinset_mem** 是 Mathlib 中的一个引理，位于命名空间 `Fint
ype`。
形式化陈述：piFinset_update_eq_filter_piFinset_mem (s : forall i, Finset (δ i)) (i : α
) {t : Finset (δ i)} (hts : t subseteq s i) : piFinset (Function.update s i t) =
 {f in piFinset s | f i in t}
参数：s : forall i, Finset (δ i)；i : α；δ i；hts : t subseteq s i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piFinset_update_eq_filter_piFinset_mem (s : ∀ i, Finset (δ i)) (i : α) {t : Finset (δ i)}
    (hts : t ⊆ s i) : piFinset (Function.update s i t) = {f ∈ piFinset s | f i ∈ t} := by
  grind
/-
**Fintype.piFinset_update_singleton_eq_filter_piFinset_eq** 是 Mathlib 中的一个引理，位于命
名空间 `Fintype`。
形式化陈述：piFinset_update_singleton_eq_filter_piFinset_eq (s : forall i, Finset (δ i
)) (i : α) {a : δ i} (ha : a in s i) : piFinset (Function.update s i {a}) = {f i
n piFinset s | f i = a}
参数：s : forall i, Finset (δ i)；i : α；ha : a in s i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piFinset_update_singleton_eq_filter_piFinset_eq (s : ∀ i, Finset (δ i)) (i : α) {a : δ i}
    (ha : a ∈ s i) :
    piFinset (Function.update s i {a}) = {f ∈ piFinset s | f i = a} := by
  grind

end Fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
/-
**Pi.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instFintype {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype α] [f
orall a, Fintype (β a)] : Fintype (forall a, β a)
参数：β a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent product of fintypes, indexed by a fintype, is a fintype.
-/
instance Pi.instFintype {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] : Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩

@[simp]
/-
**Fintype.piFinset_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.piFinset_univ {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintyp
e α] [forall a, Fintype (β a)] : (Fintype.piFinset fun a : α => (Finset.univ : F
inset (β a))) = (Finset.univ : Finset (forall a, β a))
参数：β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Fintype.piFinset_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl

/-- There are finitely many embeddings between finite types.

This instance used to be computable (using `DecidableEq` arguments), but
it makes things a lot harder to work with here.
-/
/-
**_root_.Function.Embedding.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.Function.Embedding.fintype {α β} [Fintype α] [Fintype β] : Fintype 
(α ↪ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are finitely many embeddings between finite types.

This instance used to be computable (using `DecidableEq` arguments), but
it makes things a lot harder to work with here.
-/
noncomputable instance _root_.Function.Embedding.fintype {α β} [Fintype α] [Fintype β] :
    Fintype (α ↪ β) := by
  classical exact Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)
/-
**RelHom.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RelHom.instFintype {α β} [Fintype α] [Fintype β] [DecidableEq α] {r : α ->
 α -> Prop} {s : β -> β -> Prop} [DecidableRel r] [DecidableRel s] : Fintype (r 
->r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.map_rel'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} {s :
 β → β → Prop} (self : r →r s) {a b : α},   r a b → s (self.toFun a) (self.toFun
 b)
-/
instance RelHom.instFintype {α β} [Fintype α] [Fintype β] [DecidableEq α] {r : α → α → Prop}
    {s : β → β → Prop} [DecidableRel r] [DecidableRel s] : Fintype (r →r s) :=
  Fintype.ofEquiv {f : α → β // ∀ {x y}, r x y → s (f x) (f y)} <| Equiv.mk
    (fun f ↦ ⟨f.1, f.2⟩) (fun f ↦ ⟨f.1, f.2⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)
/-
**RelEmbedding.instFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：RelEmbedding.instFintype {α β} [Fintype α] [Fintype β] {r : α -> α -> Prop
} {s : β -> β -> Prop} : Fintype (r ↪r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.toEmbedding_injective`：toEmbedding_injective : Injective (t
oEmbedding : r ↪r s -> (α ↪ β))
-/
noncomputable instance RelEmbedding.instFintype {α β} [Fintype α] [Fintype β]
    {r : α → α → Prop} {s : β → β → Prop} : Fintype (r ↪r s) :=
  Fintype.ofInjective _ RelEmbedding.toEmbedding_injective

@[simp]
/-
**Finset.univ_pi_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_pi_univ {α : Type*} {β : α -> Type*} [DecidableEq α] [Fintype 
α] [forall a, Fintype (β a)] : (Finset.univ.pi fun a : α => (Finset.univ : Finse
t (β a))) = Finset.univ
参数：β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Finset.univ_pi_univ {α : Type*} {β : α → Type*} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by
  ext; simp

/-! ### Diagonal -/

namespace Finset
variable {ι : Type*} [DecidableEq (ι → α)] {s : Finset α} {f : ι → α}

/-
**Finset.piFinset_filter_const** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piFinset_filter_const [DecidableEq ι] [Fintype ι] : {f in Fintype.piFinset
 fun _ : ι => s | exists a in s, const ι a = f} = s.piDiag ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma piFinset_filter_const [DecidableEq ι] [Fintype ι] :
    {f ∈ Fintype.piFinset fun _ : ι ↦ s | ∃ a ∈ s, const ι a = f} = s.piDiag ι := by aesop
/-
**Finset.piDiag_subset_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：piDiag_subset_piFinset [DecidableEq ι] [Fintype ι] : s.piDiag ι subseteq F
intype.piFinset fun _ => s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma piDiag_subset_piFinset [DecidableEq ι] [Fintype ι] :
    s.piDiag ι ⊆ Fintype.piFinset fun _ ↦ s := by simp [← piFinset_filter_const]

end Finset

namespace Set

/-! ### Constructors for `Set.Finite`

Every constructor here should have a corresponding `Fintype` instance in the previous section
(or in the `Fintype` module).

The implementation of these constructors ideally should be no more than `Set.toFinite`,
after possibly setting up some `Fintype` and classical `Decidable` instances.
-/


section SetFiniteConstructors

section Pi
variable {ι : Type*} [Finite ι] {κ : ι → Type*} {t : ∀ i, Set (κ i)}

/-- Finite product of finite sets is finite -/
/-
**Set.Finite.pi** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_3} [Finite ι] {κ : ι → Type u_4} {t : (i : ι) → Set (κ i)}, 
  (∀ (i : ι), (t i).Finite) → (Set.univ.pi t).Finite
参数：i : ι；κ i；∀ (i : ι), (t i).Finite；Set.univ.pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.coe_piFinset`：coe_piFinset (t : forall a, Finset (δ a)) : (piFin
set t : Set (forall a, δ a)) = Set.pi Set.univ fun a => t a
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
Finite product of finite sets is finite
-/
theorem Finite.pi (ht : ∀ i, (t i).Finite) : (pi univ t).Finite := by
  cases nonempty_fintype ι
  lift t to ∀ d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet

/-- Finite product of finite sets is finite. Note this is a variant of `Set.Finite.pi` without the
extra `i ∈ univ` binder. -/
/-
**Set.Finite.pi'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_3} [Finite ι] {κ : ι → Type u_4} {t : (i : ι) → Set (κ i)}, 
  (∀ (i : ι), (t i).Finite) → {f | ∀ (i : ι), f i ∈ t i}.Finite
参数：i : ι；κ i；∀ (i : ι), (t i).Finite；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.Finite.pi`：∀ {ι : Type u_3} [Finite ι] {κ : ι → Type u_4} {t : (i : 
ι) → Set (κ i)},   (∀ (i : ι), (t i).Finite) → (Set.univ.pi t).Finite

--- 原说明 ---
Finite product of finite sets is finite. Note this is a variant of `Set.Finite.p
i` without the
extra `i ∈ univ` binder.
-/
lemma Finite.pi' (ht : ∀ i, (t i).Finite) : {f : ∀ i, κ i | ∀ i, f i ∈ t i}.Finite := by
  simpa [Set.pi] using Finite.pi ht

end Pi

end SetFiniteConstructors

/-
**Set.forall_finite_image_eval_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ -> Type*} {s : 
Set (forall d, κ d)} : (forall d, (eval d '' s).Finite) ↔ s.Finite
参数：forall d, κ d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.pi`：∀ {ι : Type u_3} [Finite ι] {κ : ι → Type u_4} {t : (i : 
ι) → Set (κ i)},   (∀ (i : ι), (t i).Finite) → (Set.univ.pi t).Finite
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem forall_finite_image_eval_iff {δ : Type*} [Finite δ] {κ : δ → Type*} {s : Set (∀ d, κ d)} :
    (∀ d, (eval d '' s).Finite) ↔ s.Finite :=
  ⟨fun h => (Finite.pi h).subset <| subset_pi_eval_image _ _, fun h _ => h.image _⟩

@[simp]
/-
**Set.iUnion_cons** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_cons {n : Nat} (f : Fin n -> Set α) (s : Set α) : iUnion (Fin.cons 
s f) = s union ⋃ i, f i
参数：f : Fin n -> Set α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iUnion_cons {n : ℕ} (f : Fin n → Set α) (s : Set α) :
    iUnion (Fin.cons s f) = s ∪ ⋃ i, f i := by
  ext
  simp [Fin.exists_iff_succ]

@[simp]
/-
**Set.iUnion_snoc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_snoc {n : Nat} (f : Fin n -> Set α) (s : Set α) : iUnion (Fin.snoc 
f s) = (⋃ i, f i) union s
参数：f : Fin n -> Set α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iUnion_snoc {n : ℕ} (f : Fin n → Set α) (s : Set α) :
    iUnion (Fin.snoc f s) = (⋃ i, f i) ∪ s := by
  ext
  simp [Fin.exists_iff_castSucc, or_comm]
/-
**Set.iUnion_fin_add_one_eq_iUnion_succ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_fin_add_one_eq_iUnion_succ {n : Nat} (f : Fin (n + 1) -> Set α) : ⋃
 i, f i = f 0 union Set.iUnion (f ∘ Fin.succ)
参数：f : Fin (n + 1) -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.iUnion_cons`：iUnion_cons {n : Nat} (f : Fin n -> Set α) (s : Set α) 
: iUnion (Fin.cons s f) = s union ⋃ i, f i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma iUnion_fin_add_one_eq_iUnion_succ {n : ℕ} (f : Fin (n + 1) → Set α) :
    ⋃ i, f i = f 0 ∪ Set.iUnion (f ∘ Fin.succ) := by
  cases f using Fin.consCases
  simp [Function.comp_def]
/-
**Set.iUnion_fin_add_one_eq_iUnion_castSucc** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：iUnion_fin_add_one_eq_iUnion_castSucc {n : Nat} (f : Fin (n + 1) -> Set α)
 : ⋃ i, f i = Set.iUnion (f ∘ Fin.castSucc) union f (.last n)
参数：f : Fin (n + 1) -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.iUnion_snoc`：iUnion_snoc {n : Nat} (f : Fin n -> Set α) (s : Set α) 
: iUnion (Fin.snoc f s) = (⋃ i, f i) union s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma iUnion_fin_add_one_eq_iUnion_castSucc {n : ℕ} (f : Fin (n + 1) → Set α) :
    ⋃ i, f i = Set.iUnion (f ∘ Fin.castSucc) ∪ f (.last n) := by
  cases f using Fin.snocCases
  simp [Function.comp_def]

end Set

