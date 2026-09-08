/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Multiset.Pi
public import Mathlib.Logic.Function.DependsOn

/-!
# The Cartesian product of finsets

## Main definitions

* `Finset.pi`: Cartesian product of finsets indexed by a finset.
-/

@[expose] public section

open Function

namespace Finset

open Multiset

/-! ### pi -/


section Pi

variable {α : Type*}

/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
/-
**Finset.Pi.empty** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Pi`。
形式化陈述：{α : Type u_1} → (β : α → Sort u_2) → (a : α) → a ∈ ∅ → β a
参数：β : α → Sort u_2；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty dependent product function, defined on the empty set. The assumption `
a ∈ ∅` is never
satisfied.
-/
def Pi.empty (β : α → Sort*) (a : α) (h : a ∈ (∅ : Finset α)) : β a :=
  Multiset.Pi.empty β a h

universe u v
variable {β : α → Type u} {δ : α → Sort v} {s : Finset α} {t : ∀ a, Finset (β a)}

section
variable [DecidableEq α]

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `β a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
/-
**Finset.pi** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：pi (s : Finset α) (t : forall a, Finset (β a)) : Finset (forall a in s, β 
a)
参数：s : Finset α；t : forall a, Finset (β a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `s` of `α` and for all `a : α` a finset `t a` of `β a`, then one 
can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t 
a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`.
-/
def pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a) :=
  ⟨s.1.pi fun a => (t a).1, s.nodup.pi fun a _ => (t a).nodup⟩

@[simp]
/-
**Finset.pi_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_val (s : Finset α) (t : forall a, Finset (β a)) : (s.pi t).1 = s.1.pi f
un a => (t a).1
参数：s : Finset α；t : forall a, Finset (β a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_val (s : Finset α) (t : ∀ a, Finset (β a)) : (s.pi t).1 = s.1.pi fun a => (t a).1 :=
  rfl

@[simp, grind =]
/-
**Finset.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : forall a in s, β a
} : f in s.pi t ↔ forall (a) (h : a in s), f a h in t a
参数：β a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_pi`：mem_pi (m : Multiset α) (t : forall a, Multiset (β a)) 
(f : forall a in m, β a) : f in pi m t ↔ forall (a) (h : a in m), f a h in t a
-/
theorem mem_pi {s : Finset α} {t : ∀ a, Finset (β a)} {f : ∀ a ∈ s, β a} :
    f ∈ s.pi t ↔ ∀ (a) (h : a ∈ s), f a h ∈ t a :=
  Multiset.mem_pi _ _ _

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.Pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
/-
**Finset.Pi.cons** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Pi`。
形式化陈述：{α : Type u_1} →   {δ : α → Sort v} →     [inst : DecidableEq α] →       (
s : Finset α) → (a : α) → δ a → ((a : α) → a ∈ s → δ a) → (a' : α) → a' ∈ insert
 a s → δ a'
参数：s : Finset α；a : α；(a : α) → a ∈ s → δ a；a' : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f` defined on a finset `s`, define a new function on the finse
t `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denot
ed
`s.Pi.cons a b f`. If `a` already belongs to `s`, the new function takes the val
ue `b` at `a`
anyway.
-/
def Pi.cons (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) :
    δ a' :=
  Multiset.Pi.cons s.1 a b f _ (Multiset.mem_cons.2 <| mem_insert.symm.2 h)

@[simp]
/-
**Finset.Pi.cons_same** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Pi`。
形式化陈述：∀ {α : Type u_1} {δ : α → Sort v} [inst : DecidableEq α] (s : Finset α) (a
 : α) (b : δ a) (f : (a : α) → a ∈ s → δ a)   (h : a ∈ insert a s), Finset.Pi.co
ns s a b f a h = b
参数：s : Finset α；a : α；b : δ a；f : (a : α) → a ∈ s → δ a；h : a ∈ insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.cons_same`：cons_same {b : δ a} {f : forall a in m, δ a} (h :
 a in a ::ₘ m) : cons m a b f a h = b
-/
theorem Pi.cons_same (s : Finset α) (a : α) (b : δ a) (f : ∀ a, a ∈ s → δ a) (h : a ∈ insert a s) :
    Pi.cons s a b f a h = b :=
  Multiset.Pi.cons_same _
/-
**Finset.Pi.cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Pi`。
形式化陈述：∀ {α : Type u_1} {δ : α → Sort v} [inst : DecidableEq α] {s : Finset α} {a
 a' : α} {b : δ a} {f : (a : α) → a ∈ s → δ a}   {h : a' ∈ insert a s} (ha : a ≠
 a'), Finset.Pi.cons s a b f a' h = f a' ⋯
参数：a : α；ha : a ≠ a'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.cons_ne`：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ 
a} (h' : a' in a ::ₘ m) (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.
1 h').res…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem Pi.cons_ne {s : Finset α} {a a' : α} {b : δ a} {f : ∀ a, a ∈ s → δ a} {h : a' ∈ insert a s}
    (ha : a ≠ a') : Pi.cons s a b f a' h = f a' ((mem_insert.1 h).resolve_left ha.symm) :=
  Multiset.Pi.cons_ne _ (Ne.symm ha)
/-
**Finset.Pi.cons_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Pi`。
形式化陈述：∀ {α : Type u_1} {δ : α → Sort v} [inst : DecidableEq α] {a : α} {b : δ a}
 {s : Finset α},   a ∉ s → Function.Injective (Finset.Pi.cons s a b)
参数：Finset.Pi.cons s a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Pi.cons_injective`：cons_injective {a : α} {b : δ a} {s : Multis
et α} (hs : a ∉ s) : Function.Injective (Pi.cons s a b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Pi.cons_injective {a : α} {b : δ a} {s : Finset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun e₁ e₂ eq =>
  @Multiset.Pi.cons_injective α _ δ a b s.1 hs _ _ <|
    funext fun e =>
      funext fun h =>
        have :
          Pi.cons s a b e₁ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) =
            Pi.cons s a b e₂ e (by simpa only [Multiset.mem_cons, mem_insert] using! h) := by
          rw [eq]
        this

@[simp]
/-
**Finset.pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_empty {t : forall a : α, Finset (β a)} : pi (∅ : Finset α) t = singleto
n (Pi.empty β)
参数：β a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_empty {t : ∀ a : α, Finset (β a)} : pi (∅ : Finset α) t = singleton (Pi.empty β) :=
  rfl

@[simp]
/-
**Finset.pi_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pi_nonempty : (s.pi t).Nonempty ↔ forall a in s, (t a).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pi_nonempty : (s.pi t).Nonempty ↔ ∀ a ∈ s, (t a).Nonempty := by
  simp [Finset.Nonempty, Classical.skolem]

@[aesop safe apply (rule_sets := [finsetNonempty])]
alias ⟨_, pi_nonempty_of_forall_nonempty⟩ := pi_nonempty

@[simp]
/-
**Finset.pi_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pi_eq_empty : s.pi t = ∅ ↔ exists a in s, t a = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.pi_nonempty`：pi_nonempty : (s.pi t).Nonempty ↔ forall a in s, (t 
a).Nonempty
-/
lemma pi_eq_empty : s.pi t = ∅ ↔ ∃ a ∈ s, t a = ∅ := by
  contrapose!; exact pi_nonempty

@[simp]
/-
**Finset.pi_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_insert [forall a, DecidableEq (β a)] {s : Finset α} {t : forall a : α, 
Finset (β a)} {a : α} (ha : a ∉ s) : pi (insert a s) t = (t a).biUnion fun b => 
(pi s t).image (Pi.cons s a b)
参数：β a；β a；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Multiset.pi_cons`：pi_cons (m : Multiset α) (t : forall a, Multiset (β a)
) (a : α) : pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `Multiset.Pi.cons_injective`：cons_injective {a : α} {b : δ a} {s : Multis
et α} (hs : a ∉ s) : Function.Injective (Pi.cons s a b)
· 使用定理 `Finset.insert_val_of_notMem`：insert_val_of_notMem {a : α} {s : Finset α}
 (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1
-/
theorem pi_insert [∀ a, DecidableEq (β a)] {s : Finset α} {t : ∀ a : α, Finset (β a)} {a : α}
    (ha : a ∉ s) : pi (insert a s) t = (t a).biUnion fun b => (pi s t).image (Pi.cons s a b) := by
  apply eq_of_veq
  rw [← (pi (insert a s) t).2.dedup]
  refine
    (fun s' (h : s' = a ::ₘ s.1) =>
        (?_ :
          dedup (Multiset.pi s' fun a => (t a).1) =
            dedup
              ((t a).1.bind fun b =>
                dedup <|
                  (Multiset.pi s.1 fun a : α => (t a).val).map fun f a' h' =>
                    Multiset.Pi.cons s.1 a b f a' (h ▸ h'))))
      _ (insert_val_of_notMem ha)
  subst s'; rw [pi_cons]
  congr; funext b
  exact ((pi s t).nodup.map <| Multiset.Pi.cons_injective ha).dedup.symm
/-
**Finset.pi_singletons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_singletons {β : Type*} (s : Finset α) (f : α -> β) : (s.pi fun a => ({f
 a} : Finset β)) = {fun a _ => f a}
参数：s : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_singletons {β : Type*} (s : Finset α) (f : α → β) :
    (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a} := by grind
/-
**Finset.pi_const_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_const_singleton {β : Type*} (s : Finset α) (i : β) : (s.pi fun _ => ({i
} : Finset β)) = {fun _ _ => i}
参数：s : Finset α；i : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pi_singletons`：pi_singletons {β : Type*} (s : Finset α) (f : α ->
 β) : (s.pi fun a => ({f a} : Finset β)) = {fun a _ => f a}
-/
theorem pi_const_singleton {β : Type*} (s : Finset α) (i : β) :
    (s.pi fun _ => ({i} : Finset β)) = {fun _ _ => i} :=
  pi_singletons s fun _ => i
/-
**Finset.pi_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_subset {s : Finset α} (t₁ t₂ : forall a, Finset (β a)) (h : forall a in
 s, t₁ a subseteq t₂ a) : s.pi t₁ subseteq s.pi t₂
参数：t₁ t₂ : forall a, Finset (β a)；h : forall a in s, t₁ a subseteq t₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_pi`：mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : f
orall a in s, β a} : f in s.pi t ↔ forall (a) (h : a in s), f a h in t a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem pi_subset {s : Finset α} (t₁ t₂ : ∀ a, Finset (β a)) (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) :
    s.pi t₁ ⊆ s.pi t₂ := fun _ hg => mem_pi.2 fun a ha => h a ha (mem_pi.mp hg a ha)
/-
**Finset.pi_disjoint_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pi_disjoint_of_disjoint {δ : α -> Type*} {s : Finset α} (t₁ t₂ : forall a,
 Finset (δ a)) {a : α} (ha : a in s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.
pi t₁) (s.pi t₂)
参数：t₁ t₂ : forall a, Finset (δ a)；ha : a in s；h : Disjoint (t₁ a) (t₂ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_pi`：mem_pi {s : Finset α} {t : forall a, Finset (β a)} {f : f
orall a in s, β a} : f in s.pi t ↔ forall (a) (h : a in s), f a h in t a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem pi_disjoint_of_disjoint {δ : α → Type*} {s : Finset α} (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (ha : a ∈ s) (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a ha) (mem_pi.mp hf₁ a ha) (f₂ a ha) (mem_pi.mp hf₂ a ha) <|
      congr_fun (congr_fun eq₁₂ a) ha

end

/-! ### Diagonal -/

variable {ι : Type*} [DecidableEq (ι → α)] {s : Finset α} {f : ι → α}

/-- The diagonal of a finset `s : Finset α` as a finset of functions `ι → α`, namely the set of
constant functions valued in `s`. -/
/-
**Finset.piDiag** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι -> α)] : Finset (ι -> α)
参数：s : Finset α；ι : Type*；ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal of a finset `s : Finset α` as a finset of functions `ι → α`, namely
 the set of
constant functions valued in `s`.
-/
def piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι → α)] : Finset (ι → α) := s.image (const ι)
/-
**Finset.mem_piDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : DecidableEq (ι → α)] {s : Finset α
} {f : ι → α},   f ∈ s.piDiag ι ↔ ∃ a ∈ s, Function.const ι a = f
参数：ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
@[simp] lemma mem_piDiag : f ∈ s.piDiag ι ↔ ∃ a ∈ s, const ι a = f := mem_image
/-
**Finset.card_piDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} (s : Finset α) (ι : Type u_3) [inst : DecidableEq (ι → α)
] [Nonempty ι], (s.piDiag ι).card = s.card
参数：s : Finset α；ι : Type u_3；ι → α；s.piDiag ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.piDiag.eq_1`：∀ {α : Type u_1} (s : Finset α) (ι : Type u_3) [inst
 : DecidableEq (ι → α)],   s.piDiag ι = Finset.image (Function.const ι) s
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Function.const_injective`：const_injective [Nonempty α] : Injective (cons
t α : β -> α -> β)
-/
@[simp] lemma card_piDiag (s : Finset α) (ι : Type*) [DecidableEq (ι → α)] [Nonempty ι] :
    (s.piDiag ι).card = s.card := by rw [piDiag, card_image_of_injective _ const_injective]

/-! ### Restriction -/

variable {π : ι → Type*}

/-- Restrict domain of a function `f` to a finite set `s`. -/
@[simp]
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain of a function `f` to a finite set `s`.
-/
def restrict (s : Finset ι) (f : (i : ι) → π i) : (i : s) → π i := fun x ↦ f x
/-
**Finset.restrict_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：restrict_def (s : Finset ι) : s.restrict (π
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_def (s : Finset ι) : s.restrict (π := π) = fun f x ↦ f x := rfl

variable {s t u : Finset ι}
/-
**Finset._root_.Set.piCongrLeft_comp_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Fins
et`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.piCongrLeft_comp_domRestrict :
    (s.equivToSet.symm.piCongrLeft (fun i : s ↦ π i)) ∘ (s : Set ι).domRestrict = s.restrict := rfl

@[deprecated (since := "2026-07-19")]
alias _root_.Set.piCongrLeft_comp_restrict := _root_.Set.piCongrLeft_comp_domRestrict
/-
**Finset.piCongrLeft_comp_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：piCongrLeft_comp_restrict : (s.equivToSet.piCongrLeft (fun i : s => π i)) 
∘ s.restrict = (s : Set ι).domRestrict
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrLeft_comp_restrict :
    (s.equivToSet.piCongrLeft (fun i : s ↦ π i)) ∘ s.restrict = (s : Set ι).domRestrict := rfl

/-- If a function `f` is restricted to a finite set `t`, and `s ⊆ t`,
this is the restriction to `s`. -/
@[simp]
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f` is restricted to a finite set `t`, and `s ⊆ t`,
this is the restriction to `s`.
-/
def restrict₂ (hst : s ⊆ t) (f : (i : t) → π i) (i : s) : π i := f ⟨i.1, hst i.2⟩
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict₂_def (hst : s ⊆ t) : restrict₂ (π := π) hst = fun f x ↦ f ⟨x.1, hst x.2⟩ := rfl
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict₂_comp_restrict (hst : s ⊆ t) :
    (restrict₂ (π := π) hst) ∘ t.restrict = s.restrict := rfl
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict₂_comp_restrict₂ (hst : s ⊆ t) (htu : t ⊆ u) :
    (restrict₂ (π := π) hst) ∘ (restrict₂ htu) = restrict₂ (hst.trans htu) := rfl
/-
**Finset.dependsOn_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dependsOn_restrict (s : Finset ι) : DependsOn (s.restrict (π
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.dependsOn_domRestrict`：Set.dependsOn_domRestrict (s : Set ι) : Depen
dsOn (s.domRestrict (π
-/
lemma dependsOn_restrict (s : Finset ι) : DependsOn (s.restrict (π := π)) s :=
  (s : Set ι).dependsOn_domRestrict
/-
**Finset.restrict_preimage_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：restrict_preimage_univ [DecidablePred (· in s)] (t : (i : s) -> Set (π i))
 : s.restrict ⁻¹' (Set.univ.pi t) = Set.pi s (fun i => if h : i in s then t ⟨i, 
h⟩ else Set.univ)
参数：· in s；t : (i : s) -> Set (π i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_preimage_univ [DecidablePred (· ∈ s)] (t : (i : s) → Set (π i)) :
    s.restrict ⁻¹' (Set.univ.pi t) =
      Set.pi s (fun i ↦ if h : i ∈ s then t ⟨i, h⟩ else Set.univ) := by
  ext
  simp_all
/-
**Finset.domRestrict_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：domRestrict_preimage [DecidableEq ι] {I : Set ι} [DecidablePred (· in I)] 
(s : Finset I) (u : (i : I) -> Set (π i)) : I.domRestrict ⁻¹' Set.pi s u = Set.p
i (s.image Subtype.val) (fun i => if h : i in I then u ⟨i, h⟩ else .univ)
参数：· in I；s : Finset I；u : (i : I) -> Set (π i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma domRestrict_preimage [DecidableEq ι] {I : Set ι}
    [DecidablePred (· ∈ I)] (s : Finset I) (u : (i : I) → Set (π i)) :
    I.domRestrict ⁻¹' Set.pi s u =
      Set.pi (s.image Subtype.val) (fun i ↦ if h : i ∈ I then u ⟨i, h⟩ else .univ) := by
  grind

@[deprecated (since := "2026-07-19")] alias restrict_preimage := domRestrict_preimage
/-
**Finset.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：restrict (s : Finset ι) (f : (i : ι) -> π i) : (i : s) -> π i
参数：s : Finset ι；f : (i : ι) -> π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict₂_preimage [DecidablePred (· ∈ s)] (hst : s ⊆ t) (u : (i : s) → Set (π i)) :
    (restrict₂ hst) ⁻¹' (Set.univ.pi u) =
      (@Set.univ t).pi (fun j ↦ if h : j.1 ∈ s then u ⟨j.1, h⟩ else Set.univ) := by
  grind [restrict₂]

end Pi

end Finset

