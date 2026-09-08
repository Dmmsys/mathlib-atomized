/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Order structures and monotonicity lemmas for `Set`
-/

public section

open Function

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

/-
**Set.monotoneOn_iff_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotoneOn_iff_monotone : MonotoneOn f s ↔ Monotone fun a : s => f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monotoneOn_iff_monotone : MonotoneOn f s ↔
    Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]
/-
**Set.antitoneOn_iff_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：antitoneOn_iff_antitone : AntitoneOn f s ↔ Antitone fun a : s => f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem antitoneOn_iff_antitone : AntitoneOn f s ↔
    Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]
/-
**Set.strictMonoOn_iff_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictMonoOn_iff_strictMono : StrictMonoOn f s ↔ StrictMono fun a : s => f
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem strictMonoOn_iff_strictMono : StrictMonoOn f s ↔
    StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]
/-
**Set.strictAntiOn_iff_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔ StrictAnti fun a : s => f
 a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔
    StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
/-
**Set.not_monotoneOn_not_antitoneOn_iff_exists_le_le** 是 Mathlib 中的一个定理，位于命名空间 `
Set`。
形式化陈述：not_monotoneOn_not_antitoneOn_iff_exists_le_le : ¬MonotoneOn f s ∧ ¬Antito
neOn f s ↔ existsᵉ (a in s) (b in s) (c in s), a <= b ∧ b <= c ∧ (f a < f b ∧ f 
c < f b ∨ f b < f a ∧ f b < f c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function between linear orders which is neither monotone nor antitone makes a 
dent upright or
downright.
-/
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a ≤ b ∧ b ≤ c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ ∈ s)]

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
/-
**Set.not_monotoneOn_not_antitoneOn_iff_exists_lt_lt** 是 Mathlib 中的一个定理，位于命名空间 `
Set`。
形式化陈述：not_monotoneOn_not_antitoneOn_iff_exists_lt_lt : ¬MonotoneOn f s ∧ ¬Antito
neOn f s ↔ existsᵉ (a in s) (b in s) (c in s), a < b ∧ b < c ∧ (f a < f b ∧ f c 
< f b ∨ f b < f a ∧ f b < f c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_left_comm`：∀ {a b c : Prop}, a ∧ b ∧ c ↔ b ∧ a ∧ c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function between linear orders which is neither monotone nor antitone makes a 
dent upright or
downright.
-/
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a < b ∧ b < c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ ∈ s)]

end LinearOrder

end Set

/-! ### Monotone lemmas for sets -/

section Monotone
variable {α β : Type*}

/-
**Monotone.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Mon
otone g) : Monotone fun x => f x inter g x
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.inf`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeInf β] {f g : α → β},   Monotone f → Monotone g → Monotone (f ⊓ g)
-/
theorem Monotone.inter [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∩ g x :=
  hf.inf hg
/-
**MonotoneOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : Set β} (hf : Monoton
eOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x inter g x) s
参数：hf : MonotoneOn f s；hg : MonotoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.inf`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeInf β] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s
 → M…
-/
theorem MonotoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
/-
**Antitone.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Ant
itone g) : Antitone fun x => f x inter g x
参数：hf : Antitone f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.inf`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeInf β] {f g : α → β},   Antitone f → Antitone g → Antitone (f ⊓ g)
-/
theorem Antitone.inter [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∩ g x :=
  hf.inf hg
/-
**AntitoneOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : Set β} (hf : Antiton
eOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x inter g x) s
参数：hf : AntitoneOn f s；hg : AntitoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.inf`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeInf β] {f g : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn g s
 → A…
-/
theorem AntitoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
/-
**Monotone.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.union [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Mon
otone g) : Monotone fun x => f x union g x
参数：hf : Monotone f；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeSup β] {f g : α → β},   Monotone f → Monotone g → Monotone (f ⊔ g)
-/
theorem Monotone.union [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∪ g x :=
  hf.sup hg
/-
**MonotoneOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.union [Preorder β] {f g : β -> Set α} {s : Set β} (hf : Monoton
eOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x union g x) s
参数：hf : MonotoneOn f s；hg : MonotoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeSup β] {f g : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn g s
 → M…
-/
theorem MonotoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg
/-
**Antitone.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.union [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Ant
itone g) : Antitone fun x => f x union g x
参数：hf : Antitone f；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 : 
SemilatticeSup β] {f g : α → β},   Antitone f → Antitone g → Antitone (f ⊔ g)
-/
theorem Antitone.union [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∪ g x :=
  hf.sup hg
/-
**AntitoneOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.union [Preorder β] {f g : β -> Set α} {s : Set β} (hf : Antiton
eOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x union g x) s
参数：hf : AntitoneOn f s；hg : AntitoneOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.sup`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 
: SemilatticeSup β] {f g : α → β} {s : Set α},   AntitoneOn f s → AntitoneOn g s
 → A…
-/
theorem AntitoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg

namespace Set

/-
**Set.monotone_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：monotone_ofPred [Preorder α] {p : α -> β -> Prop} (hp : forall b, Monotone
 fun a => p a b) : Monotone fun a => { b | p a b }
参数：hp : forall b, Monotone fun a => p a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monotone_ofPred [Preorder α] {p : α → β → Prop} (hp : ∀ b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias monotone_setOf := monotone_ofPred
/-
**Set.antitone_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：antitone_ofPred [Preorder α] {p : α -> β -> Prop} (hp : forall b, Antitone
 fun a => p a b) : Antitone fun a => { b | p a b }
参数：hp : forall b, Antitone fun a => p a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antitone_ofPred [Preorder α] {p : α → β → Prop} (hp : ∀ b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias antitone_setOf := antitone_ofPred

/-- Quantifying over a set is antitone in the set -/
/-
**Set.antitone_bforall** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：antitone_bforall {P : α -> Prop} : Antitone fun s : Set α => forall x in s
, P x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quantifying over a set is antitone in the set
-/
theorem antitone_bforall {P : α → Prop} : Antitone fun s : Set α => ∀ x ∈ s, P x :=
  fun _ _ hst h x hx => h x <| hst hx

end Set

end Monotone

