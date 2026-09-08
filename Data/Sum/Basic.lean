/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Additional lemmas about sum types

Most of the former contents of this file have been moved to Batteries.
-/

@[expose] public section


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

/-
**not_isLeft_and_isRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_isLeft_and_isRight {x : α oplus β} : ¬(x.isLeft ∧ x.isRight)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
-/
lemma not_isLeft_and_isRight {x : α ⊕ β} : ¬(x.isLeft ∧ x.isRight) := by simp

namespace Sum

@[simp]
/-
**Sum.elim_swap** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_swap {α β γ : Type*} {f : α -> γ} {g : β -> γ} : Sum.elim f g ∘ Sum.s
wap = Sum.elim g f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem elim_swap {α β γ : Type*} {f : α → γ} {g : β → γ} :
    Sum.elim f g ∘ Sum.swap = Sum.elim g f := by
  grind

-- Lean has removed the `@[simp]` attribute on these. For now Mathlib adds it back.
attribute [simp] Sum.forall Sum.exists
/-
**Sum.exists_sum** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：exists_sum {γ : α oplus β -> Sort*} (p : (forall ab, γ ab) -> Prop) : (exi
sts fab, p fab) ↔ (exists fa fb, p (Sum.rec fa fb))
参数：p : (forall ab, γ ab) -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `Sum.forall_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : α ⊕ β → Sort u_3} {
p : ((ab : α ⊕ β) → γ ab) → Prop},   (∀ (fab : (ab : α ⊕ β) → γ ab), p fab) ↔   
  ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_sum {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not, forall_sum]
  simp
/-
**Sum.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inl_injective : Function.Injective (inl : α -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl.inj`：∀ {α : Type u} {β : Type v} {val val_1 : α}, Sum.inl val = 
Sum.inl val_1 → val = val_1
-/
theorem inl_injective : Function.Injective (inl : α → α ⊕ β) := fun _ _ ↦ inl.inj
/-
**Sum.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：inr_injective : Function.Injective (inr : β -> α oplus β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr.inj`：∀ {α : Type u} {β : Type v} {val val_1 : β}, Sum.inr val = 
Sum.inr val_1 → val = val_1
-/
theorem inr_injective : Function.Injective (inr : β → α ⊕ β) := fun _ _ ↦ inr.inj
/-
**Sum.sum_rec_congr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：sum_rec_congr (P : α oplus β -> Sort*) (f : forall i, P (inl i)) (g : fora
ll i, P (inr i)) {x y : α oplus β} (h : x = y) : @Sum.rec _ _ _ f g x = cast (co
ngr_arg P h.symm) (@Sum.rec _ _ _ f g y)
参数：P : α oplus β -> Sort*；f : forall i, P (inl i)；g : forall i, P (inr i)；h : x 
= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem sum_rec_congr (P : α ⊕ β → Sort*) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : α ⊕ β} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

section get

variable {x : α ⊕ β}

set_option backward.isDefEq.respectTransparency false in
/-
**Sum.eq_left_iff_getLeft_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ exists h, x.getLeft h = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Bool.false_eq_true`：(false = true) = False
-/
theorem eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ ∃ h, x.getLeft h = a := by
  cases x <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**Sum.eq_right_iff_getRight_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：eq_right_iff_getRight_eq {b : β} : x = inr b ↔ exists h, x.getRight h = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem eq_right_iff_getRight_eq {b : β} : x = inr b ↔ ∃ h, x.getRight h = b := by
  cases x <;> simp
/-
**Sum.getLeft_eq_getLeft** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) : x.getLeft h
₁ = x.getLeft?.get h₂
参数：h₁ : x.isLeft；h₂ : x.getLeft?.isSome。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) :
    x.getLeft h₁ = x.getLeft?.get h₂ := by grind
/-
**Sum.getRight_eq_getRight** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) : x.getRi
ght h₁ = x.getRight?.get h₂
参数：h₁ : x.isRight；h₂ : x.getRight?.isSome。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) :
    x.getRight h₁ = x.getRight?.get h₂ := by grind
/-
**Sum.isSome_getLeft** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem isSome_getLeft?_iff_isLeft : x.getLeft?.isSome ↔ x.isLeft := by
  grind
/-
**Sum.isSome_getRight** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem isSome_getRight?_iff_isRight : x.getRight?.isSome ↔ x.isRight := by
  grind

end get

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
/-
**Sum.update_elim_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_elim_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α -> γ} {g 
: β -> γ} {i : α} {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f
 i x) g
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.update_eq_iff`：update_eq_iff {a : α} {b : β a} {f g : forall a,
 β a} : update f a b = g ↔ b = g a ∧ forall x != a, f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem update_elim_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
/-
**Sum.update_elim_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_elim_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α -> γ} {g 
: β -> γ} {i : β} {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update
 g i x)
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.update_eq_iff`：update_eq_iff {a : α} {b : β a} {f g : forall a,
 β a} : update f a b = g ↔ b = g a ∧ forall x != a, f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem update_elim_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
/-
**Sum.update_inl_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inl_comp_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplus
 β -> γ} {i : α} {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_injective`：update_comp_eq_of_injective {β : S
ort*} (g : α' -> β) {f : α -> α'} (hf : Function.Injective f) (i : α) (a : β) : 
Function.update g (f i) a …
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _

@[simp]
/-
**Sum.update_inl_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inl_apply_inl [DecidableEq α] [DecidableEq (α oplus β)] {f : α oplu
s β -> γ} {i j : α} {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x 
j
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  grind

@[simp]
/-
**Sum.update_inl_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inl_comp_inr [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α}
 {x : γ} : update f (inl i) x ∘ inr = f ∘ inr
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_forall_ne`：update_comp_eq_of_forall_ne {α β :
 Sort*} (g : α' -> β) {f : α -> α'} {i : α'} (a : β) (h : forall x, f x != i) : 
update g i a ∘ f = g ∘ f
· 使用定理 `Sum.inr_ne_inl`：∀ {β : Type u_1} {b : β} {α : Type u_2} {a : α}, Sum.inr
 b ≠ Sum.inl a
-/
theorem update_inl_comp_inr [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inr_ne_inl
/-
**Sum.update_inl_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inl_apply_inr [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α
} {j : β} {x : γ} : update f (inl i) x (inr j) = f (inr j)
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Sum.inr_ne_inl`：∀ {β : Type u_1} {b : β} {α : Type u_2} {a : α}, Sum.inr
 b ≠ Sum.inl a
-/
theorem update_inl_apply_inr [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_of_ne inr_ne_inl ..

@[simp]
/-
**Sum.update_inr_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inr_comp_inl [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : β}
 {x : γ} : update f (inr i) x ∘ inl = f ∘ inl
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_forall_ne`：update_comp_eq_of_forall_ne {α β :
 Sort*} (g : α' -> β) {f : α -> α'} {i : α'} (a : β) (h : forall x, f x != i) : 
update g i a ∘ f = g ∘ f
· 使用定理 `Sum.inl_ne_inr`：∀ {α : Type u_1} {a : α} {β : Type u_2} {b : β}, Sum.inl
 a ≠ Sum.inr b
-/
theorem update_inr_comp_inl [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inl_ne_inr
/-
**Sum.update_inr_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inr_apply_inl [DecidableEq (α oplus β)] {f : α oplus β -> γ} {i : α
} {j : β} {x : γ} : update f (inr j) x (inl i) = f (inl i)
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Sum.inl_ne_inr`：∀ {α : Type u_1} {a : α} {β : Type u_2} {b : β}, Sum.inl
 a ≠ Sum.inr b
-/
theorem update_inr_apply_inl [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_of_ne inl_ne_inr ..

@[simp]
/-
**Sum.update_inr_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inr_comp_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplus
 β -> γ} {i : β} {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_comp_eq_of_injective`：update_comp_eq_of_injective {β : S
ort*} (g : α' -> β) {f : α -> α'} (hf : Function.Injective f) (i : α) (a : β) : 
Function.update g (f i) a …
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _

@[simp]
/-
**Sum.update_inr_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inr_apply_inr [DecidableEq β] [DecidableEq (α oplus β)] {f : α oplu
s β -> γ} {i j : β} {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x 
j
参数：α oplus β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.update_inr_comp_inr`：update_inr_comp_inr [DecidableEq β] [DecidableE
q (α oplus β)] {f : α oplus β -> γ} {i : β} {x : γ} : update f (inr i) x ∘ inr =
 update (f ∘ …
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr, Function.comp_apply]

@[simp]
/-
**Sum.update_inl_apply_inl'** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inl_apply_inl' {γ : α oplus β -> Type*} [DecidableEq α] [DecidableE
q (α oplus β)] {f : (i : α oplus β) -> γ i} {i : α} {x : γ (.inl i)} (j : α) : u
pdate f (.inl i) x (Sum.inl j) = update (fun j => f (.inl j)) i x j
参数：α oplus β；i : α oplus β；.inl i；j : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_apply_of_injective`：update_apply_of_injective (g : foral
l a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i)) (j : 
α') : update g (f i) a (…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
theorem update_inl_apply_inl' {γ : α ⊕ β → Type*} [DecidableEq α] [DecidableEq (α ⊕ β)]
    {f : (i : α ⊕ β) → γ i} {i : α} {x : γ (.inl i)} (j : α) :
    update f (.inl i) x (Sum.inl j) = update (fun j ↦ f (.inl j)) i x j :=
  Function.update_apply_of_injective f Sum.inl_injective i x j

@[simp]
/-
**Sum.update_inr_apply_inr'** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：update_inr_apply_inr' {γ : α oplus β -> Type*} [DecidableEq β] [DecidableE
q (α oplus β)] {f : (i : α oplus β) -> γ i} {i : β} {x : γ (.inr i)} (j : β) : u
pdate f (.inr i) x (Sum.inr j) = update (fun j => f (.inr j)) i x j
参数：α oplus β；i : α oplus β；.inr i；j : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_apply_of_injective`：update_apply_of_injective (g : foral
l a, β a) {f : α' -> α} (hf : Function.Injective f) (i : α') (a : β (f i)) (j : 
α') : update g (f i) a (…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem update_inr_apply_inr' {γ : α ⊕ β → Type*} [DecidableEq β] [DecidableEq (α ⊕ β)]
    {f : (i : α ⊕ β) → γ i} {i : β} {x : γ (.inr i)} (j : β) :
    update f (.inr i) x (Sum.inr j) = update (fun j ↦ f (.inr j)) i x j :=
  Function.update_apply_of_injective f Sum.inr_injective i x j

@[simp]
/-
**Sum.rec_update_left** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：rec_update_left {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β] (
f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (a : α) (x : γ (.inl a)) : 
Sum.rec (update f a x) g = update (Sum.rec f g) (.inl a) x
参数：f : forall a, γ (.inl a)；g : forall b, γ (.inr b)；a : α；x : γ (.inl a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.rec_update`：rec_update {ι κ : Sort*} {α : κ -> Sort*} [Decidabl
eEq ι] [DecidableEq κ] {ctor : ι -> κ} (_ : Function.Injective ctor) (recursor :
 ((i : ι)…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
lemma rec_update_left {γ : α ⊕ β → Sort*} [DecidableEq α] [DecidableEq β]
    (f : ∀ a, γ (.inl a)) (g : ∀ b, γ (.inr b)) (a : α) (x : γ (.inl a)) :
    Sum.rec (update f a x) g = update (Sum.rec f g) (.inl a) x :=
  Function.rec_update Sum.inl_injective (Sum.rec · g) (fun _ _ => rfl) (fun
    | _, _, .inl _, h => (h _ rfl).elim
    | _, _, .inr _, _ => rfl) _ _ _

@[simp]
/-
**Sum.rec_update_right** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：rec_update_right {γ : α oplus β -> Sort*} [DecidableEq α] [DecidableEq β] 
(f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (b : β) (x : γ (.inr b)) :
 Sum.rec f (update g b x) = update (Sum.rec f g) (.inr b) x
参数：f : forall a, γ (.inl a)；g : forall b, γ (.inr b)；b : β；x : γ (.inr b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.rec_update`：rec_update {ι κ : Sort*} {α : κ -> Sort*} [Decidabl
eEq ι] [DecidableEq κ] {ctor : ι -> κ} (_ : Function.Injective ctor) (recursor :
 ((i : ι)…
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
lemma rec_update_right {γ : α ⊕ β → Sort*} [DecidableEq α] [DecidableEq β]
    (f : ∀ a, γ (.inl a)) (g : ∀ b, γ (.inr b)) (b : β) (x : γ (.inr b)) :
    Sum.rec f (update g b x) = update (Sum.rec f g) (.inr b) x :=
  Function.rec_update Sum.inr_injective (Sum.rec f) (fun _ _ => rfl) (fun
    | _, _, .inr _, h => (h _ rfl).elim
    | _, _, .inl _, _ => rfl) _ _ _

@[simp]
/-
**Sum.elim_update_left** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：elim_update_left {γ : Sort*} [DecidableEq α] [DecidableEq β] (f : α -> γ) 
(g : β -> γ) (a : α) (x : γ) : Sum.elim (update f a x) g = update (Sum.elim f g)
 (.inl a) x
参数：f : α -> γ；g : β -> γ；a : α；x : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.rec_update_left`：rec_update_left {γ : α oplus β -> Sort*} [Decidable
Eq α] [DecidableEq β] (f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (a :
 α) (x : …
-/
lemma elim_update_left {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α → γ) (g : β → γ) (a : α) (x : γ) :
    Sum.elim (update f a x) g = update (Sum.elim f g) (.inl a) x :=
  rec_update_left _ _ _ _

@[simp]
/-
**Sum.elim_update_right** 是 Mathlib 中的一个引理，位于命名空间 `Sum`。
形式化陈述：elim_update_right {γ : Sort*} [DecidableEq α] [DecidableEq β] (f : α -> γ)
 (g : β -> γ) (b : β) (x : γ) : Sum.elim f (update g b x) = update (Sum.elim f g
) (.inr b) x
参数：f : α -> γ；g : β -> γ；b : β；x : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sum.rec_update_right`：rec_update_right {γ : α oplus β -> Sort*} [Decidab
leEq α] [DecidableEq β] (f : forall a, γ (.inl a)) (g : forall b, γ (.inr b)) (b
 : β) (x :…
-/
lemma elim_update_right {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α → γ) (g : β → γ) (b : β) (x : γ) :
    Sum.elim f (update g b x) = update (Sum.elim f g) (.inr b) x :=
  rec_update_right _ _ _ _

@[simp]
/-
**Sum.swap_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：swap_leftInverse : Function.LeftInverse (@swap α β) swap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α ⊕ β), x.swap.swap 
= x
-/
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
/-
**Sum.swap_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：swap_rightInverse : Function.RightInverse (@swap α β) swap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α ⊕ β), x.swap.swap 
= x
-/
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

namespace LiftRel

variable {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ}
  {a : α} {b : β} {c : γ} {d : δ}

/-
**Sum.LiftRel.isLeft_congr** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isLeft_congr (h : LiftRel r s x y) : x.isLeft ↔ y.isLeft
参数：h : LiftRel r s x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isLeft_congr (h : LiftRel r s x y) : x.isLeft ↔ y.isLeft := by cases h <;> rfl
/-
**Sum.LiftRel.isRight_congr** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isRight_congr (h : LiftRel r s x y) : x.isRight ↔ y.isRight
参数：h : LiftRel r s x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRight_congr (h : LiftRel r s x y) : x.isRight ↔ y.isRight := by cases h <;> rfl
/-
**Sum.LiftRel.isLeft_left** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isLeft_left (h : LiftRel r s x (inl c)) : x.isLeft
参数：h : LiftRel r s x (inl c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem isLeft_left (h : LiftRel r s x (inl c)) : x.isLeft := by cases h; rfl
/-
**Sum.LiftRel.isLeft_right** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isLeft_right (h : LiftRel r s (inl a) y) : y.isLeft
参数：h : LiftRel r s (inl a) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem isLeft_right (h : LiftRel r s (inl a) y) : y.isLeft := by cases h; rfl
/-
**Sum.LiftRel.isRight_left** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isRight_left (h : LiftRel r s x (inr d)) : x.isRight
参数：h : LiftRel r s x (inr d)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem isRight_left (h : LiftRel r s x (inr d)) : x.isRight := by cases h; rfl
/-
**Sum.LiftRel.isRight_right** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：isRight_right (h : LiftRel r s (inr b) y) : y.isRight
参数：h : LiftRel r s (inr b) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem isRight_right (h : LiftRel r s (inr b) y) : y.isRight := by cases h; rfl
/-
**Sum.LiftRel.exists_of_isLeft_left** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：exists_of_isLeft_left (h₁ : LiftRel r s x y) (h₂ : x.isLeft) : exists a c,
 r a c ∧ x = inl a ∧ y = inl c
参数：h₁ : LiftRel r s x y；h₂ : x.isLeft。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_of_isLeft_left (h₁ : LiftRel r s x y) (h₂ : x.isLeft) :
    ∃ a c, r a c ∧ x = inl a ∧ y = inl c := by
  grind
/-
**Sum.LiftRel.exists_of_isLeft_right** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：exists_of_isLeft_right (h₁ : LiftRel r s x y) (h₂ : y.isLeft) : exists a c
, r a c ∧ x = inl a ∧ y = inl c
参数：h₁ : LiftRel r s x y；h₂ : y.isLeft。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.LiftRel.exists_of_isLeft_left`：exists_of_isLeft_left (h₁ : LiftRel r
 s x y) (h₂ : x.isLeft) : exists a c, r a c ∧ x = inl a ∧ y = inl c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.LiftRel.isLeft_congr`：isLeft_congr (h : LiftRel r s x y) : x.isLeft 
↔ y.isLeft
-/
theorem exists_of_isLeft_right (h₁ : LiftRel r s x y) (h₂ : y.isLeft) :
    ∃ a c, r a c ∧ x = inl a ∧ y = inl c := exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)
/-
**Sum.LiftRel.exists_of_isRight_left** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：exists_of_isRight_left (h₁ : LiftRel r s x y) (h₂ : x.isRight) : exists b 
d, s b d ∧ x = inr b ∧ y = inr d
参数：h₁ : LiftRel r s x y；h₂ : x.isRight。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_of_isRight_left (h₁ : LiftRel r s x y) (h₂ : x.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d := by
  grind
/-
**Sum.LiftRel.exists_of_isRight_right** 是 Mathlib 中的一个定理，位于命名空间 `Sum.LiftRel`。
形式化陈述：exists_of_isRight_right (h₁ : LiftRel r s x y) (h₂ : y.isRight) : exists b
 d, s b d ∧ x = inr b ∧ y = inr d
参数：h₁ : LiftRel r s x y；h₂ : y.isRight。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.LiftRel.exists_of_isRight_left`：exists_of_isRight_left (h₁ : LiftRel
 r s x y) (h₂ : x.isRight) : exists b d, s b d ∧ x = inr b ∧ y = inr d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sum.LiftRel.isRight_congr`：isRight_congr (h : LiftRel r s x y) : x.isRig
ht ↔ y.isRight
-/
theorem exists_of_isRight_right (h₁ : LiftRel r s x y) (h₂ : y.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d :=
  exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

end LiftRel

end Sum

open Sum

namespace Function

/-
**Function.Injective.sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Sort u_3} {f : α → γ} {g : β → γ},   Func
tion.Injective f → Function.Injective g → (∀ (a : α) (b : β), f a ≠ g b) → Funct
ion.Injective (Sum.elim f g)
参数：∀ (a : α) (b : β), f a ≠ g b；Sum.elim f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Injective.sumElim {γ : Sort*} {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Injective (Sum.elim f g)
  | inl _, inl _, h => congr_arg inl <| hf h
  | inl _, inr _, h => (hfg _ _ h).elim
  | inr _, inl _, h => (hfg _ _ h.symm).elim
  | inr _, inr _, h => congr_arg inr <| hg h
/-
**Function.Injective.sumMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {f : α → β} {g : α
' → β'},   Function.Injective f → Function.Injective g → Function.Injective (Sum
.map f g)
参数：Sum.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Sum.inl.inj`：∀ {α : Type u} {β : Type v} {val val_1 : α}, Sum.inl val = 
Sum.inl val_1 → val = val_1
· 使用定理 `Sum.inr.inj`：∀ {α : Type u} {β : Type v} {val val_1 : β}, Sum.inr val = 
Sum.inr val_1 → val = val_1
-/
theorem Injective.sumMap {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
  | inl _, inl _, h => congr_arg inl <| hf <| inl.inj h
  | inr _, inr _, h => congr_arg inr <| hg <| inr.inj h
/-
**Function.Surjective.sumMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {f : α → β} {g : α
' → β'},   Function.Surjective f → Function.Surjective g → Function.Surjective (
Sum.map f g)
参数：Sum.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Surjective.sumMap {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩
/-
**Function.Bijective.sumMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {f : α → β} {g : α
' → β'},   Function.Bijective f → Function.Bijective g → Function.Bijective (Sum
.map f g)
参数：Sum.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.sumMap`：∀ {α : Type u} {α' : Type w} {β : Type v} {β'
 : Type x} {f : α → β} {g : α' → β'},   Function.Injective f → Function.Injectiv
e g → Function.…
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Function.Surjective.sumMap`：∀ {α : Type u} {α' : Type w} {β : Type v} {β
' : Type x} {f : α → β} {g : α' → β'},   Function.Surjective f → Function.Surjec
tive g → Functio…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem Bijective.sumMap {f : α → β} {g : α' → β'} (hf : Bijective f) (hg : Bijective g) :
    Bijective (Sum.map f g) :=
  ⟨hf.injective.sumMap hg.injective, hf.surjective.sumMap hg.surjective⟩

end Function

namespace Sum

open Function

@[simp]
/-
**Sum.elim_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_injective {γ : Sort*} {f : α -> γ} {g : β -> γ} : Injective (Sum.elim
 f g) ↔ Injective f ∧ Injective g ∧ forall a b, f a != g b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Sum.inl_ne_inr`：∀ {α : Type u_1} {a : α} {β : Type u_2} {b : β}, Sum.inl
 a ≠ Sum.inr b
· 使用定理 `Function.Injective.sumElim`：∀ {α : Type u} {β : Type v} {γ : Sort u_3} {
f : α → γ} {g : β → γ},   Function.Injective f → Function.Injective g → (∀ (a : 
α) (b : β), f a …
-/
theorem elim_injective {γ : Sort*} {f : α → γ} {g : β → γ} :
    Injective (Sum.elim f g) ↔ Injective f ∧ Injective g ∧ ∀ a b, f a ≠ g b where
  mp h := ⟨h.comp inl_injective, h.comp inr_injective, fun _ _ => h.ne inl_ne_inr⟩
  mpr | ⟨hf, hg, hfg⟩ => hf.sumElim hg hfg

@[simp]
/-
**Sum.elim_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：elim_injective' {γ : Sort*} {f : α -> γ} : Injective (Sum.elim f : (β -> γ
) -> (α oplus β -> γ))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem elim_injective' {γ : Sort*} {f : α → γ} :
    Injective (Sum.elim f : (β → γ) → (α ⊕ β → γ)) :=
  fun g₁ g₂ hg ↦ funext fun b ↦ by simpa using congr_fun hg (Sum.inr b)

@[simp]
/-
**Sum.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：map_injective {f : α -> γ} {g : β -> δ} : Injective (Sum.map f g) ↔ Inject
ive f ∧ Injective g where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Function.Injective.sumMap`：∀ {α : Type u} {α' : Type w} {β : Type v} {β'
 : Type x} {f : α → β} {g : α' → β'},   Function.Injective f → Function.Injectiv
e g → Function.…
-/
theorem map_injective {f : α → γ} {g : β → δ} :
    Injective (Sum.map f g) ↔ Injective f ∧ Injective g where
  mp h := ⟨.of_comp <| h.comp inl_injective, .of_comp <| h.comp inr_injective⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
/-
**Sum.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：map_surjective {f : α -> γ} {g : β -> δ} : Surjective (Sum.map f g) ↔ Surj
ective f ∧ Surjective g where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Function.Surjective.sumMap`：∀ {α : Type u} {α' : Type w} {β : Type v} {β
' : Type x} {f : α → β} {g : α' → β'},   Function.Surjective f → Function.Surjec
tive g → Functio…
-/
theorem map_surjective {f : α → γ} {g : β → δ} :
    Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g where
  mp h := ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
/-
**Sum.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：map_bijective {f : α -> γ} {g : β -> δ} : Bijective (Sum.map f g) ↔ Biject
ive f ∧ Bijective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Sum.map_injective`：map_injective {f : α -> γ} {g : β -> δ} : Injective (
Sum.map f g) ↔ Injective f ∧ Injective g where mp h
· 使用定理 `Sum.map_surjective`：map_surjective {f : α -> γ} {g : β -> δ} : Surjectiv
e (Sum.map f g) ↔ Surjective f ∧ Surjective g where mp h
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
-/
theorem map_bijective {f : α → γ} {g : β → δ} :
    Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g :=
  (map_injective.and map_surjective).trans <| and_and_and_comm

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/-
**Sum3.in** 是 Mathlib 中的一个定义，位于命名空间 `Sum3`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the first summand into a ternary sum.
-/
def in₀ (a : α) : α ⊕ (β ⊕ γ) :=
  inl a

/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/-
**Sum3.in** 是 Mathlib 中的一个定义，位于命名空间 `Sum3`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the second summand into a ternary sum.
-/
def in₁ (b : β) : α ⊕ (β ⊕ γ) :=
  inr <| inl b

/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
/-
**Sum3.in** 是 Mathlib 中的一个定义，位于命名空间 `Sum3`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the third summand into a ternary sum.
-/
def in₂ (c : γ) : α ⊕ (β ⊕ γ) :=
  inr <| inr c

end Sum3

/-!
### PSum
-/

namespace PSum

variable {α β : Sort*}

/-
**PSum.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `PSum`。
形式化陈述：inl_injective : Function.Injective (PSum.inl : α -> α oplus' β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSum.inl.inj`：∀ {α : Sort u} {β : Sort v} {val val_1 : α}, PSum.inl val 
= PSum.inl val_1 → val = val_1
-/
theorem inl_injective : Function.Injective (PSum.inl : α → α ⊕' β) := fun _ _ ↦ inl.inj
/-
**PSum.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `PSum`。
形式化陈述：inr_injective : Function.Injective (PSum.inr : β -> α oplus' β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PSum.inr.inj`：∀ {α : Sort u} {β : Sort v} {val val_1 : β}, PSum.inr val 
= PSum.inr val_1 → val = val_1
-/
theorem inr_injective : Function.Injective (PSum.inr : β → α ⊕' β) := fun _ _ ↦ inr.inj

end PSum

