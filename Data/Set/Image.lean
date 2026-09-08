/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Batteries.Tactic.Congr
public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Set.SymmDiff
public import Mathlib.Data.Set.Inclusion

/-!
# Images and preimages of sets

## Main definitions

* `preimage f t : Set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `range f : Set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

## Notation

* `f ⁻¹' t` for `Set.preimage f t`

* `f '' s` for `Set.image f s`

## Tags

set, sets, image, preimage, pre-image, range

-/

public section

assert_not_exists WithTop OrderIso

universe u v

open Function Set

namespace Set

variable {α β γ : Type*} {ι : Sort*}

/-! ### Inverse image -/


section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
/-
**Set.preimage_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_empty : f ⁻¹' ∅ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl
/-
**Set.preimage_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_congr {f g : α -> β} {s : Set β} (h : forall x : α, f x = g x) : 
f ⁻¹' s = g ⁻¹' s
参数：h : forall x : α, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  simp [h]

@[gcongr]
/-
**Set.preimage_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹' s subseteq f ⁻¹' t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun _ hx => h hx

@[simp, mfld_simps]
/-
**Set.preimage_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_univ : f ⁻¹' univ = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl
/-
**Set.subset_preimage_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_preimage_univ {s : Set α} : s subseteq f ⁻¹' univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _

@[simp, mfld_simps]
/-
**Set.preimage_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f ⁻¹' s inter f ⁻¹' t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl

@[simp]
/-
**Set.preimage_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_union {s t : Set β} : f ⁻¹' (s union t) = f ⁻¹' s union f ⁻¹' t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl

@[simp]
/-
**Set.preimage_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl

@[simp]
/-
**Set.preimage_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sdiff (f : α -> β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹
' t
参数：f : α -> β；s t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_sdiff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl

@[deprecated (since := "2026-06-03")] alias preimage_diff := preimage_sdiff

open scoped symmDiff in
@[simp]
/-
**Set.preimage_symmDiff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_symmDiff {f : α -> β} (s t : Set β) : f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆
 (f ⁻¹' t)
参数：s t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_symmDiff {f : α → β} (s t : Set β) : f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) :=
  rfl

@[simp]
/-
**Set.preimage_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_ite (f : α -> β) (s t₁ t₂ : Set β) : f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s
).ite (f ⁻¹' t₁) (f ⁻¹' t₂)
参数：f : α -> β；s t₁ t₂ : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) :
    f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl

@[simp]
/-
**Set.preimage_ofPred_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_ofPred_eq {p : α -> Prop} {f : β -> α} : f ⁻¹' { a | p a } = { a 
| p (f a) }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_ofPred_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl

@[deprecated (since := "2026-07-09")] alias preimage_setOf_eq := preimage_ofPred_eq

@[simp]
/-
**Set.preimage_id_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_id_eq : preimage (id : α -> α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_id_eq : preimage (id : α → α) = id :=
  rfl

@[mfld_simps]
/-
**Set.preimage_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_id {s : Set α} : id ⁻¹' s = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl

@[simp, mfld_simps]
/-
**Set.preimage_id'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl

@[simp]
/-
**Set.preimage_const_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_of_mem {b : β} {s : Set β} (h : b in s) : (fun _ : α => b) 
⁻¹' s = univ
参数：h : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
-/
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun _ : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun _ => h

@[simp]
/-
**Set.preimage_const_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const_of_notMem {b : β} {s : Set β} (h : b ∉ s) : (fun _ : α => b
) ⁻¹' s = ∅
参数：h : b ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
-/
theorem preimage_const_of_notMem {b : β} {s : Set β} (h : b ∉ s) : (fun _ : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun _ hx => h hx
/-
**Set.preimage_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_const (b : β) (s : Set β) [Decidable (b in s)] : (fun _ : α => b)
 ⁻¹' s = if b in s then univ else ∅
参数：b : β；s : Set β；b in s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] :
    (fun _ : α => b) ⁻¹' s = if b ∈ s then univ else ∅ := by grind

/-- If preimage of each singleton under `f : α → β` is either empty or the whole type,
then `f` is a constant. -/
/-
**Set.exists_eq_const_of_preimage_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_eq_const_of_preimage_singleton [Nonempty β] {f : α -> β} (hf : fora
ll b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = univ) : exists b, f = const α b
参数：hf : forall b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a

--- 原说明 ---
If preimage of each singleton under `f : α → β` is either empty or the whole typ
e,
then `f` is a constant.
-/
lemma exists_eq_const_of_preimage_singleton [Nonempty β] {f : α → β}
    (hf : ∀ b : β, f ⁻¹' {b} = ∅ ∨ f ⁻¹' {b} = univ) : ∃ b, f = const α b := by
  rcases em (∃ b, f ⁻¹' {b} = univ) with ⟨b, hb⟩ | hf'
  · exact ⟨b, funext fun x ↦ eq_univ_iff_forall.1 hb x⟩
  · have : ∀ x b, f x ≠ b := fun x b ↦
      eq_empty_iff_forall_notMem.1 ((hf b).resolve_right fun h ↦ hf' ⟨b, h⟩) x
    exact ⟨Classical.arbitrary β, funext fun x ↦ absurd rfl (this x _)⟩
/-
**Set.preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹' s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹' s :=
  rfl
/-
**Set.preimage_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g :=
  rfl
/-
**Set.preimage_iterate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iterate_eq {f : α -> α} {n : Nat} : Set.preimage f^[n] = (Set.pre
image f)^[n]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Set.preimage_comp_eq`：preimage_comp_eq : preimage (g ∘ f) = preimage f ∘
 preimage g
-/
theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.preimage f^[n] = (Set.preimage f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ, iterate_succ', preimage_comp_eq, ih]
/-
**Set.preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_preimage {g : β -> γ} {f : α -> β} {s : Set γ} : f ⁻¹' g ⁻¹' s = 
(fun x => g (f x)) ⁻¹' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
-/
theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} :
    f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm
/-
**Set.eq_preimage_subtype_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_preimage_subtype_val_iff {p : α -> Prop} {s : Set (Subtype p)} {t : Set
 α} : s = Subtype.val ⁻¹' t ↔ forall (x) (h : p x), (⟨x, h⟩ : Subtype p) in s ↔ 
x in t
参数：Subtype p。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t := by grind
/-
**Set.nonempty_of_nonempty_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_of_nonempty_preimage {s : Set β} {f : α -> β} (hf : (f ⁻¹' s).Non
empty) : s.Nonempty
参数：hf : (f ⁻¹' s).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) :
    s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩
/-
**Set.nonempty_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_preimage_iff {s : Set β} {f : α -> β} : (f ⁻¹' s).Nonempty ↔ (s i
nter range f).Nonempty
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
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nonempty_preimage_iff {s : Set β} {f : α → β} :
    (f ⁻¹' s).Nonempty ↔ (s ∩ range f).Nonempty := by
  simp [Set.Nonempty]
/-
**Set.preimage_singleton_true** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop), p ⁻¹' {True} = {a | p a}
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_singleton_true (p : α → Prop) : p ⁻¹' {True} = {a | p a} := by ext; simp
/-
**Set.preimage_singleton_false** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop), p ⁻¹' {False} = {a | ¬p a}
参数：p : α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem preimage_singleton_false (p : α → Prop) : p ⁻¹' {False} = {a | ¬p a} := by ext; simp
/-
**Set.preimage_subtype_coe_eq_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_subtype_coe_eq_compl {s u v : Set α} (hsuv : s subseteq u union v
) (H : s inter (u inter v) = ∅) : ((↑) : s -> α) ⁻¹' u = ((↑) ⁻¹' v)ᶜ
参数：hsuv : s subseteq u union v；H : s inter (u inter v) = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
-/
theorem preimage_subtype_coe_eq_compl {s u v : Set α} (hsuv : s ⊆ u ∪ v)
    (H : s ∩ (u ∩ v) = ∅) : ((↑) : s → α) ⁻¹' u = ((↑) ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_notMem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
  · grind
/-
**Set.preimage_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_subset {s t} (hs : s subseteq f '' t) (hf : Set.InjOn f (f ⁻¹' s)
) : f ⁻¹' s subseteq t
参数：hs : s subseteq f '' t；hf : Set.InjOn f (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma preimage_subset {s t} (hs : s ⊆ f '' t) (hf : Set.InjOn f (f ⁻¹' s)) : f ⁻¹' s ⊆ t := by
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hs ha
  rwa [hf ha _ hba.symm]
  simpa [hba]

end Preimage

/-! ### Image of a set under a function -/


section Image

variable {f : α → β} {s t : Set α}

/-
**Set.image_eta** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eta (f : α -> β) : f '' s = (fun x => f x) '' s
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_eta (f : α → β) : f '' s = (fun x => f x) '' s :=
  rfl
/-
**Set._root_.Function.Injective.mem_set_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f '' s ↔ a ∈ s :=
  ⟨fun ⟨_, hb, Eq⟩ => hf Eq ▸ hb, by grind⟩
/-
**Set.preimage_subset_of_surjOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：preimage_subset_of_surjOn {t : Set β} (hf : Injective f) (h : SurjOn f s t
) : f ⁻¹' t subseteq s
参数：hf : Injective f；h : SurjOn f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
-/
lemma preimage_subset_of_surjOn {t : Set β} (hf : Injective f) (h : SurjOn f s t) :
    f ⁻¹' t ⊆ s := fun _ hx ↦
  hf.mem_set_image.1 <| h hx
/-
**Set.forall_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_mem_image {f : α -> β} {s : Set α} {p : β -> Prop} : (forall y in f
 '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
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
theorem forall_mem_image {f : α → β} {s : Set α} {p : β → Prop} :
    (∀ y ∈ f '' s, p y) ↔ ∀ ⦃x⦄, x ∈ s → p (f x) := by simp
/-
**Set.exists_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_mem_image {f : α -> β} {s : Set α} {p : β -> Prop} : (exists y in f
 '' s, p y) ↔ exists x in s, p (f x)
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
theorem exists_mem_image {f : α → β} {s : Set α} {p : β → Prop} :
    (∃ y ∈ f '' s, p y) ↔ ∃ x ∈ s, p (f x) := by simp

@[congr]
/-
**Set.image_congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_congr {f g : α -> β} {s : Set α} (h : forall a in s, f a = g a) : f 
'' s = g '' s
参数：h : forall a in s, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f '' s = g '' s := by
  aesop

/-- A common special case of `image_congr` -/
/-
**Set.image_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_congr' {f g : α -> β} {s : Set α} (h : forall x : α, f x = g x) : f 
'' s = g '' s
参数：h : forall x : α, f x = g x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A common special case of `image_congr`
-/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f '' s = g '' s := by
  grind

@[gcongr]
/-
**Set.image_mono** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_mono (h : s subseteq t) : f '' s subseteq f '' t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_mono (h : s ⊆ t) : f '' s ⊆ f '' t := by grind

/-- `Set.image` is monotone. See `Set.image_mono` for the statement in terms of `⊆`. -/
/-
**Set.monotone_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：monotone_image : Monotone (image f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t

--- 原说明 ---
`Set.image` is monotone. See `Set.image_mono` for the statement in terms of `⊆`.
-/
lemma monotone_image : Monotone (image f) := fun _ _ => image_mono
/-
**Set.image_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g '' a = f '' g '' 
a
参数：f : β -> γ；g : α -> β；a : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g '' a = f '' g '' a := by aesop
/-
**Set.image_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_comp_eq {g : β -> γ} : image (g ∘ f) = image g ∘ image f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_comp_eq {g : β → γ} : image (g ∘ f) = image g ∘ image f := by grind
/-
**Set.image_comp_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_comp_image {g : β -> γ} : image g ∘ image f = image (g ∘ f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_comp_image {g : β → γ} : image g ∘ image f = image (g ∘ f) := by grind

/-- A variant of `image_comp`, useful for rewriting -/
@[grind =]
/-
**Set.image_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '' f '' s = (fun x =
> g (f x)) '' s
参数：g : β -> γ；f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a

--- 原说明 ---
A variant of `image_comp`, useful for rewriting
-/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g '' f '' s = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm
/-
**Set.image_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_comm {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ} (h
_comm : forall a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').imag
e g'
参数：h_comm : forall a, f (g a) = g' (f' a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.image g).image f = (s.image f').image g' := by grind
/-
**Set._root_.Function.Semiconj.set_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun _ =>
  image_comm h
/-
**Set._root_.Function.Commute.set_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  Function.Semiconj.set_image h
/-
**Set.image_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_union (f : α -> β) (s t : Set α) : f '' (s union t) = f '' s union f
 '' t
参数：f : α -> β；s t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t := by grind

@[simp]
/-
**Set.image_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_empty (f : α -> β) : f '' ∅ = ∅
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_empty (f : α → β) : f '' ∅ = ∅ := by grind
/-
**Set.image_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inter_subset (f : α -> β) (s t : Set α) : f '' (s inter t) subseteq 
f '' s inter f '' t
参数：f : α -> β；s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_mono inter_subset_left) (image_mono inter_subset_right)
/-
**Set.image_sdiff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sdiff_subset (f : α -> β) (s t : Set α) : f '' (s \ t) subseteq f ''
 s inter f '' tᶜ
参数：f : α -> β；s t : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
-/
theorem image_sdiff_subset (f : α → β) (s t : Set α) : f '' (s \ t) ⊆ f '' s ∩ f '' tᶜ :=
  image_inter_subset f s tᶜ

@[deprecated (since := "2026-06-03")] alias image_diff_subset := image_sdiff_subset
/-
**Set.image_inter_on** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inter_on {f : α -> β} {s t : Set α} (h : forall x in t, forall y in 
s, f x = f y -> x = y) : f '' (s inter t) = f '' s inter f '' t
参数：h : forall x in t, forall y in s, f x = f y -> x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f '' (s ∩ t) = f '' s ∩ f '' t :=
  (image_inter_subset _ _ _).antisymm
    fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ ↦
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩
/-
**Set.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inter {f : α -> β} {s t : Set α} (H : Injective f) : f '' (s inter t
) = f '' s inter f '' t
参数：H : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter_on`：image_inter_on {f : α -> β} {s t : Set α} (h : foral
l x in t, forall y in s, f x = f y -> x = y) : f '' (s inter t) = f '' s inter f
 '' t
-/
theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f '' (s ∩ t) = f '' s ∩ f '' t :=
  image_inter_on fun _ _ _ _ h => H h
/-
**Set.image_univ_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_univ_of_surjective {ι : Type*} {f : ι -> β} (H : Surjective f) : f '
' univ = univ
参数：H : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem image_univ_of_surjective {ι : Type*} {f : ι → β} (H : Surjective f) : f '' univ = univ :=
  eq_univ_of_forall <| by simpa [image]

@[simp]
/-
**Set.image_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_singleton {f : α -> β} {a : α} : f '' {a} = {f a}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} := by grind

@[simp]
/-
**Set.Nonempty.image_const** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonempty → ∀ (a : β), (fun 
x => a) '' s = {a}
参数：a : β；fun x => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
-/
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext fun _ =>
    ⟨fun ⟨_, _, h⟩ => h ▸ mem_singleton _, fun h =>
      (eq_of_mem_singleton h).symm ▸ hs.imp fun _ hy => ⟨hy, rfl⟩⟩

@[simp, mfld_simps]
/-
**Set.image_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_empty {α β} {f : α -> β} {s : Set α} : f '' s = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f '' s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_notMem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

@[simp, mfld_simps]
/-
**Set.empty_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_eq_image {α β} {f : α -> β} {s : Set α} : ∅ = f '' s ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.image_eq_empty`：image_eq_empty {α β} {f : α -> β} {s : Set α} : f ''
 s = ∅ ↔ s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem empty_eq_image {α β} {f : α → β} {s : Set α} : ∅ = f '' s ↔ s = ∅ := by
  rw [eq_comm, image_eq_empty]
/-
**Set.preimage_compl_eq_image_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_compl_eq_image_compl [BooleanAlgebra α] (s : Set α) : Compl.compl
 ⁻¹' s = Compl.compl '' s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `compl_eq_comm`：compl_eq_comm : xᶜ = y ↔ yᶜ = x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (s : Set α) :
    Compl.compl ⁻¹' s = Compl.compl '' s :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h =>
      Exists.elim h fun _ hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩
/-
**Set.mem_compl_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_compl_image [BooleanAlgebra α] (t : α) (s : Set α) : t in Compl.compl 
'' s ↔ tᶜ in s
参数：t : α；s : Set α。
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
theorem mem_compl_image [BooleanAlgebra α] (t : α) (s : Set α) :
    t ∈ Compl.compl '' s ↔ tᶜ ∈ s := by
  simp [← preimage_compl_eq_image_compl]

@[simp]
/-
**Set.image_id_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_id_eq : image (id : α -> α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem image_id_eq : image (id : α → α) = id := by ext; simp

/-- A variant of `image_id` -/
@[simp]
/-
**Set.image_id'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_id' (s : Set α) : (fun x => x) '' s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A variant of `image_id`
-/
theorem image_id' (s : Set α) : (fun x => x) '' s = s := by
  ext
  simp
/-
**Set.image_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_id (s : Set α) : id '' s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_id (s : Set α) : id '' s = s := by simp
/-
**Set.image_iterate_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_iterate_eq {f : α -> α} {n : Nat} : image (f^[n]) = (image f)^[n]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id_eq`：image_id_eq : image (id : α -> α) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp_eq`：image_comp_eq {g : β -> γ} : image (g ∘ f) = image g 
∘ image f
-/
lemma image_iterate_eq {f : α → α} {n : ℕ} : image (f^[n]) = (image f)^[n] := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ', iterate_succ', ← ih, image_comp_eq]
/-
**Set.compl_compl_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_compl_image [BooleanAlgebra α] (s : Set α) : Compl.compl '' Compl.co
mpl '' s = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `compl_comp_compl`：compl_comp_compl : compl ∘ compl = @id α
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem compl_compl_image [BooleanAlgebra α] (s : Set α) :
    Compl.compl '' Compl.compl '' s = s := by
  rw [← image_comp, compl_comp_compl, image_id]
/-
**Set.image_insert_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_insert_eq {f : α -> β} {a : α} {s : Set α} : f '' insert a s = inser
t (f a) (f '' s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_insert_eq {f : α → β} {a : α} {s : Set α} :
    f '' insert a s = insert (f a) (f '' s) := by grind
/-
**Set.image_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, f b}
参数：f : α -> β；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} := by grind
/-
**Set._root_.Function.LeftInverse.mem_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Se
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.LeftInverse.mem_preimage_iff {f : α → β} {g : β → α} (hfg : LeftInverse g f)
    {s : Set α} {x : α} : f x ∈ g ⁻¹' s ↔ x ∈ s := by
  rw [Set.mem_preimage, hfg x]
/-
**Set.image_subset_preimage_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_preimage_of_inverse {f : α -> β} {g : β -> α} (I : LeftInvers
e g f) (s : Set α) : f '' s subseteq g ⁻¹' s
参数：I : LeftInverse g f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.LeftInverse.mem_preimage_iff`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {g : β → α},   Function.LeftInverse g f → ∀ {s : Set α} {x : α}, f x 
∈ g ⁻¹' s ↔ x ∈ s
-/
theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) :
    f '' s ⊆ g ⁻¹' s := fun _ ⟨_, h, e⟩ => e ▸ I.mem_preimage_iff.mpr h
/-
**Set.preimage_subset_image_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_subset_image_of_inverse {f : α -> β} {g : β -> α} (I : LeftInvers
e g f) (s : Set β) : f ⁻¹' s subseteq g '' s
参数：I : LeftInverse g f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) :
    f ⁻¹' s ⊆ g '' s := fun b h => ⟨f b, h, I b⟩
/-
**Set.range_inter_ssubset_iff_preimage_ssubset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inter_ssubset_iff_preimage_ssubset {f : α -> β} {s s' : Set β} : ran
ge f inter s ⊂ range f inter s' ↔ f ⁻¹' s ⊂ f ⁻¹' s'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem range_inter_ssubset_iff_preimage_ssubset {f : α → β} {s s' : Set β} :
    range f ∩ s ⊂ range f ∩ s' ↔ f ⁻¹' s ⊂ f ⁻¹' s' := by
  simp only [Set.ssubset_iff_exists]
  apply and_congr ?_ (by aesop)
  constructor
  all_goals
    intro r x hx
    simp_all only [subset_inter_iff, inter_subset_left, true_and, mem_preimage,
      mem_inter_iff, mem_range, true_and]
    aesop
/-
**Set.image_eq_preimage_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_preimage_of_inverse {f : α -> β} {g : β -> α} (h₁ : LeftInverse g
 f) (h₂ : RightInverse g f) : image f = preimage g
参数：h₁ : LeftInverse g f；h₂ : RightInverse g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_subset_preimage_of_inverse`：image_subset_preimage_of_inverse {
f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set α) : f '' s subseteq g ⁻
¹' s
· 使用定理 `Set.preimage_subset_image_of_inverse`：preimage_subset_image_of_inverse {
f : α -> β} {g : β -> α} (I : LeftInverse g f) (s : Set β) : f ⁻¹' s subseteq g 
'' s
-/
theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : image f = preimage g :=
  funext fun s =>
    Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)
/-
**Set._root_.Function.Involutive.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空
间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Involutive.image_eq_preimage_symm {f : α → α} (hf : f.Involutive) :
    image f = preimage f :=
  image_eq_preimage_of_inverse hf.leftInverse hf.rightInverse
/-
**Set.mem_image_iff_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_image_iff_of_inverse {f : α -> β} {g : β -> α} {b : β} {s : Set α} (h₁
 : LeftInverse g f) (h₂ : RightInverse g f) : b in f '' s ↔ g b in s
参数：h₁ : LeftInverse g f；h₂ : RightInverse g f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f '' s ↔ g b ∈ s := by
  rw [image_eq_preimage_of_inverse h₁ h₂, mem_preimage]
/-
**Set.image_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_compl_subset {f : α -> β} {s : Set α} (H : Injective f) : f '' sᶜ su
bseteq (f '' s)ᶜ
参数：H : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [disjoint_iff_inf_le, ← image_inter H]
/-
**Set.subset_image_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_image_compl {f : α -> β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ
 subseteq f '' sᶜ
参数：H : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]
/-
**Set.image_compl_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_compl_eq {f : α -> β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '
' s)ᶜ
参数：H : Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_compl_subset`：image_compl_subset {f : α -> β} {s : Set α} (H :
 Injective f) : f '' sᶜ subseteq (f '' s)ᶜ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_image_compl`：subset_image_compl {f : α -> β} {s : Set α} (H :
 Surjective f) : (f '' s)ᶜ subseteq f '' sᶜ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '' s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)
/-
**Set.subset_image_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem subset_image_sdiff (f : α → β) (s t : Set α) : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rw [sdiff_subset_iff, ← image_union, union_sdiff_self]
  exact image_mono subset_union_right
/-
**Set.image_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set α) : f '' (s \ t) =
 f '' s \ f '' t
参数：hf : Injective f；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.image_sdiff_subset`：image_sdiff_subset (f : α -> β) (s t : Set α) : 
f '' (s \ t) subseteq f '' s inter f '' tᶜ
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Set.image_compl_subset`：image_compl_subset {f : α -> β} {s : Set α} (H :
 Injective f) : f '' sᶜ subseteq (f '' s)ᶜ
· 使用定理 `_private.Mathlib.Data.Set.Image.0.Set.subset_image_sdiff`：∀ {α : Type u_
1} {β : Type u_2} (f : α → β) (s t : Set α), f '' s \ f '' t ⊆ f '' (s \ t)
-/
theorem image_sdiff {f : α → β} (hf : Injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  Subset.antisymm
    (Subset.trans (image_sdiff_subset f s t) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_sdiff f s t)

@[deprecated image_sdiff (since := "2026-06-03")] alias subset_image_diff := subset_image_sdiff
@[deprecated (since := "2026-06-03")] alias image_diff := image_sdiff

open scoped symmDiff in
/-
**Set.image_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_symmDiff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ 
(f '' t)
参数：hf : Injective f；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_symmDiff (hf : Injective f) (s t : Set α) : f '' s ∆ t = (f '' s) ∆ (f '' t) := by
  simp_rw [Set.symmDiff_def, image_union, image_sdiff hf]
/-
**Set.Nonempty.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set α}, s.Nonempty → (f '
' s).Nonempty
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩
/-
**Set.Nonempty.of_image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : Set α}, (f '' s).Nonempty
 → s.Nonempty
参数：f '' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.of_image {f : α → β} {s : Set α} : (f '' s).Nonempty → s.Nonempty
  | ⟨_, x, hx, _⟩ => ⟨x, hx⟩

@[simp]
/-
**Set.image_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_nonempty {f : α -> β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : 
Set α}, (f '' s).Nonempty → s.Nonempty
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem image_nonempty {f : α → β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.image f⟩
/-
**Set.Nonempty.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.Nonempty → ∀ {f : α → β}, F
unction.Surjective f → (f ⁻¹' s).Nonempty
参数：f ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, by grind⟩
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f .of_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
/-
**Set.image_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_iff {s : Set α} {t : Set β} {f : α -> β} : f '' s subseteq t 
↔ s subseteq f ⁻¹' t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)

--- 原说明 ---
image and preimage are a Galois connection
-/
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  forall_mem_image
/-
**Set.image_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_subset (f : α -> β) (s : Set β) : f '' f ⁻¹' s subseteq s
参数：f : α -> β；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem image_preimage_subset (f : α → β) (s : Set β) : f '' f ⁻¹' s ⊆ s :=
  image_subset_iff.2 Subset.rfl
/-
**Set.subset_preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_preimage_image (f : α -> β) (s : Set α) : s subseteq f ⁻¹' f '' s
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' f '' s := fun _ =>
  mem_image_of_mem f
/-
**Set.preimage_image_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_image_univ {f : α -> β} : f ⁻¹' f '' univ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `trivial`：True
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem preimage_image_univ {f : α → β} : f ⁻¹' f '' univ = univ :=
  Subset.antisymm (fun _ _ => trivial) (subset_preimage_image f univ)

@[simp]
/-
**Set.preimage_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_image_eq {f : α -> β} (s : Set α) (h : Injective f) : f ⁻¹' f '' 
s = s
参数：s : Set α；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' f '' s = s :=
  Subset.antisymm (fun _ ⟨_, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

@[simp]
/-
**Set.image_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_eq {f : α -> β} (s : Set β) (h : Surjective f) : f '' f ⁻¹'
 s = s
参数：s : Set β；h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f '' f ⁻¹' s = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, by grind⟩

@[simp]
/-
**Set.Nonempty.subset_preimage_const** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Nonempty → ∀ (t : Set β) (a
 : β), s ⊆ (fun x => a) ⁻¹' t ↔ a ∈ t
参数：t : Set β；a : β；fun x => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nonempty.subset_preimage_const {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β) :
    s ⊆ (fun _ => a) ⁻¹' t ↔ a ∈ t := by
  rw [← image_subset_iff, hs.image_const, singleton_subset_iff]

@[simp]
/-
**Set.preimage_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_injective : Injective (preimage f) ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} {f : α → β},   Function.Injective f → ∀ (g : γ → α), Function.Injective (
f ∘ g) ↔ Function.In…
· 使用定理 `Set.mem_injective`：∀ {α : Type u}, Function.Injective Membership.mem
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `Set.ofPred_bijective`：ofPred_bijective : Bijective (ofPred : (α -> Prop)
 -> Set α)
· 使用定理 `Function.injective_comp_right_iff_surjective`：injective_comp_right_iff_s
urjective {γ : Type*} [Nontrivial γ] : Injective (fun g : β -> γ => g ∘ f) ↔ Sur
jective f
· 使用定理 `instNontrivialProp`：Nontrivial Prop
-/
theorem preimage_injective : Injective (preimage f) ↔ Surjective f := by
  rw [← Injective.of_comp_iff Set.mem_injective, ← Injective.of_comp_iff' _ Set.ofPred_bijective]
  exact injective_comp_right_iff_surjective

@[simp]
/-
**Set.preimage_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_surjective : Surjective (preimage f) ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Surjective g → (Function.Surjective 
(f ∘ g) ↔ Function.Su…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Set.ofPred_bijective`：ofPred_bijective : Bijective (ofPred : (α -> Prop)
 -> Set α)
· 使用定理 `Function.Surjective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : S
ort u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Surjectiv
e (f ∘ g) ↔ Function.S…
· 使用定理 `Set.mem_bijective`：∀ {α : Type u}, Function.Bijective Membership.mem
· 使用定理 `Function.surjective_comp_right_iff_injective`：surjective_comp_right_iff_
injective {γ : Type*} [Nontrivial γ] : Surjective (fun g : β -> γ => g ∘ f) ↔ In
jective f
· 使用定理 `instNontrivialProp`：Nontrivial Prop
-/
theorem preimage_surjective : Surjective (preimage f) ↔ Injective f := by
  rw [← Surjective.of_comp_iff _ Set.ofPred_bijective.surjective,
    ← Surjective.of_comp_iff' Set.mem_bijective]
  exact surjective_comp_right_iff_injective

@[simp]
/-
**Set.preimage_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_preimage {f : β -> α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t 
↔ s = t
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_injective`：preimage_injective : Injective (preimage f) ↔ Su
rjective f
-/
theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  (preimage_injective.mpr hf).eq_iff
/-
**Set.image_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inter_preimage (f : α -> β) (s : Set α) (t : Set β) : f '' (s inter 
f ⁻¹' t) = f '' s inter t
参数：f : α -> β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) :
    f '' (s ∩ f ⁻¹' t) = f '' s ∩ t := by grind
/-
**Set.image_preimage_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_inter (f : α -> β) (s : Set α) (t : Set β) : f '' (f ⁻¹' t 
inter s) = t inter f '' s
参数：f : α -> β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) :
    f '' (f ⁻¹' t ∩ s) = t ∩ f '' s := by simp only [inter_comm, image_inter_preimage]

@[simp]
/-
**Set.image_inter_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_inter_nonempty_iff {f : α -> β} {s : Set α} {t : Set β} : (f '' s in
ter t).Nonempty ↔ (s inter f ⁻¹' t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} :
    (f '' s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty := by
  rw [← image_inter_preimage, image_nonempty]
/-
**Set.disjoint_image_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_left {f : α -> β} {s : Set α} {t : Set β} : Disjoint (f '' 
s) t ↔ Disjoint s (f ⁻¹' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_image_left {f : α → β} {s : Set α} {t : Set β} :
    Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t) := by
  simp_rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty, image_inter_nonempty_iff]
/-
**Set.disjoint_image_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_right {f : α -> β} {s : Set α} {t : Set β} : Disjoint t (f 
'' s) ↔ Disjoint (f ⁻¹' t) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Set.disjoint_image_left`：disjoint_image_left {f : α -> β} {s : Set α} {t
 : Set β} : Disjoint (f '' s) t ↔ Disjoint s (f ⁻¹' t)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_image_right {f : α → β} {s : Set α} {t : Set β} :
    Disjoint t (f '' s) ↔ Disjoint (f ⁻¹' t) s := by
  rw [disjoint_comm, disjoint_comm (b := s), disjoint_image_left]
/-
**Set.image_sdiff_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sdiff_preimage {f : α -> β} {s : Set α} {t : Set β} : f '' (s \ f ⁻¹
' t) = f '' s \ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_sdiff_preimage {f : α → β} {s : Set α} {t : Set β} :
    f '' (s \ f ⁻¹' t) = f '' s \ t := by simp_rw [sdiff_eq, ← preimage_compl, image_inter_preimage]

@[deprecated (since := "2026-06-03")] alias image_diff_preimage := image_sdiff_preimage
/-
**Set.compl_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_image : image (compl : Set α -> Set α) = preimage compl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl
/-
**Set.compl_image_ofPred** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_image_ofPred {p : Set α -> Prop} : compl '' { s | p s } = { s | p sᶜ
 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Set.compl_image`：compl_image : image (compl : Set α -> Set α) = preimage
 compl
-/
theorem compl_image_ofPred {p : Set α → Prop} : compl '' { s | p s } = { s | p sᶜ } :=
  congr_fun compl_image {x | p x}

@[deprecated (since := "2026-07-13")] alias compl_image_set_of := compl_image_ofPred
/-
**Set.inter_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：inter_preimage_subset (s : Set α) (t : Set β) (f : α -> β) : s inter f ⁻¹'
 t subseteq f ⁻¹' (f '' s inter t)
参数：s : Set α；t : Set β；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) := fun _ h => ⟨mem_image_of_mem _ h.left, h.right⟩
/-
**Set.union_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：union_preimage_subset (s : Set α) (t : Set β) (f : α -> β) : s union f ⁻¹'
 t subseteq f ⁻¹' (f '' s union t)
参数：s : Set α；t : Set β；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) := fun _ h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r
/-
**Set.subset_image_union** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_image_union (f : α -> β) (s : Set α) (t : Set β) : f '' (s union f 
⁻¹' t) subseteq f '' s union t
参数：f : α -> β；s : Set α；t : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.union_preimage_subset`：union_preimage_subset (s : Set α) (t : Set β)
 (f : α -> β) : s union f ⁻¹' t subseteq f ⁻¹' (f '' s union t)
-/
theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)
/-
**Set.preimage_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_subset_iff {A : Set α} {B : Set β} {f : α -> β} : f ⁻¹' B subsete
q A ↔ forall a : α, f a in B -> a in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl
/-
**Set.image_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_image {f : α -> β} (hf : Injective f) : f '' s = f '' t ↔ s = t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem image_eq_image {f : α → β} (hf : Injective f) : f '' s = f '' t ↔ s = t :=
  Iff.symm <|
    (Iff.intro fun eq => eq ▸ rfl) fun eq => by
      rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]
/-
**Set.subset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_image_iff {t : Set β} : t subseteq f '' s ↔ exists u, u subseteq s 
∧ f '' u = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_inter`：image_preimage_inter (f : α -> β) (s : Set α) 
(t : Set β) : f '' (f ⁻¹' t inter s) = t inter f '' s
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem subset_image_iff {t : Set β} :
    t ⊆ f '' s ↔ ∃ u, u ⊆ s ∧ f '' u = t := by
  refine ⟨fun h ↦ ⟨f ⁻¹' t ∩ s, inter_subset_right, ?_⟩,
    fun ⟨u, hu, hu'⟩ ↦ hu'.symm ▸ image_mono hu⟩
  rwa [image_preimage_inter, inter_eq_left]

@[simp]
/-
**Set.exists_subset_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：exists_subset_image_iff {p : Set β -> Prop} : (exists t subseteq f '' s, p
 t) ↔ exists t subseteq s, p (f '' t)
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
lemma exists_subset_image_iff {p : Set β → Prop} : (∃ t ⊆ f '' s, p t) ↔ ∃ t ⊆ s, p (f '' t) := by
  simp [subset_image_iff]

@[simp]
/-
**Set.forall_subset_image_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：forall_subset_image_iff {p : Set β -> Prop} : (forall t subseteq f '' s, p
 t) ↔ forall t subseteq s, p (f '' t)
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
lemma forall_subset_image_iff {p : Set β → Prop} : (∀ t ⊆ f '' s, p t) ↔ ∀ t ⊆ s, p (f '' t) := by
  simp [subset_image_iff]
/-
**Set.image_subset_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_image_iff {f : α -> β} (hf : Injective f) : f '' s subseteq f
 '' t ↔ s subseteq t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f '' s ⊆ f '' t ↔ s ⊆ t := by
  grind [Set.image_subset_iff, Set.preimage_image_eq]
/-
**Set.prod_quotient_preimage_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s -> β) {h : 
α -> β} (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) : { x : Quotient s × Quot
ient s | (g x.1, g x.2) in r } = (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : 
α × α => (h a.1, h a.2)) ⁻¹' r)
参数：g : Quotient s -> β；Hh : h = g ∘ Quotient.mk''；r : Set (β × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β}
    (Hh : h = g ∘ Quotient.mk'') (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quot.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩
/-
**Set.exists_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_image_iff (f : α -> β) (x : Set α) (P : β -> Prop) : (exists a : f 
'' x, P a) ↔ exists a : x, P (f a)
参数：f : α -> β；x : Set α；P : β -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) :
    (∃ a : f '' x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.prop.choose_spec.1⟩, a.prop.choose_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩
/-
**Set.imageFactorization_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：imageFactorization_eq {f : α -> β} {s : Set α} : Subtype.val ∘ imageFactor
ization f s = f ∘ Subtype.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem imageFactorization_eq {f : α → β} {s : Set α} :
    Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun _ => rfl
/-
**Set.imageFactorization_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：imageFactorization_surjective {f : α -> β} {s : Set α} : Surjective (image
Factorization f s)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageFactorization_surjective {f : α → β} {s : Set α} :
    Surjective (imageFactorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
/-
**Set.image_perm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a != a } subse
teq s) : σ '' s = s
参数：hs : { a : α | σ a != a } subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x

--- 原说明 ---
If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ
` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ '' s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine ⟨?_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
  · refine iff_of_true ⟨σ.symm i, hs fun h => hi ?_, σ.apply_symm_apply _⟩ (hs hi)
    grind

end Image

/-! ### Lemmas about the powerset and image. -/

/-- The powerset of `{a} ∪ s` is `𝒫 s` together with `{a} ∪ t` for each `t ∈ 𝒫 s`. -/
/-
**Set.powerset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_insert (s : Set α) (a : α) : 𝒫 insert a s = 𝒫 s union insert a ''
 𝒫 s
参数：s : Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b

--- 原说明 ---
The powerset of `{a} ∪ s` is `𝒫 s` together with `{a} ∪ t` for each `t ∈ 𝒫 s`.
-/
theorem powerset_insert (s : Set α) (a : α) : 𝒫 insert a s = 𝒫 s ∪ insert a '' 𝒫 s := by
  ext t
  constructor
  · intro h
    by_cases hs : a ∈ t
    · right
      refine ⟨t \ {a}, by grind⟩
    · grind
  · grind
/-
**Set.disjoint_powerset_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_powerset_insert {s : Set α} {a : α} (h : a ∉ s) : Disjoint (𝒫 s) 
(insert a '' 𝒫 s)
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_powerset_insert {s : Set α} {a : α} (h : a ∉ s) :
    Disjoint (𝒫 s) (insert a '' 𝒫 s) := by
  grind
/-
**Set.powerset_insert_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：powerset_insert_injOn {s : Set α} {a : α} (h : a ∉ s) : Set.InjOn (insert 
a) (𝒫 s)
参数：h : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powerset_insert_injOn {s : Set α} {a : α} (h : a ∉ s) :
    Set.InjOn (insert a) (𝒫 s) := fun u u_mem v v_mem eq ↦ by
  grind

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α} {s t : Set α}

/-
**Set.forall_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_mem_range {p : α -> Prop} : (forall a in range f, p a) ↔ forall i, 
p (f i)
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
theorem forall_mem_range {p : α → Prop} : (∀ a ∈ range f, p a) ↔ ∀ i, p (f i) := by simp
/-
**Set.forall_subtype_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_subtype_range_iff {p : range f -> Prop} : (forall a : range f, p a)
 ↔ forall i, p ⟨f i, mem_range_self _⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forall_subtype_range_iff {p : range f → Prop} :
    (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ := by grind
/-
**Set.exists_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_range_iff {p : α -> Prop} : (exists a in range f, p a) ↔ exists i, 
p (f i)
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
theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ ∃ i, p (f i) := by simp
/-
**Set.exists_subtype_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_subtype_range_iff {p : range f -> Prop} : (exists a : range f, p a)
 ↔ exists i, p ⟨f i, mem_range_self _⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_subtype_range_iff {p : range f → Prop} :
    (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ := by grind
/-
**Set.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_univ : range f = univ ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
-/
theorem range_eq_univ : range f = univ ↔ Surjective f :=
  eq_univ_iff_forall

alias ⟨_, _root_.Function.Surjective.range_eq⟩ := range_eq_univ

@[simp]
/-
**Set.subset_range_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_range_of_surjective {f : α -> β} (h : Surjective f) (s : Set β) : s
 subseteq range f
参数：h : Surjective f；s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
-/
theorem subset_range_of_surjective {f : α → β} (h : Surjective f) (s : Set β) :
    s ⊆ range f := Surjective.range_eq h ▸ subset_univ s

@[simp]
/-
**Set.image_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_univ {f : α -> β} : f '' univ = range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_univ {f : α → β} : f '' univ = range f := by grind
/-
**Set.image_compl_eq_range_sdiff_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_compl_eq_range_sdiff_image {f : α -> β} (hf : Injective f) (s : Set 
α) : f '' sᶜ = range f \ f '' s
参数：hf : Injective f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
-/
lemma image_compl_eq_range_sdiff_image {f : α → β} (hf : Injective f) (s : Set α) :
    f '' sᶜ = range f \ f '' s := by rw [← image_univ, ← image_sdiff hf, compl_eq_univ_sdiff]

@[deprecated (since := "2026-06-03")]
alias image_compl_eq_range_diff_image := image_compl_eq_range_sdiff_image

/-- Alias of `Set.image_compl_eq_range_sdiff_image`. -/
/-
**Set.range_sdiff_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：range_sdiff_image {f : α -> β} (hf : Injective f) (s : Set α) : range f \ 
f '' s = f '' sᶜ
参数：hf : Injective f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_compl_eq_range_sdiff_image`：image_compl_eq_range_sdiff_image {
f : α -> β} (hf : Injective f) (s : Set α) : f '' sᶜ = range f \ f '' s

--- 原说明 ---
Alias of `Set.image_compl_eq_range_sdiff_image`.
-/
lemma range_sdiff_image {f : α → β} (hf : Injective f) (s : Set α) :
    range f \ f '' s = f '' sᶜ := by
  rw [image_compl_eq_range_sdiff_image hf]

@[deprecated (since := "2026-06-03")] alias range_diff_image := range_sdiff_image

@[simp]
/-
**Set.preimage_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_univ_iff {f : α -> β} {s} : f ⁻¹' s = univ ↔ range f subseteq 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_eq_univ_iff {f : α → β} {s} : f ⁻¹' s = univ ↔ range f ⊆ s := by
  rw [← univ_subset_iff, ← image_subset_iff, image_univ]
/-
**Set.image_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_subset_range (f : α -> β) (s) : f '' s subseteq range f
参数：f : α -> β；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem image_subset_range (f : α → β) (s) : f '' s ⊆ range f := by
  rw [← image_univ]; exact image_mono (subset_univ _)
/-
**Set.mem_range_of_mem_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_range_of_mem_image (f : α -> β) (s) {x : β} (h : x in f '' s) : x in r
ange f
参数：f : α -> β；s；h : x in f '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f '' s) : x ∈ range f :=
  image_subset_range f s h
/-
**Set._root_.Nat.mem_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Nat.mem_range_succ (i : ℕ) : i ∈ range Nat.succ ↔ 0 < i :=
  ⟨by grind, fun h => ⟨_, Nat.succ_pred_eq_of_pos h⟩⟩
/-
**Set.Nonempty.preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.Nonempty → ∀ {f : α → β}, s
 ⊆ Set.range f → (f ⁻¹' s).Nonempty
参数：f ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ range f) :
    (f ⁻¹' s).Nonempty :=
  let ⟨_, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, by grind⟩
/-
**Set.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g '' range f
参数：g : α -> β；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f := by aesop

/--
Variant of `range_comp` using a lambda instead of function composition.
-/
/-
**Set.range_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_comp' (g : α -> β) (f : ι -> α) : range (fun x => g (f x)) = g '' ra
nge f
参数：g : α -> β；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f

--- 原说明 ---
Variant of `range_comp` using a lambda instead of function composition.
-/
theorem range_comp' (g : α → β) (f : ι → α) : range (fun x => g (f x)) = g '' range f :=
  range_comp g f
/-
**Set.range_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_subset_iff : range f subseteq s ↔ forall y, f y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_mem_range
/-
**Set.range_subset_range_iff_exists_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_subset_range_iff_exists_comp {f : α -> γ} {g : β -> γ} : range f sub
seteq range g ↔ exists h : α -> β, f = g ∘ h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem range_subset_range_iff_exists_comp {f : α → γ} {g : β → γ} :
    range f ⊆ range g ↔ ∃ h : α → β, f = g ∘ h := by
  simp only [range_subset_iff, mem_range, Classical.skolem, funext_iff, (· ∘ ·), eq_comm]
/-
**Set.range_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_iff (f : α -> β) (s : Set β) : range f = s ↔ (forall a, f a in s)
 ∧ forall b in s, exists a, f a = b
参数：f : α -> β；s : Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_eq_iff (f : α → β) (s : Set β) :
    range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b := by grind
/-
**Set.range_comp_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_comp_subset_range (f : α -> β) (g : β -> γ) : range (g ∘ f) subseteq
 range g
参数：f : α -> β；g : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g := by grind
/-
**Set.range_nonempty_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨_, x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩
/-
**Set.range_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_nonempty [h : Nonempty ι] (f : ι -> α) : (range f).Nonempty
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_nonempty_iff_nonempty`：range_nonempty_iff_nonempty : (range f)
.Nonempty ↔ Nonempty ι
-/
theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h

@[simp]
/-
**Set.range_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_empty_iff {f : ι -> α} : range f = ∅ ↔ IsEmpty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Set.range_nonempty_iff_nonempty`：range_nonempty_iff_nonempty : (range f)
.Nonempty ↔ Nonempty ι
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]
/-
**Set.range_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = ∅
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_empty_iff`：range_eq_empty_iff {f : ι -> α} : range f = ∅ ↔ 
IsEmpty ι
-/
theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›

@[simp]
/-
**Set.range_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_singleton_iff [Nonempty ι] {y} : Set.range f = {y} ↔ forall (x : 
ι), f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_eq_singleton_iff [Nonempty ι] {y} :
    Set.range f = {y} ↔ ∀ (x : ι), f x = y := by
  simp_rw [Set.ext_iff, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun h _ => by simp_rw [← h, exists_apply_eq_apply],
      fun h _ => by simp_rw [h, exists_const, eq_comm]⟩
/-
**Set.range_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eq_singleton [Nonempty ι] {y} (hy : forall (x : ι), f x = y) : Set.r
ange f = {y}
参数：hy : forall (x : ι), f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_singleton_iff`：range_eq_singleton_iff [Nonempty ι] {y} : Se
t.range f = {y} ↔ forall (x : ι), f x = y
-/
theorem range_eq_singleton [Nonempty ι] {y} (hy : ∀ (x : ι), f x = y) :
    Set.range f = {y} := range_eq_singleton_iff.mpr hy
/-
**Set.instNonemptyRange** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instNonemptyRange [Nonempty ι] (f : ι -> α) : Nonempty (range f)
参数：f : ι -> α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
instance instNonemptyRange [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
/-
**Set.image_union_image_compl_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_union_image_compl_eq_range (f : α -> β) : f '' s union f '' sᶜ = ran
ge f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_union_image_compl_eq_range (f : α → β) : f '' s ∪ f '' sᶜ = range f := by grind
/-
**Set.insert_image_compl_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_image_compl_eq_range (f : α -> β) (x : α) : insert (f x) (f '' {x}ᶜ
) = range f
参数：f : α -> β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f '' {x}ᶜ) = range f := by
  grind
/-
**Set.image_preimage_eq_range_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_eq_range_inter {f : α -> β} {t : Set β} : f '' f ⁻¹' t = ra
nge f inter t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_preimage_eq_range_inter {f : α → β} {t : Set β} : f '' f ⁻¹' t = range f ∩ t := by
  grind
/-
**Set.image_preimage_eq_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_eq_inter_range {f : α -> β} {t : Set β} : f '' f ⁻¹' t = t 
inter range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f '' f ⁻¹' t = t ∩ range f := by
  grind
/-
**Set.image_preimage_eq_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_eq_of_subset {f : α -> β} {s : Set β} (hs : s subseteq rang
e f) : f '' f ⁻¹' s = s
参数：hs : s subseteq range f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) :
    f '' f ⁻¹' s = s := by grind
/-
**Set.image_preimage_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_preimage_eq_iff {f : α -> β} {s : Set β} : f '' f ⁻¹' s = s ↔ s subs
eteq range f
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f '' f ⁻¹' s = s ↔ s ⊆ range f := by grind
/-
**Set.subset_range_iff_exists_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_range_iff_exists_image_eq {f : α -> β} {s : Set β} : s subseteq ran
ge f ↔ exists t, f '' t = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_preimage_eq_iff`：image_preimage_eq_iff {f : α -> β} {s : Set β
} : f '' f ⁻¹' s = s ↔ s subseteq range f
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ range f ↔ ∃ t, f '' t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨_, ht⟩ => ht ▸ image_subset_range _ _⟩
/-
**Set.range_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_image (f : α -> β) : range (image f) = 𝒫 range f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.subset_range_iff_exists_image_eq`：subset_range_iff_exists_image_eq {
f : α -> β} {s : Set β} : s subseteq range f ↔ exists t, f '' t = s
-/
theorem range_image (f : α → β) : range (image f) = 𝒫 range f :=
  ext fun _ => subset_range_iff_exists_image_eq.symm

@[simp]
/-
**Set.exists_subset_range_and_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：exists_subset_range_and_iff {f : α -> β} {p : Set β -> Prop} : (exists s, 
s subseteq range f ∧ p s) ↔ exists s, p (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
· 使用定理 `Set.range_image`：range_image (f : α -> β) : range (image f) = 𝒫 range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exists_subset_range_and_iff {f : α → β} {p : Set β → Prop} :
    (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f '' s) := by
  rw [← exists_range_iff, range_image]; rfl

@[simp]
/-
**Set.forall_subset_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：forall_subset_range_iff {f : α -> β} {p : Set β -> Prop} : (forall s, s su
bseteq range f -> p s) ↔ forall s, p (f '' s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.range_image`：range_image (f : α -> β) : range (image f) = 𝒫 range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_subset_range_iff {f : α → β} {p : Set β → Prop} :
    (∀ s, s ⊆ range f → p s) ↔ ∀ s, p (f '' s) := by
  rw [← forall_mem_range, range_image]; simp only [mem_powerset_iff]

@[simp]
/-
**Set.preimage_subset_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_subset_preimage_iff {s t : Set α} {f : β -> α} (hs : s subseteq r
ange f) : f ⁻¹' s subseteq f ⁻¹' t ↔ s subseteq t
参数：hs : s subseteq range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
  intro h x; apply h
/-
**Set.preimage_eq_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_preimage' {s t : Set α} {f : β -> α} (hs : s subseteq range f)
 (ht : t subseteq range f) : f ⁻¹' s = f ⁻¹' t ↔ s = t
参数：hs : s subseteq range f；ht : t subseteq range f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_subset_preimage_iff`：preimage_subset_preimage_iff {s t : Se
t α} {f : β -> α} (hs : s subseteq range f) : f ⁻¹' s subseteq f ⁻¹' t ↔ s subse
teq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply Subset.antisymm
    · rw [← preimage_subset_preimage_iff hs, h]
    · rw [← preimage_subset_preimage_iff ht, h]
  rintro rfl; rfl

-- Not `@[simp]` since `simp` can prove this.
/-
**Set.preimage_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inter_range {f : α -> β} {s : Set β} : f ⁻¹' (s inter range f) = 
f ⁻¹' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
-/
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩

-- Not `@[simp]` since `simp` can prove this.
/-
**Set.preimage_range_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_range_inter {f : α -> β} {s : Set β} : f ⁻¹' (range f inter s) = 
f ⁻¹' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.preimage_inter_range`：preimage_inter_range {f : α -> β} {s : Set β} 
: f ⁻¹' (s inter range f) = f ⁻¹' s
-/
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]
/-
**Set.preimage_image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_image_preimage {f : α -> β} {s : Set β} : f ⁻¹' f '' f ⁻¹' s = f 
⁻¹' s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `Set.preimage_range_inter`：preimage_range_inter {f : α -> β} {s : Set β} 
: f ⁻¹' (range f inter s) = f ⁻¹' s
-/
theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' f '' f ⁻¹' s = f ⁻¹' s := by
  rw [image_preimage_eq_range_inter, preimage_range_inter]

@[simp, mfld_simps]
/-
**Set.range_id** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_id : range (@id α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
theorem range_id : range (@id α) = univ :=
  range_eq_univ.2 surjective_id

@[simp, mfld_simps]
/-
**Set.range_id'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_id' : (range fun x : α => x) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id' : (range fun x : α => x) = univ :=
  range_id

@[simp]
/-
**Set._root_.Prod.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjective.range_eq

@[simp]
/-
**Set._root_.Prod.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq

@[simp]
/-
**Set.range_eval** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_eval {α : ι -> Sort _} [forall i, Nonempty (α i)] (i : ι) : range (e
val i : (forall i, α i) -> α i) = univ
参数：α i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
-/
theorem range_eval {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq
/-
**Set.range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inl : range (@Sum.inl α β) = {x | Sum.isLeft x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Bool.false_eq_true`：(false = true) = False
-/
theorem range_inl : range (@Sum.inl α β) = {x | Sum.isLeft x} := by ext (_ | _) <;> simp
/-
**Set.range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inr : range (@Sum.inr α β) = {x | Sum.isRight x}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_inr : range (@Sum.inr α β) = {x | Sum.isRight x} := by ext (_ | _) <;> simp
/-
**Set.isCompl_range_inl_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isCompl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.i
nr)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_le`：of_le (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y) : IsCompl x y
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem isCompl_range_inl_range_inr : IsCompl (range <| @Sum.inl α β) (range Sum.inr) :=
  IsCompl.of_le
    (by
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, h⟩⟩
      exact Sum.noConfusion rfl rfl (heq_of_eq h))
    (by rintro (x | y) - <;> [left; right] <;> exact mem_range_self _)

@[simp]
/-
**Set.range_inl_union_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inl_union_range_inr : range (Sum.inl : α -> α oplus β) union range S
um.inr = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem range_inl_union_range_inr : range (Sum.inl : α → α ⊕ β) ∪ range Sum.inr = univ :=
  isCompl_range_inl_range_inr.sup_eq_top

@[simp]
/-
**Set.range_inl_inter_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inl_inter_range_inr : range (Sum.inl : α -> α oplus β) inter range S
um.inr = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem range_inl_inter_range_inr : range (Sum.inl : α → α ⊕ β) ∩ range Sum.inr = ∅ :=
  isCompl_range_inl_range_inr.inf_eq_bot

@[simp]
/-
**Set.range_inr_union_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inr_union_range_inl : range (Sum.inr : β -> α oplus β) union range S
um.inl = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem range_inr_union_range_inl : range (Sum.inr : β → α ⊕ β) ∪ range Sum.inl = univ :=
  isCompl_range_inl_range_inr.symm.sup_eq_top

@[simp]
/-
**Set.range_inr_inter_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inr_inter_range_inl : range (Sum.inr : β -> α oplus β) inter range S
um.inl = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem range_inr_inter_range_inl : range (Sum.inr : β → α ⊕ β) ∩ range Sum.inl = ∅ :=
  isCompl_range_inl_range_inr.symm.inf_eq_bot

@[simp]
/-
**Set.preimage_inl_image_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' @Sum.inr α β '' s = ∅
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' @Sum.inr α β '' s = ∅ := by
  ext
  simp

@[simp]
/-
**Set.preimage_inr_image_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' @Sum.inl α β '' s = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' @Sum.inl α β '' s = ∅ := by
  ext
  simp

@[simp]
/-
**Set.preimage_inl_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β -> α oplus β) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.preimage_inl_image_inr`：preimage_inl_image_inr (s : Set β) : Sum.inl
 ⁻¹' @Sum.inr α β '' s = ∅
-/
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → α ⊕ β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]

@[simp]
/-
**Set.preimage_inr_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α -> α oplus β) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.preimage_inr_image_inl`：preimage_inr_image_inl (s : Set α) : Sum.inr
 ⁻¹' @Sum.inl α β '' s = ∅
-/
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → α ⊕ β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]

@[simp]
/-
**Set.compl_range_inl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_range_inl : (range (Sum.inl : α -> α oplus β))ᶜ = range (Sum.inr : β
 -> α oplus β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem compl_range_inl : (range (Sum.inl : α → α ⊕ β))ᶜ = range (Sum.inr : β → α ⊕ β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr

@[simp]
/-
**Set.compl_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_range_inr : (range (Sum.inr : β -> α oplus β))ᶜ = range (Sum.inl : α
 -> α oplus β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_inl_range_inr`：isCompl_range_inl_range_inr : IsCompl (
range <| @Sum.inl α β) (range Sum.inr)
-/
theorem compl_range_inr : (range (Sum.inr : β → α ⊕ β))ᶜ = range (Sum.inl : α → α ⊕ β) :=
  IsCompl.compl_eq isCompl_range_inl_range_inr.symm
/-
**Set.preimage_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_sumElim (s : Set γ) (f : α -> γ) (g : β -> γ) : Sum.elim f g ⁻¹' 
s = Sum.inl '' f ⁻¹' s union Sum.inr '' g ⁻¹' s
参数：s : Set γ；f : α -> γ；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem preimage_sumElim (s : Set γ) (f : α → γ) (g : β → γ) :
    Sum.elim f g ⁻¹' s = Sum.inl '' f ⁻¹' s ∪ Sum.inr '' g ⁻¹' s := by
  ext (_ | _) <;> simp
/-
**Set.image_preimage_inl_union_image_preimage_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
形式化陈述：image_preimage_inl_union_image_preimage_inr (s : Set (α oplus β)) : Sum.in
l '' Sum.inl ⁻¹' s union Sum.inr '' Sum.inr ⁻¹' s = s
参数：s : Set (α oplus β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_sumElim`：preimage_sumElim (s : Set γ) (f : α -> γ) (g : β -
> γ) : Sum.elim f g ⁻¹' s = Sum.inl '' f ⁻¹' s union Sum.inr '' g ⁻¹' s
· 使用定理 `Sum.elim_inl_inr`：∀ {α : Type u_1} {β : Type u_2}, Sum.elim Sum.inl Sum.
inr = id
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem image_preimage_inl_union_image_preimage_inr (s : Set (α ⊕ β)) :
    Sum.inl '' Sum.inl ⁻¹' s ∪ Sum.inr '' Sum.inr ⁻¹' s = s := by
  rw [← preimage_sumElim, Sum.elim_inl_inr, preimage_id]
/-
**Set.image_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_sumElim (s : Set (α oplus β)) (f : α -> γ) (g : β -> γ) : Sum.elim f
 g '' s = f '' Sum.inl ⁻¹' s union g '' Sum.inr ⁻¹' s
参数：s : Set (α oplus β)；f : α -> γ；g : β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_sumElim (s : Set (α ⊕ β)) (f : α → γ) (g : β → γ) :
    Sum.elim f g '' s = f '' Sum.inl ⁻¹' s ∪ g '' Sum.inr ⁻¹' s := by
  grind

@[simp]
/-
**Set.range_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r) = univ
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  Quot.mk_surjective.range_eq

@[simp]
/-
**Set.range_quot_lift** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quot_lift {r : ι -> ι -> Prop} (hf : forall x y, r x y -> f x = f y)
 : range (Quot.lift f hf) = range f
参数：hf : forall x y, r x y -> f x = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
    range (Quot.lift f hf) = range f :=
  ext fun _ => Quot.mk_surjective.exists

@[simp]
/-
**Set.range_quotient_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quotient_mk {s : Setoid α} : range (Quotient.mk s) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quot_mk`：range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r
) = univ
-/
theorem range_quotient_mk {s : Setoid α} : range (Quotient.mk s) = univ :=
  range_quot_mk _

@[simp]
/-
**Set.range_quotient_lift** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quotient_lift [s : Setoid ι] (hf) : range (Quotient.lift f hf : Quot
ient s -> α) = range f
参数：hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quot_lift`：range_quot_lift {r : ι -> ι -> Prop} (hf : forall x
 y, r x y -> f x = f y) : range (Quot.lift f hf) = range f
-/
theorem range_quotient_lift [s : Setoid ι] (hf) :
    range (Quotient.lift f hf : Quotient s → α) = range f :=
  range_quot_lift _

@[simp]
/-
**Set.range_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α -> Quotient s)
 = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quot_mk`：range_quot_mk (r : α -> α -> Prop) : range (Quot.mk r
) = univ
-/
theorem range_quotient_mk' {s : Setoid α} : range (Quotient.mk' : α → Quotient s) = univ :=
  range_quot_mk _
/-
**Set.Quotient.range_mk''** 是 Mathlib 中的一个定理，位于命名空间 `Set.Quotient`。
形式化陈述：∀ {α : Type u_1} {sa : Setoid α}, Set.range Quotient.mk'' = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quotient_mk`：range_quotient_mk {s : Setoid α} : range (Quotien
t.mk s) = univ
-/
lemma Quotient.range_mk'' {sa : Setoid α} : range (Quotient.mk'' (s₁ := sa)) = univ :=
  range_quotient_mk

@[simp]
/-
**Set.range_quotient_lift_on'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_quotient_lift_on' {s : Setoid ι} (hf) : (range fun x : Quotient s =>
 Quotient.liftOn' x f hf) = range f
参数：hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_quot_lift`：range_quot_lift {r : ι -> ι -> Prop} (hf : forall x
 y, r x y -> f x = f y) : range (Quot.lift f hf) = range f
-/
theorem range_quotient_lift_on' {s : Setoid ι} (hf) :
    (range fun x : Quotient s => Quotient.liftOn' x f hf) = range f :=
  range_quot_lift _
/-
**Set.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：canLift (c) (p) [CanLift α β c p] : CanLift (Set α) (Set β) (c '' ·) fun s
 => forall x in s, p x where prf _ hs
参数：c；p。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_range_iff_exists_image_eq`：subset_range_iff_exists_image_eq {
f : α -> β} {s : Set β} : s subseteq range f ↔ exists t, f '' t = s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) (c '' ·) fun s => ∀ x ∈ s, p x where
  prf _ hs := subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)
/-
**Set.range_const_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_const_subset {c : α} : (range fun _ : ι => c) subseteq {c}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
-/
theorem range_const_subset {c : α} : (range fun _ : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun _ => rfl

@[simp]
/-
**Set.range_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_const : forall [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_eq_singleton`：range_eq_singleton [Nonempty ι] {y} (hy : forall
 (x : ι), f x = y) : Set.range f = {y}
-/
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun _ : ι => c) = {c} :=
  range_eq_singleton (fun _ => rfl)
/-
**Set.range_subtype_map** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_subtype_map {p : α -> Prop} {q : β -> Prop} (f : α -> β) (h : forall
 x, p x -> q (f x)) : range (Subtype.map f h) = (↑) ⁻¹' f '' { x | p x }
参数：f : α -> β；h : forall x, p x -> q (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    range (Subtype.map f h) = (↑) ⁻¹' f '' { x | p x } := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map]
  simp only [Subtype.mk.injEq, exists_prop, mem_ofPred_eq]
/-
**Set.image_swap_eq_preimage_swap** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `Prod.swap_leftInverse`：swap_leftInverse : Function.LeftInverse (@swap α 
β) swap
· 使用定理 `Prod.swap_rightInverse`：swap_rightInverse : Function.RightInverse (@swap
 α β) swap
-/
theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_leftInverse Prod.swap_rightInverse
/-
**Set.preimage_singleton_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_singleton_nonempty {f : α -> β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ 
y in range f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl
/-
**Set.preimage_singleton_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_singleton_eq_empty {f : α -> β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ ran
ge f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.preimage_singleton_nonempty`：preimage_singleton_nonempty {f : α -> β
} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y in range f
-/
theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not
/-
**Set.range_subset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_subset_singleton {f : ι -> α} {x : α} : range f subseteq {x} ↔ f = c
onst ι x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x := by
  simp [funext_iff]
/-
**Set.image_compl_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_compl_preimage {f : α -> β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = range f 
\ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `Set.image_sdiff_preimage`：image_sdiff_preimage {f : α -> β} {s : Set α} 
{t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem image_compl_preimage {f : α → β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = range f \ s := by
  rw [compl_eq_univ_sdiff, image_sdiff_preimage, image_univ]
/-
**Set.rangeFactorization_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：rangeFactorization_eq {f : ι -> β} : Subtype.val ∘ rangeFactorization f = 
f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem rangeFactorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun _ => rfl

@[simp]
/-
**Set.rangeFactorization_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：rangeFactorization_coe (f : ι -> β) (a : ι) : (rangeFactorization f a : β)
 = f a
参数：f : ι -> β；a : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rangeFactorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl

@[simp]
/-
**Set.coe_comp_rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：coe_comp_rangeFactorization (f : ι -> β) : (↑) ∘ rangeFactorization f = f
参数：f : ι -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_rangeFactorization (f : ι → β) : (↑) ∘ rangeFactorization f = f := rfl
/-
**Set.image_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_eq_range (f : α -> β) (s : Set α) : f '' s = range fun x : s => f x
参数：f : α -> β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem image_eq_range (f : α → β) (s : Set α) : f '' s = range fun x : s => f x := by
  ext
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
  · rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩
/-
**Set._root_.Sum.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Sum.range_eq (f : α ⊕ β → γ) :
    range f = range (f ∘ Sum.inl) ∪ range (f ∘ Sum.inr) :=
  ext fun _ => Sum.exists

@[simp]
/-
**Set.Sum.elim_range** 是 Mathlib 中的一个定理，位于命名空间 `Set.Sum`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → γ) (g : β → γ),   
Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
参数：f : α → γ；g : β → γ；Sum.elim f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.range_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α ⊕ β 
→ γ),   Set.range f = Set.range (f ∘ Sum.inl) ∪ Set.range (f ∘ Sum.inr)
-/
theorem Sum.elim_range (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  Sum.range_eq _
/-
**Set.range_ite_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_ite_subset' {p : Prop} [Decidable p] {f g : α -> β} : range (if p th
en f else g) subseteq range f union range g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} :
    range (if p then f else g) ⊆ range f ∪ range g := by grind
/-
**Set.range_ite_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_ite_subset {p : α -> Prop} [DecidablePred p] {f g : α -> β} : (range
 fun x => if p x then f x else g x) subseteq range f union range g
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (range fun x => if p x then f x else g x) ⊆ range f ∪ range g := by grind

@[simp]
/-
**Set.preimage_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_range (f : α -> β) : f ⁻¹' range f = univ
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self

/-- The range of a function from a `Unique` type contains just the
function applied to its single value. -/
/-
**Set.range_unique** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_unique [Unique ι] : range f = {f default}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The range of a function from a `Unique` type contains just the
function applied to its single value.
-/
theorem range_unique [Unique ι] : range f = {f default} := by
  aesop (add simp [Unique.eq_default])

@[simp]
/-
**Set.range_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_singleton {x : α} (f : ({x} : Set α) -> β) : range f = {f ⟨x, mem_si
ngleton x⟩}
参数：f : ({x} : Set α) -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_unique`：range_unique [Unique ι] : range f = {f default}
-/
theorem range_singleton {x : α} (f : ({x} : Set α) → β) : range f = {f ⟨x, mem_singleton x⟩} :=
  range_unique

@[simp]
/-
**Set.range_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_insert {x : α} {s : Set α} (f : ((insert x s) : Set α) -> β) : range
 f = insert (f ⟨x, mem_insert x s⟩) (range fun y : s => f ⟨y, mem_insert_of_mem 
_ y.2⟩)
参数：f : ((insert x s) : Set α) -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem range_insert {x : α} {s : Set α} (f : ((insert x s) : Set α) → β) :
    range f = insert (f ⟨x, mem_insert x s⟩)
      (range fun y : s ↦ f ⟨y, mem_insert_of_mem _ y.2⟩) := by
  aesop
/-
**Set.range_sdiff_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_sdiff_image_subset (f : α -> β) (s : Set α) : range f \ f '' s subse
teq f '' sᶜ
参数：f : α -> β；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_sdiff_image_subset (f : α → β) (s : Set α) : range f \ f '' s ⊆ f '' sᶜ :=
  fun _ ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

@[deprecated (since := "2026-06-03")] alias range_diff_image_subset := range_sdiff_image_subset

@[simp]
/-
**Set.range_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_inclusion (h : s subseteq t) : range (inclusion h) = { x : t | (x : 
α) in s }
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_inclusion (h : s ⊆ t) : range (inclusion h) = { x : t | (x : α) ∈ s } := by
  ext ⟨x, hx⟩
  simp

-- When `f` is injective, see also `Equiv.ofInjective`.
/-
**Set.leftInverse_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：leftInverse_rangeSplitting (f : α -> β) : LeftInverse (rangeFactorization 
f) (rangeSplitting f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
-/
theorem leftInverse_rangeSplitting (f : α → β) :
    LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [rangeFactorization_coe]
  apply apply_rangeSplitting
/-
**Set.rangeSplitting_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：rangeSplitting_injective (f : α -> β) : Injective (rangeSplitting f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Set.leftInverse_rangeSplitting`：leftInverse_rangeSplitting (f : α -> β) 
: LeftInverse (rangeFactorization f) (rangeSplitting f)
-/
theorem rangeSplitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).injective
/-
**Set.rightInverse_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：rightInverse_rangeSplitting {f : α -> β} (h : Injective f) : RightInverse 
(rangeFactorization f) (rangeSplitting f)
参数：h : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.rightInverse_of_injective`：∀ {α : Sort u_1} {β : So
rt u_2} {f : α → β} {g : β → α},   Function.LeftInverse f g → Function.Injective
 f → Function.RightInverse f g
· 使用定理 `Set.leftInverse_rangeSplitting`：leftInverse_rangeSplitting (f : α -> β) 
: LeftInverse (rangeFactorization f) (rangeSplitting f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem rightInverse_rangeSplitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (leftInverse_rangeSplitting f).rightInverse_of_injective fun _ _ hxy =>
    h <| Subtype.ext_iff.1 hxy

@[simp]
/-
**Set.leftInverse_rangeFactorization_iff_injective** 是 Mathlib 中的一个引理，位于命名空间 `Se
t`。
形式化陈述：leftInverse_rangeFactorization_iff_injective (f : α -> β) : LeftInverse (r
angeSplitting f) (rangeFactorization f) ↔ f.Injective
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.rangeFactorization_injective`：∀ {α : Type u} {ι : Sort u_1} {f : ι →
 α}, Function.Injective (Set.rangeFactorization f) ↔ Function.Injective f
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.RightInverse.id`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f
 : α → β}, Function.RightInverse g f → f ∘ g = id
· 使用定理 `Set.rightInverse_rangeSplitting`：rightInverse_rangeSplitting {f : α -> β
} (h : Injective f) : RightInverse (rangeFactorization f) (rangeSplitting f)
-/
lemma leftInverse_rangeFactorization_iff_injective (f : α → β) :
    LeftInverse (rangeSplitting f) (rangeFactorization f) ↔ f.Injective :=
  ⟨(rangeFactorization_injective.mp ·.injective),
    fun h ↦ congrFun' (rightInverse_rangeSplitting h).id⟩
/-
**Set.preimage_rangeSplitting** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_rangeSplitting {f : α -> β} (hf : Injective f) : preimage (rangeS
plitting f) = image (rangeFactorization f)
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `Set.rightInverse_rangeSplitting`：rightInverse_rangeSplitting {f : α -> β
} (h : Injective f) : RightInverse (rangeFactorization f) (rangeSplitting f)
· 使用定理 `Set.leftInverse_rangeSplitting`：leftInverse_rangeSplitting (f : α -> β) 
: LeftInverse (rangeFactorization f) (rangeSplitting f)
-/
theorem preimage_rangeSplitting {f : α → β} (hf : Injective f) :
    preimage (rangeSplitting f) = image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (rightInverse_rangeSplitting hf)
      (leftInverse_rangeSplitting f)).symm
/-
**Set.rangeSplitting_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：rangeSplitting_strictMono [LinearOrder α] [Preorder β] {f : α -> β} (hf : 
Monotone f) : StrictMono (rangeSplitting f)
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
-/
theorem rangeSplitting_strictMono [LinearOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    StrictMono (rangeSplitting f) := by
  refine fun x y h ↦ hf.reflect_lt ?_
  simpa [apply_rangeSplitting f]
/-
**Set.isCompl_range_some_none** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：isCompl_range_some_none (α : Type*) : IsCompl (range (some : α -> Option α
)) {none}
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.of_le`：of_le (h₁ : x ⊓ y <= ⊥) (h₂ : ⊤ <= x ⊔ y) : IsCompl x y
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem isCompl_range_some_none (α : Type*) : IsCompl (range (some : α → Option α)) {none} :=
  IsCompl.of_le (fun _ ⟨⟨_, ha⟩, (hn : _ = none)⟩ => Option.some_ne_none _ (ha.trans hn))
    fun x _ => Option.casesOn x (Or.inr rfl) fun _ => Or.inl <| mem_range_self _

@[simp]
/-
**Set.compl_range_some** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：compl_range_some (α : Type*) : (range (some : α -> Option α))ᶜ = {none}
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}
-/
theorem compl_range_some (α : Type*) : (range (some : α → Option α))ᶜ = {none} :=
  (isCompl_range_some_none α).compl_eq

@[simp]
/-
**Set.range_some_inter_none** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_some_inter_none (α : Type*) : range (some : α -> Option α) inter {no
ne} = ∅
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}
-/
theorem range_some_inter_none (α : Type*) : range (some : α → Option α) ∩ {none} = ∅ :=
  (isCompl_range_some_none α).inf_eq_bot

-- Not `@[simp]` since `simp` can prove this.
/-
**Set.range_some_union_none** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_some_union_none (α : Type*) : range (some : α -> Option α) union {no
ne} = univ
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}
-/
theorem range_some_union_none (α : Type*) : range (some : α → Option α) ∪ {none} = univ :=
  (isCompl_range_some_none α).sup_eq_top

@[simp]
/-
**Set.insert_none_range_some** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：insert_none_range_some (α : Type*) : insert none (range (some : α -> Optio
n α)) = univ
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}
-/
theorem insert_none_range_some (α : Type*) : insert none (range (some : α → Option α)) = univ :=
  (isCompl_range_some_none α).symm.sup_eq_top
/-
**Set.image_of_range_union_range_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_of_range_union_range_eq_univ {α β γ γ' δ δ' : Type*} {h : β -> α} {f
 : γ -> β} {f₁ : γ' -> α} {f₂ : γ -> γ'} {g : δ -> β} {g₁ : δ' -> α} {g₂ : δ -> 
δ'} (hf : h ∘ f = f₁ ∘ f₂) (hg : h ∘ g = g₁ ∘ g₂) (hfg : range f union range g =
 univ) (s : Set β) : h '' s = f₁ '' f₂ '' f ⁻¹' s union g₁ '' g₂ '' g ⁻¹' s
参数：hf : h ∘ f = f₁ ∘ f₂；hg : h ∘ g = g₁ ∘ g₂；hfg : range f union range g = univ；
s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Set.inter_union_distrib_left`：inter_union_distrib_left (s t u : Set α) :
 s inter (t union u) = s inter t union s inter u
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
lemma image_of_range_union_range_eq_univ {α β γ γ' δ δ' : Type*}
    {h : β → α} {f : γ → β} {f₁ : γ' → α} {f₂ : γ → γ'} {g : δ → β} {g₁ : δ' → α} {g₂ : δ → δ'}
    (hf : h ∘ f = f₁ ∘ f₂) (hg : h ∘ g = g₁ ∘ g₂) (hfg : range f ∪ range g = univ) (s : Set β) :
    h '' s = f₁ '' f₂ '' f ⁻¹' s ∪ g₁ '' g₂ '' g ⁻¹' s := by
  rw [← image_comp, ← image_comp, ← hf, ← hg, image_comp, image_comp, image_preimage_eq_inter_range,
    image_preimage_eq_inter_range, ← image_union, ← inter_union_distrib_left, hfg, inter_univ]

end Range

section Subsingleton

variable {s : Set α} {f : α → β}

/-- The image of a subsingleton is a subsingleton. -/
/-
**Set.Subsingleton.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.Subsingleton → ∀ (f : α → β
), (f '' s).Subsingleton
参数：f : α → β；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The image of a subsingleton is a subsingleton.
-/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f '' s).Subsingleton :=
  fun _ ⟨_, hx, Hx⟩ _ ⟨_, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
/-
**Set.Subsingleton.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : Set β}, s.Subsingleton → 
Function.Injective f → (f ⁻¹' s).Subsingleton
参数：f ⁻¹' s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a subsingleton under an injective map is a subsingleton.
-/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton)
    (hf : Function.Injective f) : (f ⁻¹' s).Subsingleton := fun _ ha _ hb => hf <| hs ha hb

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
/-
**Set.subsingleton_of_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_image (hf : Function.Injective f) (s : Set α) (hs : (f '' 
s).Subsingleton) : s.Subsingleton
参数：hf : Function.Injective f；s : Set α；hs : (f '' s).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.anti`：∀ {α : Type u} {s t : Set α}, t.Subsingleton → s 
⊆ t → s.Subsingleton
· 使用定理 `Set.Subsingleton.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
s : Set β}, s.Subsingleton → Function.Injective f → (f ⁻¹' s).Subsingleton
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
If the image of a set under an injective map is a subsingleton, the set is a sub
singleton.
-/
theorem subsingleton_of_image (hf : Function.Injective f) (s : Set α)
    (hs : (f '' s).Subsingleton) : s.Subsingleton :=
  (hs.preimage hf).anti <| subset_preimage_image _ _

/-- If the preimage of a set under a surjective map is a subsingleton,
the set is a subsingleton. -/
/-
**Set.subsingleton_of_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_of_preimage (hf : Function.Surjective f) (s : Set β) (hs : (f
 ⁻¹' s).Subsingleton) : s.Subsingleton
参数：hf : Function.Surjective f；s : Set β；hs : (f ⁻¹' s).Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If the preimage of a set under a surjective map is a subsingleton,
the set is a subsingleton.
-/
theorem subsingleton_of_preimage (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)
/-
**Set.subsingleton_range** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subsingleton_range {α : Sort*} [Subsingleton α] (f : α -> β) : (range f).S
ubsingleton
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem subsingleton_range {α : Sort*} [Subsingleton α] (f : α → β) : (range f).Subsingleton :=
  forall_mem_range.2 fun x => forall_mem_range.2 fun y => congr_arg f (Subsingleton.elim x y)

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
/-
**Set.Nontrivial.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : Set β}, s.Nontrivial → Fu
nction.Surjective f → (f ⁻¹' s).Nontrivial
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
The preimage of a nontrivial set under a surjective map is nontrivial.
-/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial)
    (hf : Function.Surjective f) : (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/-- The image of a nontrivial set under an injective map is nontrivial. -/
/-
**Set.Nontrivial.image** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, s.Nontrivial → Fu
nction.Injective f → (f '' s).Nontrivial
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂

--- 原说明 ---
The image of a nontrivial set under an injective map is nontrivial.
-/
theorem Nontrivial.image (hs : s.Nontrivial) (hf : Function.Injective f) :
    (f '' s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩
/-
**Set.Nontrivial.image_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Nontrivial`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, s.Nontrivial → Se
t.InjOn f s → (f '' s).Nontrivial
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem Nontrivial.image_of_injOn (hs : s.Nontrivial) (hf : s.InjOn f) :
    (f '' s).Nontrivial := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hs
  exact ⟨f x, mem_image_of_mem _ hx, f y, mem_image_of_mem _ hy, (hxy <| hf hx hy ·)⟩

/-- If the image of a set is nontrivial, the set is nontrivial. -/
/-
**Set.nontrivial_of_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_image (f : α -> β) (s : Set α) (hs : (f '' s).Nontrivial) : 
s.Nontrivial
参数：f : α -> β；s : Set α；hs : (f '' s).Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If the image of a set is nontrivial, the set is nontrivial.
-/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f '' s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

@[simp]
/-
**Set.image_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_nontrivial (hf : f.Injective) : (f '' s).Nontrivial ↔ s.Nontrivial
参数：hf : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_image`：nontrivial_of_image (f : α -> β) (s : Set α) (h
s : (f '' s).Nontrivial) : s.Nontrivial
· 使用定理 `Set.Nontrivial.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α
 → β}, s.Nontrivial → Function.Injective f → (f '' s).Nontrivial
-/
theorem image_nontrivial (hf : f.Injective) : (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h ↦ h.image hf⟩

@[simp]
/-
**Set.InjOn.image_nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.InjOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β}, Set.InjOn f s → (
(f '' s).Nontrivial ↔ s.Nontrivial)
参数：(f '' s).Nontrivial ↔ s.Nontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nontrivial_of_image`：nontrivial_of_image (f : α -> β) (s : Set α) (h
s : (f '' s).Nontrivial) : s.Nontrivial
· 使用定理 `Set.Nontrivial.image_of_injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set 
α} {f : α → β}, s.Nontrivial → Set.InjOn f s → (f '' s).Nontrivial
-/
theorem InjOn.image_nontrivial_iff (hf : s.InjOn f) :
    (f '' s).Nontrivial ↔ s.Nontrivial :=
  ⟨nontrivial_of_image f s, fun h ↦ h.image_of_injOn hf⟩

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
/-
**Set.nontrivial_of_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nontrivial_of_preimage (hf : Function.Injective f) (s : Set β) (hs : (f ⁻¹
' s).Nontrivial) : s.Nontrivial
参数：hf : Function.Injective f；s : Set β；hs : (f ⁻¹' s).Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.mono`：∀ {α : Type u} {s t : Set α}, s.Nontrivial → s ⊆ t 
→ t.Nontrivial
· 使用定理 `Set.Nontrivial.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α
 → β}, s.Nontrivial → Function.Injective f → (f '' s).Nontrivial
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s

--- 原说明 ---
If the preimage of a set under an injective map is nontrivial, the set is nontri
vial.
-/
theorem nontrivial_of_preimage (hf : Function.Injective f) (s : Set β)
    (hs : (f ⁻¹' s).Nontrivial) : s.Nontrivial :=
  (hs.image hf).mono <| image_preimage_subset _ _

end Subsingleton

end Set

namespace Function

variable {α β : Type*} {ι : Sort*} {f : α → β}

open Set

/-
**Function.Surjective.preimage_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Sur
jective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Surjective f → Funct
ion.Injective (Set.preimage f)
参数：Set.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.preimage_eq_preimage`：preimage_eq_preimage {f : β -> α} (hf : Surjec
tive f) : f ⁻¹' s = f ⁻¹' t ↔ s = t
-/
theorem Surjective.preimage_injective (hf : Surjective f) : Injective (preimage f) := fun _ _ =>
  (preimage_eq_preimage hf).1
/-
**Function.Injective.preimage_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → ∀ (s :
 Set α), f ⁻¹' f '' s = s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' f '' s = s :=
  preimage_image_eq s hf
/-
**Function.Injective.preimage_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inj
ective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → Functi
on.Surjective (Set.preimage f)
参数：Set.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_surjective`：preimage_surjective : Surjective (preimage f) ↔
 Injective f
-/
theorem Injective.preimage_surjective (hf : Injective f) : Surjective (preimage f) :=
  Set.preimage_surjective.mpr hf
/-
**Function.Injective.subsingleton_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Function.
Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β},   Function.Injective f → ∀ {s
 : Set α}, (f '' s).Subsingleton ↔ s.Subsingleton
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_of_image`：subsingleton_of_image (hf : Function.Injectiv
e f) (s : Set α) (hs : (f '' s).Subsingleton) : s.Subsingleton
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
-/
theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} :
    (f '' s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩
/-
**Function.Surjective.image_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surject
ive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Surjective f → ∀ (s 
: Set β), f '' f ⁻¹' s = s
参数：s : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
-/
theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f '' f ⁻¹' s = s :=
  image_preimage_eq s hf
/-
**Function.Surjective.image_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surje
ctive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Surjective f → Funct
ion.Surjective (Set.image f)
参数：Set.image f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
-/
theorem Surjective.image_surjective (hf : Surjective f) : Surjective (image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

@[simp]
/-
**Function.Surjective.nonempty_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surj
ective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Surjective f → ∀ {s 
: Set β}, (f ⁻¹' s).Nonempty ↔ s.Nonempty
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} :
    (f ⁻¹' s).Nonempty ↔ s.Nonempty := by rw [← image_nonempty, hf.image_preimage]
/-
**Function.Injective.image_injective** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injecti
ve`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → Functi
on.Injective (Set.image f)
参数：Set.image f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem Injective.image_injective (hf : Injective f) : Injective (image f) := by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]
/-
**Function.Injective.image_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inject
ive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → Strict
Mono (Set.image f)
参数：Set.image f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用引理 `Set.monotone_image`：monotone_image : Monotone (image f)
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
-/
lemma Injective.image_strictMono (inj : Function.Injective f) : StrictMono (image f) :=
  monotone_image.strictMono_of_injective inj.image_injective
/-
**Function.Surjective.preimage_subset_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fu
nction.Surjective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Set β}, Function.Surjec
tive f → (f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t)
参数：f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_subset_preimage_iff`：preimage_subset_preimage_iff {s t : Se
t α} {f : β -> α} (hs : s subseteq range f) : f ⁻¹' s subseteq f ⁻¹' t ↔ s subse
teq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) :
    f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  apply Set.preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ
/-
**Function.Surjective.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`
。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_3} {ι' : Sort u_4} {f : ι → ι'},   Function.S
urjective f → ∀ (g : ι' → α), Set.range (g ∘ f) = Set.range g
参数：g : ι' → α；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
-/
theorem Surjective.range_comp {ι' : Sort*} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    range (g ∘ f) = range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm
/-
**Function.Injective.mem_range_iff_existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Funct
ion.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → ∀ {b :
 β}, b ∈ Set.range f ↔ ∃! a, f a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ExistsUnique.exists`：∀ {α : Sort u_1} {p : α → Prop}, (∃! x, p x) → ∃ x,
 p x
-/
theorem Injective.mem_range_iff_existsUnique (hf : Injective f) {b : β} :
    b ∈ range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun _ ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

alias ⟨Injective.existsUnique_of_mem_range, _⟩ := Injective.mem_range_iff_existsUnique
/-
**Function.Injective.compl_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injectiv
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → ∀ (s :
 Set α), (f '' s)ᶜ = f '' sᶜ ∪ (Set.range f)ᶜ
参数：s : Set α；f '' s；Set.range f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) :
    (f '' s)ᶜ = f '' sᶜ ∪ (range f)ᶜ := by
  grind
/-
**Function.LeftInverse.image_image** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInver
se`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse g f → ∀ (s : Set α), g '' f '' s = s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) :
    g '' f '' s = s := by rw [← image_comp, h.comp_eq_id, image_id]
/-
**Function.LeftInverse.preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Lef
tInverse`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α}, Function.LeftInve
rse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s = s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `Set.preimage_id`：preimage_id {s : Set α} : id ⁻¹' s = s
-/
theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) :
    f ⁻¹' g ⁻¹' s = s := by rw [← preimage_comp, h.comp_eq_id, preimage_id]
/-
**Function.Involutive.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Type u_1} {f : α → α}, Function.Involutive f → Function.Involutive 
(Set.preimage f)
参数：Set.preimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.preimage_preimage`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s
 = s
· 使用定理 `Function.Involutive.rightInverse`：∀ {α : Sort u} {f : α → α}, Function.I
nvolutive f → Function.RightInverse f f
-/
protected theorem Involutive.preimage {f : α → α} (hf : Involutive f) : Involutive (preimage f) :=
  hf.rightInverse.preimage_preimage
/-
**Function.LeftInverse.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {g : β → α},   Function.LeftIn
verse g f → ∀ (s : Set α), f '' s = Set.range f ∩ g ⁻¹' s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `Function.LeftInverse.preimage_preimage`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β} {g : β → α}, Function.LeftInverse g f → ∀ (s : Set α), f ⁻¹' g ⁻¹' s
 = s
-/
theorem LeftInverse.image_eq {f : α → β} {g : β → α} (hfg : LeftInverse g f) (s : Set α) :
    f '' s = range f ∩ g ⁻¹' s := by
  rw [← image_preimage_eq_range_inter, hfg.preimage_preimage]

end Function

namespace EquivLike

variable {ι ι' : Sort*} {E : Type*} [EquivLike E ι ι']

/-
**EquivLike.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `EquivLike`。
形式化陈述：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [inst : EquivLike E ι ι'] 
{α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e) = Set.range f
参数：f : ι' → α；e : E；f ∘ ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
@[simp] lemma range_comp {α : Type*} (f : ι' → α) (e : E) : range (f ∘ e) = range f :=
  (EquivLike.surjective _).range_comp _

end EquivLike

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type*}

/-
**Subtype.coe_image** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_image {p : α -> Prop} {s : Set (Subtype p)} : (↑) '' s = { x | exists 
h : p x, (⟨x, h⟩ : Subtype p) in s }
参数：Subtype p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem coe_image {p : α → Prop} {s : Set (Subtype p)} :
    (↑) '' s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a =>
    ⟨fun ⟨⟨_, ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]
/-
**Subtype.coe_image_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_image_of_subset {s t : Set α} (h : t subseteq s) : (↑) '' { x : ↥s | ↑
x in t } = t
参数：h : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : (↑) '' { x : ↥s | ↑x ∈ t } = t := by
  ext x
  rw [mem_image]
  exact ⟨fun ⟨_, hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩
/-
**Subtype.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：range_coe {s : Set α} : range ((↑) : s -> α) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_image`：coe_image {p : α -> Prop} {s : Set (Subtype p)} : (↑)
 '' s = { x | exists h : p x, (⟨x, h⟩ : Subtype p) in s }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_coe {s : Set α} : range ((↑) : s → α) = s := by
  rw [← image_univ]
  simp [-image_univ, coe_image]

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
/-
**Subtype.range_val** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：range_val {s : Set α} : range (Subtype.val : s -> α) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s

--- 原说明 ---
A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype
 of something.
  In that case, the coercion doesn't fire anymore.
-/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : Set α` the function `(↑) : s → α`, then the inferred implicit arguments of `(↑)` are
  `↑α (fun x ↦ x ∈ s)`. -/
@[simp]
/-
**Subtype.range_coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：range_coe_subtype {p : α -> Prop} : range ((↑) : Subtype p -> α) = { x | p
 x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s

--- 原说明 ---
We make this the simp lemma instead of `range_coe`. The reason is that if we wri
te
  for `s : Set α` the function `(↑) : s → α`, then the inferred implicit argumen
ts of `(↑)` are
  `↑α (fun x ↦ x ∈ s)`.
-/
theorem range_coe_subtype {p : α → Prop} : range ((↑) : Subtype p → α) = { x | p x } :=
  range_coe

@[simp]
/-
**Subtype.coe_preimage_self** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_preimage_self (s : Set α) : ((↑) : s -> α) ⁻¹' s = univ
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem coe_preimage_self (s : Set α) : ((↑) : s → α) ⁻¹' s = univ := by
  rw [← preimage_range, range_coe]
/-
**Subtype.range_val_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：range_val_subtype {p : α -> Prop} : range (Subtype.val : Subtype p -> α) =
 { x | p x }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe
/-
**Subtype.coe_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_image_subset (s : Set α) (t : Set s) : ((↑) : s -> α) '' t subseteq s
参数：s : Set α；t : Set s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_image_subset (s : Set α) (t : Set s) : ((↑) : s → α) '' t ⊆ s :=
  fun x ⟨y, _, yvaleq⟩ => by
  rw [← yvaleq]; exact y.property
/-
**Subtype.coe_image_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：coe_image_univ (s : Set α) : ((↑) : s -> α) '' Set.univ = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem coe_image_univ (s : Set α) : ((↑) : s → α) '' Set.univ = s :=
  image_univ.trans range_coe

@[simp]
/-
**Subtype.image_preimage_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_preimage_coe (s t : Set α) : ((↑) : s -> α) '' ((↑) : s -> α) ⁻¹' t 
= s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_preimage_eq_range_inter`：image_preimage_eq_range_inter {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = range f inter t
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem image_preimage_coe (s t : Set α) : ((↑) : s → α) '' ((↑) : s → α) ⁻¹' t = s ∩ t :=
  image_preimage_eq_range_inter.trans <| congr_arg (· ∩ t) range_coe
/-
**Subtype.image_preimage_val** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：image_preimage_val (s t : Set α) : (Subtype.val : s -> α) '' Subtype.val ⁻
¹' t = s inter t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
-/
theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) '' Subtype.val ⁻¹' t = s ∩ t :=
  image_preimage_coe s t
/-
**Subtype.preimage_coe_eq_preimage_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_eq_preimage_coe_iff {s t u : Set α} : ((↑) : s -> α) ⁻¹' t = 
((↑) : s -> α) ⁻¹' u ↔ s inter t = s inter u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} :
    ((↑) : s → α) ⁻¹' t = ((↑) : s → α) ⁻¹' u ↔ s ∩ t = s ∩ u := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]
/-
**Subtype.preimage_coe_self_inter** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_self_inter (s t : Set α) : ((↑) : s -> α) ⁻¹' (s inter t) = (
(↑) : s -> α) ⁻¹' t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.preimage_coe_eq_preimage_coe_iff`：preimage_coe_eq_preimage_coe_i
ff {s t u : Set α} : ((↑) : s -> α) ⁻¹' t = ((↑) : s -> α) ⁻¹' u ↔ s inter t = s
 inter u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem preimage_coe_self_inter (s t : Set α) :
    ((↑) : s → α) ⁻¹' (s ∩ t) = ((↑) : s → α) ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, ← inter_assoc, inter_self]

-- Not `@[simp]` since `simp` can prove this.
/-
**Subtype.preimage_coe_inter_self** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_inter_self (s t : Set α) : ((↑) : s -> α) ⁻¹' (t inter s) = (
(↑) : s -> α) ⁻¹' t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Subtype.preimage_coe_self_inter`：preimage_coe_self_inter (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t
-/
theorem preimage_coe_inter_self (s t : Set α) :
    ((↑) : s → α) ⁻¹' (t ∩ s) = ((↑) : s → α) ⁻¹' t := by
  rw [inter_comm, preimage_coe_self_inter]
/-
**Subtype.preimage_val_eq_preimage_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_val_eq_preimage_val_iff (s t u : Set α) : (Subtype.val : s -> α) 
⁻¹' t = Subtype.val ⁻¹' u ↔ s inter t = s inter u
参数：s t u : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.preimage_coe_eq_preimage_coe_iff`：preimage_coe_eq_preimage_coe_i
ff {s t u : Set α} : ((↑) : s -> α) ⁻¹' t = ((↑) : s -> α) ⁻¹' u ↔ s inter t = s
 inter u
-/
theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ s ∩ t = s ∩ u :=
  preimage_coe_eq_preimage_coe_iff
/-
**Subtype.preimage_val_subset_preimage_val_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subtyp
e`。
形式化陈述：preimage_val_subset_preimage_val_iff (s t u : Set α) : (Subtype.val ⁻¹' t 
: Set s) subseteq Subtype.val ⁻¹' u ↔ s inter t subseteq s inter u
参数：s t u : Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma preimage_val_subset_preimage_val_iff (s t u : Set α) :
    (Subtype.val ⁻¹' t : Set s) ⊆ Subtype.val ⁻¹' u ↔ s ∩ t ⊆ s ∩ u := by
  constructor
  · rw [← image_preimage_coe, ← image_preimage_coe]
    exact image_mono
  · intro h x a
    exact (h ⟨x.2, a⟩).2
/-
**Subtype.exists_set_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：exists_set_subtype {t : Set α} (p : Set α -> Prop) : (exists s : Set t, p 
(((↑) : t -> α) '' s)) ↔ exists s : Set α, s subseteq t ∧ p s
参数：p : Set α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.exists_subset_range_and_iff`：exists_subset_range_and_iff {f : α -> β
} {p : Set β -> Prop} : (exists s, s subseteq range f ∧ p s) ↔ exists s, p (f ''
 s)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exists_set_subtype {t : Set α} (p : Set α → Prop) :
    (∃ s : Set t, p (((↑) : t → α) '' s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s := by
  rw [← exists_subset_range_and_iff, range_coe]
/-
**Subtype.forall_set_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：forall_set_subtype {t : Set α} (p : Set α -> Prop) : (forall s : Set t, p 
(((↑) : t -> α) '' s)) ↔ forall s : Set α, s subseteq t -> p s
参数：p : Set α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.forall_subset_range_iff`：forall_subset_range_iff {f : α -> β} {p : S
et β -> Prop} : (forall s, s subseteq range f -> p s) ↔ forall s, p (f '' s)
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_set_subtype {t : Set α} (p : Set α → Prop) :
    (∀ s : Set t, p (((↑) : t → α) '' s)) ↔ ∀ s : Set α, s ⊆ t → p s := by
  rw [← forall_subset_range_iff, range_coe]
/-
**Subtype.preimage_coe_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_nonempty {s t : Set α} : (((↑) : s -> α) ⁻¹' t).Nonempty ↔ (s
 inter t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_coe_nonempty {s t : Set α} :
    (((↑) : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty := by
  rw [← image_preimage_coe, image_nonempty]
/-
**Subtype.preimage_coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_eq_empty {s t : Set α} : ((↑) : s -> α) ⁻¹' t = ∅ ↔ s inter t
 = ∅
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
theorem preimage_coe_eq_empty {s t : Set α} : ((↑) : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

-- Not `@[simp]` since `simp` can prove this.
/-
**Subtype.preimage_coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_compl (s : Set α) : ((↑) : s -> α) ⁻¹' sᶜ = ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.preimage_coe_eq_empty`：preimage_coe_eq_empty {s t : Set α} : ((↑
) : s -> α) ⁻¹' t = ∅ ↔ s inter t = ∅
· 使用定理 `Set.inter_compl_self`：inter_compl_self (s : Set α) : s inter sᶜ = ∅
-/
theorem preimage_coe_compl (s : Set α) : ((↑) : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]
/-
**Subtype.preimage_coe_compl'** 是 Mathlib 中的一个定理，位于命名空间 `Subtype`。
形式化陈述：preimage_coe_compl' (s : Set α) : (fun x : (sᶜ : Set α) => (x : α)) ⁻¹' s 
= ∅
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.preimage_coe_eq_empty`：preimage_coe_eq_empty {s t : Set α} : ((↑
) : s -> α) ⁻¹' t = ∅ ↔ s inter t = ∅
· 使用定理 `Set.compl_inter_self`：compl_inter_self (s : Set α) : sᶜ inter s = ∅
-/
theorem preimage_coe_compl' (s : Set α) :
    (fun x : (sᶜ : Set α) => (x : α)) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)

end Subtype

/-! ### Images and preimages on `Option` -/


namespace Option

/-
**Option.injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：injective_iff {α β} {f : Option α -> β} : Injective f ↔ Injective (f ∘ som
e) ∧ f none ∉ range (f ∘ some)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Option.some_ne_none`：∀ {α : Type u_1} (x : α), some x ≠ none
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine
    ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne <| Option.some_ne_none _⟩, ?_⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]
/-
**Option.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：range_eq {α β} (f : Option α -> β) : range f = insert (f none) (range (f ∘
 some))
参数：f : Option α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Option.exists`：∀ {α : Type u_1} {p : Option α → Prop}, (∃ x, p x) ↔ p no
ne ∨ ∃ x, p (some x)
· 使用定理 `Iff.or`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq {α β} (f : Option α → β) : range f = insert (f none) (range (f ∘ some)) :=
  Set.ext fun _ => Option.exists.trans <| eq_comm.or Iff.rfl

/-- The range of `Option.elim b f` is `{b} ∪ range f`. -/
/-
**Option.range_elim** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：range_elim {α β} (b : β) (f : α -> β) : range (fun o : Option α => o.elim 
b f) = insert b (range f)
参数：b : β；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.range_eq`：range_eq {α β} (f : Option α -> β) : range f = insert (
f none) (range (f ∘ some))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The range of `Option.elim b f` is `{b} ∪ range f`.
-/
theorem range_elim {α β} (b : β) (f : α → β) :
    range (fun o : Option α => o.elim b f) = insert b (range f) := by
  rw [range_eq]
  simp [Function.comp_def]

/-- The image of `range some` under `Option.elim b f` equals `range f`. -/
/-
**Option.image_elim_range_some_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：image_elim_range_some_eq_range {α β} (f : α -> β) (b : β) : (fun o : Optio
n α => o.elim b f) '' range some = range f
参数：f : α -> β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of `range some` under `Option.elim b f` equals `range f`.
-/
theorem image_elim_range_some_eq_range {α β} (f : α → β) (b : β) :
    (fun o : Option α => o.elim b f) '' range some = range f := by
  rw [← range_comp']
  simp

end Option

namespace Set

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
/-
**Set.image_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_surjective : Surjective (image f) ↔ Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.image_surjective`：∀ {α : Type u_1} {β : Type u_2} {f
 : α → β}, Function.Surjective f → Function.Surjective (Set.image f)
-/
theorem image_surjective : Surjective (image f) ↔ Surjective f := by
  refine ⟨fun h y => ?_, Surjective.image_surjective⟩
  rcases h {y} with ⟨s, hs⟩
  have := mem_singleton y; rw [← hs] at this; rcases this with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

@[simp]
/-
**Set.image_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_injective : Injective (image f) ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
-/
theorem image_injective : Injective (image f) ↔ Injective f := by
  refine ⟨fun h x x' hx => ?_, Injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]; apply h
  rw [image_singleton, image_singleton, hx]
/-
**Set.preimage_eq_iff_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_iff_eq_image {f : α -> β} (hf : Bijective f) {s t} : f ⁻¹' s =
 t ↔ s = f '' t
参数：hf : Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} :
    f ⁻¹' s = t ↔ s = f '' t := by rw [← image_eq_image hf.1, hf.2.image_preimage]
/-
**Set.eq_preimage_iff_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_preimage_iff_image_eq {f : α -> β} (hf : Bijective f) {s t} : s = f ⁻¹'
 t ↔ f '' s = t
参数：hf : Bijective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_image`：image_eq_image {f : α -> β} (hf : Injective f) : f '
' s = f '' t ↔ s = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Surjective f → ∀ (s : Set β), f '' f ⁻¹' s = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} :
    s = f ⁻¹' t ↔ f '' s = t := by rw [← image_eq_image hf.1, hf.2.image_preimage]

end ImagePreimage

end Set

/-! ### Disjoint lemmas for image and preimage -/

section Disjoint
variable {α β γ : Type*} {f : α → β} {s t : Set α}

/-
**Disjoint.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Disjoint s t) : Disjoint
 (f ⁻¹' s) (f ⁻¹' t)
参数：f : α -> β；h : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem Disjoint.preimage (f : α → β) {s t : Set β} (h : Disjoint s t) :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) :=
  disjoint_iff_inf_le.mpr fun _ hx => h.le_bot hx
/-
**Codisjoint.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Codisjoint.preimage (f : α -> β) {s t : Set β} (h : Codisjoint s t) : Codi
sjoint (f ⁻¹' s) (f ⁻¹' t)
参数：f : α -> β；h : Codisjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Codisjoint.preimage (f : α → β) {s t : Set β} (h : Codisjoint s t) :
    Codisjoint (f ⁻¹' s) (f ⁻¹' t) := by
  simp only [codisjoint_iff_le_sup, Set.sup_eq_union, top_le_iff, ← Set.preimage_union] at h ⊢
  rw [h]; rfl
/-
**IsCompl.preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompl.preimage (f : α -> β) {s t : Set β} (h : IsCompl s t) : IsCompl (f
 ⁻¹' s) (f ⁻¹' t)
参数：f : α -> β；h : IsCompl s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用引理 `Codisjoint.preimage`：Codisjoint.preimage (f : α -> β) {s t : Set β} (h :
 Codisjoint s t) : Codisjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
lemma IsCompl.preimage (f : α → β) {s t : Set β} (h : IsCompl s t) :
    IsCompl (f ⁻¹' s) (f ⁻¹' t) :=
  ⟨h.1.preimage f, h.2.preimage f⟩

namespace Set

/-
**Set.disjoint_image_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_image {f : β -> α} {g : γ -> α} {s : Set β} {t : Set γ} (h 
: forall b in s, forall c in t, f b != g c) : Disjoint (f '' s) (g '' t)
参数：h : forall b in s, forall c in t, f b != g c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
-/
theorem disjoint_image_image {f : β → α} {g : γ → α} {s : Set β} {t : Set γ}
    (h : ∀ b ∈ s, ∀ c ∈ t, f b ≠ g c) : Disjoint (f '' s) (g '' t) :=
  disjoint_iff_inf_le.mpr <| by rintro a ⟨⟨b, hb, eq⟩, c, hc, rfl⟩; exact h b hb c hc eq
/-
**Set.disjoint_image_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_of_injective (hf : Injective f) {s t : Set α} (hd : Disjoin
t s t) : Disjoint (f '' s) (f '' t)
参数：hf : Injective f；hd : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.disjoint_image_image`：disjoint_image_image {f : β -> α} {g : γ -> α}
 {s : Set β} {t : Set γ} (h : forall b in s, forall c in t, f b != g c) : Disjoi
nt (f '' s) (g…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_image_of_injective (hf : Injective f) {s t : Set α} (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) :=
  disjoint_image_image fun _ hx _ hy => hf.ne fun H => Set.disjoint_iff.1 hd ⟨hx, H.symm ▸ hy⟩
/-
**Set._root_.Disjoint.of_image** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.of_image (h : Disjoint (f '' s) (f '' t)) : Disjoint s t :=
  disjoint_iff_inf_le.mpr fun _ hx =>
    disjoint_left.1 h (mem_image_of_mem _ hx.1) (mem_image_of_mem _ hx.2)

@[simp]
/-
**Set.disjoint_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjo
int s t
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s t : Se
t α}, Disjoint (f '' s) (f '' t) → Disjoint s t
· 使用定理 `Set.disjoint_image_of_injective`：disjoint_image_of_injective (hf : Injec
tive f) {s t : Set α} (hd : Disjoint s t) : Disjoint (f '' s) (f '' t)
-/
theorem disjoint_image_iff (hf : Injective f) : Disjoint (f '' s) (f '' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_image, disjoint_image_of_injective hf⟩
/-
**Set._root_.Disjoint.of_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.of_preimage (hf : Surjective f) {s t : Set β}
    (h : Disjoint (f ⁻¹' s) (f ⁻¹' t)) : Disjoint s t := by
  rw [disjoint_iff_inter_eq_empty, ← image_preimage_eq (_ ∩ _) hf, preimage_inter, h.inter_eq,
    image_empty]

@[simp]
/-
**Set.disjoint_preimage_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_preimage_iff (hf : Surjective f) {s t : Set β} : Disjoint (f ⁻¹' 
s) (f ⁻¹' t) ↔ Disjoint s t
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.of_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β},   Fun
ction.Surjective f → ∀ {s t : Set β}, Disjoint (f ⁻¹' s) (f ⁻¹' t) → Disjoint s 
t
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
-/
theorem disjoint_preimage_iff (hf : Surjective f) {s t : Set β} :
    Disjoint (f ⁻¹' s) (f ⁻¹' t) ↔ Disjoint s t :=
  ⟨Disjoint.of_preimage hf, Disjoint.preimage _⟩
/-
**Set.preimage_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_empty {s : Set β} (h : Disjoint s (range f)) : f ⁻¹' s = ∅
参数：h : Disjoint s (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_range`：preimage_range (f : α -> β) : f ⁻¹' range f = univ
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
-/
theorem preimage_eq_empty {s : Set β} (h : Disjoint s (range f)) :
    f ⁻¹' s = ∅ := by
  simpa using h.preimage f
/-
**Set.preimage_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_eq_empty`：preimage_eq_empty {s : Set β} (h : Disjoint s (ra
nge f)) : f ⁻¹' s = ∅
-/
theorem preimage_eq_empty_iff {s : Set β} : f ⁻¹' s = ∅ ↔ Disjoint s (range f) :=
  ⟨fun h => by
    simp only [eq_empty_iff_forall_notMem, mem_preimage] at h ⊢
    grind,
  preimage_eq_empty⟩

@[simp]
/-
**Set.disjoint_image_inl_image_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_inl_image_inr {u : Set α} {v : Set β} : Disjoint (Sum.inl '
' u) (Sum.inr '' v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.disjoint_image_image`：disjoint_image_image {f : β -> α} {g : γ -> α}
 {s : Set β} {t : Set γ} (h : forall b in s, forall c in t, f b != g c) : Disjoi
nt (f '' s) (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem disjoint_image_inl_image_inr {u : Set α} {v : Set β} :
    Disjoint (Sum.inl '' u) (Sum.inr '' v) :=
  disjoint_image_image <| by simp

@[simp]
/-
**Set.disjoint_range_inl_image_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_range_inl_image_inr {v : Set β} : Disjoint (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_range_inl_image_inr {v : Set β} :
    Disjoint (α := Set (α ⊕ β)) (range Sum.inl) (Sum.inr '' v) := by
  grind

@[simp]
/-
**Set.disjoint_image_inl_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_image_inl_range_inr {u : Set α} : Disjoint (α
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_image_inl_range_inr {u : Set α} :
    Disjoint (α := Set (α ⊕ β)) (Sum.inl '' u) (range Sum.inr) := by
  grind

end Set

end Disjoint

section Sigma

variable {α : Type*} {β : α → Type*} {i j : α} {s : Set (β i)}

/-
**sigma_mk_preimage_image'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigma_mk_preimage_image' (h : i != j) : Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅
参数：h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sigma_mk_preimage_image' (h : i ≠ j) : Sigma.mk j ⁻¹' Sigma.mk i '' s = ∅ := by
  simp [image, h]
/-
**sigma_mk_preimage_image_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' Sigma.mk i '' s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma sigma_mk_preimage_image_eq_self : Sigma.mk i ⁻¹' Sigma.mk i '' s = s := by
  simp [image]

end Sigma

