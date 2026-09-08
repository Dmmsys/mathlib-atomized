/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutations of `Option α`
-/

@[expose] public section


open Equiv

@[simp]
/-
**Equiv.optionCongr_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.optionCongr_one {α : Type*} : (1 : Perm α).optionCongr = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.optionCongr_refl`：optionCongr_refl : optionCongr (Equiv.refl α) = 
Equiv.refl _
-/
theorem Equiv.optionCongr_one {α : Type*} : (1 : Perm α).optionCongr = 1 :=
  Equiv.optionCongr_refl

@[simp]
/-
**Equiv.optionCongr_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.optionCongr_swap {α : Type*} [DecidableEq α] (x y : α) : optionCongr
 (swap x y) = swap (some x) (some y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem Equiv.optionCongr_swap {α : Type*} [DecidableEq α] (x y : α) :
    optionCongr (swap x y) = swap (some x) (some y) := by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    · simp only [hx, optionCongr_apply, Option.map_some, swap_apply_left,
             Option.some.injEq]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]

@[simp]
/-
**Equiv.optionCongr_sign** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.optionCongr_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α
) : Perm.sign e.optionCongr = Perm.sign e
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.swap_induction_on`：swap_induction_on [Finite α] {motive : Per
m α -> Prop} (f : Perm α) (one : motive 1) (swap_mul : forall f x y, x != y -> m
otive f -> motive …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.optionCongr_refl`：optionCongr_refl : optionCongr (Equiv.refl α) = 
Equiv.refl _
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.optionCongr_trans`：optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : o
ptionCongr (e₁.trans e₂) = (optionCongr e₁).trans (optionCongr e₂)
· 使用定理 `Equiv.optionCongr_swap`：Equiv.optionCongr_swap {α : Type*} [DecidableEq 
α] (x y : α) : optionCongr (swap x y) = swap (some x) (some y)
· 使用定理 `Equiv.Perm.sign_trans`：sign_trans (f g : Perm α) : sign (f.trans g) = si
gn g * sign f
· 使用定理 `Equiv.Perm.sign_swap'`：sign_swap' {x y : α} : sign (swap x y) = if x = y
 then 1 else -1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem Equiv.optionCongr_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign e.optionCongr = Perm.sign e := by
  induction e using Perm.swap_induction_on with
  | one => simp [Perm.one_def]
  | swap_mul f x y hne h =>
    simp [h, hne, Perm.mul_def]

@[simp]
/-
**map_equiv_removeNone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_equiv_removeNone {α : Type*} [DecidableEq α] (σ : Perm (Option α)) : (
removeNone σ).optionCongr = swap none (σ none) * σ
参数：σ : Perm (Option α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.removeNone_none`：removeNone_none {x : α} (h : e (some x) = none) :
 some (removeNone e x) = e none
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.removeNone_some`：removeNone_some {x : α} (h : exists x', e (some x
) = some x') : some (removeNone e x) = e (some x)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
-/
theorem map_equiv_removeNone {α : Type*} [DecidableEq α] (σ : Perm (Option α)) :
    (removeNone σ).optionCongr = swap none (σ none) * σ := by
  ext1 x
  have : Option.map (⇑(removeNone σ)) x = (swap none (σ none)) (σ x) := by
    obtain - | x := x
    · simp
    · cases h : σ (some _)
      · simp [removeNone_none _ h]
      · have hn : σ (some x) ≠ none := by simp [h]
        have hσn : σ (some x) ≠ σ none := σ.injective.ne (by simp)
        simp [removeNone_some _ ⟨_, h⟩, ← h, swap_apply_of_ne_of_ne hn hσn]
  simpa using this

/-- Permutations of `Option α` are equivalent to fixing an
`Option α` and permuting the remaining with a `Perm α`.
The fixed `Option α` is swapped with `none`. -/
@[simps]
/-
**Equiv.Perm.decomposeOption** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeOption {α : Type*} [DecidableEq α] : Perm (Option α) ≃
 Option α × Perm α where toFun σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Permutations of `Option α` are equivalent to fixing an
`Option α` and permuting the remaining with a `Perm α`.
The fixed `Option α` is swapped with `none`.
-/
def Equiv.Perm.decomposeOption {α : Type*} [DecidableEq α] :
    Perm (Option α) ≃ Option α × Perm α where
  toFun σ := (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ => by
    have : removeNone (swap none x * σ.optionCongr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [this]
/-
**Equiv.Perm.decomposeOption_symm_of_none_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeOption_symm_of_none_apply {α : Type*} [DecidableEq α] 
(e : Perm α) (i : Option α) : Equiv.Perm.decomposeOption.symm (none, e) i = i.ma
p e
参数：e : Perm α；i : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.optionCongr_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) (a 
: Option α), e.optionCongr a = Option.map (⇑e) a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.Perm.decomposeOption_symm_of_none_apply {α : Type*} [DecidableEq α] (e : Perm α)
    (i : Option α) : Equiv.Perm.decomposeOption.symm (none, e) i = i.map e := by simp
/-
**Equiv.Perm.decomposeOption_symm_sign** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.decomposeOption_symm_sign {α : Type*} [DecidableEq α] [Fintype 
α] (e : Perm α) : Perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = Perm.s
ign e
参数：e : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.Perm.decomposeOption_symm_apply`：∀ {α : Type u_1} [inst : Decidabl
eEq α] (i : Option α × Equiv.Perm α),   Equiv.Perm.decomposeOption.symm i = Equi
v.swap none i.1 * Equiv.opt…
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
· 使用定理 `Equiv.Perm.sign_mul`：sign_mul (f g : Perm α) : sign (f * g) = sign f * s
ign g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.sign_refl`：sign_refl : sign (Equiv.refl α) = 1
· 使用定理 `Equiv.optionCongr_sign`：Equiv.optionCongr_sign {α : Type*} [DecidableEq 
α] [Fintype α] (e : Perm α) : Perm.sign e.optionCongr = Perm.sign e
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Equiv.Perm.decomposeOption_symm_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = Perm.sign e := by simp

/-- The set of all permutations of `Option α` can be constructed by augmenting the set of
permutations of `α` by each element of `Option α` in turn. -/
/-
**Finset.univ_perm_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.univ_perm_option {α : Type*} [DecidableEq α] [Fintype α] : @Finset.
univ (Perm <| Option α) _ = (Finset.univ : Finset <| Option α × Perm α).map Equi
v.Perm.decomposeOption.symm.toEmbedding
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.univ_map_equiv_to_embedding`：univ_map_equiv_to_embedding {α β : T
ype*} [Fintype α] [Fintype β] (e : α ≃ β) : univ.map e.toEmbedding = univ

--- 原说明 ---
The set of all permutations of `Option α` can be constructed by augmenting the s
et of
permutations of `α` by each element of `Option α` in turn.
-/
theorem Finset.univ_perm_option {α : Type*} [DecidableEq α] [Fintype α] :
    @Finset.univ (Perm <| Option α) _ =
      (Finset.univ : Finset <| Option α × Perm α).map Equiv.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm
