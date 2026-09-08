/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Order

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.
-/

@[expose] public section

open Function

variable {α : Type*}

namespace DFinsupp

/-- Non-dependent special case of `DFinsupp.addZeroClass` to help typeclass search. -/
/-
**DFinsupp.addZeroClass'** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-dependent special case of `DFinsupp.addZeroClass` to help typeclass search.
-/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @DFinsupp.addZeroClass α (fun _ ↦ β) _

variable [DecidableEq α]

/-- A DFinsupp version of `Finsupp.toMultiset`. -/
/-
**DFinsupp.toMultiset** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset : (Π₀ _ : α, Nat) ->+ Multiset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A DFinsupp version of `Finsupp.toMultiset`.
-/
def toMultiset : (Π₀ _ : α, ℕ) →+ Multiset α :=
  DFinsupp.sumAddHom fun a : α ↦ Multiset.replicateAddMonoidHom a

@[simp]
/-
**DFinsupp.toMultiset_single** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_single (a : α) (n : Nat) : toMultiset (DFinsupp.single a n) = M
ultiset.replicate n a
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
-/
theorem toMultiset_single (a : α) (n : ℕ) :
    toMultiset (DFinsupp.single a n) = Multiset.replicate n a :=
  DFinsupp.sumAddHom_single _ _ _

end DFinsupp

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- A DFinsupp version of `Multiset.toFinsupp`. -/
/-
**Multiset.toDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp : Multiset α ->+ Π₀ _ : α, Nat where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A DFinsupp version of `Multiset.toFinsupp`.
-/
def toDFinsupp : Multiset α →+ Π₀ _ : α, ℕ where
  toFun s :=
    { toFun := fun n ↦ s.count n
      support' := Trunc.mk ⟨s, fun i ↦ (em (i ∈ s)).imp_right Multiset.count_eq_zero_of_notMem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ ↦ Multiset.count_add _ _ _

@[simp]
/-
**Multiset.toDFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_apply (s : Multiset α) (a : α) : Multiset.toDFinsupp s a = s.co
unt a
参数：s : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDFinsupp_apply (s : Multiset α) (a : α) : Multiset.toDFinsupp s a = s.count a :=
  rfl

@[simp]
/-
**Multiset.toDFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Multiset.count_ne_zero`：count_ne_zero {a : α} : count a s != 0 ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
-/
theorem toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset :=
  Finset.filter_true_of_mem fun _ hx ↦ count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Multiset.toDFinsupp_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_replicate (a : α) (n : Nat) : toDFinsupp (Multiset.replicate n 
a) = DFinsupp.single a n
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDFinsupp_replicate (a : α) (n : ℕ) :
    toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n := by
  ext i
  dsimp [toDFinsupp]
  simp [count_replicate]

@[simp]
/-
**Multiset.toDFinsupp_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.replicate_one`：replicate_one (a : α) : replicate 1 a = {a}
· 使用定理 `Multiset.toDFinsupp_replicate`：toDFinsupp_replicate (a : α) (n : Nat) : 
toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n
-/
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one, toDFinsupp_replicate]

/-- `Multiset.toDFinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/-
**Multiset.equivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：equivDFinsupp : Multiset α ≃+ Π₀ _ : α, Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiset.toDFinsupp` as an `AddEquiv`.
-/
def equivDFinsupp : Multiset α ≃+ Π₀ _ : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)

@[simp]
/-
**Multiset.toDFinsupp_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toD
Finsupp s) = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
-/
theorem toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toDFinsupp s) = s :=
  equivDFinsupp.symm_apply_apply s
/-
**Multiset.toDFinsupp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_injective : Injective (toDFinsupp : Multiset α -> Π₀ _a, Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
-/
theorem toDFinsupp_injective : Injective (toDFinsupp : Multiset α → Π₀ _a, ℕ) :=
  equivDFinsupp.injective

@[simp]
/-
**Multiset.toDFinsupp_inj** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Multiset.toDFinsupp_injective`：toDFinsupp_injective : Injective (toDFins
upp : Multiset α -> Π₀ _a, Nat)
-/
theorem toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t :=
  toDFinsupp_injective.eq_iff

@[simp]
/-
**Multiset.toDFinsupp_le_toDFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_le_toDFinsupp : toDFinsupp s <= toDFinsupp t ↔ s <= t
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
theorem toDFinsupp_le_toDFinsupp : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]

@[simp]
/-
**Multiset.toDFinsupp_lt_toDFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Multiset.toDFinsupp_le_toDFinsupp`：toDFinsupp_le_toDFinsupp : toDFinsupp
 s <= toDFinsupp t ↔ s <= t
-/
theorem toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp

@[simp]
/-
**Multiset.toDFinsupp_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s inter t) = toDFinsupp 
s ⊓ toDFinsupp t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s ∩ t) = toDFinsupp s ⊓ toDFinsupp t := by
  ext i; simp

@[simp]
/-
**Multiset.toDFinsupp_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toDFinsupp_union (s t : Multiset α) : toDFinsupp (s union t) = toDFinsupp 
s ⊔ toDFinsupp t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDFinsupp_union (s t : Multiset α) : toDFinsupp (s ∪ t) = toDFinsupp s ⊔ toDFinsupp t := by
  ext i; simp

end Multiset


namespace DFinsupp

variable [DecidableEq α] {f g : Π₀ _a : α, ℕ}

@[simp]
/-
**DFinsupp.toMultiset_toDFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_toDFinsupp (f : Π₀ _ : α, Nat) : Multiset.toDFinsupp (DFinsupp.
toMultiset f) = f
参数：f : Π₀ _ : α, Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
-/
theorem toMultiset_toDFinsupp (f : Π₀ _ : α, ℕ) :
    Multiset.toDFinsupp (DFinsupp.toMultiset f) = f :=
  Multiset.equivDFinsupp.apply_symm_apply f
/-
**DFinsupp.toMultiset_injective** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_injective : Injective (toMultiset : (Π₀ _a, Nat) -> Multiset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
-/
theorem toMultiset_injective : Injective (toMultiset : (Π₀ _a, ℕ) → Multiset α) :=
  Multiset.equivDFinsupp.symm.injective

@[simp]
/-
**DFinsupp.toMultiset_inj** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_inj : toMultiset f = toMultiset g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFinsupp.toMultiset_injective`：toMultiset_injective : Injective (toMulti
set : (Π₀ _a, Nat) -> Multiset α)
-/
theorem toMultiset_inj : toMultiset f = toMultiset g ↔ f = g :=
  toMultiset_injective.eq_iff

@[simp]
/-
**DFinsupp.toMultiset_le_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_le_toMultiset : toMultiset f <= toMultiset g ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.toMultiset_toDFinsupp`：toMultiset_toDFinsupp (f : Π₀ _ : α, Nat
) : Multiset.toDFinsupp (DFinsupp.toMultiset f) = f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toMultiset_le_toMultiset : toMultiset f ≤ toMultiset g ↔ f ≤ g := by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]

@[simp]
/-
**DFinsupp.toMultiset_lt_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.toMultiset_toDFinsupp`：toMultiset_toDFinsupp (f : Π₀ _ : α, Nat
) : Multiset.toDFinsupp (DFinsupp.toMultiset f) = f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g := by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]

variable (f g)

@[simp]
/-
**DFinsupp.toMultiset_inf** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_inf : toMultiset (f ⊓ g) = toMultiset f inter toMultiset g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toDFinsupp_injective`：toDFinsupp_injective : Injective (toDFins
upp : Multiset α -> Π₀ _a, Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.toMultiset_toDFinsupp`：toMultiset_toDFinsupp (f : Π₀ _ : α, Nat
) : Multiset.toDFinsupp (DFinsupp.toMultiset f) = f
· 使用定理 `Multiset.toDFinsupp_inter`：toDFinsupp_inter (s t : Multiset α) : toDFins
upp (s inter t) = toDFinsupp s ⊓ toDFinsupp t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMultiset_inf : toMultiset (f ⊓ g) = toMultiset f ∩ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp

@[simp]
/-
**DFinsupp.toMultiset_sup** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toMultiset_sup : toMultiset (f ⊔ g) = toMultiset f union toMultiset g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.toDFinsupp_injective`：toDFinsupp_injective : Injective (toDFins
upp : Multiset α -> Π₀ _a, Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.toMultiset_toDFinsupp`：toMultiset_toDFinsupp (f : Π₀ _ : α, Nat
) : Multiset.toDFinsupp (DFinsupp.toMultiset f) = f
· 使用定理 `Multiset.toDFinsupp_union`：toDFinsupp_union (s t : Multiset α) : toDFins
upp (s union t) = toDFinsupp s ⊔ toDFinsupp t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMultiset_sup : toMultiset (f ⊔ g) = toMultiset f ∪ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp

end DFinsupp

