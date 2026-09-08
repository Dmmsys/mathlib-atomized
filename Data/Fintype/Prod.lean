/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for the product of two fintypes.

-/

public section


open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/-
**Set.toFinset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s 
×ˢ t)] : (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset
参数：s : Set α；t : Set β；s ×ˢ t。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by
  ext
  simp
/-
**Set.toFinset_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_offDiag {s : Set α} [Fintype s] [Fintype s.offDiag] : s.offDiag.t
oFinset = s.toFinset.offDiag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem toFinset_offDiag {s : Set α} [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
  Finset.ext <| by simp

@[deprecated (since := "2026-01-09")]
alias toFinset_off_diag := toFinset_offDiag

end Set

/-
**instFintypeProd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instFintypeProd (α β : Type*) [Fintype α] [Fintype β] : Fintype (α × β)
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintypeProd (α β : Type*) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

namespace Finset
variable [Fintype α] [Fintype β] {s : Finset α} {t : Finset β}

/-
**Finset.univ_product_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β], F
inset.univ ×ˢ Finset.univ = Finset.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma univ_product_univ : univ ×ˢ univ = (univ : Finset (α × β)) := rfl
/-
**Finset.product_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] {s
 : Finset α} {t : Finset β} [Nonempty α]   [Nonempty β], s ×ˢ t = Finset.univ ↔ 
s = Finset.univ ∧ t = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma product_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

end Finset

@[simp]
/-
**Fintype.card_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] : Fintype.card (α 
× β) = Fintype.card α * Fintype.card β
参数：α β : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
-/
theorem Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _

/-- The number of strictly ordered pairs `(a, b)` in `α` is `(Fintype.card α).choose 2`. -/
/-
**Fintype.card_product_filter_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fintype.card_product_filter_lt [Fintype α] [LinearOrder α] : #{x : α × α |
 x.1 < x.2} = (Fintype.card α).choose 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_product_filter_lt`：card_product_filter_lt [LinearOrder α] : 
#{x in s ×ˢ s | x.1 < x.2} = (#s).choose 2

--- 原说明 ---
The number of strictly ordered pairs `(a, b)` in `α` is `(Fintype.card α).choose
 2`.
-/
lemma Fintype.card_product_filter_lt [Fintype α] [LinearOrder α] :
    #{x : α × α | x.1 < x.2} = (Fintype.card α).choose 2 := by
  simpa using Finset.card_product_filter_lt (s := univ)

section

attribute [local instance] Fintype.ofFinite in
@[simp]
/-
**infinite_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ 
Infinite β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Infinite.nonempty`：∀ (α : Type u_4) [Infinite α], Nonempty α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
-/
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β := by
  refine
    ⟨fun H => ?_, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  contrapose! H; have := H.1 ⟨b⟩; have := H.2 ⟨a⟩
  infer_instance
/-
**Pi.infinite_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.infinite_of_left {ι : Sort*} {π : ι -> Type*} [forall i, Nontrivial <| 
π i] [Infinite ι] : Infinite (forall i : ι, π i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
-/
instance Pi.infinite_of_left {ι : Sort*} {π : ι → Type*} [∀ i, Nontrivial <| π i] [Infinite ι] :
    Infinite (∀ i : ι, π i) := by
  classical
  choose m n hm using fun i => exists_pair_ne (π i)
  refine Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => ?_
  simp_rw [update_eq_iff, update_of_ne hne] at h
  exact (hm x h.1.symm).elim

/-- If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` is infinite. -/
/-
**Pi.infinite_of_exists_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.infinite_of_exists_right {ι : Sort*} {π : ι -> Sort*} (i : ι) [Infinite
 <| π i] [forall i, Nonempty <| π i] : Infinite (forall i : ι, π i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Function.update_injective`：update_injective (f : forall a, β a) (a' : α)
 : Injective (update f a')

--- 原说明 ---
If at least one `π i` is infinite and the rest nonempty, the pi type of all `π` 
is infinite.
-/
theorem Pi.infinite_of_exists_right {ι : Sort*} {π : ι → Sort*} (i : ι) [Infinite <| π i]
    [∀ i, Nonempty <| π i] : Infinite (∀ i : ι, π i) := by
  classical
  let ⟨m⟩ := @Pi.instNonempty ι π _
  exact Infinite.of_injective _ (update_injective m i)

/-- See `Pi.infinite_of_exists_right` for the case that only one `π i` is infinite. -/
/-
**Pi.infinite_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.infinite_of_right {ι : Sort*} {π : ι -> Type*} [forall i, Infinite <| π
 i] [Nonempty ι] : Infinite (forall i : ι, π i)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.infinite_of_exists_right`：Pi.infinite_of_exists_right {ι : Sort*} {π 
: ι -> Sort*} (i : ι) [Infinite <| π i] [forall i, Nonempty <| π i] : Infinite (
forall i : ι, π i…
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α

--- 原说明 ---
See `Pi.infinite_of_exists_right` for the case that only one `π i` is infinite.
-/
instance Pi.infinite_of_right {ι : Sort*} {π : ι → Type*} [∀ i, Infinite <| π i] [Nonempty ι] :
    Infinite (∀ i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)

/-- Non-dependent version of `Pi.infinite_of_left`. -/
/-
**Function.infinite_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.infinite_of_left {ι : Sort*} {π : Type*} [Nontrivial π] [Infinite
 ι] : Infinite (ι -> π)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-dependent version of `Pi.infinite_of_left`.
-/
instance Function.infinite_of_left {ι : Sort*} {π : Type*} [Nontrivial π] [Infinite ι] :
    Infinite (ι → π) :=
  Pi.infinite_of_left

/-- Non-dependent version of `Pi.infinite_of_exists_right` and `Pi.infinite_of_right`. -/
/-
**Function.infinite_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Function.infinite_of_right {ι : Sort*} {π : Type*} [Infinite π] [Nonempty 
ι] : Infinite (ι -> π)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Non-dependent version of `Pi.infinite_of_exists_right` and `Pi.infinite_of_right
`.
-/
instance Function.infinite_of_right {ι : Sort*} {π : Type*} [Infinite π] [Nonempty ι] :
    Infinite (ι → π) :=
  Pi.infinite_of_right

end

