/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Order.Filter.CountablyGenerated

/-!
# Convergence to infinity and countably generated filters

In this file we prove that

- `Filter.atTop` and `Filter.atBot` filters on a countable type are countably generated;
- `Filter.exists_seq_tendsto`: if `f` is a nontrivial countably generated filter,
  then there exists a sequence that converges. to `f`;
- `Filter.tendsto_iff_seq_tendsto`: convergence along a countably generated filter
  is equivalent to convergence along all sequences that converge to this filter.
-/

public section

open Set

namespace Filter

variable {α β : Type*}

/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) atTop.isCountablyGenerated [Preorder α] [Countable α] :
    (atTop : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 200) atBot.isCountablyGenerated [Preorder α] [Countable α] :
    (atBot : Filter <| α).IsCountablyGenerated :=
  isCountablyGenerated_seq _
/-
**Filter.instIsCountablyGeneratedAtTopProd** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instIsCountablyGeneratedAtTopProd [Preorder α] [IsCountablyGenerated (atTo
p : Filter α)] [Preorder β] [IsCountablyGenerated (atTop : Filter β)] : IsCounta
blyGenerated (atTop : Filter (α × β))
参数：atTop : Filter α；atTop : Filter β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Filter.prod.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (la : 
Filter α) (lb : Filter β) [la.IsCountablyGenerated] [lb.IsCountablyGenerated],  
 (la ×ˢ lb).IsCountabl…
-/
instance instIsCountablyGeneratedAtTopProd [Preorder α] [IsCountablyGenerated (atTop : Filter α)]
    [Preorder β] [IsCountablyGenerated (atTop : Filter β)] :
    IsCountablyGenerated (atTop : Filter (α × β)) := by
  rw [← prod_atTop_atTop_eq]
  infer_instance
/-
**Filter.instIsCountablyGeneratedAtBotProd** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instIsCountablyGeneratedAtBotProd [Preorder α] [IsCountablyGenerated (atBo
t : Filter α)] [Preorder β] [IsCountablyGenerated (atBot : Filter β)] : IsCounta
blyGenerated (atBot : Filter (α × β))
参数：atBot : Filter α；atBot : Filter β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atBot_atBot_eq`：prod_atBot_atBot_eq [Preorder α] [Preorder β
] : (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β))
· 使用定理 `Filter.prod.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (la : 
Filter α) (lb : Filter β) [la.IsCountablyGenerated] [lb.IsCountablyGenerated],  
 (la ×ˢ lb).IsCountabl…
-/
instance instIsCountablyGeneratedAtBotProd [Preorder α] [IsCountablyGenerated (atBot : Filter α)]
    [Preorder β] [IsCountablyGenerated (atBot : Filter β)] :
    IsCountablyGenerated (atBot : Filter (α × β)) := by
  rw [← prod_atBot_atBot_eq]
  infer_instance
/-
**Filter._root_.OrderDual.instIsCountablyGeneratedAtTop** 是 Mathlib 中的一个实例，位于命名空
间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsCountablyGeneratedAtTop [Preorder α]
    [IsCountablyGenerated (atBot : Filter α)] : IsCountablyGenerated (atTop : Filter αᵒᵈ) := ‹_›
/-
**Filter._root_.OrderDual.instIsCountablyGeneratedAtBot** 是 Mathlib 中的一个实例，位于命名空
间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsCountablyGeneratedAtBot [Preorder α]
    [IsCountablyGenerated (atTop : Filter α)] : IsCountablyGenerated (atBot : Filter αᵒᵈ) := ‹_›
/-
**Filter.atTop_countable_basis** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atTop_countable_basis [Preorder α] [IsDirectedOrder α] [Nonempty α] [Count
able α] : HasCountableBasis (atTop : Filter α) (fun _ => True) Ici
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
lemma atTop_countable_basis [Preorder α] [IsDirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atTop : Filter α) (fun _ => True) Ici :=
  { atTop_basis with countable := to_countable _ }
/-
**Filter.atBot_countable_basis** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：atBot_countable_basis [Preorder α] [IsCodirectedOrder α] [Nonempty α] [Cou
ntable α] : HasCountableBasis (atBot : Filter α) (fun _ => True) Iic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
-/
lemma atBot_countable_basis [Preorder α] [IsCodirectedOrder α] [Nonempty α] [Countable α] :
    HasCountableBasis (atBot : Filter α) (fun _ => True) Iic :=
  { atBot_basis with countable := to_countable _ }

/-- If `f` is a nontrivial countably generated filter, then there exists a sequence that converges
to `f`. -/
/-
**Filter.exists_seq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_seq_tendsto (f : Filter α) [IsCountablyGenerated f] [NeBot f] : exi
sts x : Nat -> α, Tendsto x atTop f
参数：f : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_antitone_basis`：exists_antitone_basis (f : Filter α) [f.Is
CountablyGenerated] : exists x : Nat -> Set α, f.HasAntitoneBasis x
· 使用定理 `Filter.HasAntitoneBasis.tendsto`：∀ {ι : Type u_1} {α : Type u_3} [inst :
 Preorder ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ {φ : ι →
 α}, (∀ (i : ι), φ i …
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.HasAntitoneBasis.mem`：∀ {α : Type u_1} {ι : Type u_4} [inst : Pre
order ι] {l : Filter α} {s : ι → Set α},   l.HasAntitoneBasis s → ∀ (i : ι), s i
 ∈ l
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `f` is a nontrivial countably generated filter, then there exists a sequence 
that converges
to `f`.
-/
theorem exists_seq_tendsto (f : Filter α) [IsCountablyGenerated f] [NeBot f] :
    ∃ x : ℕ → α, Tendsto x atTop f := by
  obtain ⟨B, h⟩ := f.exists_antitone_basis
  choose x hx using fun n => Filter.nonempty_of_mem (h.mem n)
  exact ⟨x, h.tendsto hx⟩
/-
**Filter.exists_seq_monotone_tendsto_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
形式化陈述：exists_seq_monotone_tendsto_atTop_atTop (α : Type*) [Preorder α] [Nonempty
 α] [IsDirectedOrder α] [(atTop : Filter α).IsCountablyGenerated] : exists xs : 
Nat -> α, Monotone xs ∧ Tendsto xs atTop atTop
参数：α : Type*；atTop : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `exists_ge_ge`：exists_ge_ge [LE α] [IsDirectedOrder α] (a b : α) : exists
 c, a <= c ∧ b <= c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α]
    [IsDirectedOrder α] [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧ Tendsto xs atTop atTop := by
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  choose c hleft hright using exists_ge_ge (α := α)
  set xs : ℕ → α := fun n => (List.range n).foldl (fun x n ↦ c x (ys n)) (ys 0)
  have hsucc (n : ℕ) : xs (n + 1) = c (xs n) (ys n) := by simp [xs, List.range_succ]
  refine ⟨xs, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hsucc]
    apply hleft
  · refine (tendsto_add_atTop_iff_nat 1).1 <| tendsto_atTop_mono (fun n ↦ ?_) h
    rw [hsucc]
    apply hright
/-
**Filter.exists_seq_antitone_tendsto_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
形式化陈述：exists_seq_antitone_tendsto_atTop_atBot (α : Type*) [Preorder α] [Nonempty
 α] [IsCodirectedOrder α] [(atBot : Filter α).IsCountablyGenerated] : exists xs 
: Nat -> α, Antitone xs ∧ Tendsto xs atTop atBot
参数：α : Type*；atBot : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_monotone_tendsto_atTop_atTop`：exists_seq_monotone_tend
sto_atTop_atTop (α : Type*) [Preorder α] [Nonempty α] [IsDirectedOrder α] [(atTo
p : Filter α).IsCountablyGenerated] …
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `OrderDual.isDirected_le`：∀ {α : Type u_1} [inst : LE α] [IsCodirectedOrd
er α], IsDirectedOrder αᵒᵈ
· 使用定理 `OrderDual.instIsCountablyGeneratedAtTop`：∀ {α : Type u_1} [inst : Preord
er α] [Filter.atBot.IsCountablyGenerated], Filter.atTop.IsCountablyGenerated
-/
theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type*) [Preorder α] [Nonempty α]
    [IsCodirectedOrder α] [(atBot : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Antitone xs ∧ Tendsto xs atTop atBot :=
  exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ

/-- An abstract version of continuity of sequentially continuous functions on metric spaces:
if a filter `k` is countably generated then `Tendsto f k l` iff for every sequence `u`
converging to `k`, `f ∘ u` tends to `l`. -/
/-
**Filter.tendsto_iff_seq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_seq_tendsto {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCo
untablyGenerated] : Tendsto f k l ↔ forall x : Nat -> α, Tendsto x atTop k -> Te
ndsto (f ∘ x) atTop l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.Inf.isCountablyGenerated`：∀ {α : Type u_1} (f g : Filter α) [f.Is
CountablyGenerated] [g.IsCountablyGenerated], (f ⊓ g).IsCountablyGenerated
· 使用定理 `Filter.isCountablyGenerated_principal`：isCountablyGenerated_principal (s
 : Set α) : IsCountablyGenerated (𝓟 s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
An abstract version of continuity of sequentially continuous functions on metric
 spaces:
if a filter `k` is countably generated then `Tendsto f k l` iff for every sequen
ce `u`
converging to `k`, `f ∘ u` tends to `l`.
-/
theorem tendsto_iff_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    Tendsto f k l ↔ ∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l := by
  refine ⟨fun h x hx => h.comp hx, fun H s hs => ?_⟩
  contrapose! H
  have : NeBot (k ⊓ 𝓟 (f ⁻¹' sᶜ)) := by simpa [neBot_iff, inf_principal_eq_bot]
  rcases (k ⊓ 𝓟 (f ⁻¹' sᶜ)).exists_seq_tendsto with ⟨x, hx⟩
  rw [tendsto_inf, tendsto_principal] at hx
  refine ⟨x, hx.1, fun h => ?_⟩
  rcases (hx.2.and (h hs)).exists with ⟨N, hnotMem, hmem⟩
  exact hnotMem hmem
/-
**Filter.tendsto_of_seq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_of_seq_tendsto {f : α -> β} {k : Filter α} {l : Filter β} [k.IsCou
ntablyGenerated] : (forall x : Nat -> α, Tendsto x atTop k -> Tendsto (f ∘ x) at
Top l) -> Tendsto f k l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_seq_tendsto`：tendsto_iff_seq_tendsto {f : α -> β} {k 
: Filter α} {l : Filter β} [k.IsCountablyGenerated] : Tendsto f k l ↔ forall x :
 Nat -> α, Tendsto x…
-/
theorem tendsto_of_seq_tendsto {f : α → β} {k : Filter α} {l : Filter β} [k.IsCountablyGenerated] :
    (∀ x : ℕ → α, Tendsto x atTop k → Tendsto (f ∘ x) atTop l) → Tendsto f k l :=
  tendsto_iff_seq_tendsto.2
/-
**Filter.eventually_iff_seq_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_iff_seq_eventually {ι : Type*} {l : Filter ι} {p : ι -> Prop} [
l.IsCountablyGenerated] : (forallᶠ n in l, p n) ↔ forall x : Nat -> ι, Tendsto x
 atTop l -> forallᶠ n : Nat in atTop, p (x n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.tendsto_iff_seq_tendsto`：tendsto_iff_seq_tendsto {f : α -> β} {k 
: Filter α} {l : Filter β} [k.IsCountablyGenerated] : Tendsto f k l ↔ forall x :
 Nat -> α, Tendsto x…
-/
theorem eventually_iff_seq_eventually {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∀ᶠ n in l, p n) ↔ ∀ x : ℕ → ι, Tendsto x atTop l → ∀ᶠ n : ℕ in atTop, p (x n) := by
  simpa using tendsto_iff_seq_tendsto (f := id) (l := 𝓟 {x | p x})
/-
**Filter.frequently_iff_seq_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_iff_seq_frequently {ι : Type*} {l : Filter ι} {p : ι -> Prop} [
l.IsCountablyGenerated] : (existsᶠ n in l, p n) ↔ exists x : Nat -> ι, Tendsto x
 atTop l ∧ existsᶠ n : Nat in atTop, p (x n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_iff_seq_eventually`：eventually_iff_seq_eventually {ι :
 Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] : (forallᶠ n in 
l, p n) ↔ forall x : Nat -…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem frequently_iff_seq_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ x : ℕ → ι, Tendsto x atTop l ∧ ∃ᶠ n : ℕ in atTop, p (x n) := by
  simp only [Filter.Frequently, eventually_iff_seq_eventually (l := l)]
  push Not; rfl
/-
**Filter.exists_seq_forall_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_seq_forall_of_frequently {ι : Type*} {l : Filter ι} {p : ι -> Prop}
 [l.IsCountablyGenerated] (h : existsᶠ n in l, p n) : exists ns : Nat -> ι, Tend
sto ns atTop l ∧ forall n, p (ns n)
参数：h : existsᶠ n in l, p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_iff_seq_frequently`：frequently_iff_seq_frequently {ι :
 Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] : (existsᶠ n in 
l, p n) ↔ exists x : Nat -…
· 使用定理 `Filter.subseq_forall_of_frequently`：subseq_forall_of_frequently {ι : Typ
e*} {x : Nat -> ι} {p : ι -> Prop} {l : Filter ι} (h_tendsto : Tendsto x atTop l
) (h : existsᶠ n in atTo…
-/
theorem exists_seq_forall_of_frequently {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] (h : ∃ᶠ n in l, p n) :
    ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) := by
  rw [frequently_iff_seq_frequently] at h
  obtain ⟨x, hx_tendsto, hx_freq⟩ := h
  obtain ⟨n_to_n, h_tendsto, h_freq⟩ := subseq_forall_of_frequently hx_tendsto hx_freq
  exact ⟨x ∘ n_to_n, h_tendsto, h_freq⟩
/-
**Filter.frequently_iff_seq_forall** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：frequently_iff_seq_forall {ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.Is
CountablyGenerated] : (existsᶠ n in l, p n) ↔ exists ns : Nat -> ι, Tendsto ns a
tTop l ∧ forall n, p (ns n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma frequently_iff_seq_forall {ι : Type*} {l : Filter ι} {p : ι → Prop}
    [l.IsCountablyGenerated] :
    (∃ᶠ n in l, p n) ↔ ∃ ns : ℕ → ι, Tendsto ns atTop l ∧ ∀ n, p (ns n) :=
  ⟨exists_seq_forall_of_frequently, fun ⟨_ns, hnsl, hpns⟩ ↦
    hnsl.frequently <| Frequently.of_forall hpns⟩

/-- A sequence converges if every subsequence has a convergent subsequence. -/
/-
**Filter.tendsto_of_subseq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_of_subseq_tendsto {ι : Type*} {x : ι -> α} {f : Filter α} {l : Fil
ter ι} [l.IsCountablyGenerated] (hxy : forall ns : Nat -> ι, Tendsto ns atTop l 
-> exists ms : Nat -> Nat, Tendsto (fun n => x (ns <| ms n)) atTop f) : Tendsto 
x l f
参数：hxy : forall ns : Nat -> ι, Tendsto ns atTop l -> exists ms : Nat -> Nat, Ten
dsto (fun n => x (ns <| ms n)) atTop f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.not_tendsto_iff_exists_frequently_notMem`：not_tendsto_iff_exists_
frequently_notMem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : ¬Tendsto f l₁ l
₂ ↔ exists s in l₂, existsᶠ x in l₁, …
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…

--- 原说明 ---
A sequence converges if every subsequence has a convergent subsequence.
-/
theorem tendsto_of_subseq_tendsto {ι : Type*} {x : ι → α} {f : Filter α} {l : Filter ι}
    [l.IsCountablyGenerated]
    (hxy : ∀ ns : ℕ → ι, Tendsto ns atTop l →
      ∃ ms : ℕ → ℕ, Tendsto (fun n => x (ns <| ms n)) atTop f) :
    Tendsto x l f := by
  contrapose! hxy
  obtain ⟨s, hs, hfreq⟩ : ∃ s ∈ f, ∃ᶠ n in l, x n ∉ s := by
    rwa [not_tendsto_iff_exists_frequently_notMem] at hxy
  obtain ⟨y, hy_tendsto, hy_freq⟩ := exists_seq_forall_of_frequently hfreq
  refine ⟨y, hy_tendsto, fun ms hms_tendsto ↦ ?_⟩
  rcases (hms_tendsto.eventually_mem hs).exists with ⟨n, hn⟩
  exact absurd hn <| hy_freq _
/-
**Filter.exists_seq_comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_seq_comp_tendsto {ι : Type*} {g : Filter ι} [IsCountablyGenerated g
] {u : ι -> α} {f : Filter α} [IsCountablyGenerated f] (hx : NeBot (f ⊓ map u g)
) : exists θ : Nat -> ι, Tendsto θ atTop g ∧ Tendsto (u ∘ θ) atTop f
参数：hx : NeBot (f ⊓ map u g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.Inf.isCountablyGenerated`：∀ {α : Type u_1} (f g : Filter α) [f.Is
CountablyGenerated] [g.IsCountablyGenerated], (f ⊓ g).IsCountablyGenerated
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_neBot_iff`：map_neBot_iff (f : α -> β) {F : Filter α} : NeBot 
(map f F) ↔ NeBot F
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.push_pull'`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (F : Filt
er α) (G : Filter β),   Filter.map f (Filter.comap f G ⊓ F) = G ⊓ Filter.map f F
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem exists_seq_comp_tendsto {ι : Type*} {g : Filter ι} [IsCountablyGenerated g] {u : ι → α}
    {f : Filter α} [IsCountablyGenerated f]
    (hx : NeBot (f ⊓ map u g)) : ∃ θ : ℕ → ι, Tendsto θ atTop g ∧ Tendsto (u ∘ θ) atTop f := by
  rw [← Filter.push_pull', map_neBot_iff] at hx
  obtain ⟨θ, hθ⟩ := exists_seq_tendsto (comap u f ⊓ g)
  exact ⟨θ, (tendsto_inf.1 hθ).2, tendsto_comap_iff.1 (tendsto_inf.1 hθ).1⟩
/-
**Filter.subseq_tendsto_of_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：subseq_tendsto_of_neBot {f : Filter α} [IsCountablyGenerated f] {u : Nat -
> α} (hx : NeBot (f ⊓ map u atTop)) : exists θ : Nat -> Nat, StrictMono θ ∧ Tend
sto (u ∘ θ) atTop f
参数：hx : NeBot (f ⊓ map u atTop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_comp_tendsto`：exists_seq_comp_tendsto {ι : Type*} {g :
 Filter ι} [IsCountablyGenerated g] {u : ι -> α} {f : Filter α} [IsCountablyGene
rated f] (hx : NeBot…
· 使用定理 `Filter.atTop.isCountablyGenerated`：∀ {α : Type u_1} [inst : Preorder α] 
[Countable α], Filter.atTop.IsCountablyGenerated
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.strictMono_subseq_of_tendsto_atTop`：strictMono_subseq_of_tendsto_
atTop [LinearOrder β] [NoMaxOrder β] {u : Nat -> β} (hu : Tendsto u atTop atTop)
 : exists φ : Nat -> Nat, Stric…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
-/
theorem subseq_tendsto_of_neBot {f : Filter α} [IsCountablyGenerated f] {u : ℕ → α}
    (hx : NeBot (f ⊓ map u atTop)) : ∃ θ : ℕ → ℕ, StrictMono θ ∧ Tendsto (u ∘ θ) atTop f := by
  obtain ⟨φ, hφ⟩ := exists_seq_comp_tendsto hx
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ StrictMono (φ ∘ ψ) :=
    strictMono_subseq_of_tendsto_atTop hφ.1
  exact ⟨φ ∘ ψ, hψφ, hφ.2.comp hψ.tendsto_atTop⟩

end Filter

