/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.Measurability

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/

@[expose] public section

assert_not_exists Covariant MonoidWithZero

open Set Encodable Function Equiv

variable {α β γ δ δ' : Type*} {ι : Sort*} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
/-
**MeasurableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_7 → Type u_7
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measurable space is a space equipped with a σ-algebra.
-/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h

/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/
/-
**MeasurableSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MeasurableSet [MeasurableSpace α] (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MeasurableSet s` means that `s` is measurable (in the ambient measure space on 
`α`)
-/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s

/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/
scoped[MeasureTheory] notation "MeasurableSet[" m "]" => @MeasurableSet _ m

open MeasureTheory

section

open scoped symmDiff

@[simp, measurability]
/-
**MeasurableSet.empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_empty`：∀ {α : Type u_7} (self : Measurable
Space α), MeasurableSpace.MeasurableSet' self ∅
-/
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  MeasurableSpace.measurableSet_empty _

variable {m : MeasurableSpace α}

@[measurability]
/-
**MeasurableSet.compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α}, MeasurableSet s → Me
asurableSet sᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_compl`：∀ {α : Type u_7} (self : Measurable
Space α) (s : Set α),   MeasurableSpace.MeasurableSet' self s → MeasurableSpace.
MeasurableSet' self sᶜ
-/
protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=
  MeasurableSpace.measurableSet_compl _ s
/-
**MeasurableSet.of_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α}, MeasurableSet sᶜ → M
easurableSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
/-
**MeasurableSet.compl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩

@[simp, measurability]
/-
**MeasurableSet.univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α}, MeasurableSet Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  .of_compl <| by simp

@[nontriviality, measurability]
/-
**Subsingleton.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.set_cases`：set_cases {p : Set α -> Prop} (h0 : p ∅) (h1 : p
 univ) (s) : p s
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
/-
**MeasurableSet.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : Mea
surableSet t
参数：hs : MeasurableSet s；h : s = t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

@[measurability]
/-
**MeasurableSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpace α} [Countable ι] ⦃f :
 ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → MeasurableSet (⋃ b, f b)
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `exists_surjective_nat`：exists_surjective_nat (α : Sort u) [Nonempty α] [
Countable α] : exists f : Nat -> α, Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_congr_of_surjective`：iUnion_congr_of_surjective {f : ι -> Set
 α} {g : ι₂ -> Set α} (h : ι -> ι₂) (h1 : Surjective h) (h2 : forall x, g (h x) 
= f x) : ⋃ x, f x = …
· 使用定理 `MeasurableSpace.measurableSet_iUnion`：∀ {α : Type u_7} (self : Measurabl
eSpace α) (f : ℕ → Set α),   (∀ (i : ℕ), MeasurableSpace.MeasurableSet' self (f 
i)) → MeasurableSpace.Meas…
-/
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι → Set α⦄
    (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _
/-
**MeasurableSet.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace α} {f : β → Set α} {s
 : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b)) → MeasurableSet (⋃ b ∈
 s, f b)
参数：∀ b ∈ s, MeasurableSet (f b)；⋃ b ∈ s, f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
-/
protected theorem MeasurableSet.biUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)
/-
**Set.Finite.measurableSet_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.measurableSet_biUnion {f : β -> Set α} {s : Set β} (hs : s.Fini
te) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b in s, f b)
参数：hs : s.Finite；h : forall b in s, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem Set.Finite.measurableSet_biUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  .biUnion hs.countable h
/-
**Finset.measurableSet_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurableSet_biUnion {f : β -> Set α} (s : Finset β) (h : forall b
 in s, MeasurableSet (f b)) : MeasurableSet (⋃ b in s, f b)
参数：s : Finset β；h : forall b in s, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.measurableSet_biUnion`：Set.Finite.measurableSet_biUnion {f : 
β -> Set α} {s : Set β} (hs : s.Finite) (h : forall b in s, MeasurableSet (f b))
 : MeasurableSet (⋃ b …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.measurableSet_biUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biUnion h
/-
**MeasurableSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s : Set (Set α)},   s.Countable 
→ (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)
参数：Set α；∀ t ∈ s, MeasurableSet t；⋃₀ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
-/
protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h
/-
**Set.Finite.measurableSet_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite) (h : for
all t in s, MeasurableSet t) : MeasurableSet (⋃₀ s)
参数：Set α；hs : s.Finite；h : forall t in s, MeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.sUnion`：∀ {α : Type u_1} {m : MeasurableSpace α} {s : Set 
(Set α)},   s.Countable → (∀ t ∈ s, MeasurableSet t) → MeasurableSet (⋃₀ s)
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h

@[measurability]
/-
**MeasurableSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.iInter [Countable ι] {f : ι -> Set α} (h : forall b, Measura
bleSet (f b)) : MeasurableSet (⋂ b, f b)
参数：h : forall b, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem MeasurableSet.iInter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  .of_compl <| by rw [compl_iInter]; exact .iUnion fun b => (h b).compl
/-
**MeasurableSet.biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.biInter {f : β -> Set α} {s : Set β} (hs : s.Countable) (h :
 forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b)
参数：hs : s.Countable；h : forall b in s, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpac
e α}, MeasurableSet sᶜ → MeasurableSet s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iInter₂`：compl_iInter₂ (s : forall i, κ i -> Set α) : (⋂ (i) (
j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem MeasurableSet.biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .of_compl <| by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl
/-
**Set.Finite.measurableSet_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.measurableSet_biInter {f : β -> Set α} {s : Set β} (hs : s.Fini
te) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b)
参数：hs : s.Finite；h : forall b in s, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem Set.Finite.measurableSet_biInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .biInter hs.countable h
/-
**Finset.measurableSet_biInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.measurableSet_biInter {f : β -> Set α} (s : Finset β) (h : forall b
 in s, MeasurableSet (f b)) : MeasurableSet (⋂ b in s, f b)
参数：s : Finset β；h : forall b in s, MeasurableSet (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.measurableSet_biInter`：Set.Finite.measurableSet_biInter {f : 
β -> Set α} {s : Set β} (hs : s.Finite) (h : forall b in s, MeasurableSet (f b))
 : MeasurableSet (⋂ b …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem Finset.measurableSet_biInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biInter h
/-
**MeasurableSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : forall t in
 s, MeasurableSet t) : MeasurableSet (⋂₀ s)
参数：Set α；hs : s.Countable；h : forall t in s, MeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_eq_biInter`：sInter_eq_biInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
-/
theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h
/-
**Set.Finite.measurableSet_sInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite) (h : for
all t in s, MeasurableSet t) : MeasurableSet (⋂₀ s)
参数：Set α；hs : s.Finite；h : forall t in s, MeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.sInter`：MeasurableSet.sInter {s : Set (Set α)} (hs : s.Cou
ntable) (h : forall t in s, MeasurableSet t) : MeasurableSet (⋂₀ s)
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h

@[simp, measurability]
/-
**MeasurableSet.union** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α}, MeasurableSet s₁
 → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
参数：s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
-/
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
/-
**MeasurableSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α}, MeasurableSet s₁
 → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
参数：s₁ ∩ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_compl_compl_union_compl`：inter_eq_compl_compl_union_compl (
s t : Set α) : s inter t = (sᶜ union tᶜ)ᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
-/
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
/-
**MeasurableSet.diff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α}, MeasurableSet s₁
 → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
参数：s₁ \ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp, measurability]
/-
**MeasurableSet.himp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α}, MeasurableSet s₁
 → MeasurableSet s₂ → MeasurableSet (s₁ ⇨ s₂)
参数：s₁ ⇨ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
/-
**MeasurableSet.symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α},   MeasurableSet 
s₁ → MeasurableSet s₂ → MeasurableSet (symmDiff s₁ s₂)
参数：symmDiff s₁ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
/-
**MeasurableSet.bihimp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α},   MeasurableSet 
s₁ → MeasurableSet s₂ → MeasurableSet (bihimp s₁ s₂)
参数：bihimp s₁ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.himp`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ⇨ s₂)
-/
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
/-
**MeasurableSet.ite** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {t s₁ s₂ : Set α},   MeasurableSe
t t → MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (t.ite s₁ s₂)
参数：t.ite s₁ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

open scoped Classical in
/-
**MeasurableSet.ite'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p -> MeasurableSet s) (h
t : ¬p -> MeasurableSet t) : MeasurableSet (ite p s t)
参数：hs : p -> MeasurableSet s；ht : ¬p -> MeasurableSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]
/-
**MeasurableSet.cond** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Set α},   MeasurableSet 
s₁ → MeasurableSet s₂ → ∀ {i : Bool}, MeasurableSet (bif i then s₁ else s₂)
参数：bif i then s₁ else s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts [h₂, h₁]
/-
**MeasurableSet.const** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop), MeasurableSet {_a | p
}
参数：p : Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]
/-
**MeasurableSet.imp** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p q : α → Prop},   MeasurableSet
 {x | p x} → MeasurableSet {x | q x} → MeasurableSet {x | p x → q x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
protected lemma MeasurableSet.imp {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x → q x} := by
  have h_eq : {x | p x → q x} = {x | p x}ᶜ ∪ {x | q x} := by grind
  rw [h_eq]
  exact hs.compl.union ht
/-
**MeasurableSet.iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {p q : α → Prop},   MeasurableSet
 {x | p x} → MeasurableSet {x | q x} → MeasurableSet {x | p x ↔ q x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.imp`：∀ {α : Type u_1} {m : MeasurableSpace α} {p q : α → P
rop},   MeasurableSet {x | p x} → MeasurableSet {x | q x} → MeasurableSet {x | p
 x → q …
-/
protected lemma MeasurableSet.iff {p q : α → Prop}
    (hs : MeasurableSet {x | p x}) (ht : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ↔ q x} := by
  have h_eq : {x | p x ↔ q x} = {x | p x → q x} ∩ {x | q x → p x} := by ext; simp; grind
  rw [h_eq]
  exact (hs.imp ht).inter (ht.imp hs)

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
/-
**nonempty_measurable_superset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_measurable_superset (s : Set α) : Nonempty { t // s subseteq t ∧ 
MeasurableSet t }
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ

--- 原说明 ---
Every set has a measurable superset. Declare this as local instance as needed.
-/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end

/-
**MeasurableSpace.measurableSet_injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableS
pace`。
形式化陈述：∀ {α : Type u_1}, Function.Injective (@MeasurableSet α)
参数：@MeasurableSet α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MeasurableSpace.measurableSet_injective : Injective (@MeasurableSet α)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _ => by congr

@[ext]
/-
**MeasurableSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h : forall s : Set α, Mea
surableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
参数：h : forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_injective`：∀ {α : Type u_1}, Function.Inje
ctive (@MeasurableSet α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α}
    (h : ∀ s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂ :=
  measurableSet_injective <| funext fun s => propext (h s)

/-- A typeclass mixin for `MeasurableSpace`s such that each singleton is measurable. -/
/-
**MeasurableSingletonClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_7) → [MeasurableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass mixin for `MeasurableSpace`s such that each singleton is measurable.
-/
class MeasurableSingletonClass (α : Type*) [MeasurableSpace α] : Prop where
  /-- A singleton is a measurable set. -/
  measurableSet_singleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurableSet_singleton)

@[simp]
/-
**MeasurableSet.singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasurableSet.singleton [MeasurableSpace α] [MeasurableSingletonClass α] (
a : α) : MeasurableSet {a}
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
lemma MeasurableSet.singleton [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} :=
  measurableSet_singleton a

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-
**measurableSet_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_eq {a : α} : MeasurableSet { x | x = a }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } := .singleton a

@[measurability]
/-
**MeasurableSet.insert** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [MeasurableSingletonClass α] {
s : Set α},   MeasurableSet s → ∀ (a : α), MeasurableSet (insert a s)
参数：a : α；insert a s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
protected theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  .union (.singleton a) hs

@[simp]
/-
**measurableSet_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ Me
asurableSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `MeasurableSet.insert`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] {s : Set α},   MeasurableSet s → ∀ (a : α), MeasurableSet
 (insert a…
-/
theorem measurableSet_insert {a : α} {s : Set α} :
    MeasurableSet (insert a s) ↔ MeasurableSet s := by
  classical
  exact ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_sdiff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩
/-
**Set.Subsingleton.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : Measura
bleSet s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on .empty .singleton
/-
**Set.Finite.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.insert`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] {s : Set α},   MeasurableSet s → ∀ (a : α), MeasurableSet
 (insert a…
-/
theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]
/-
**Finset.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [MeasurableSingletonClass α] (
s : Finset α), MeasurableSet ↑s
参数：s : Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.measurableSet
/-
**Set.Countable.measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet
 s
参数：hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_of_singleton`：biUnion_of_singleton (s : Set α) : ⋃ x in s, {
x} = s
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用引理 `MeasurableSet.singleton`：MeasurableSet.singleton [MeasurableSpace α] [Me
asurableSingletonClass α] (a : α) : MeasurableSet {a}
-/
theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

end MeasurableSingletonClass

namespace MeasurableSpace

/-- Copy of a `MeasurableSpace` with a new `MeasurableSet` equal to the old one. Useful to fix
definitional equalities. -/
@[instance_reducible]
/-
**MeasurableSpace.copy** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：{α : Type u_1} →   (m : MeasurableSpace α) → (p : Set α → Prop) → (∀ (s : 
Set α), p s ↔ MeasurableSet s) → MeasurableSpace α
参数：m : MeasurableSpace α；p : Set α → Prop；∀ (s : Set α), p s ↔ MeasurableSet s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `MeasurableSpace` with a new `MeasurableSet` equal to the old one. Use
ful to fix
definitional equalities.
-/
protected def copy (m : MeasurableSpace α) (p : Set α → Prop) (h : ∀ s, p s ↔ MeasurableSet[m] s) :
    MeasurableSpace α where
  MeasurableSet' := p
  measurableSet_empty := by simpa only [h] using! m.measurableSet_empty
  measurableSet_compl := by simpa only [h] using! m.measurableSet_compl
  measurableSet_iUnion := by simpa only [h] using! m.measurableSet_iUnion
/-
**MeasurableSpace.measurableSet_copy** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace`
。
形式化陈述：measurableSet_copy {m : MeasurableSpace α} {p : Set α -> Prop} (h : forall
 s, p s ↔ MeasurableSet[m] s) {s} : MeasurableSet[.copy m p h] s ↔ p s
参数：h : forall s, p s ↔ MeasurableSet[m] s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma measurableSet_copy {m : MeasurableSpace α} {p : Set α → Prop}
    (h : ∀ s, p s ↔ MeasurableSet[m] s) {s} : MeasurableSet[.copy m p h] s ↔ p s :=
  Iff.rfl
/-
**MeasurableSpace.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace`。
形式化陈述：copy_eq {m : MeasurableSpace α} {p : Set α -> Prop} (h : forall s, p s ↔ M
easurableSet[m] s) : m.copy p h = m
参数：h : forall s, p s ↔ MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
-/
lemma copy_eq {m : MeasurableSpace α} {p : Set α → Prop} (h : ∀ s, p s ↔ MeasurableSet[m] s) :
    m.copy p h = m :=
  ext h

section CompleteLattice

/-
**MeasurableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s
/-
**MeasurableSpace.le_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：le_def {α} {a b : MeasurableSpace α} : a <= b ↔ a.MeasurableSet' <= b.Meas
urableSet'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.MeasurableSet' ≤ b.MeasurableSet' :=
  Iff.rfl
/-
**MeasurableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (MeasurableSpace α) :=
  { PartialOrder.lift (@MeasurableSet α) measurableSet_injective with
    le := LE.le
    lt := fun m₁ m₂ => m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
/-
**MeasurableSpace.GenerateMeasurable** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasurableSpac
e`。
形式化陈述：{α : Type u_1} → Set (Set α) → Set α → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest σ-algebra containing a collection `s` of basic sets
-/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | protected basic : ∀ u ∈ s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | protected iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
@[instance_reducible]
/-
**MeasurableSpace.generateFrom** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：generateFrom (s : Set (Set α)) : MeasurableSpace α where MeasurableSet'
参数：s : Set (Set α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the smallest measure space containing a collection of basic sets
-/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion
/-
**MeasurableSpace.measurableSet_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Measurab
leSpace`。
形式化陈述：measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t in s) : M
easurableSet[generateFrom s] t
参数：Set α；ht : t in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) :
    MeasurableSet[generateFrom s] t :=
  .basic t ht

@[elab_as_elim]
/-
**MeasurableSpace.generateFrom_induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSp
ace`。
形式化陈述：generateFrom_induction (C : Set (Set α)) (p : forall s : Set α, Measurable
Set[generateFrom C] s -> Prop) (hC : forall t in C, forall ht, p t ht) (empty : 
p ∅ (measurableSet_empty _)) (compl : forall t ht, p t ht -> p tᶜ ht.compl) (iUn
ion : forall (s : Nat -> Set α) (hs : forall n, MeasurableSet[generateFrom C] (s
 n)), (forall n, p (s n) (hs n)) -> p (⋃ i, s i) (.iUnion hs)) (s : Set α) (hs :
 MeasurableSet[generateFrom C] s) : p s hs
参数：C : Set (Set α)；p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop
；hC : forall t in C, forall ht, p t ht；empty : p ∅ (measurableSet_empty _)；compl
 : forall t ht, p t ht -> p tᶜ ht.compl；iUnion : forall (s : Nat -> Set α) (hs :
 forall n, MeasurableSet[generateFrom C] (s n)), (forall n, p (s n) (hs n)) -> p
 (⋃ i, s i) (.iUnion hs)；s : Set α；hs : MeasurableSet[generateFrom C] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_empty`：∀ {α : Type u_7} (self : Measurable
Space α), MeasurableSpace.MeasurableSet' self ∅
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem generateFrom_induction (C : Set (Set α))
    (p : ∀ s : Set α, MeasurableSet[generateFrom C] s → Prop) (hC : ∀ t ∈ C, ∀ ht, p t ht)
    (empty : p ∅ (measurableSet_empty _)) (compl : ∀ t ht, p t ht → p tᶜ ht.compl)
    (iUnion : ∀ (s : ℕ → Set α) (hs : ∀ n, MeasurableSet[generateFrom C] (s n)),
      (∀ n, p (s n) (hs n)) → p (⋃ i, s i) (.iUnion hs)) (s : Set α)
    (hs : MeasurableSet[generateFrom C] s) : p s hs := by
  induction hs
  exacts [hC _ ‹_› _, empty, compl _ ‹_› ‹_›, iUnion ‹_› ‹_› ‹_›]
/-
**MeasurableSpace.generateFrom_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α} (h : forall t in
 s, MeasurableSet[m] t) : generateFrom s <= m
参数：Set α；h : forall t in s, MeasurableSet[m] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α}
    (h : ∀ t ∈ s, MeasurableSet[m] t) : generateFrom s ≤ m :=
  fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf
/-
**MeasurableSpace.generateFrom_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace
`。
形式化陈述：generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) : generateFr
om s <= m ↔ s subseteq { t | MeasurableSet[m] t }
参数：Set α；m : MeasurableSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
-/
theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | MeasurableSet[m] t } :=
  Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h

@[simp]
/-
**MeasurableSpace.generateFrom_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Measurab
leSpace`。
形式化陈述：generateFrom_measurableSet [MeasurableSpace α] : generateFrom {s : Set α |
 MeasurableSet s} = ‹_›
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
-/
theorem generateFrom_measurableSet [MeasurableSpace α] :
    generateFrom {s : Set α | MeasurableSet s} = ‹_› :=
  le_antisymm (generateFrom_le fun _ => id) fun _ h => measurableSet_generateFrom h
/-
**MeasurableSpace.forall_generateFrom_mem_iff_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasurableSpace`。
形式化陈述：forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} : (forall 
s, MeasurableSet[generateFrom S] s -> (x in s ↔ y in s)) ↔ (forall s in S, x in 
s ↔ y in s)
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.generateFrom_induction`：generateFrom_induction (C : Set 
(Set α)) (p : forall s : Set α, MeasurableSet[generateFrom C] s -> Prop) (hC : f
orall t in C, forall ht, p t…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} :
    (∀ s, MeasurableSet[generateFrom S] s → (x ∈ s ↔ y ∈ s)) ↔ (∀ s ∈ S, x ∈ s ↔ y ∈ s) := by
  refine ⟨fun H s hs ↦ H s (.basic s hs), fun H s ↦ ?_⟩
  apply generateFrom_induction
  · exact fun s hs _ ↦ H s hs
  · rfl
  · exact fun _ _ ↦ Iff.not
  · intro f _ hf
    simp only [mem_iUnion, hf]

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
@[instance_reducible]
/-
**MeasurableSpace.mkOfClosure** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：{α : Type u_1} → (g : Set (Set α)) → {t | MeasurableSet t} = g → Measurabl
eSpace α
参数：g : Set (Set α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a collection of subsets of `α` such that the `σ`-algebra generated fro
m `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra.
-/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | MeasurableSet[generateFrom g] t } = g) :
    MeasurableSpace α :=
  (generateFrom g).copy (· ∈ g) <| Set.ext_iff.1 hg.symm
/-
**MeasurableSpace.mkOfClosure_sets** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：mkOfClosure_sets {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom 
s] t } = s} : MeasurableSpace.mkOfClosure s hs = generateFrom s
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasurableSpace.copy_eq`：copy_eq {m : MeasurableSpace α} {p : Set α -> P
rop} (h : forall s, p s ↔ MeasurableSet[m] s) : m.copy p h = m
-/
theorem mkOfClosure_sets {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  copy_eq _

/-- We get a Galois insertion between `σ`-algebras on `α` and `Set (Set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
/-
**MeasurableSpace.giGenerateFrom** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableSpace`。
形式化陈述：giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | Measurab
leSet[m] t } where gc _
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.generateFrom_le_iff`：generateFrom_le_iff {s : Set (Set α
)} (m : MeasurableSpace α) : generateFrom s <= m ↔ s subseteq { t | MeasurableSe
t[m] t }

--- 原说明 ---
We get a Galois insertion between `σ`-algebras on `α` and `Set (Set α)` by using
 `generate_from`
  on one side and the collection of measurable sets on the other side.
-/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | MeasurableSet[m] t } where
  gc _ := generateFrom_le_iff
  le_l_u _ _ h := measurableSet_generateFrom h
  choice g hg := MeasurableSpace.mkOfClosure g <| le_antisymm hg <| (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets
/-
**MeasurableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice
/-
**MeasurableSpace.** 是 Mathlib 中的一个实例，位于命名空间 `MeasurableSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MeasurableSpace α) := ⟨⊤⟩

@[gcongr, mono]
/-
**MeasurableSpace.generateFrom_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：generateFrom_mono {s t : Set (Set α)} (h : s subseteq t) : generateFrom s 
<= generateFrom t
参数：Set α；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generateFrom_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h
/-
**MeasurableSpace.generateFrom_sup_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `Measu
rableSpace`。
形式化陈述：generateFrom_sup_generateFrom {s t : Set (Set α)} : generateFrom s ⊔ gener
ateFrom t = generateFrom (s union t)
参数：Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm
/-
**MeasurableSpace.iSup_generateFrom** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace`。
形式化陈述：iSup_generateFrom (s : ι -> Set (Set α)) : ⨆ i, generateFrom (s i) = gener
ateFrom (⋃ i, s i)
参数：s : ι -> Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
lemma iSup_generateFrom (s : ι → Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]
/-
**MeasurableSpace.generateFrom_empty** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableSpace`
。
形式化陈述：generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥ :=
  le_bot_iff.mp (generateFrom_le (by simp))
/-
**MeasurableSpace.generateFrom_singleton_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measur
ableSpace`。
形式化陈述：generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
-/
theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp [@MeasurableSet.empty α ⊥]
/-
**MeasurableSpace.generateFrom_singleton_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measura
bleSpace`。
形式化陈述：generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpa
ce α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp

@[simp]
/-
**MeasurableSpace.generateFrom_insert_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measurable
Space`。
形式化陈述：generateFrom_insert_univ (S : Set (Set α)) : generateFrom (insert Set.univ
 S) = generateFrom S
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_sup_generateFrom`：generateFrom_sup_generate
From {s t : Set (Set α)} : generateFrom s ⊔ generateFrom t = generateFrom (s uni
on t)
· 使用定理 `MeasurableSpace.generateFrom_singleton_univ`：generateFrom_singleton_univ
 : generateFrom {Set.univ} = (⊥ : MeasurableSpace α)
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_univ, bot_sup_eq]

@[simp]
/-
**MeasurableSpace.generateFrom_insert_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measurabl
eSpace`。
形式化陈述：generateFrom_insert_empty (S : Set (Set α)) : generateFrom (insert ∅ S) = 
generateFrom S
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSpace.generateFrom_sup_generateFrom`：generateFrom_sup_generate
From {s t : Set (Set α)} : generateFrom s ⊔ generateFrom t = generateFrom (s uni
on t)
· 使用定理 `MeasurableSpace.generateFrom_singleton_empty`：generateFrom_singleton_emp
ty : generateFrom {∅} = (⊥ : MeasurableSpace α)
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
-/
theorem generateFrom_insert_empty (S : Set (Set α)) :
    generateFrom (insert ∅ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_empty, bot_sup_eq]
/-
**MeasurableSpace.measurableSet_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpa
ce`。
形式化陈述：measurableSet_bot_iff {s : Set α} : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.sUnion_mem_empty_univ`：sUnion_mem_empty_univ {S : Set (Set α)} (h : 
S subseteq {∅, univ}) : ⋃₀ S in ({∅, univ} : Set (Set α))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `MeasurableSpace.measurableSet_empty`：∀ {α : Type u_7} (self : Measurable
Space α), MeasurableSpace.MeasurableSet' self ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_bot_iff {s : Set α} : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp +contextual [or_imp]
      measurableSet_iUnion := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl
/-
**MeasurableSpace.measurableSet_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, MeasurableSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
@[simp, measurability] theorem measurableSet_top {s : Set α} : MeasurableSet[⊤] s := trivial

@[simp]
-- The `m₁` parameter gets filled in by typeclass instance synthesis (for some reason...)
-- so we have to order it *after* `m₂`. Otherwise `simp` can't apply this lemma.
/-
**MeasurableSpace.measurableSet_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：measurableSet_inf {m₂ m₁ : MeasurableSpace α} {s : Set α} : MeasurableSet[
m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ MeasurableSet[m₂] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_inf {m₂ m₁ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ MeasurableSet[m₂] s :=
  Iff.rfl

@[simp]
/-
**MeasurableSpace.measurableSet_sInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`
。
形式化陈述：measurableSet_sInf {ms : Set (MeasurableSpace α)} {s : Set α} : Measurable
Set[sInf ms] s ↔ forall m in ms, MeasurableSet[m] s
参数：MeasurableSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measurableSet_sInf {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sInf ms] s ↔ ∀ m ∈ ms, MeasurableSet[m] s :=
  show s ∈ ⋂₀ _ ↔ _ by simp
/-
**MeasurableSpace.measurableSet_iInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`
。
形式化陈述：measurableSet_iInf {ι} {m : ι -> MeasurableSpace α} {s : Set α} : Measurab
leSet[iInf m] s ↔ forall i, MeasurableSet[m i] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `MeasurableSpace.measurableSet_sInf`：measurableSet_sInf {ms : Set (Measur
ableSpace α)} {s : Set α} : MeasurableSet[sInf ms] s ↔ forall m in ms, Measurabl
eSet[m] s
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_iInf {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iInf m] s ↔ ∀ i, MeasurableSet[m i] s := by
  rw [iInf, measurableSet_sInf, forall_mem_range]
/-
**MeasurableSpace.measurableSet_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`。
形式化陈述：measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} : MeasurableSet[
m₁ ⊔ m₂] s ↔ GenerateMeasurable {s | MeasurableSet[m₁] s ∨ MeasurableSet[m₂] s} 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊔ m₂] s ↔
      GenerateMeasurable {s | MeasurableSet[m₁] s ∨ MeasurableSet[m₂] s} s :=
  Iff.rfl
/-
**MeasurableSpace.measurableSet_sSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`
。
形式化陈述：measurableSet_sSup {ms : Set (MeasurableSpace α)} {s : Set α} : Measurable
Set[sSup ms] s ↔ GenerateMeasurable { s : Set α | exists m in ms, MeasurableSet[
m] s } s
参数：MeasurableSpace α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem measurableSet_sSup {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sSup ms] s ↔
      GenerateMeasurable { s : Set α | ∃ m ∈ ms, MeasurableSet[m] s } s := by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← ofPred_exists]
/-
**MeasurableSpace.measurableSet_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSpace`
。
形式化陈述：measurableSet_iSup {ι} {m : ι -> MeasurableSpace α} {s : Set α} : Measurab
leSet[iSup m] s ↔ GenerateMeasurable { s : Set α | exists i, MeasurableSet[m i] 
s } s
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
theorem measurableSet_iSup {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iSup m] s ↔ GenerateMeasurable { s : Set α | ∃ i, MeasurableSet[m i] s } s := by
  unfold iSup
  simp only [measurableSet_sSup, exists_range_iff]
/-
**MeasurableSpace.measurableSpace_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableS
pace`。
形式化陈述：measurableSpace_iSup_eq (m : ι -> MeasurableSpace α) : ⨆ n, m n = generate
From { s | exists n, MeasurableSet[m n] s }
参数：m : ι -> MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.measurableSet_iSup`：measurableSet_iSup {ι} {m : ι -> Mea
surableSpace α} {s : Set α} : MeasurableSet[iSup m] s ↔ GenerateMeasurable { s :
 Set α | exists i, Measu…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measurableSpace_iSup_eq (m : ι → MeasurableSpace α) :
    ⨆ n, m n = generateFrom { s | ∃ n, MeasurableSet[m n] s } := by
  ext s
  rw [measurableSet_iSup]
  rfl
/-
**MeasurableSpace.generateFrom_iUnion_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `M
easurableSpace`。
形式化陈述：generateFrom_iUnion_measurableSet (m : ι -> MeasurableSpace α) : generateF
rom (⋃ n, { t | MeasurableSet[m n] t }) = ⨆ n, m n
参数：m : ι -> MeasurableSpace α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem generateFrom_iUnion_measurableSet (m : ι → MeasurableSpace α) :
    generateFrom (⋃ n, { t | MeasurableSet[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_iSup_u m

end CompleteLattice

end MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop, wikidata Q516776]
/-
**Measurable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable.
-/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @Measurable ..])
  (by fun_prop (disch := measurability))

namespace MeasureTheory

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measurable[" m "]" => @Measurable _ _ m _
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.
-/
scoped notation "Measurable[" mα ", " mβ "]" => @Measurable _ _ mα mβ

end MeasureTheory

section MeasurableFunctions

/-
**measurable_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_id {_ : MeasurableSpace α} : Measurable (@id α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurable_id {_ : MeasurableSpace α} : Measurable (@id α) := fun _ => id

@[fun_prop]
/-
**measurable_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
-/
theorem measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a := measurable_id

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
@[to_fun]
/-
**Measurable.comp** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : MeasurableSpace α} {x_
1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ} {f : α → β}, Meas
urable g → Measurable f → Measurable (g ∘ f)
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)

attribute [fun_prop] Measurable.fun_comp

@[deprecated (since := "2026-01-23")] alias Measurable.comp' := Measurable.fun_comp

@[simp, fun_prop]
/-
**measurable_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
 Measurable fun _ : β => a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.const`：∀ {α : Type u_1} {m : MeasurableSpace α} (p : Prop)
, MeasurableSet {_a | p}
-/
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a ∈ s)

@[fun_prop]
/-
**Measurable.le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm :
 m <= m0) {f : α -> β} (hf : Measurable[m] f) : Measurable[m0] f
参数：hm : m <= m0；hf : Measurable[m] f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m ≤ m0)
    {f : α → β} (hf : Measurable[m] f) : Measurable[m0] f := fun _ hs => hm _ (hf hs)

end MeasurableFunctions

/-- A typeclass mixin for `MeasurableSpace`s such that all sets are measurable. -/
/-
**DiscreteMeasurableSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_7) → [MeasurableSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass mixin for `MeasurableSpace`s such that all sets are measurable.
-/
class DiscreteMeasurableSpace (α : Type*) [MeasurableSpace α] : Prop where
  /-- Do not use this. Use `MeasurableSet.of_discrete` instead. -/
  forall_measurableSet : ∀ s : Set α, MeasurableSet s
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk _ (_) fun _ ↦ MeasurableSpace.measurableSet_top

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteMeasurableSpace
variable [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α] {s : Set α} {f : α → β}

/-
**MeasurableSet.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `MeasurableSet`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [DiscreteMeasurableSpace α] {s
 : Set α}, MeasurableSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteMeasurableSpace.forall_measurableSet`：∀ {α : Type u_7} {inst : M
easurableSpace α} [self : DiscreteMeasurableSpace α] (s : Set α), MeasurableSet 
s
-/
@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _
/-
**Measurable.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] [DiscreteMeasurableSpace α]   {f : α → β}, Measurable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.of_discrete`：∀ {α : Type u_1} [inst : MeasurableSpace α] [
DiscreteMeasurableSpace α] {s : Set α}, MeasurableSet s
-/
@[fun_prop] lemma Measurable.of_discrete : Measurable f := fun _ _ ↦ .of_discrete

/-- Warning: Creates a typeclass loop with `MeasurableSingletonClass.toDiscreteMeasurableSpace`.
To be monitored. -/
-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableSingletonClass :
    MeasurableSingletonClass α where
  measurableSet_singleton _ := .of_discrete

end DiscreteMeasurableSpace

