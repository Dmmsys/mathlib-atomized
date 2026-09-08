/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Set.Lattice

/-!
# Constructions involving sets of sets.

## Finite Intersections

We define a structure `FiniteInter` which asserts that a set `S` of subsets of `α` is
closed under finite intersections.

We define `finiteInterClosure` which, given a set `S` of subsets of `α`, is the smallest
set of subsets of `α` which is closed under finite intersections.

`finiteInterClosure S` is endowed with a term of type `FiniteInter` using
`finiteInterClosure_finiteInter`.

-/

public section


variable {α : Type*} (S : Set (Set α))

/-- A structure encapsulating the fact that a set of sets is closed under finite intersection. -/
/-
**FiniteInter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → Set (Set α) → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure encapsulating the fact that a set of sets is closed under finite int
ersection.
-/
structure FiniteInter : Prop where
  /-- `univ_mem` states that `Set.univ` is in `S`. -/
  univ_mem : Set.univ ∈ S
  /-- `inter_mem` states that any two intersections of sets in `S` is also in `S`. -/
  inter_mem : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ∩ t ∈ S

namespace FiniteInter

/-- The smallest set of sets containing `S` which is closed under finite intersections. -/
/-
**FiniteInter.finiteInterClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 `FiniteInter`。
形式化陈述：{α : Type u_1} → Set (Set α) → Set (Set α)
参数：Set α；Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest set of sets containing `S` which is closed under finite intersectio
ns.
-/
inductive finiteInterClosure : Set (Set α)
  | basic {s} : s ∈ S → finiteInterClosure s
  | univ : finiteInterClosure Set.univ
  | inter {s t} : finiteInterClosure s → finiteInterClosure t → finiteInterClosure (s ∩ t)
/-
**FiniteInter.finiteInterClosure_finiteInter** 是 Mathlib 中的一个定理，位于命名空间 `FiniteIn
ter`。
形式化陈述：finiteInterClosure_finiteInter : FiniteInter (finiteInterClosure S)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finiteInterClosure_finiteInter : FiniteInter (finiteInterClosure S) :=
  { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }

variable {S}
/-
**FiniteInter.finiteInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `FiniteInter`。
形式化陈述：finiteInter_mem (cond : FiniteInter S) (F : Finset (Set α)) : ↑F subseteq 
S -> ⋂₀ (↑F : Set (Set α)) in S
参数：cond : FiniteInter S；F : Finset (Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FiniteInter.univ_mem`：∀ {α : Type u_1} {S : Set (Set α)}, FiniteInter S 
→ Set.univ ∈ S
· 使用定理 `FiniteInter.inter_mem`：∀ {α : Type u_1} {S : Set (Set α)}, FiniteInter S
 → ∀ ⦃s : Set α⦄, s ∈ S → ∀ ⦃t : Set α⦄, t ∈ S → s ∩ t ∈ S
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.sInter_insert`：sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ inse
rt s T = s inter ⋂₀ T
-/
theorem finiteInter_mem (cond : FiniteInter S) (F : Finset (Set α)) :
    ↑F ⊆ S → ⋂₀ (↑F : Set (Set α)) ∈ S := by
  refine Finset.induction_on F (fun _ => ?_) ?_
  · simp [cond.univ_mem]
  · intro a s _ h1 h2
    suffices a ∩ ⋂₀ ↑s ∈ S by simpa
    exact
      cond.inter_mem (h2 (Finset.mem_insert_self a s))
        (h1 fun x hx => h2 <| Finset.mem_insert_of_mem hx)
/-
**FiniteInter.finiteInterClosure_insert** 是 Mathlib 中的一个定理，位于命名空间 `FiniteInter`。
形式化陈述：finiteInterClosure_insert {A : Set α} (cond : FiniteInter S) (P) (H : P in
 finiteInterClosure (insert A S)) : P in S ∨ exists Q in S, P = A inter Q
参数：cond : FiniteInter S；P；H : P in finiteInterClosure (insert A S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteInter.univ_mem`：∀ {α : Type u_1} {S : Set (Set α)}, FiniteInter S 
→ Set.univ ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `FiniteInter.inter_mem`：∀ {α : Type u_1} {S : Set (Set α)}, FiniteInter S
 → ∀ ⦃s : Set α⦄, s ∈ S → ∀ ⦃t : Set α⦄, t ∈ S → s ∩ t ∈ S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem finiteInterClosure_insert {A : Set α} (cond : FiniteInter S) (P)
    (H : P ∈ finiteInterClosure (insert A S)) : P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q := by
  induction H with
  | basic h =>
    cases h
    · exact Or.inr ⟨Set.univ, cond.univ_mem, by simpa⟩
    · exact Or.inl (by assumption)
  | univ => exact Or.inl cond.univ_mem
  | @inter T1 T2 _ _ h1 h2 =>
    rcases h1 with (h | ⟨Q, hQ, rfl⟩) <;> rcases h2 with (i | ⟨R, hR, rfl⟩)
    · exact Or.inl (cond.inter_mem h i)
    · exact
        Or.inr ⟨T1 ∩ R, cond.inter_mem h hR, by simp only [← Set.inter_assoc, Set.inter_comm _ A]⟩
    · exact Or.inr ⟨Q ∩ T2, cond.inter_mem hQ i, by simp only [Set.inter_assoc]⟩
    · exact
        Or.inr
          ⟨Q ∩ R, cond.inter_mem hQ hR, by
            ext x
            constructor <;> simp +contextual⟩

open Set
/-
**FiniteInter.mk** 是 Mathlib 中的一个ctor，位于命名空间 `FiniteInter`。
形式化陈述：∀ {α : Type u_1} {S : Set (Set α)},   Set.univ ∈ S → (∀ ⦃s : Set α⦄, s ∈ S
 → ∀ ⦃t : Set α⦄, t ∈ S → s ∩ t ∈ S) → FiniteInter S
参数：Set α；∀ ⦃s : Set α⦄, s ∈ S → ∀ ⦃t : Set α⦄, t ∈ S → s ∩ t ∈ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk₂ (h : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s ∩ t ∈ S) :
    FiniteInter (insert (univ : Set α) S) where
  univ_mem := Set.mem_insert Set.univ S
  inter_mem s hs t ht := by aesop

end FiniteInter

/-- This is a hybrid of `Set.biUnion_empty` and `Finset.biUnion_empty` (the index set on the LHS is
the empty finset, but `s` is a family of sets, not finsets). -/
/-
**Set.biUnion_empty_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.biUnion_empty_finset {ι X : Type*} {s : ι -> Set X} : ⋃ i in (∅ : Fins
et ι), s i = ∅
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
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is a hybrid of `Set.biUnion_empty` and `Finset.biUnion_empty` (the index se
t on the LHS is
the empty finset, but `s` is a family of sets, not finsets).
-/
theorem Set.biUnion_empty_finset {ι X : Type*} {s : ι → Set X} :
    ⋃ i ∈ (∅ : Finset ι), s i = ∅ := by
  simp
