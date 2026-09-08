/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

import Mathlib.Topology.Compactness.Compact
public import Mathlib.Data.Set.Finite.Basic

/-!
# Combinatorial compactness and the Rado selection lemma

This file contains compactness arguments for constructing infinite objects from finite
approximations. The main result is a formalization of Rado's selection principle, as an application
of compactness to combinatorics.

We give four versions, depending on whether the "partial" functions are defined locally or globally,
and whether we use `Finset` or `Set.Finite`. The precise formulation of the lemma is therefore
`Finset.rado_selection_subtype` or `Set.Finite.rado_selection_subtype`, but the versions avoiding
subtypes are easier to prove and often easier to apply, so they are provided too.

## Main results

* `Finset.rado_selection`: Given functions `g : Finset α → α → β` where `β` is finite,
  there exists a single function `χ : α → β` which is constructed out of `g`.
  More precisely, for each finite set `s`, there exists a larger set `t ⊇ s` such that
  `χ` and `g t` agree on `s`.
  In fact, we can more generally allow each `g s` to be a dependent function, as `(a : α) → β a`, so
  the type of `g` will be `Finset α → (a : α) → β a`.

* `Finset.rado_selection_subtype`: A variant where `g` takes elements in the subtype.

* `Set.Finite.rado_selection`: A variant using `Set.Finite`.

* `Set.Finite.rado_selection`: A variant using `Set.Finite` and where `g` takes elements in the
  subtype.

## Implementation notes

The proof uses the fact that the product of finite discrete spaces is compact
(by Tychonoff's theorem). The closed sets corresponding to "agreeing with `g s` on `s`"
have the finite intersection property, so their intersection is nonempty.

## References

* de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs and a problem
  in the theory of relations".
* Rado, R. (1949). "Axiomatic treatment of rank in infinite sets".

-/

public section

variable {α : Type*} {β : α → Type*} [∀ a, Finite (β a)]

/--
Given a (dependent) function `g s : (a : α) → β a` for each finset `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
/-
**Finset.rado_selection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.rado_selection (g : Finset α -> (a : α) -> β a) : exists χ : (a : α
) -> β a, forall s : Finset α, exists t : Finset α, s subseteq t ∧ forall x in s
, χ x = g t x
参数：g : Finset α -> (a : α) -> β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `discreteTopology_bot`：discreteTopology_bot (α : Type*) : @DiscreteTopolo
gy α ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Finset.continuous_restrict`：Finset.continuous_restrict (s : Finset ι) : 
Continuous (s.restrict (π
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Finset.subset_biUnion_of_mem`：subset_biUnion_of_mem (u : α -> Finset β) 
{x : α} (xs : x in s) : u x subseteq s.biUnion u
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CompactSpace.iInter_nonempty`：CompactSpace.iInter_nonempty {ι : Type v} 
[CompactSpace X] {t : ι -> Set X} (htc : forall i, IsClosed (t i)) (hst : forall
 s : Finset ι, (⋂ …
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X

--- 原说明 ---
Given a (dependent) function `g s : (a : α) → β a` for each finset `s` of `α`, p
rovided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that
 on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ
` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection (g : Finset α → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by
  classical
  let instTop (a : α) : TopologicalSpace (β a) := ⊥
  have instDiscr (a : α) : DiscreteTopology (β a) := discreteTopology_bot _
  let e (s : Finset α) : Set ((a : α) → β a) := {f | ∃ t, s ⊆ t ∧ ∀ x ∈ s, f x = g t x}
  have (s : Finset α) : s.restrict ⁻¹' {f | ∃ t, s ⊆ t ∧ ∀ x, f x = g t x} = e s := by simp [e]
  have he' (s : Finset α) : IsClosed (e s) := by
    rw [← this]
    exact (isClosed_discrete _).preimage (by fun_prop)
  have he'' (B : Finset (Finset α)) : (⋂ i ∈ B, e i).Nonempty := by
    refine ⟨g (B.biUnion id), ?_⟩
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, e]
    intro i hi
    exact ⟨_, subset_biUnion_of_mem id hi, by simp⟩
  simpa using! CompactSpace.iInter_nonempty he' he''

/--
Given a (dependent) function `g s : (a : s) → β a` for each finset `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
/-
**Finset.rado_selection_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.rado_selection_subtype (g : (s : Finset α) -> (a : s) -> β a) : exi
sts χ : (a : α) -> β a, forall s : Finset α, exists (t : Finset α) (hst : s subs
eteq t), forall x : s, χ x = g t (Set.inclusion hst x)
参数：g : (s : Finset α) -> (a : s) -> β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.rado_selection`：Finset.rado_selection (g : Finset α -> (a : α) ->
 β a) : exists χ : (a : α) -> β a, forall s : Finset α, exists t : Finset α, s s
ubseteq t ∧…

--- 原说明 ---
Given a (dependent) function `g s : (a : s) → β a` for each finset `s` of `α`, p
rovided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that
 on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ
` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Finset.rado_selection_subtype (g : (s : Finset α) → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α,
      ∃ (t : Finset α) (hst : s ⊆ t), ∀ x : s, χ x = g t (Set.inclusion hst x) := by
  classical
  have (a : α) : Nonempty (β a) := ⟨g {a} ⟨a, by simp⟩⟩
  let g' (s) (a : α) : β a := if ha : a ∈ s then g s ⟨a, ha⟩ else Classical.arbitrary (β a)
  have hg (s : Finset α) (x : s) : g s x = g' s x := by simp [g']
  simpa [hg] using Finset.rado_selection g'

/--
Given a (dependent) function `g s : (a : α) → β a` for each finite set `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
/-
**Set.Finite.rado_selection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.rado_selection (g : (s : Set α) -> s.Finite -> (a : α) -> β a) 
: exists χ : (a : α) -> β a, forall s : Set α, s.Finite -> exists (t : Set α) (h
t : t.Finite), s subseteq t ∧ forall x in s, χ x = g t ht x
参数：g : (s : Set α) -> s.Finite -> (a : α) -> β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Finset.rado_selection`：Finset.rado_selection (g : Finset α -> (a : α) ->
 β a) : exists χ : (a : α) -> β a, forall s : Finset α, exists t : Finset α, s s
ubseteq t ∧…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
Given a (dependent) function `g s : (a : α) → β a` for each finite set `s` of `α
`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that
 on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ
` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection (g : (s : Set α) → s.Finite → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite), s ⊆ t ∧ ∀ x ∈ s, χ x = g t ht x := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, ht'⟩ := hχ hs.toFinset
  exact ⟨t, by simp_all⟩

/--
Given a (dependent) function `g s : (a : s) → β a` for each finite set `s` of `α`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
/-
**Set.Finite.rado_selection_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.rado_selection_subtype (g : (s : Set α) -> s.Finite -> (a : s) 
-> β a) : exists χ : (a : α) -> β a, forall s : Set α, s.Finite -> exists (t : S
et α) (ht : t.Finite) (hst : s subseteq t), forall x : s, χ x = g t ht (Set.incl
usion hst x)
参数：g : (s : Set α) -> s.Finite -> (a : s) -> β a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Finset.rado_selection_subtype`：Finset.rado_selection_subtype (g : (s : F
inset α) -> (a : s) -> β a) : exists χ : (a : α) -> β a, forall s : Finset α, ex
ists (t : Finset α)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
Given a (dependent) function `g s : (a : s) → β a` for each finite set `s` of `α
`, provided that
each `β a` is finite, we can find another function `χ : (a : α) → β a` such that
 on every `s`,
there is some larger `t` such that `χ` agrees with `g t` on `s`.
Informally, we are stitching together the local functions `g s` into a global `χ
` such that on
each `s`, `χ` can be expressed in terms of one of the `g`.
-/
theorem Set.Finite.rado_selection_subtype (g : (s : Set α) → s.Finite → (a : s) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Set α, s.Finite →
      ∃ (t : Set α) (ht : t.Finite) (hst : s ⊆ t), ∀ x : s, χ x = g t ht (Set.inclusion hst x) := by
  obtain ⟨χ, hχ⟩ := Finset.rado_selection_subtype (β := β) (fun s ↦ g s s.finite_toSet)
  refine ⟨χ, fun s hs ↦ ?_⟩
  obtain ⟨t, ht, hst⟩ := hχ hs.toFinset
  simp only [Set.Finite.toFinset_subset] at ht
  exact ⟨t, by simp_all⟩

end

