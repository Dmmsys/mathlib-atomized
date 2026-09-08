/-
Copyright (c) 2025 Ansar Azhdarov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ansar Azhdarov
-/
module

public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn

/-!
# Teichmuller-Tukey

This file defines the notion of being of finite character for a family of sets and proves the
Teichmuller-Tukey lemma.

## Main definitions

- `IsOfFiniteCharacter` : A family of sets $F$ is of finite character iff for every set $X$,
  $X ∈ F$ iff every finite subset of $X$ is in $F$.

## Main results

- `IsOfFiniteCharacter.exists_maximal` : Teichmuller-Tukey lemma, saying that every nonempty
  family of finite character has a maximal element.

## References

- <https://en.wikipedia.org/wiki/Teichm%C3%BCller%E2%80%93Tukey_lemma>
-/

@[expose] public section

open Set Finite

variable {α : Type*} (F : Set (Set α))

namespace Order

/-- A family of sets $F$ is of finite character iff for every set $X$, $X ∈ F$ iff every finite
subset of $X$ is in $F$ -/
/-
**Order.IsOfFiniteCharacter** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：IsOfFiniteCharacter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of sets $F$ is of finite character iff for every set $X$, $X ∈ F$ iff e
very finite
subset of $X$ is in $F$
-/
def IsOfFiniteCharacter := ∀ x, x ∈ F ↔ ∀ y ⊆ x, y.Finite → y ∈ F

/-- **Teichmuller-Tukey lemma**. Every nonempty family of finite character has a maximal element. -/
/-
**Order.IsOfFiniteCharacter.exists_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsOf
FiniteCharacter`。
形式化陈述：∀ {α : Type u_1} {F : Set (Set α)},   Order.IsOfFiniteCharacter F → ∀ {x :
 Set α}, x ∈ F → ∃ m, x ⊆ m ∧ Maximal (fun x => x ∈ F) m
参数：Set α；fun x => x ∈ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion`：DirectedOn.exis
ts_mem_subset_of_finite_of_subset_sUnion {α : Type*} {c : Set (Set α)} (hn : c.N
onempty) (hc : DirectedOn (· subseteq ·) c) {…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S

--- 原说明 ---
**Teichmuller-Tukey lemma**. Every nonempty family of finite character has a max
imal element.
-/
theorem IsOfFiniteCharacter.exists_maximal {F} (hF : IsOfFiniteCharacter F) {x : Set α}
    (xF : x ∈ F) : ∃ m, x ⊆ m ∧ Maximal (· ∈ F) m := by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne ↦
    ⟨sUnion c, ?_, fun s sc ↦ subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to `F`. -/
  refine (hF (sUnion c)).mpr fun s sc sfin ↦ ?_
  /- Use the finite character property and the fact that any finite subset of the union is also a
  subset of some element of the chain. -/
  obtain ⟨t, tc, st⟩ := cch.directedOn.exists_mem_subset_of_finite_of_subset_sUnion cne sfin sc
  exact (hF t).mp (cF tc) s st sfin

end Order

