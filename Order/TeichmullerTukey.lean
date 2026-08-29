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

/--
Definition of `IsOfFiniteCharacter` / `IsOfFiniteCharacter` 的定义

English:
definition IsOfFiniteCharacter
  body: forall x, x in F ↔ forall y subseteq x, y.Finite -> y in F

中文:
定义 IsOfFiniteCharacter
  定义体: forall x, x in F ↔ forall y subseteq x, y.Finite -> y in F

Depends on / 依赖: Finite, subseteq, y.Finite
-/
def IsOfFiniteCharacter := forall x, x in F ↔ forall y subseteq x, y.Finite -> y in F

/--
theorem `IsOfFiniteCharacter.exists_maximal` / 定理 `IsOfFiniteCharacter.exists_maximal`

English:
theorem IsOfFiniteCharacter.exists_maximal
  statement: {F} (hF : IsOfFiniteCharacter F) {x : Set α}
  proof: by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne =>
    ⟨sUnion c, ?_, fun s sc => subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to `F`. -/
  refine (hF (sUnion c)).mpr fun s sc sfin => ?_
  /- Use the finite character property and the fact that any finite subset of the union is also a
  subset of some element of the chain. -/
  obtain ⟨t, tc, st⟩ := cch.directedOn.exists_mem_subset_of_finite_of_subset_sUnion cne sfin sc
  exact (hF t).mp (cF tc) s st sfin

中文:
定理 IsOfFiniteCharacter.存在_maximal
  结论: {F} (hF : IsOfFiniteCharacter F) {x : 集合 α}
  证明: by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne =>
    ⟨sUnion c, ?_, fun s sc => subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to `F`. -/
  refine (hF (sUnion c)).mpr fun s sc sfin => ?_
  /- Use the finite character property and the fact that any finite subset of the union is also a
  subset of some element of the chain. -/
  obtain ⟨t, tc, st⟩ := cch.directedOn.exists_mem_subset_of_finite_of_subset_sUnion cne sfin sc
  exact (hF t).mp (cF tc) s st sfin
-/
theorem IsOfFiniteCharacter.exists_maximal {F} (hF : IsOfFiniteCharacter F) {x : Set α}
    (xF : x in F) : exists m, x subseteq m ∧ Maximal (· in F) m := by
  /- Apply Zorn's lemma. Take the union of the elements of a chain as its upper bound. -/
  refine zorn_subset_nonempty F (fun c cF cch cne =>
    ⟨sUnion c, ?_, fun s sc => subset_sUnion_of_mem sc⟩) x xF
  /- Prove that the union belongs to `F`. -/
  refine (hF (sUnion c)).mpr fun s sc sfin => ?_
  /- Use the finite character property and the fact that any finite subset of the union is also a
  subset of some element of the chain. -/
  obtain ⟨t, tc, st⟩ := cch.directedOn.exists_mem_subset_of_finite_of_subset_sUnion cne sfin sc
  exact (hF t).mp (cF tc) s st sfin

end Order
