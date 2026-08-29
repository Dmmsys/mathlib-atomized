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

/--
Definition of `FiniteInter` / `FiniteInter` 的定义

English:
structure FiniteInter
  parameters: : Prop where
  axioms and operations (2):
    - univ_mem : Set.univ in S
    - inter_mem : forall ⦃s⦄, s in S -> forall ⦃t⦄, t in S -> s inter t in S

中文:
结构 Finite整数er
  参数: : 命题 where
  公理与运算 (2 个):
    - univ_mem : 集合.univ in S
    - inter_mem : 对任意 ⦃s⦄, s in S -> 对任意 ⦃t⦄, t in S -> s inter t in S
-/
structure FiniteInter : Prop where
  /-- `univ_mem` states that `Set.univ` is in `S`. -/
  univ_mem : Set.univ in S
  /-- `inter_mem` states that any two intersections of sets in `S` is also in `S`. -/
  inter_mem : forall ⦃s⦄, s in S -> forall ⦃t⦄, t in S -> s inter t in S

namespace FiniteInter

/--
Inductive type `finiteInterClosure` / 归纳类型 `finiteInterClosure`

English:
inductive finiteInterClosure
  parameters: : Set (Set α)
  constructors (3):
    - basic: {s} : s in S -> finiteInterClosure s
    - univ: finiteInterClosure Set.univ
    - inter: {s t} : finiteInterClosure s -> finiteInterClosure t -> finiteInterClosure (s inter t)

中文:
归纳类型 finite整数erClosure
  参数: : 集合 (集合 α)
  构造子 (3 个):
    - basic: {s} : s in S -> finite整数erClosure s
    - univ: finite整数erClosure 集合.univ
    - inter: {s t} : finite整数erClosure s -> finite整数erClosure t -> finite整数erClosure (s inter t)
-/
inductive finiteInterClosure : Set (Set α)
  | basic {s} : s in S -> finiteInterClosure s
  | univ : finiteInterClosure Set.univ
  | inter {s t} : finiteInterClosure s -> finiteInterClosure t -> finiteInterClosure (s inter t)

/--
theorem `finiteInterClosure_finiteInter` / 定理 `finiteInterClosure_finiteInter`

English:
theorem finiteInterClosure_finiteInter
  statement: FiniteInter (finiteInterClosure S)
  proof: { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }

中文:
定理 finite整数erClosure_finite整数er
  结论: Finite整数er (finite整数erClosure S)
  证明: { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }

Depends on / 依赖: finiteInterClosure, finiteInterClosure.inter, finiteInterClosure.univ, inter_mem, univ_mem
-/
theorem finiteInterClosure_finiteInter : FiniteInter (finiteInterClosure S) :=
  { univ_mem := finiteInterClosure.univ
    inter_mem := fun _ h _ => finiteInterClosure.inter h }

variable {S}

/--
theorem `finiteInter_mem` / 定理 `finiteInter_mem`

English:
theorem finiteInter_mem
  given: (cond : FiniteInter S) (F : Finset (Set α))
  proof: by
  refine Finset.induction_on F (fun _ => ?_) ?_
  · simp [cond.univ_mem]
  · intro a s _ h1 h2
    suffices a inter ⋂₀ ↑s in S by simpa
    exact
      cond.inter_mem (h2 (Finset.mem_insert_self a s))
        (h1 fun x hx => h2 <| Finset.mem_insert_of_mem hx)

中文:
定理 finite整数er_mem
  条件: (cond : Finite整数er S) (F : 有限集 (集合 α))
  证明: by
  refine Finset.induction_on F (fun _ => ?_) ?_
  · simp [cond.univ_mem]
  · intro a s _ h1 h2
    suffices a inter ⋂₀ ↑s in S by simpa
    exact
      cond.inter_mem (h2 (Finset.mem_insert_self a s))
        (h1 fun x hx => h2 <| Finset.mem_insert_of_mem hx)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, cond.inter_mem, cond.univ_mem, induction_on, inter_mem, mem_insert_of_mem, mem_insert_self, univ_mem
-/
theorem finiteInter_mem (cond : FiniteInter S) (F : Finset (Set α)) :
    ↑F subseteq S -> ⋂₀ (↑F : Set (Set α)) in S := by
  refine Finset.induction_on F (fun _ => ?_) ?_
  · simp [cond.univ_mem]
  · intro a s _ h1 h2
    suffices a inter ⋂₀ ↑s in S by simpa
    exact
      cond.inter_mem (h2 (Finset.mem_insert_self a s))
        (h1 fun x hx => h2 <| Finset.mem_insert_of_mem hx)

/--
theorem `finiteInterClosure_insert` / 定理 `finiteInterClosure_insert`

English:
theorem finiteInterClosure_insert
  statement: {A : Set α} (cond : FiniteInter S) (P)
  proof: by
  induction H with
  | basic h =>
    cases h
    · exact Or.inr ⟨Set.univ, cond.univ_mem, by simpa⟩
    · exact Or.inl (by assumption)
  | univ => exact Or.inl cond.univ_mem
  | @inter T1 T2 _ _ h1 h2 =>
    rcases h1 with (h | ⟨Q, hQ, rfl⟩) <;> rcases h2 with (i | ⟨R, hR, rfl⟩)
    · exact Or.i

中文:
定理 finite整数erClosure_insert
  结论: {A : 集合 α} (cond : Finite整数er S) (P)
  证明: by
  induction H with
  | basic h =>
    cases h
    · exact Or.inr ⟨Set.univ, cond.univ_mem, by simpa⟩
    · exact Or.inl (by assumption)
  | univ => exact Or.inl cond.univ_mem
  | @inter T1 T2 _ _ h1 h2 =>
    rcases h1 with (h | ⟨Q, hQ, rfl⟩) <;> rcases h2 with (i | ⟨R, hR, rfl⟩)
    · exact Or.i

Depends on / 依赖: Or.inl, Or.inr, Set.inter_assoc, Set.inter_comm, Set.univ, cond.inter_mem, cond.univ_mem, inter_assoc, inter_comm, inter_mem, univ_mem
-/
theorem finiteInterClosure_insert {A : Set α} (cond : FiniteInter S) (P)
    (H : P in finiteInterClosure (insert A S)) : P in S ∨ exists Q in S, P = A inter Q := by
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
        Or.inr ⟨T1 inter R, cond.inter_mem h hR, by simp only [← Set.inter_assoc, Set.inter_comm _ A]⟩
    · exact Or.inr ⟨Q inter T2, cond.inter_mem hQ i, by simp only [Set.inter_assoc]⟩
    · exact
        Or.inr
          ⟨Q inter R, cond.inter_mem hQ hR, by
            ext x
            constructor <;> simp +contextual⟩

open Set

/--
theorem `mk₂` / 定理 `mk₂`

English:
theorem mk₂
  given: (h : forall ⦃s⦄, s in S -> forall ⦃t⦄, t in S -> s inter t in S)
  proof: Set.mem_insert Set.univ S
  inter_mem s hs t ht := by aesop

中文:
定理 mk₂
  条件: (h : 对任意 ⦃s⦄, s in S -> 对任意 ⦃t⦄, t in S -> s inter t in S)
  证明: Set.mem_insert Set.univ S
  inter_mem s hs t ht := by aesop

Depends on / 依赖: Set.mem_insert, Set.univ, mem_insert
-/
theorem mk₂ (h : forall ⦃s⦄, s in S -> forall ⦃t⦄, t in S -> s inter t in S) :
    FiniteInter (insert (univ : Set α) S) where
  univ_mem := Set.mem_insert Set.univ S
  inter_mem s hs t ht := by aesop

end FiniteInter

/--
theorem `Set.biUnion_empty_finset` / 定理 `Set.biUnion_empty_finset`

English:
theorem Set.biUnion_empty_finset
  given: {ι X : Type*} {s : ι -> Set X}
  proof: by
  simp

中文:
定理 集合.biUnion_empty_finset
  条件: {ι X : 类型} {s : ι -> 集合 X}
  证明: by
  simp
-/
theorem Set.biUnion_empty_finset {ι X : Type*} {s : ι -> Set X} :
    ⋃ i in (∅ : Finset ι), s i = ∅ := by
  simp
