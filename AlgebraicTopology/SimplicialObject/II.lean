/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# A construction by Gabriel and Zisman

In this file, we construct a cosimplicial object `SimplexCategory.II`
in `SimplexCategoryᵒᵖ`, i.e. a functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ`.
If we identify `SimplexCategory` with the category of finite nonempty
linearly ordered types, this functor could be interpreted as the
contravariant functor which sends a finite nonempty linearly ordered type `T`
to `T →o Fin 2` (with `f ≤ g ↔ ∀ i, g i ≤ f i`, which turns out to
be a linear order); in particular, it sends `Fin (n + 1)` to a linearly
ordered type which is isomorphic to `Fin (n + 2)`. As a result, we define
`SimplexCategory.II` as a functor which sends `⦋n⦌` to `⦋n + 1⦌`: on morphisms,
it sends faces to degeneracies and vice versa. This construction appeared
in *Calculus of fractions and homotopy theory*, chapter III, paragraph 1.1,
by Gabriel and Zisman.

## References

* [P. Gabriel, M. Zisman, *Calculus of fractions and homotopy theory*][gabriel-zisman-1967]

-/

@[expose] public section

open CategoryTheory Simplicial Opposite

namespace SimplexCategory

namespace II

variable {n m : Nat}

/--
Definition of `finset` / `finset` 的定义

English:
definition finset
  signature: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2))
  body: Finset.univ.filter (fun i => i = Fin.last _ ∨
    exists (h : i != Fin.last _), x <= (f (i.castPred h)).castSucc)

中文:
定义 finset
  签名: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2))
  定义体: Finset.univ.filter (fun i => i = Fin.last _ ∨
    exists (h : i != Fin.last _), x <= (f (i.castPred h)).castSucc)

Depends on / 依赖: Fin.last, Finset, Finset.univ.filter, castPred, castSucc, filter, i.castPred
-/
def finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i => i = Fin.last _ ∨
    exists (h : i != Fin.last _), x <= (f (i.castPred h)).castSucc)

/--
lemma `mem_finset_iff` / 引理 `mem_finset_iff`

English:
lemma mem_finset_iff
  given: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2))
  proof: by
  simp [finset]

@[simp]

中文:
引理 mem_finset_iff
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2)) (i : 有限集 (n + 2))
  证明: by
  simp [finset]

@[simp]

Depends on / 依赖: finset
-/
lemma mem_finset_iff (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 2)) :
    i in finset f x ↔ i = Fin.last _ ∨
      exists (h : i != Fin.last _), x <= (f (i.castPred h)).castSucc := by
  simp [finset]

@[simp]
/--
lemma `last_mem_finset` / 引理 `last_mem_finset`

English:
lemma last_mem_finset
  given: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2))
  proof: by
  simp [mem_finset_iff]

@[simp]

中文:
引理 last_mem_finset
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2))
  证明: by
  simp [mem_finset_iff]

@[simp]

Depends on / 依赖: mem_finset_iff
-/
lemma last_mem_finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) :
    Fin.last _ in finset f x := by
  simp [mem_finset_iff]

@[simp]
/--
lemma `castSucc_mem_finset_iff` / 引理 `castSucc_mem_finset_iff`

English:
lemma castSucc_mem_finset_iff
  proof: by
  simp [mem_finset_iff, Fin.castPred_castSucc]

中文:
引理 castSucc_mem_finset_iff
  证明: by
  simp [mem_finset_iff, Fin.castPred_castSucc]

Depends on / 依赖: Fin.castPred_castSucc, castPred_castSucc, mem_finset_iff
-/
lemma castSucc_mem_finset_iff
    (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (i : Fin (n + 1)) :
    i.castSucc in finset f x ↔ x <= (f i).castSucc := by
  simp [mem_finset_iff, Fin.castPred_castSucc]

/--
lemma `nonempty_finset` / 引理 `nonempty_finset`

English:
lemma nonempty_finset
  given: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2))
  proof: ⟨Fin.last _, by simp [mem_finset_iff]⟩

中文:
引理 nonempty_finset
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2))
  证明: ⟨Fin.last _, by simp [mem_finset_iff]⟩

Depends on / 依赖: Fin.last, mem_finset_iff
-/
lemma nonempty_finset (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) :
    (finset f x).Nonempty :=
  ⟨Fin.last _, by simp [mem_finset_iff]⟩

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2))
  body: (finset f x).min' (nonempty_finset f x)

中文:
定义 map'
  签名: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2))
  定义体: (finset f x).min' (nonempty_finset f x)

Depends on / 依赖: finset, nonempty_finset
-/
def map' (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) : Fin (n + 2) :=
  (finset f x).min' (nonempty_finset f x)

/--
lemma `map'_eq_last_iff` / 引理 `map'_eq_last_iff`

English:
lemma map'_eq_last_iff
  given: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2))
  proof: by
  simp only [map', Finset.min'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_gt (h i)

中文:
引理 map'_eq_last_iff
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2))
  证明: by
  simp only [map', Finset.min'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_gt (h i)
-/
lemma map'_eq_last_iff (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) :
    map' f x = Fin.last _ ↔ forall (i : Fin (n + 1)), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, last_mem_finset, Fin.last_le_iff, true_and]
  constructor
  · intro h i
    by_contra!
    exact i.castSucc_ne_last (h i.castSucc (by simpa))
  · intro h i hi
    by_contra!
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last this
    simp only [castSucc_mem_finset_iff] at hi
    exact hi.not_gt (h i)

/--
lemma `map'_eq_castSucc_iff` / 引理 `map'_eq_castSucc_iff`

English:
lemma map'_eq_castSucc_iff
  given: (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1))
  proof: by
  simp only [map', Finset.min'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]

中文:
引理 map'_eq_castSucc_iff
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1)) (x : 有限集 (m + 2)) (y : 有限集 (n + 1))
  证明: by
  simp only [map', Finset.min'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]
-/
lemma map'_eq_castSucc_iff (f : Fin (n + 1) ->o Fin (m + 1)) (x : Fin (m + 2)) (y : Fin (n + 1)) :
    map' f x = y.castSucc ↔ x <= (f y).castSucc ∧
      forall (i : Fin (n + 1)) (_ : i < y), (f i).castSucc < x := by
  simp only [map', Finset.min'_eq_iff, castSucc_mem_finset_iff, and_congr_right_iff]
  intro h
  constructor
  · intro h' i hi
    by_contra!
    exact hi.not_ge (by simpa using h' i.castSucc (by simpa))
  · intro h' i hi
    obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_le_castSucc_iff]
      by_contra!
      exact (h' i this).not_ge (by simpa using hi)
    · apply Fin.le_last

@[simp]
/--
lemma `map'_last` / 引理 `map'_last`

English:
lemma map'_last
  given: (f : Fin (n + 1) ->o Fin (m + 1))
  proof: by
  simp [map'_eq_last_iff]

@[simp]

中文:
引理 map'_last
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1))
  证明: by
  simp [map'_eq_last_iff]

@[simp]
-/
lemma map'_last (f : Fin (n + 1) ->o Fin (m + 1)) :
    map' f (Fin.last _) = Fin.last _ := by
  simp [map'_eq_last_iff]

@[simp]
/--
lemma `map'_zero` / 引理 `map'_zero`

English:
lemma map'_zero
  given: (f : Fin (n + 1) ->o Fin (m + 1))
  proof: by
  simp [← Fin.castSucc_zero, -Fin.castSucc_zero', map'_eq_castSucc_iff]

@[simp]

中文:
引理 map'_zero
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1))
  证明: by
  simp [← Fin.castSucc_zero, -Fin.castSucc_zero', map'_eq_castSucc_iff]

@[simp]
-/
lemma map'_zero (f : Fin (n + 1) ->o Fin (m + 1)) :
    map' f 0 = 0 := by
  simp [← Fin.castSucc_zero, -Fin.castSucc_zero', map'_eq_castSucc_iff]

@[simp]
/--
lemma `map'_id` / 引理 `map'_id`

English:
lemma map'_id
  given: (x : Fin (n + 2))
  statement: map' OrderHom.id x = x
  proof: by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    simp
  · simp

中文:
引理 map'_id
  条件: (x : 有限集 (n + 2))
  结论: map' 序态射.id x = x
  证明: by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    simp
  · simp
-/
lemma map'_id (x : Fin (n + 2)) : map' OrderHom.id x = x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · rw [map'_eq_castSucc_iff]
    simp
  · simp

/--
lemma `map'_map'` / 引理 `map'_map'`

English:
lemma map'_map'
  statement: {p : Nat} (f : Fin (n + 1) ->o Fin (m + 1))
  proof: by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · rw [hz, Eq.comm]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · rw [hz, Eq.comm]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · rw [Eq.comm, hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simp]

中文:
引理 map'_map'
  结论: {p : 自然数} (f : 有限集 (n + 1) ->o 有限集 (m + 1))
  证明: by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · rw [hz, Eq.comm]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · rw [hz, Eq.comm]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · rw [Eq.comm, hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simp]
-/
lemma map'_map' {p : Nat} (f : Fin (n + 1) ->o Fin (m + 1))
    (g : Fin (m + 1) ->o Fin (p + 1)) (x : Fin (p + 2)) :
    map' f (map' g x) = map' (g.comp f) x := by
  obtain ⟨x, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
  · obtain ⟨y, hy⟩ | hx := Fin.eq_castSucc_or_eq_last (map' g x.castSucc)
    · rw [hy]
      rw [map'_eq_castSucc_iff] at hy
      obtain ⟨z, hz⟩ | hz := Fin.eq_castSucc_or_eq_last (map' f y.castSucc)
      · rw [hz, Eq.comm]
        rw [map'_eq_castSucc_iff] at hz ⊢
        constructor
        · refine hy.1.trans ?_
          simp only [OrderHom.comp_coe, Function.comp_apply, Fin.castSucc_le_castSucc_iff]
          exact g.monotone (by simpa using hz.1)
        · intro i hi
          exact hy.2 (f i) (by simpa using hz.2 i hi)
      · rw [hz, Eq.comm]
        rw [map'_eq_last_iff] at hz ⊢
        intro i
        exact hy.2 (f i) (by simpa using hz i)
    · rw [Eq.comm, hx, map'_last]
      rw [map'_eq_last_iff] at hx ⊢
      intro i
      apply hx
  · simp

@[simp]
/--
lemma `map'_succAboveOrderEmb` / 引理 `map'_succAboveOrderEmb`

English:
lemma map'_succAboveOrderEmb
  given: {n : Nat} (i : Fin (n + 2)) (x : Fin (n + 3))
  proof: by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hx : x <= i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        simp [map'_eq_last_iff]
    · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases! h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]

中文:
引理 map'_succAboveOrderEmb
  条件: {n : 自然数} (i : 有限集 (n + 2)) (x : 有限集 (n + 3))
  证明: by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hx : x <= i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        simp [map'_eq_last_iff]
    · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases! h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]
-/
lemma map'_succAboveOrderEmb {n : Nat} (i : Fin (n + 2)) (x : Fin (n + 3)) :
    map' i.succAboveOrderEmb.toOrderHom x = i.predAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hx : x <= i
    · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa), Fin.castPred_castSucc]
      obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
      · simp only [map'_eq_castSucc_iff, OrderEmbedding.toOrderHom_coe,
          Fin.succAboveOrderEmb_apply, Fin.castSucc_le_castSucc_iff,
          Fin.castSucc_lt_castSucc_iff]
        constructor
        · obtain hx | rfl := hx.lt_or_eq
          · rwa [Fin.succAbove_of_castSucc_lt]
          · simpa only [Fin.succAbove_castSucc_self] using Fin.castSucc_le_succ x
        · intro j hj
          rwa [Fin.succAbove_of_castSucc_lt _ _ (lt_of_lt_of_le (by simpa) hx),
            Fin.castSucc_lt_castSucc_iff]
      · obtain rfl : i = Fin.last _ := Fin.last_le_iff.1 hx
        simp [map'_eq_last_iff]
    · obtain ⟨x, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx)
      rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff]),
        Fin.pred_castSucc_succ, map'_eq_castSucc_iff]
      simp only [Fin.succAbove_of_lt_succ _ _ hx,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply,
        le_refl, Fin.castSucc_lt_castSucc_iff, true_and]
      intro j hj
      by_cases! h : j.castSucc < i
      · simpa [Fin.succAbove_of_castSucc_lt _ _ h] using hj.le
      · rwa [Fin.succAbove_of_le_castSucc _ _ h, Fin.succ_lt_succ_iff]
  · simp

@[simp]
/--
lemma `map'_predAbove` / 引理 `map'_predAbove`

English:
lemma map'_predAbove
  given: {n : Nat} (i : Fin (n + 1)) (x : Fin (n + 2))
  proof: by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hi : i < x
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · simp [map'_last]

中文:
引理 map'_predAbove
  条件: {n : 自然数} (i : 有限集 (n + 1)) (x : 有限集 (n + 2))
  证明: by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hi : i < x
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · simp [map'_last]
-/
lemma map'_predAbove {n : Nat} (i : Fin (n + 1)) (x : Fin (n + 2)) :
    map' { toFun := i.predAbove, monotone' := Fin.predAbove_right_monotone i } x =
      i.succ.castSucc.succAbove x := by
  obtain ⟨x, rfl⟩ | rfl := x.eq_castSucc_or_eq_last
  · by_cases! hi : i < x
    · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc, map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · rw [Fin.predAbove_of_castSucc_lt _ _
          (by simpa only [Fin.castSucc_lt_succ_iff] using hi.le), Fin.pred_succ]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rwa [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff,
            Fin.succ_pred]
        · rw [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
          exact lt_of_le_of_lt h hi
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa), map'_eq_castSucc_iff]
      simp only [OrderHom.coe_mk, Fin.castSucc_le_castSucc_iff, Fin.castSucc_lt_castSucc_iff]
      constructor
      · simp only [i.predAbove_of_le_castSucc x.castSucc (by simpa),
          Fin.castPred_castSucc, le_refl]
      · intro j hj
        by_cases! h : i.castSucc < j
        · rw [Fin.predAbove_of_castSucc_lt _ _ h, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
          exact hj.trans x.castSucc_lt_succ
        · rwa [Fin.predAbove_of_le_castSucc _ _ h, ← Fin.castSucc_lt_castSucc_iff,
            Fin.castSucc_castPred]
  · simp [map'_last]

/--
lemma `monotone_map'` / 引理 `monotone_map'`

English:
lemma monotone_map'
  given: (f : Fin (n + 1) ->o Fin (m + 1))
  proof: by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz => by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

中文:
引理 monotone_map'
  条件: (f : 有限集 (n + 1) ->o 有限集 (m + 1))
  证明: by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz => by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

Depends on / 依赖: Finset, Finset.min, _subset, castSucc_mem_finset_iff, eq_castSucc_or_eq_last, hxy.trans, z.eq_castSucc_or_eq_last
-/
lemma monotone_map' (f : Fin (n + 1) ->o Fin (m + 1)) :
    Monotone (map' f) := by
  intro x y hxy
  exact Finset.min'_subset _ (fun z hz => by
    obtain ⟨z, rfl⟩ | rfl := z.eq_castSucc_or_eq_last
    · simp only [castSucc_mem_finset_iff] at hz ⊢
      exact hxy.trans hz
    · simp)

end II

/-- The functor `SimplexCategory ⥤ SimplexCategoryᵒᵖ` (i.e. a cosimplicial
object in `SimplexCategoryᵒᵖ`) which sends `⦋n⦌` to the object in `SimplexCategoryᵒᵖ`
that is associated to the linearly ordered type `⦋n + 1⦌` (which could be
identified to the ordered type `⦋n⦌ →o ⦋1⦌`). -/
@[simps obj]
/--
Definition of `II` / `II` 的定义

English:
definition II
  signature: : CosimplicialObject SimplexCategoryᵒᵖ where
  body: op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]

中文:
定义 II
  签名: : CosimplicialObject SimplexCategoryᵒᵖ where
  定义体: op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]

Depends on / 依赖: n.len
-/
def II : CosimplicialObject SimplexCategoryᵒᵖ where
  obj n := op ⦋n.len + 1⦌
  map f := op (Hom.mk
    { toFun := II.map' f.toOrderHom
      monotone' := II.monotone_map' _ })
  map_id n := Quiver.Hom.unop_inj (by
    ext x : 3
    exact II.map'_id x)
  map_comp {m n p} f g := Quiver.Hom.unop_inj (by
    ext x : 3
    exact (II.map'_map' _ _ _).symm)

@[simp]
/--
lemma `II_δ` / 引理 `II_δ`

English:
lemma II_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]

中文:
引理 II_δ
  条件: {n : 自然数} (i : 有限集 (n + 2))
  证明: Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]

Depends on / 依赖: II.map, Quiver, Quiver.Hom.unop_inj, _succAboveOrderEmb, unop_inj
-/
lemma II_δ {n : Nat} (i : Fin (n + 2)) :
    II.δ i = (σ i).op :=
  Quiver.Hom.unop_inj (by ext : 3; apply II.map'_succAboveOrderEmb)

@[simp]
/--
lemma `II_σ` / 引理 `II_σ`

English:
lemma II_σ
  given: {n : Nat} (i : Fin (n + 1))
  proof: Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

中文:
引理 II_σ
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

Depends on / 依赖: II.map, Quiver, Quiver.Hom.unop_inj, _predAbove, unop_inj
-/
lemma II_σ {n : Nat} (i : Fin (n + 1)) :
    II.σ i = (δ i.succ.castSucc).op :=
  Quiver.Hom.unop_inj (by ext x : 3; apply II.map'_predAbove)

end SimplexCategory
