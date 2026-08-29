/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Limit

/-!
# Transfinite iteration of a function `I → I`

Given `φ : I → I` where `[SupSet I]`, we define the `j`th transfinite iteration of `φ`
for any `j : J`, with `J` a well-ordered type: this is `transfiniteIterate φ j : I → I`.
If `i₀ : I`, then `transfiniteIterate φ ⊥ i₀ = i₀`; if `j` is a non-maximal element,
then `transfiniteIterate φ (Order.succ j) i₀ = φ (transfiniteIterate φ j i₀)`; and
if `j` is a limit element, `transfiniteIterate φ j i₀` is the supremum
of the `transfiniteIterate φ l i₀` for `l < j`.

If `I` is a complete lattice, we show that `j ↦ transfiniteIterate φ j i₀` is
a monotone function if `i ≤ φ i` for all `i`. Moreover, if `i < φ i`
when `i ≠ ⊤`, we show in the lemma `top_mem_range_transfiniteIteration` that
there exists `j : J` such that `transfiniteIteration φ i₀ j = ⊤` if we assume that
`j ↦ transfiniteIterate φ i₀ j : J → I` is not injective (which shall hold
when we know `Cardinal.mk I < Cardinal.mk J`).

## TODO (@joelriou)
* deduce that in a Grothendieck abelian category, there is a *set* `I` of monomorphisms
  such that any monomorphism is a transfinite composition of pushouts of morphisms in `I`,
  and then an object `X` is injective iff `X ⟶ 0` has the right lifting
  property with respect to `I`.

-/

@[expose] public section

universe w u

section

variable {I : Type u} [SupSet I] (φ : I -> I)
  {J : Type w} [LinearOrder J] [SuccOrder J] [WellFoundedLT J]

/--
Definition of `transfiniteIterate` / `transfiniteIterate` 的定义

English:
definition transfiniteIterate
  signature: (j : J)
  body: SuccOrder.limitRecOn j
    (fun _ _ => id) (fun _ _ g => φ ∘ g) (fun y _ h => ⨆ (x : Set.Iio y), h x.1 x.2)

@[simp]

中文:
定义 transfiniteIterate
  签名: (j : J)
  定义体: SuccOrder.limitRecOn j
    (fun _ _ => id) (fun _ _ g => φ ∘ g) (fun y _ h => ⨆ (x : Set.Iio y), h x.1 x.2)

@[simp]

Depends on / 依赖: Set.Iio, SuccOrder, SuccOrder.limitRecOn, limitRecOn
-/
noncomputable def transfiniteIterate (j : J) : I -> I :=
  SuccOrder.limitRecOn j
    (fun _ _ => id) (fun _ _ g => φ ∘ g) (fun y _ h => ⨆ (x : Set.Iio y), h x.1 x.2)

@[simp]
/--
lemma `transfiniteIterate_bot` / 引理 `transfiniteIterate_bot`

English:
lemma transfiniteIterate_bot
  given: [OrderBot J] (i₀ : I)
  proof: by
  dsimp [transfiniteIterate]
  simp only [isMin_iff_eq_bot, SuccOrder.limitRecOn_isMin, id_eq]

中文:
引理 transfiniteIterate_bot
  条件: [OrderBot J] (i₀ : I)
  证明: by
  dsimp [transfiniteIterate]
  simp only [isMin_iff_eq_bot, SuccOrder.limitRecOn_isMin, id_eq]

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_isMin, id_eq, isMin_iff_eq_bot, limitRecOn_isMin, transfiniteIterate
-/
lemma transfiniteIterate_bot [OrderBot J] (i₀ : I) :
    transfiniteIterate φ (⊥ : J) i₀ = i₀ := by
  dsimp [transfiniteIterate]
  simp only [isMin_iff_eq_bot, SuccOrder.limitRecOn_isMin, id_eq]

/--
lemma `transfiniteIterate_succ` / 引理 `transfiniteIterate_succ`

English:
lemma transfiniteIterate_succ
  given: (i₀ : I) (j : J) (hj : ¬ IsMax j)
  proof: by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_succ_of_not_isMax _ _ _ hj]
  rfl

中文:
引理 transfiniteIterate_succ
  条件: (i₀ : I) (j : J) (hj : ¬ IsMax j)
  证明: by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_succ_of_not_isMax _ _ _ hj]
  rfl

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_succ_of_not_isMax, limitRecOn_succ_of_not_isMax, transfiniteIterate
-/
lemma transfiniteIterate_succ (i₀ : I) (j : J) (hj : ¬ IsMax j) :
    transfiniteIterate φ (Order.succ j) i₀ =
      φ (transfiniteIterate φ j i₀) := by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_succ_of_not_isMax _ _ _ hj]
  rfl

/--
lemma `transfiniteIterate_limit` / 引理 `transfiniteIterate_limit`

English:
lemma transfiniteIterate_limit
  given: (i₀ : I) (j : J) (hj : Order.IsSuccLimit j)
  proof: by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hj]
  simp only [iSup_apply]

中文:
引理 transfiniteIterate_limit
  条件: (i₀ : I) (j : J) (hj : Order.IsSuccLimit j)
  证明: by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hj]
  simp only [iSup_apply]

Depends on / 依赖: SuccOrder, SuccOrder.limitRecOn_of_isSuccLimit, iSup_apply, limitRecOn_of_isSuccLimit, transfiniteIterate
-/
lemma transfiniteIterate_limit (i₀ : I) (j : J) (hj : Order.IsSuccLimit j) :
    transfiniteIterate φ j i₀ =
      ⨆ (x : Set.Iio j), transfiniteIterate φ x.1 i₀ := by
  dsimp [transfiniteIterate]
  rw [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hj]
  simp only [iSup_apply]

end

section

variable {I : Type u} [CompleteLattice I] (φ : I -> I) (i₀ : I)
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/--
lemma `monotone_transfiniteIterate` / 引理 `monotone_transfiniteIterate`

English:
lemma monotone_transfiniteIterate
  given: (hφ : forall (i : I), i <= φ i)
  proof: by
  intro k j hkj
  induction j using SuccOrder.limitRecOn with
  | isMin k hk =>
    obtain rfl := hk.eq_bot
    obtain rfl : k = ⊥ := by simpa using hkj
    rfl
  | succ k' hk' hkk' =>
    obtain hkj | rfl := hkj.lt_or_eq
    · refine (hkk' ((Order.lt_succ_iff_of_not_isMax hk').mp hkj)).trans ?_


中文:
引理 monotone_transfiniteIterate
  条件: (hφ : 对任意 (i : I), i <= φ i)
  证明: by
  intro k j hkj
  induction j using SuccOrder.limitRecOn with
  | isMin k hk =>
    obtain rfl := hk.eq_bot
    obtain rfl : k = ⊥ := by simpa using hkj
    rfl
  | succ k' hk' hkk' =>
    obtain hkj | rfl := hkj.lt_or_eq
    · refine (hkk' ((Order.lt_succ_iff_of_not_isMax hk').mp hkj)).trans ?_


Depends on / 依赖: Order.lt_succ_iff_of_not_isMax, Set.Iio, SuccOrder, SuccOrder.limitRecOn, eq_bot, hk.eq_bot, hkj.lt_or_eq, isSuccLimit, le_iSup, limitRecOn, lt_or_eq, lt_succ_iff_of_not_isMax, transfiniteItera, transfiniteIterate_limit, transfiniteIterate_succ
-/
lemma monotone_transfiniteIterate (hφ : forall (i : I), i <= φ i) :
    Monotone (fun (j : J) => transfiniteIterate φ j i₀) := by
  intro k j hkj
  induction j using SuccOrder.limitRecOn with
  | isMin k hk =>
    obtain rfl := hk.eq_bot
    obtain rfl : k = ⊥ := by simpa using hkj
    rfl
  | succ k' hk' hkk' =>
    obtain hkj | rfl := hkj.lt_or_eq
    · refine (hkk' ((Order.lt_succ_iff_of_not_isMax hk').mp hkj)).trans ?_
      dsimp
      rw [transfiniteIterate_succ _ _ _ hk']
      apply hφ
    · rfl
  | isSuccLimit k' hk' _ =>
    obtain hkj | rfl := hkj.lt_or_eq
    · dsimp
      rw [transfiniteIterate_limit _ _ _ hk']
      exact le_iSup (fun (⟨l, hl⟩ : Set.Iio k') => transfiniteIterate φ l i₀) ⟨k, hkj⟩
    · rfl

/--
lemma `top_mem_range_transfiniteIterate` / 引理 `top_mem_range_transfiniteIterate`

English:
lemma top_mem_range_transfiniteIterate
  proof: by
  have hφ (i : I) : i <= φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : exists (j₁ j₂ : J) (hj : j₁ < j₂),
      transfiniteIterate φ j₁ i₀ = transfiniteIterate φ j₂ i₀ := by
    grind [Function.Injective]
  by_contra!
  suff

中文:
引理 top_mem_range_transfiniteIterate
  证明: by
  have hφ (i : I) : i <= φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : exists (j₁ j₂ : J) (hj : j₁ < j₂),
      transfiniteIterate φ j₁ i₀ = transfiniteIterate φ j₂ i₀ := by
    grind [Function.Injective]
  by_contra!
  suff

Depends on / 依赖: Function, Function.Injective, Injective, lt_of_lt_of_le, lt_self_iff_false, not_isMax_iff, transfiniteIt, transfiniteIterate
-/
lemma top_mem_range_transfiniteIterate
    (hφ' : forall i != (⊤ : I), i < φ i) (φtop : φ ⊤ = ⊤)
    (H : ¬ Function.Injective (fun (j : J) => transfiniteIterate φ j i₀)) :
    exists (j : J), transfiniteIterate φ j i₀ = ⊤ := by
  have hφ (i : I) : i <= φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : exists (j₁ j₂ : J) (hj : j₁ < j₂),
      transfiniteIterate φ j₁ i₀ = transfiniteIterate φ j₂ i₀ := by
    grind [Function.Injective]
  by_contra!
  suffices transfiniteIterate φ j₁ i₀ < transfiniteIterate φ j₂ i₀ by
    simp only [eq, lt_self_iff_false] at this
  have hj₁ : ¬ IsMax j₁ := by
    simp only [not_isMax_iff]
    exact ⟨_, hj⟩
  refine lt_of_lt_of_le (hφ' _ (this j₁)) ?_
  rw [← transfiniteIterate_succ φ i₀ j₁ hj₁]
  exact monotone_transfiniteIterate _ _ hφ (Order.succ_le_of_lt hj)

end
