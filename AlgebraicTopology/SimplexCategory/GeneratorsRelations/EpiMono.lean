/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
/-! # Epi-mono factorization in the simplex category presented by generators and relations

This file aims to establish that there is a nice epi-mono factorization in `SimplexCategoryGenRel`.
More precisely, we introduce two morphism properties `P_δ` and `P_σ` that
single out morphisms that are compositions of `δ i` (resp. `σ i`).

The main result of this file is `exists_P_σ_P_δ_factorization`, which asserts that every
morphism as a decomposition of a `P_σ` followed by a `P_δ`.

-/

@[expose] public section

namespace SimplexCategoryGenRel
open CategoryTheory

section EpiMono

/--
Definition of `splitMonoδ` / `splitMonoδ` 的定义

English:
definition splitMonoδ
  signature: {n : Nat} (i : Fin (n + 2))
  body: by
    induction i using Fin.lastCases with
    | last => exact σ (Fin.last n)
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.lastCases_castSucc]
      exact δ_comp_σ_self

中文:
定义 splitMonoδ
  签名: {n : 自然数} (i : Fin (n + 2))
  定义体: by
    induction i using Fin.lastCases with
    | last => exact σ (Fin.last n)
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.lastCases_castSucc]
      exact δ_comp_σ_self

Depends on / 依赖: Fin.last, Fin.lastCases, Fin.lastCases_castSucc, Fin.lastCases_last, lastCases, lastCases_castSucc, lastCases_last
-/
def splitMonoδ {n : Nat} (i : Fin (n + 2)) : SplitMono (δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact σ (Fin.last n)
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.lastCases_castSucc]
      exact δ_comp_σ_self

instance {n : Nat} {i : Fin (n + 2)} : IsSplitMono (δ i) := .mk' splitMonoδ i

/--
Definition of `splitEpiσ` / `splitEpiσ` 的定义

English:
definition splitEpiσ
  signature: {n : Nat} (i : Fin (n + 1))
  body: δ i.castSucc
  id := δ_comp_σ_self

中文:
定义 splitEpiσ
  签名: {n : 自然数} (i : Fin (n + 1))
  定义体: δ i.castSucc
  id := δ_comp_σ_self
-/
def splitEpiσ {n : Nat} (i : Fin (n + 1)) : SplitEpi (σ i) where
  section_ := δ i.castSucc
  id := δ_comp_σ_self

instance {n : Nat} {i : Fin (n + 1)} : IsSplitEpi (σ i) := .mk' splitEpiσ i

/--
Definition of `P_σ` / `P_σ` 的定义

English:
abbreviation P_σ
  body: degeneracies.multiplicativeClosure

中文:
缩写 P_σ
  定义体: degeneracies.multiplicativeClosure

Depends on / 依赖: degeneracies, degeneracies.multiplicativeClosure, multiplicativeClosure
-/
abbrev P_σ := degeneracies.multiplicativeClosure

/--
Definition of `P_δ` / `P_δ` 的定义

English:
abbreviation P_δ
  body: faces.multiplicativeClosure

中文:
缩写 P_δ
  定义体: faces.multiplicativeClosure

Depends on / 依赖: faces.multiplicativeClosure, multiplicativeClosure
-/
abbrev P_δ := faces.multiplicativeClosure

/--
lemma `P_σ.σ` / 引理 `P_σ.σ`

English:
lemma P_σ.σ
  given: {n : Nat} (i : Fin (n + 1))
  statement: P_σ (σ i)
  proof: .of _ (.σ i)

中文:
引理 P_σ.σ
  条件: {n : 自然数} (i : Fin (n + 1))
  结论: P_σ (σ i)
  证明: .of _ (.σ i)
-/
lemma P_σ.σ {n : Nat} (i : Fin (n + 1)) : P_σ (σ i) := .of _ (.σ i)

/--
lemma `P_δ.δ` / 引理 `P_δ.δ`

English:
lemma P_δ.δ
  given: {n : Nat} (i : Fin (n + 2))
  statement: P_δ (δ i)
  proof: .of _ (.δ i)

中文:
引理 P_δ.δ
  条件: {n : 自然数} (i : Fin (n + 2))
  结论: P_δ (δ i)
  证明: .of _ (.δ i)
-/
lemma P_δ.δ {n : Nat} (i : Fin (n + 2)) : P_δ (δ i) := .of _ (.δ i)

/--
lemma `isSplitEpi_P_σ` / 引理 `isSplitEpi_P_σ`

English:
lemma isSplitEpi_P_σ
  given: {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e)
  statement: IsSplitEpi e
  proof: by
  induction he with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

中文:
引理 isSplitEpi_P_σ
  条件: {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e)
  结论: IsSplitEpi e
  证明: by
  induction he with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

Depends on / 依赖: comp_of, infer_instance
-/
lemma isSplitEpi_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e) : IsSplitEpi e := by
  induction he with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

/--
lemma `isSplitMono_P_δ` / 引理 `isSplitMono_P_δ`

English:
lemma isSplitMono_P_δ
  given: {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m)
  proof: by
  induction hm with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

中文:
引理 isSplitMono_P_δ
  条件: {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m)
  证明: by
  induction hm with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

Depends on / 依赖: comp_of, infer_instance
-/
lemma isSplitMono_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    IsSplitMono m := by
  induction hm with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

/--
lemma `isSplitEpi_toSimplexCategory_map_of_P_σ` / 引理 `isSplitEpi_toSimplexCategory_map_of_P_σ`

English:
lemma isSplitEpi_toSimplexCategory_map_of_P_σ
  statement: {x y : SimplexCategoryGenRel} {e : x ⟶ y}
  proof: by
  constructor
  constructor
  apply SplitEpi.map
.exists_splitEpi.some exact isSplitEpi_P_σ he

中文:
引理 isSplitEpi_toSimplexCategory_map_of_P_σ
  结论: {x y : SimplexCategoryGenRel} {e : x ⟶ y}
  证明: by
  constructor
  constructor
  apply SplitEpi.map
.exists_splitEpi.some exact isSplitEpi_P_σ he

Depends on / 依赖: SplitEpi, SplitEpi.map, exists_splitEpi, exists_splitEpi.some
-/
lemma isSplitEpi_toSimplexCategory_map_of_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y}
(he : P_σ e) : IsSplitEpi toSimplexCategory.map e := by
  constructor
  constructor
  apply SplitEpi.map
.exists_splitEpi.some exact isSplitEpi_P_σ he

/--
lemma `isSplitMono_toSimplexCategory_map_of_P_δ` / 引理 `isSplitMono_toSimplexCategory_map_of_P_δ`

English:
lemma isSplitMono_toSimplexCategory_map_of_P_δ
  statement: {x y : SimplexCategoryGenRel} {m : x ⟶ y}
  proof: by
  constructor
  constructor
  apply SplitMono.map
.exists_splitMono.some exact isSplitMono_P_δ hm

中文:
引理 isSplitMono_toSimplexCategory_map_of_P_δ
  结论: {x y : SimplexCategoryGenRel} {m : x ⟶ y}
  证明: by
  constructor
  constructor
  apply SplitMono.map
.exists_splitMono.some exact isSplitMono_P_δ hm

Depends on / 依赖: SplitMono, SplitMono.map, exists_splitMono, exists_splitMono.some
-/
lemma isSplitMono_toSimplexCategory_map_of_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y}
(hm : P_δ m) : IsSplitMono toSimplexCategory.map m := by
  constructor
  constructor
  apply SplitMono.map
.exists_splitMono.some exact isSplitMono_P_δ hm

/--
lemma `eq_or_len_le_of_P_δ` / 引理 `eq_or_len_le_of_P_δ`

English:
lemma eq_or_len_le_of_P_δ
  given: {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f)
  proof: by
  induction h_δ with
  | of _ hx => cases hx; right; simp
  | id => left; use rfl; simp
  | comp_of i u _ hg h' =>
    rcases h' with ⟨e, _⟩ | h' <;>
    apply Or.inr <;>
    cases hg
    · rw [e]
      exact Nat.lt_add_one _
    · exact Nat.lt_succ_of_lt h'

中文:
引理 eq_or_len_le_of_P_δ
  条件: {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f)
  证明: by
  induction h_δ with
  | of _ hx => cases hx; right; simp
  | id => left; use rfl; simp
  | comp_of i u _ hg h' =>
    rcases h' with ⟨e, _⟩ | h' <;>
    apply Or.inr <;>
    cases hg
    · rw [e]
      exact Nat.lt_add_one _
    · exact Nat.lt_succ_of_lt h'

Depends on / 依赖: Nat.lt_add_one, Nat.lt_succ_of_lt, Or.inr, comp_of, lt_add_one, lt_succ_of_lt
-/
lemma eq_or_len_le_of_P_δ {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f) :
    (exists h : x = y, f = eqToHom h) ∨ x.len < y.len := by
  induction h_δ with
  | of _ hx => cases hx; right; simp
  | id => left; use rfl; simp
  | comp_of i u _ hg h' =>
    rcases h' with ⟨e, _⟩ | h' <;>
    apply Or.inr <;>
    cases hg
    · rw [e]
      exact Nat.lt_add_one _
    · exact Nat.lt_succ_of_lt h'

end EpiMono

section ExistenceOfFactorizations

/--
lemma `switch_δ_σ` / 引理 `switch_δ_σ`

English:
lemma switch_δ_σ
  given: {n : Nat} (i : Fin (n + 2)) (i' : Fin (n + 3))
  proof: by
  obtain h | rfl | h := lt_trichotomy i.castSucc i'
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | rfl := h.lt_or_eq
    · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
      rw [Fin.succ_lt_succ_iff] at h
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_la

中文:
引理 switch_δ_σ
  条件: {n : 自然数} (i : Fin (n + 2)) (i' : Fin (n + 3))
  证明: by
  obtain h | rfl | h := lt_trichotomy i.castSucc i'
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | rfl := h.lt_or_eq
    · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
      rw [Fin.succ_lt_succ_iff] at h
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_la
-/
private lemma switch_δ_σ {n : Nat} (i : Fin (n + 2)) (i' : Fin (n + 3)) :
    δ i' ≫ σ i = 𝟙 _ ∨ exists j j', δ i' ≫ σ i = σ j ≫ δ j' := by
  obtain h | rfl | h := lt_trichotomy i.castSucc i'
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | rfl := h.lt_or_eq
    · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
      rw [Fin.succ_lt_succ_iff] at h
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
      exact Or.inr ⟨i, i', by rw [δ_comp_σ_of_gt h]⟩
    · exact Or.inl δ_comp_σ_succ
  · exact Or.inl δ_comp_σ_self
  · obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
    rw [Fin.castSucc_lt_castSucc_iff] at h
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
    rw [← Fin.le_castSucc_iff] at h
    exact Or.inr ⟨i, i', by rw [δ_comp_σ_of_le h]⟩

/--
lemma `switch_δ_σ₀` / 引理 `switch_δ_σ₀`

English:
lemma switch_δ_σ₀
  given: (i : Fin 1) (i' : Fin 2)
  proof: by
  fin_cases i; fin_cases i'
  · exact δ_comp_σ_self
  · exact δ_comp_σ_succ

中文:
引理 switch_δ_σ₀
  条件: (i : Fin 1) (i' : Fin 2)
  证明: by
  fin_cases i; fin_cases i'
  · exact δ_comp_σ_self
  · exact δ_comp_σ_succ
-/
private lemma switch_δ_σ₀ (i : Fin 1) (i' : Fin 2) :
    δ i' ≫ σ i = 𝟙 _ := by
  fin_cases i; fin_cases i'
  · exact δ_comp_σ_self
  · exact δ_comp_σ_succ

/--
lemma `factor_δ_σ` / 引理 `factor_δ_σ`

English:
lemma factor_δ_σ
  given: {n : Nat} (i : Fin (n + 1)) (i' : Fin (n + 2))
  proof: by
  cases n with
  | zero => exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [switch_δ_σ₀]⟩
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i'
    · exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [h]⟩
    · exact ⟨_, _, _, P_σ.σ _, P_δ.δ _, h⟩

中文:
引理 factor_δ_σ
  条件: {n : 自然数} (i : Fin (n + 1)) (i' : Fin (n + 2))
  证明: by
  cases n with
  | zero => exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [switch_δ_σ₀]⟩
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i'
    · exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [h]⟩
    · exact ⟨_, _, _, P_σ.σ _, P_δ.δ _, h⟩
-/
private lemma factor_δ_σ {n : Nat} (i : Fin (n + 1)) (i' : Fin (n + 2)) :
    exists (z : SimplexCategoryGenRel) (e : mk n ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), δ i' ≫ σ i = e ≫ m := by
  cases n with
  | zero => exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [switch_δ_σ₀]⟩
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i'
    · exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [h]⟩
    · exact ⟨_, _, _, P_σ.σ _, P_δ.δ _, h⟩

/--
lemma `factor_P_δ_σ` / 引理 `factor_P_δ_σ`

English:
lemma factor_P_δ_σ
  statement: {n : Nat} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
  proof: by
  induction n generalizing x with
  | zero => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of j f hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | hf' := eq_or_len_le_of_P_δ hf
      · simpa using facto

中文:
引理 factor_P_δ_σ
  结论: {n : 自然数} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
  证明: by
  induction n generalizing x with
  | zero => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of j f hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | hf' := eq_or_len_le_of_P_δ hf
      · simpa using facto
-/
private lemma factor_P_δ_σ {n : Nat} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) : exists (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), f ≫ σ i = e ≫ m := by
  induction n generalizing x with
  | zero => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of j f hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | hf' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · simp at hf'
  | succ n hn =>
    cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id n => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of f g hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | h' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · obtain h'' | ⟨j, j', h''⟩ := switch_δ_σ i k
        · exact ⟨_, _, _, P_σ.id_mem _, hf, by simp [h'']⟩
        · obtain ⟨z, e, m, he, hm, fac⟩ := hn j f hf
          exact ⟨z, e, m ≫ δ j', he, P_δ.comp_mem _ _ hm (P_δ.δ j'),
            by simp [h'', reassoc_of% fac]⟩

/--
theorem `exists_P_σ_P_δ_factorization` / 定理 `exists_P_σ_P_δ_factorization`

English:
theorem exists_P_σ_P_δ_factorization
  given: {x y : SimplexCategoryGenRel} (f : x ⟶ y)
  proof: by
  induction f with
  | @id n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id_mem _, P_δ.id_mem _; simp
  | @comp_δ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    exact ⟨z, e, m ≫ δ j, he, P_δ.comp_mem _ _ hm (P_δ.δ _), by simp⟩
  | @comp_σ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl

中文:
定理 exists_P_σ_P_δ_factorization
  条件: {x y : SimplexCategoryGenRel} (f : x ⟶ y)
  证明: by
  induction f with
  | @id n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id_mem _, P_δ.id_mem _; simp
  | @comp_δ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    exact ⟨z, e, m ≫ δ j, he, P_δ.comp_mem _ _ hm (P_δ.δ _), by simp⟩
  | @comp_σ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl

Depends on / 依赖: comp_mem, id_mem
-/
theorem exists_P_σ_P_δ_factorization {x y : SimplexCategoryGenRel} (f : x ⟶ y) :
    exists (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ y)
        (_ : P_σ e) (_ : P_δ m), f = e ≫ m := by
  induction f with
  | @id n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id_mem _, P_δ.id_mem _; simp
  | @comp_δ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    exact ⟨z, e, m ≫ δ j, he, P_δ.comp_mem _ _ hm (P_δ.δ _), by simp⟩
  | @comp_σ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    cases hm with
    | of g hg =>
      rcases hg with ⟨i⟩
      obtain ⟨_, _, _, ⟨he₁, hm₁, h₁⟩⟩ := factor_δ_σ j i
      exact ⟨_, _, _, P_σ.comp_mem _ _ he he₁, hm₁,
        by simp [← h₁]⟩
    | @id n =>
      exact ⟨mk n', e ≫ σ j, 𝟙 _, P_σ.comp_mem _ _ he (P_σ.σ _), P_δ.id_mem _, by simp⟩
    | comp_of f g hf hg =>
      cases n' with
      | zero =>
        cases hg
        exact ⟨_, _, _, he, hf, by simp [switch_δ_σ₀]⟩
      | succ n =>
        rcases hg with ⟨i⟩
        obtain h' | ⟨j', j'', h'⟩ := switch_δ_σ j i
        · exact ⟨_, _, _, he, hf, by simp [h']⟩
        · obtain ⟨_, _, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_P_δ_σ j' f hf
          exact ⟨_, _, m₁ ≫ δ j'', P_σ.comp_mem _ _ he he₁, P_δ.comp_mem _ _ hm₁ (P_δ.δ _),
            by simp [← reassoc_of% h₁, h']⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasFactorization P_σ P_δ
  body: by
    obtain ⟨z, e, m, he, hm, fac⟩ := exists_P_σ_P_δ_factorization f
    exact ⟨⟨z, e, m, fac.symm, he, hm⟩⟩

中文:
实例 :
  签名: Morphism命题erty.HasFactorization P_σ P_δ
  定义体: by
    obtain ⟨z, e, m, he, hm, fac⟩ := exists_P_σ_P_δ_factorization f
    exact ⟨⟨z, e, m, fac.symm, he, hm⟩⟩

Depends on / 依赖: fac.symm
-/
instance : MorphismProperty.HasFactorization P_σ P_δ where
  nonempty_mapFactorizationData f := by
    obtain ⟨z, e, m, he, hm, fac⟩ := exists_P_σ_P_δ_factorization f
    exact ⟨⟨z, e, m, fac.symm, he, hm⟩⟩

end ExistenceOfFactorizations

end SimplexCategoryGenRel
