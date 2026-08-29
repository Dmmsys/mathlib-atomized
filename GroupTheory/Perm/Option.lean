/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutations of `Option α`
-/

@[expose] public section


open Equiv

@[simp]
/--
theorem `Equiv.optionCongr_one` / 定理 `Equiv.optionCongr_one`

English:
theorem Equiv.optionCongr_one
  given: {α : Type*}
  statement: (1 : Perm α).optionCongr = 1
  proof: Equiv.optionCongr_refl

@[simp]

中文:
定理 Equiv.optionCongr_one
  条件: {α : 类型}
  结论: (1 : Perm α).optionCongr = 1
  证明: Equiv.optionCongr_refl

@[simp]

Depends on / 依赖: Equiv.optionCongr_refl, optionCongr_refl
-/
theorem Equiv.optionCongr_one {α : Type*} : (1 : Perm α).optionCongr = 1 :=
  Equiv.optionCongr_refl

@[simp]
/--
theorem `Equiv.optionCongr_swap` / 定理 `Equiv.optionCongr_swap`

English:
theorem Equiv.optionCongr_swap
  given: {α : Type*} [DecidableEq α] (x y : α)
  proof: by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    · simp only [hx, optionCongr_apply, Option.map_some, swap_apply_left,
             Option.some.injEq]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]

@[simp]

中文:
定理 Equiv.optionCongr_swap
  条件: {α : 类型} [DecidableEq α] (x y : α)
  证明: by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    · simp only [hx, optionCongr_apply, Option.map_some, swap_apply_left,
             Option.some.injEq]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]

@[simp]

Depends on / 依赖: Option.map_some, Option.some.injEq, map_some, optionCongr_apply, swap_apply_left, swap_apply_of_ne_of_ne
-/
theorem Equiv.optionCongr_swap {α : Type*} [DecidableEq α] (x y : α) :
    optionCongr (swap x y) = swap (some x) (some y) := by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    · simp only [hx, optionCongr_apply, Option.map_some, swap_apply_left,
             Option.some.injEq]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]

@[simp]
/--
theorem `Equiv.optionCongr_sign` / 定理 `Equiv.optionCongr_sign`

English:
theorem Equiv.optionCongr_sign
  given: {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α)
  proof: by
  induction e using Perm.swap_induction_on with
  | one => simp [Perm.one_def]
  | swap_mul f x y hne h =>
    simp [h, hne, Perm.mul_def]

@[simp]

中文:
定理 Equiv.optionCongr_sign
  条件: {α : 类型} [DecidableEq α] [Fintype α] (e : Perm α)
  证明: by
  induction e using Perm.swap_induction_on with
  | one => simp [Perm.one_def]
  | swap_mul f x y hne h =>
    simp [h, hne, Perm.mul_def]

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, AlgHom.rangeRestrict_surjective, EquivLike, EquivLike.comp_surjective, Perm.mul_def, Perm.one_def, Perm.swap_induction_on, coe_comp, coe_toAlgHom, comp_surjective, mulMap, mul_def, one_def, rangeRestrict_surjective, simp_rw, swap_induction_on, swap_mul
-/
theorem Equiv.optionCongr_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign e.optionCongr = Perm.sign e := by
  induction e using Perm.swap_induction_on with
  | one => simp [Perm.one_def]
  | swap_mul f x y hne h =>
    simp [h, hne, Perm.mul_def]

@[simp]
/--
theorem `map_equiv_removeNone` / 定理 `map_equiv_removeNone`

English:
theorem map_equiv_removeNone
  given: {α : Type*} [DecidableEq α] (σ : Perm (Option α))
  proof: by
  ext1 x
  have : Option.map (⇑(removeNone σ)) x = (swap none (σ none)) (σ x) := by
    obtain - | x := x
    · simp
    · cases h : σ (some _)
      · simp [removeNone_none _ h]
      · have hn : σ (some x) != none := by simp [h]
        have hσn : σ (some x) != σ none := σ.injective.ne (by simp

中文:
定理 map_equiv_removeNone
  条件: {α : 类型} [DecidableEq α] (σ : Perm (Option α))
  证明: by
  ext1 x
  have : Option.map (⇑(removeNone σ)) x = (swap none (σ none)) (σ x) := by
    obtain - | x := x
    · simp
    · cases h : σ (some _)
      · simp [removeNone_none _ h]
      · have hn : σ (some x) != none := by simp [h]
        have hσn : σ (some x) != σ none := σ.injective.ne (by simp

Depends on / 依赖: Option.map, injective, injective.ne, removeNone, removeNone_none, removeNone_some, swap_apply_of_ne_of_ne
-/
theorem map_equiv_removeNone {α : Type*} [DecidableEq α] (σ : Perm (Option α)) :
    (removeNone σ).optionCongr = swap none (σ none) * σ := by
  ext1 x
  have : Option.map (⇑(removeNone σ)) x = (swap none (σ none)) (σ x) := by
    obtain - | x := x
    · simp
    · cases h : σ (some _)
      · simp [removeNone_none _ h]
      · have hn : σ (some x) != none := by simp [h]
        have hσn : σ (some x) != σ none := σ.injective.ne (by simp)
        simp [removeNone_some _ ⟨_, h⟩, ← h, swap_apply_of_ne_of_ne hn hσn]
  simpa using this

/-- Permutations of `Option α` are equivalent to fixing an
`Option α` and permuting the remaining with a `Perm α`.
The fixed `Option α` is swapped with `none`. -/
@[simps]
/--
Definition of `Equiv.Perm.decomposeOption` / `Equiv.Perm.decomposeOption` 的定义

English:
definition Equiv.Perm.decomposeOption
  signature: {α : Type*} [DecidableEq α]
  body: (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ => by
    have : removeNone (swap none x * σ.optionCongr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [this]

中文:
定义 Equiv.Perm.decomposeOption
  签名: {α : 类型} [DecidableEq α]
  定义体: (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ => by
    have : removeNone (swap none x * σ.optionCongr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [this]

Depends on / 依赖: removeNone
-/
def Equiv.Perm.decomposeOption {α : Type*} [DecidableEq α] :
    Perm (Option α) ≃ Option α × Perm α where
  toFun σ := (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ => by
    have : removeNone (swap none x * σ.optionCongr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [this]

/--
theorem `Equiv.Perm.decomposeOption_symm_of_none_apply` / 定理 `Equiv.Perm.decomposeOption_symm_of_none_apply`

English:
theorem Equiv.Perm.decomposeOption_symm_of_none_apply
  statement: {α : Type*} [DecidableEq α] (e : Perm α)
  proof: by simp

中文:
定理 Equiv.Perm.decomposeOption_symm_of_none_apply
  结论: {α : 类型} [DecidableEq α] (e : Perm α)
  证明: by simp
-/
theorem Equiv.Perm.decomposeOption_symm_of_none_apply {α : Type*} [DecidableEq α] (e : Perm α)
    (i : Option α) : Equiv.Perm.decomposeOption.symm (none, e) i = i.map e := by simp

/--
theorem `Equiv.Perm.decomposeOption_symm_sign` / 定理 `Equiv.Perm.decomposeOption_symm_sign`

English:
theorem Equiv.Perm.decomposeOption_symm_sign
  given: {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α)
  proof: by simp

中文:
定理 Equiv.Perm.decomposeOption_symm_sign
  条件: {α : 类型} [DecidableEq α] [Fintype α] (e : Perm α)
  证明: by simp
-/
theorem Equiv.Perm.decomposeOption_symm_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = Perm.sign e := by simp

/--
theorem `Finset.univ_perm_option` / 定理 `Finset.univ_perm_option`

English:
theorem Finset.univ_perm_option
  given: {α : Type*} [DecidableEq α] [Fintype α]
  proof: (Finset.univ_map_equiv_to_embedding _).symm

中文:
定理 Finset.univ_perm_option
  条件: {α : 类型} [DecidableEq α] [Fintype α]
  证明: (Finset.univ_map_equiv_to_embedding _).symm

Depends on / 依赖: Finset, Finset.univ_map_equiv_to_embedding, univ_map_equiv_to_embedding
-/
theorem Finset.univ_perm_option {α : Type*} [DecidableEq α] [Fintype α] :
    @Finset.univ (Perm <| Option α) _ =
      (Finset.univ : Finset <| Option α × Perm α).map Equiv.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm
