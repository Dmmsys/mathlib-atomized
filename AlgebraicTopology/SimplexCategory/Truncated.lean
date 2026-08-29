/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-! # Properties of the truncated simplex category

We prove that for `n > 0`, the inclusion functor from the `n`-truncated simplex category to the
untruncated simplex category, and the inclusion functor from the `n`-truncated to the `m`-truncated
simplex category, for `n ≤ m` are initial.
-/

public section

open Simplicial CategoryTheory

namespace SimplexCategory.Truncated

instance {d : Nat} {n m : Truncated d} : DecidableEq (n ⟶ m) := fun a b =>
  decidable_of_iff (a.hom.toOrderHom = b.hom.toOrderHom) (by cat_disch)

/--
Instance `initial_inclusion` / 实例 `initial_inclusion`

English:
instance initial_inclusion
  signature: {n : Nat} [NeZero n]
  body: by
  have := Nat.pos_of_neZero n
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <|

中文:
实例 initial_inclusion
  签名: {n : 自然数} [NeZero n]
  定义体: by
  have := Nat.pos_of_neZero n
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <|

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, Hom.tr, Nat.pos_of_neZero, Nonempty, Zigzag, Zigzag.of_hom, Zigzag.trans, inclusion, mkOfLe, of_hom, of_inv, pos_of_neZero, zigzag_isConnected
-/
instance initial_inclusion {n : Nat} [NeZero n] : (inclusion n).Initial := by
  have := Nat.pos_of_neZero n
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0)
  by_cases hff' : f 0 <= f' 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f 0) (f' 0) hff'⟩
· apply Zigzag.of_hom CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 0
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
· apply Zigzag.of_inv CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 1
· apply Zigzag.of_hom CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f' 0) (f 0) (le_of_not_ge hff')⟩
· apply Zigzag.of_hom CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 1
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
· apply Zigzag.of_inv CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 0
· apply Zigzag.of_hom CostructuredArrow.homMk Hom.tr ⦋0⦌.const _ 0

/--
theorem `initial_incl` / 定理 `initial_incl`

English:
theorem initial_incl
  given: {n m : Nat} [NeZero n] (hm : n <= m)
  statement: (incl n m).Initial
  proof: by
  have : (incl n m hm ⋙ inclusion m).Initial :=
    Functor.initial_of_natIso (inclCompInclusion (by lia)).symm
  apply Functor.initial_of_comp_full_faithful _ (inclusion m)

中文:
定理 initial_incl
  条件: {n m : 自然数} [NeZero n] (hm : n <= m)
  结论: (incl n m).Initial
  证明: by
  have : (incl n m hm ⋙ inclusion m).Initial :=
    Functor.initial_of_natIso (inclCompInclusion (by lia)).symm
  apply Functor.initial_of_comp_full_faithful _ (inclusion m)

Depends on / 依赖: Functor, Functor.initial_of_comp_full_faithful, Functor.initial_of_natIso, Initial, inclCompInclusion, inclusion, initial_of_comp_full_faithful, initial_of_natIso
-/
theorem initial_incl {n m : Nat} [NeZero n] (hm : n <= m) : (incl n m).Initial := by
  have : (incl n m hm ⋙ inclusion m).Initial :=
    Functor.initial_of_natIso (inclCompInclusion (by lia)).symm
  apply Functor.initial_of_comp_full_faithful _ (inclusion m)

/--
Definition of `δ` / `δ` 的定义

English:
abbreviation δ
  signature: (m : Nat) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide)
  body: Hom.tr (SimplexCategory.δ i)

中文:
缩写 δ
  签名: (m : 自然数) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide)
  定义体: Hom.tr (SimplexCategory.δ i)

Depends on / 依赖: Hom.tr, SimplexCategory, SimplexCategory.Truncated, Truncated
-/
abbrev δ (m : Nat) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
  (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n + 1⦌, hn'⟩ := Hom.tr (SimplexCategory.δ i)

/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: (m : Nat) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide)
  body: Hom.tr (SimplexCategory.σ i)

中文:
缩写 σ
  签名: (m : 自然数) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide)
  定义体: Hom.tr (SimplexCategory.σ i)

Depends on / 依赖: Hom.tr, SimplexCategory, SimplexCategory.Truncated, Truncated
-/
abbrev σ (m : Nat) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n + 1⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n⦌, hn'⟩ := Hom.tr (SimplexCategory.σ i)

section Two

/--
Definition of `δ₂` / `δ₂` 的定义

English:
abbreviation δ₂
  signature: {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide)
  body: δ 2 i hn hn'

中文:
缩写 δ₂
  签名: {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide)
  定义体: δ 2 i hn hn'
-/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) := δ 2 i hn hn'

/--
Definition of `σ₂` / `σ₂` 的定义

English:
abbreviation σ₂
  signature: {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide)
  body: σ 2 i hn hn'

@[reassoc (attr := simp)]

中文:
缩写 σ₂
  签名: {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide)
  定义体: σ 2 i hn hn'

@[reassoc (attr := simp)]
-/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) := σ 2 i hn hn'

@[reassoc (attr := simp)]
/--
lemma `δ₂_zero_comp_σ₂_zero` / 引理 `δ₂_zero_comp_σ₂_zero`

English:
lemma δ₂_zero_comp_σ₂_zero
  given: {n} (hn := by decide) (hn' := by decide)
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self)

@[reassoc]

中文:
引理 δ₂_zero_comp_σ₂_zero
  条件: {n} (hn := by decide) (hn' := by decide)
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self)

@[reassoc]

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext
-/
lemma δ₂_zero_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 0 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self)

@[reassoc]
/--
lemma `δ₂_zero_comp_σ₂_one` / 引理 `δ₂_zero_comp_σ₂_one`

English:
lemma δ₂_zero_comp_σ₂_one
  statement: δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _))

@[reassoc (attr := simp)]

中文:
引理 δ₂_zero_comp_σ₂_one
  结论: δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _))

@[reassoc (attr := simp)]

Depends on / 依赖: Fin.zero_le, ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext, zero_le
-/
lemma δ₂_zero_comp_σ₂_one : δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _))

@[reassoc (attr := simp)]
/--
lemma `δ₂_one_comp_σ₂_zero` / 引理 `δ₂_one_comp_σ₂_zero`

English:
lemma δ₂_one_comp_σ₂_zero
  given: {n} (hn := by decide) (hn' := by decide)
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ)

@[reassoc (attr := simp)]

中文:
引理 δ₂_one_comp_σ₂_zero
  条件: {n} (hn := by decide) (hn' := by decide)
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ)

@[reassoc (attr := simp)]

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext
-/
lemma δ₂_one_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 1 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ)

@[reassoc (attr := simp)]
/--
lemma `δ₂_one_comp_σ₂_one` / 引理 `δ₂_one_comp_σ₂_one`

English:
lemma δ₂_one_comp_σ₂_one
  given: {n} (hn := by decide) (hn' := by decide)
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self (n := n + 1) (i := 1))

@[reassoc (attr := simp)]

中文:
引理 δ₂_one_comp_σ₂_one
  条件: {n} (hn := by decide) (hn' := by decide)
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self (n := n + 1) (i := 1))

@[reassoc (attr := simp)]

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext
-/
lemma δ₂_one_comp_σ₂_one {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n + 1) 1 hn hn' ≫ σ₂ 1 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self (n := n + 1) (i := 1))

@[reassoc (attr := simp)]
/--
lemma `δ₂_two_comp_σ₂_one` / 引理 `δ₂_two_comp_σ₂_one`

English:
lemma δ₂_two_comp_σ₂_one
  statement: δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ' (by decide))

@[reassoc]

中文:
引理 δ₂_two_comp_σ₂_one
  结论: δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ' (by decide))

@[reassoc]

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext
-/
lemma δ₂_two_comp_σ₂_one : δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ' (by decide))

@[reassoc]
/--
lemma `δ₂_two_comp_σ₂_zero` / 引理 `δ₂_two_comp_σ₂_zero`

English:
lemma δ₂_two_comp_σ₂_zero
  statement: δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1
  proof: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt' (by decide))

中文:
引理 δ₂_two_comp_σ₂_zero
  结论: δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1
  证明: ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt' (by decide))

Depends on / 依赖: ObjectProperty, ObjectProperty.hom_ext, SimplexCategory, hom_ext
-/
lemma δ₂_two_comp_σ₂_zero : δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt' (by decide))

/--
lemma `δ₂_one_eq_const` / 引理 `δ₂_one_eq_const`

English:
lemma δ₂_one_eq_const
  statement: δ₂ (1 : Fin 2) = Hom.tr (const _ _ 0)
  proof: by decide

中文:
引理 δ₂_one_eq_const
  结论: δ₂ (1 : Fin 2) = Hom.tr (const _ _ 0)
  证明: by decide
-/
lemma δ₂_one_eq_const : δ₂ (1 : Fin 2) = Hom.tr (const _ _ 0) := by decide

/--
lemma `δ₂_zero_eq_const` / 引理 `δ₂_zero_eq_const`

English:
lemma δ₂_zero_eq_const
  statement: δ₂ (0 : Fin 2) = Hom.tr (const _ _ 1)
  proof: by decide

@[reassoc]

中文:
引理 δ₂_zero_eq_const
  结论: δ₂ (0 : Fin 2) = Hom.tr (const _ _ 1)
  证明: by decide

@[reassoc]
-/
lemma δ₂_zero_eq_const : δ₂ (0 : Fin 2) = Hom.tr (const _ _ 1) := by decide

@[reassoc]
/--
lemma `δ₂_zero_comp_δ₂_two` / 引理 `δ₂_zero_comp_δ₂_two`

English:
lemma δ₂_zero_comp_δ₂_two
  statement: δ₂ (0 : Fin 2) ≫ δ₂ 2 = δ₂ 1 ≫ δ₂ 0
  proof: by decide

中文:
引理 δ₂_zero_comp_δ₂_two
  结论: δ₂ (0 : Fin 2) ≫ δ₂ 2 = δ₂ 1 ≫ δ₂ 0
  证明: by decide
-/
lemma δ₂_zero_comp_δ₂_two : δ₂ (0 : Fin 2) ≫ δ₂ 2 = δ₂ 1 ≫ δ₂ 0 := by decide

end Two

end SimplexCategory.Truncated
