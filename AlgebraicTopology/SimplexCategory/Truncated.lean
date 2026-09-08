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

/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个实例，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {d : ℕ} {n m : Truncated d} : DecidableEq (n ⟶ m) := fun a b =>
  decidable_of_iff (a.hom.toOrderHom = b.hom.toOrderHom) (by cat_disch)

/-- For `0 < n`, the inclusion functor from the `n`-truncated simplex category to the untruncated
simplex category is initial. -/
/-
**SimplexCategory.Truncated.initial_inclusion** 是 Mathlib 中的一个实例，位于命名空间 `Simplex
Category.Truncated`。
形式化陈述：initial_inclusion {n : Nat} [NeZero n] : (inclusion n).Initial
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `CategoryTheory.Zigzag.of_inv`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₂ ⟶ j₁), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `CategoryTheory.Zigzag.of_hom`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {j₁ j₂ : J} (f : j₁ ⟶ j₂), CategoryTheory.Zigzag j₁ j₂
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a

--- 原说明 ---
For `0 < n`, the inclusion functor from the `n`-truncated simplex category to th
e untruncated
simplex category is initial.
-/
instance initial_inclusion {n : ℕ} [NeZero n] : (inclusion n).Initial := by
  have := Nat.pos_of_neZero n
  constructor
  intro Δ
  have : Nonempty (CostructuredArrow (inclusion n) Δ) := ⟨⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ 0 ⟩⟩
  apply zigzag_isConnected
  rintro ⟨⟨Δ₁, hΔ₁⟩, ⟨⟨⟩⟩, f⟩ ⟨⟨Δ₂, hΔ₂⟩, ⟨⟨⟩⟩, f'⟩
  apply Zigzag.trans (j₂ := ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f 0)⟩)
    (.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0)
  by_cases hff' : f 0 ≤ f' 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f 0) (f' 0) hff'⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
  · trans ⟨⦋1⦌ₙ, ⟨⟨⟩⟩, mkOfLe (n := Δ.len) (f' 0) (f 0) (le_of_not_ge hff')⟩
    · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 1
    · trans ⟨⦋0⦌ₙ, ⟨⟨⟩⟩, ⦋0⦌.const _ (f' 0)⟩
      · apply Zigzag.of_inv <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0
      · apply Zigzag.of_hom <| CostructuredArrow.homMk <| Hom.tr <| ⦋0⦌.const _ 0

/-- For `0 < n ≤ m`, the inclusion functor from the `n`-truncated simplex category to the
`m`-truncated simplex category is initial. -/
/-
**SimplexCategory.Truncated.initial_incl** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCateg
ory.Truncated`。
形式化陈述：initial_incl {n m : Nat} [NeZero n] (hm : n <= m) : (incl n m).Initial
参数：hm : n <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.initial_of_natIso`：initial_of_natIso {F F' : C ⥤ 
D} [Initial F] (i : F ≅ F') : Initial F' where out _
· 使用定理 `CategoryTheory.Functor.initial_of_comp_full_faithful`：initial_of_comp_fu
ll_faithful [Full G] [Faithful G] [Initial (F ⋙ G)] : Initial F where out d

--- 原说明 ---
For `0 < n ≤ m`, the inclusion functor from the `n`-truncated simplex category t
o the
`m`-truncated simplex category is initial.
-/
theorem initial_incl {n m : ℕ} [NeZero n] (hm : n ≤ m) : (incl n m).Initial := by
  have : (incl n m hm ⋙ inclusion m).Initial :=
    Functor.initial_of_natIso (inclCompInclusion (by lia)).symm
  apply Functor.initial_of_comp_full_faithful _ (inclusion m)

/-- Abbreviation for face maps in the `n`-truncated simplex category. -/
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory.Trunca
ted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for face maps in the `n`-truncated simplex category.
-/
abbrev δ (m : Nat) {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) :
  (⟨⦋n⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n + 1⦌, hn'⟩ := Hom.tr (SimplexCategory.δ i)

/-- Abbreviation for degeneracy maps in the `n`-truncated simplex category. -/
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory.Trunca
ted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for degeneracy maps in the `n`-truncated simplex category.
-/
abbrev σ (m : Nat) {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) :
    (⟨⦋n + 1⦌, hn⟩ : SimplexCategory.Truncated m) ⟶ ⟨⦋n⦌, hn'⟩ := Hom.tr (SimplexCategory.σ i)

section Two

/-- Abbreviation for face maps in the 2-truncated simplex category. -/
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory.Trunca
ted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for face maps in the 2-truncated simplex category.
-/
abbrev δ₂ {n} (i : Fin (n + 2)) (hn := by decide) (hn' := by decide) := δ 2 i hn hn'

/-- Abbreviation for face maps in the 2-truncated simplex category. -/
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimplexCategory.Trunca
ted`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation for face maps in the 2-truncated simplex category.
-/
abbrev σ₂ {n} (i : Fin (n + 1)) (hn := by decide) (hn' := by decide) := σ 2 i hn hn'

@[reassoc (attr := simp)]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_zero_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 0 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self)

@[reassoc]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_zero_comp_σ₂_one : δ₂ (0 : Fin 3) ≫ σ₂ 1 = σ₂ 0 ≫ δ₂ 0 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_le (i := 0) (j := 0) (Fin.zero_le _))

@[reassoc (attr := simp)]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_one_comp_σ₂_zero {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n) 1 hn hn' ≫ σ₂ 0 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ)

@[reassoc (attr := simp)]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_one_comp_σ₂_one {n} (hn := by decide) (hn' := by decide) :
    δ₂ (n := n + 1) 1 hn hn' ≫ σ₂ 1 hn' hn = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_self (n := n + 1) (i := 1))

@[reassoc (attr := simp)]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_two_comp_σ₂_one : δ₂ (2 : Fin 3) ≫ σ₂ 1 = 𝟙 _ :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_succ' (by decide))

@[reassoc]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_two_comp_σ₂_zero : δ₂ (2 : Fin 3) ≫ σ₂ 0 = σ₂ 0 ≫ δ₂ 1 :=
  ObjectProperty.hom_ext _ (SimplexCategory.δ_comp_σ_of_gt' (by decide))
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_one_eq_const : δ₂ (1 : Fin 2) = Hom.tr (const _ _ 0) := by decide
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_zero_eq_const : δ₂ (0 : Fin 2) = Hom.tr (const _ _ 1) := by decide

@[reassoc]
/-
**SimplexCategory.Truncated.** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategory.Truncate
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ₂_zero_comp_δ₂_two : δ₂ (0 : Fin 2) ≫ δ₂ 2 = δ₂ 1 ≫ δ₂ 0 := by decide

end Two

end SimplexCategory.Truncated

