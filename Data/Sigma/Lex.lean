/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Unbundled
public import Batteries.Logic

/-!
# Lexicographic order on a sigma type

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `PSigma.Lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `Combinatorics.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i` per say.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `Sigma.Lex` where all summands are the same
-/

public section


namespace Sigma

variable {ι : Type*} {α : ι -> Type*} {r r₁ r₂ : ι -> ι -> Prop} {s s₁ s₂ : forall i, α i -> α i -> Prop}
  {a b : Σ i, α i}

/--
Inductive type `Lex` / 归纳类型 `Lex`

English:
inductive Lex
  parameters: (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop)
  constructors (2):
    - left: {i j : ι} (a : α i) (b : α j) : r i j -> Lex r s ⟨i, a⟩ ⟨j, b⟩
    - right: {i : ι} (a b : α i) : s i a b -> Lex r s ⟨i, a⟩ ⟨i, b⟩

中文:
归纳类型 Lex
  参数: (r : ι -> ι -> 命题) (s : 对任意 i, α i -> α i -> 命题)
  构造子 (2 个):
    - left: {i j : ι} (a : α i) (b : α j) : r i j -> Lex r s ⟨i, a⟩ ⟨j, b⟩
    - right: {i : ι} (a b : α i) : s i a b -> Lex r s ⟨i, a⟩ ⟨i, b⟩
-/
inductive Lex (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) : forall _ _ : Σ i, α i, Prop
  | left {i j : ι} (a : α i) (b : α j) : r i j -> Lex r s ⟨i, a⟩ ⟨j, b⟩
  | right {i : ι} (a b : α i) : s i a b -> Lex r s ⟨i, a⟩ ⟨i, b⟩

/--
theorem `lex_iff` / 定理 `lex_iff`

English:
theorem lex_iff
  statement: Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1, s b.1 (h.rec a.2) b.2
  proof: by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ _ h

中文:
定理 lex_iff
  结论: Lex r s a b ↔ r a.1 b.1 ∨ 存在 h : a.1 = b.1, s b.1 (h.rec a.2) b.2
  证明: by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ _ h

Depends on / 依赖: Lex.left, Lex.right, Or.inl, Or.inr
-/
theorem lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ _ h

/--
Instance `Lex.decidable` / 实例 `Lex.decidable`

English:
instance Lex.decidable
  signature: (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) [DecidableEq ι]
  body: fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm

中文:
实例 Lex.decidable
  签名: (r : ι -> ι -> 命题) (s : 对任意 i, α i -> α i -> 命题) [DecidableEq ι]
  定义体: fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
-/
instance Lex.decidable (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) [DecidableEq ι]
    [DecidableRel r] [forall i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm

/--
theorem `Lex.mono` / 定理 `Lex.mono`

English:
theorem Lex.mono
  statement: (hr : forall a b, r₁ a b -> r₂ a b) (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i}
  proof: by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ _ (hs _ _ _ hab)

中文:
定理 Lex.mono
  结论: (hr : 对任意 a b, r₁ a b -> r₂ a b) (hs : 对任意 i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i}
  证明: by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ _ (hs _ _ _ hab)

Depends on / 依赖: Lex.left, Lex.right
-/
theorem Lex.mono (hr : forall a b, r₁ a b -> r₂ a b) (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ _ (hs _ _ _ hab)

/--
theorem `Lex.mono_left` / 定理 `Lex.mono_left`

English:
theorem Lex.mono_left
  given: (hr : forall a b, r₁ a b -> r₂ a b) {a b : Σ i, α i} (h : Lex r₁ s a b)
  proof: h.mono hr fun _ _ _ => id

中文:
定理 Lex.mono_left
  条件: (hr : 对任意 a b, r₁ a b -> r₂ a b) {a b : Σ i, α i} (h : Lex r₁ s a b)
  证明: h.mono hr fun _ _ _ => id

Depends on / 依赖: h.mono
-/
theorem Lex.mono_left (hr : forall a b, r₁ a b -> r₂ a b) {a b : Σ i, α i} (h : Lex r₁ s a b) :
    Lex r₂ s a b :=
  h.mono hr fun _ _ _ => id

/--
theorem `Lex.mono_right` / 定理 `Lex.mono_right`

English:
theorem Lex.mono_right
  given: (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i} (h : Lex r s₁ a b)
  proof: h.mono (fun _ _ => id) hs

中文:
定理 Lex.mono_right
  条件: (hs : 对任意 i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i} (h : Lex r s₁ a b)
  证明: h.mono (fun _ _ => id) hs

Depends on / 依赖: h.mono
-/
theorem Lex.mono_right (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ i, α i} (h : Lex r s₁ a b) :
    Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs

/--
theorem `lex_swap` / 定理 `lex_swap`

English:
theorem lex_swap
  statement: Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a
  proof: by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      · exact Lex.left _ _ h
      · exact Lex.right _ _ h

中文:
定理 lex_swap
  结论: Lex (函数.swap r) s a b ↔ Lex r (fun i => 函数.swap (s i)) b a
  证明: by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      · exact Lex.left _ _ h
      · exact Lex.right _ _ h

Depends on / 依赖: Lex.left, Lex.right
-/
theorem lex_swap : Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a := by
  constructor <;>
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      · exact Lex.left _ _ h
      · exact Lex.right _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Std.Refl (s i)] : Std.Refl (Lex r s)
  body: ⟨fun ⟨_, _⟩ => Lex.right _ _ refl _⟩

中文:
实例 [对任意
  签名: i, Std.Refl (s i)] : Std.Refl (Lex r s)
  定义体: ⟨fun ⟨_, _⟩ => Lex.right _ _ refl _⟩

Depends on / 依赖: Lex.right
-/
instance [forall i, Std.Refl (s i)] : Std.Refl (Lex r s) :=
⟨fun ⟨_, _⟩ => Lex.right _ _ refl _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] [forall i, Std.Irrefl (s i)] : Std.Irrefl (Lex r s)
  body: ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    · exact irrefl _ hi
    · exact irrefl _ ha
      ⟩

中文:
实例 [Std.Irrefl
  签名: r] [对任意 i, Std.Irrefl (s i)] : Std.Irrefl (Lex r s)
  定义体: ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    · exact irrefl _ hi
    · exact irrefl _ ha
      ⟩

Depends on / 依赖: Finite, FiniteIndex, finiteIndex_of_finite, irrefl
-/
instance [Std.Irrefl r] [forall i, Std.Irrefl (s i)] : Std.Irrefl (Lex r s) :=
  ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    · exact irrefl _ hi
    · exact irrefl _ ha
      ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: ι r] [forall i, IsTrans (α i) (s i)] : IsTrans _ (Lex r s)
  body: ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact Lex.left _ _ (_root_.trans hij hk)
    · exact Lex.left _ _ hij
    · exact Lex.left _ _ hk
    · exact Lex.right _ _ (_root_.trans hab hc)⟩

中文:
实例 [是Trans
  签名: ι r] [对任意 i, 是Trans (α i) (s i)] : 是Trans _ (Lex r s)
  定义体: ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact Lex.left _ _ (_root_.trans hij hk)
    · exact Lex.left _ _ hij
    · exact Lex.left _ _ hk
    · exact Lex.right _ _ (_root_.trans hab hc)⟩

Depends on / 依赖: Lex.left, Lex.right, _root_, _root_.trans
-/
instance [IsTrans ι r] [forall i, IsTrans (α i) (s i)] : IsTrans _ (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact Lex.left _ _ (_root_.trans hij hk)
    · exact Lex.left _ _ hij
    · exact Lex.left _ _ hk
    · exact Lex.right _ _ (_root_.trans hab hc)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Symm
  signature: r] [forall i, Std.Symm (s i)] : Std.Symm (Lex r s)
  body: ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Lex.left _ _ (symm hij)
    · exact Lex.right _ _ (symm hab)
      ⟩

中文:
实例 [Std.Symm
  签名: r] [对任意 i, Std.Symm (s i)] : Std.Symm (Lex r s)
  定义体: ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Lex.left _ _ (symm hij)
    · exact Lex.right _ _ (symm hab)
      ⟩

Depends on / 依赖: Lex.left, Lex.right
-/
instance [Std.Symm r] [forall i, Std.Symm (s i)] : Std.Symm (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    · exact Lex.left _ _ (symm hij)
    · exact Lex.right _ _ (symm hab)
      ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Asymm
  signature: r] [forall i, Std.Antisymm (s i)] : Std.Antisymm (Lex r s)
  body: ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
    · exact (irrefl _ hij).elim
    · exact (irrefl _ hji).elim
· exact congr_arg (Sigma.mk _ ·) antisymm hab hba⟩

中文:
实例 [Std.Asymm
  签名: r] [对任意 i, Std.反对称 (s i)] : Std.反对称 (Lex r s)
  定义体: ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
    · exact (irrefl _ hij).elim
    · exact (irrefl _ hji).elim
· exact congr_arg (Sigma.mk _ ·) antisymm hab hba⟩

Depends on / 依赖: Sigma.mk, antisymm, congr_arg, irrefl
-/
instance [Std.Asymm r] [forall i, Std.Antisymm (s i)] : Std.Antisymm (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
    · exact (irrefl _ hij).elim
    · exact (irrefl _ hji).elim
· exact congr_arg (Sigma.mk _ ·) antisymm hab hba⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Trichotomous
  signature: r] [forall i, Std.Total (s i)] : Std.Total (Lex r s)
  body: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | hba := total_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Lex.right _ _ hba)
    · exact Or.inr (Lex.left _ _ hji)⟩

中文:
实例 [Std.三歧
  签名: r] [对任意 i, Std.全 (s i)] : Std.全 (Lex r s)
  定义体: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | hba := total_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Lex.right _ _ hba)
    · exact Or.inr (Lex.left _ _ hji)⟩

Depends on / 依赖: Lex.left, Lex.right, Or.inl, Or.inr, total_of, trichotomous_of
-/
instance [Std.Trichotomous r] [forall i, Std.Total (s i)] : Std.Total (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | hba := total_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Lex.right _ _ hba)
    · exact Or.inr (Lex.left _ _ hji)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Trichotomous
  signature: r] [forall i, Std.Trichotomous (s i)] : Std.Trichotomous (Lex r s)
  body: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Or.inl rfl)
      ·

中文:
实例 [Std.三歧
  签名: r] [对任意 i, Std.三歧 (s i)] : Std.三歧 (Lex r s)
  定义体: Std.trichotomous_of_rel_or_eq_or_rel_swap by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Or.inl rfl)
      ·

Depends on / 依赖: Lex.left, Lex.right, Or.inl, Or.inr, Std.trichotomous_of_rel_or_eq_or_rel_swap, trichotomous_of, trichotomous_of_rel_or_eq_or_rel_swap
-/
instance [Std.Trichotomous r] [forall i, Std.Trichotomous (s i)] : Std.Trichotomous (Lex r s) :=
Std.trichotomous_of_rel_or_eq_or_rel_swap by
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr <| Lex.right _ _ hba)
    · exact Or.inr (Or.inr <| Lex.left _ _ hji)

end Sigma

/-! ### `PSigma` -/


namespace PSigma

variable {ι : Sort*} {α : ι -> Sort*} {r : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop}

/--
theorem `lex_iff` / 定理 `lex_iff`

English:
theorem lex_iff
  given: {a b : Σ' i, α i}
  proof: by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ h

中文:
定理 lex_iff
  条件: {a b : Σ' i, α i}
  证明: by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ h

Depends on / 依赖: Lex.left, Lex.right, Or.inl, Or.inr
-/
theorem lex_iff {a b : Σ' i, α i} :
    Lex r s a b ↔ r a.1 b.1 ∨ exists h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    · exact Or.inl hij
    · exact Or.inr ⟨rfl, hab⟩
  · obtain ⟨i, a⟩ := a
    dsimp only
    rintro (h | ⟨rfl, h⟩)
    · exact Lex.left _ _ h
    · exact Lex.right _ h

/--
Instance `Lex.decidable` / 实例 `Lex.decidable`

English:
instance Lex.decidable
  signature: (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) [DecidableEq ι]
  body: fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm

中文:
实例 Lex.decidable
  签名: (r : ι -> ι -> 命题) (s : 对任意 i, α i -> α i -> 命题) [DecidableEq ι]
  定义体: fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
-/
instance Lex.decidable (r : ι -> ι -> Prop) (s : forall i, α i -> α i -> Prop) [DecidableEq ι]
    [DecidableRel r] [forall i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm

/--
theorem `Lex.mono` / 定理 `Lex.mono`

English:
theorem Lex.mono
  statement: {r₁ r₂ : ι -> ι -> Prop} {s₁ s₂ : forall i, α i -> α i -> Prop}
  proof: by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ (hs _ _ _ hab)

中文:
定理 Lex.mono
  结论: {r₁ r₂ : ι -> ι -> 命题} {s₁ s₂ : 对任意 i, α i -> α i -> 命题}
  证明: by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ (hs _ _ _ hab)
-/
theorem Lex.mono {r₁ r₂ : ι -> ι -> Prop} {s₁ s₂ : forall i, α i -> α i -> Prop}
    (hr : forall a b, r₁ a b -> r₂ a b) (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ' i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  · exact Lex.left _ _ (hr _ _ hij)
  · exact Lex.right _ (hs _ _ _ hab)

/--
theorem `Lex.mono_left` / 定理 `Lex.mono_left`

English:
theorem Lex.mono_left
  statement: {r₁ r₂ : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop}
  proof: h.mono hr fun _ _ _ => id

中文:
定理 Lex.mono_left
  结论: {r₁ r₂ : ι -> ι -> 命题} {s : 对任意 i, α i -> α i -> 命题}
  证明: h.mono hr fun _ _ _ => id
-/
theorem Lex.mono_left {r₁ r₂ : ι -> ι -> Prop} {s : forall i, α i -> α i -> Prop}
    (hr : forall a b, r₁ a b -> r₂ a b) {a b : Σ' i, α i} (h : Lex r₁ s a b) : Lex r₂ s a b :=
  h.mono hr fun _ _ _ => id

/--
theorem `Lex.mono_right` / 定理 `Lex.mono_right`

English:
theorem Lex.mono_right
  statement: {r : ι -> ι -> Prop} {s₁ s₂ : forall i, α i -> α i -> Prop}
  proof: h.mono (fun _ _ => id) hs

中文:
定理 Lex.mono_right
  结论: {r : ι -> ι -> 命题} {s₁ s₂ : 对任意 i, α i -> α i -> 命题}
  证明: h.mono (fun _ _ => id) hs
-/
theorem Lex.mono_right {r : ι -> ι -> Prop} {s₁ s₂ : forall i, α i -> α i -> Prop}
    (hs : forall i a b, s₁ i a b -> s₂ i a b) {a b : Σ' i, α i} (h : Lex r s₁ a b) : Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs

end PSigma
