/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Multiple transitivity

* `MulAction.IsMultiplyPretransitive`:
  A multiplicative action of a group `G` on a type `α` is n-transitive
  if the action of `G` on `Fin n ↪ α` is pretransitive.

* `MulAction.is_zero_pretransitive` : any action is 0-pretransitive

* `MulAction.is_one_pretransitive_iff` :
  An action is 1-pretransitive iff it is pretransitive

* `MulAction.is_two_pretransitive_iff` :
  An action is 2-pretransitive if for any `a`, `b`, `c`, `d`, such that
  `a ≠ b` and `c ≠ d`, there exist `g : G` such that `g • a = b` and `g • c = d`.

* `MulAction.isPreprimitive_of_is_two_pretransitive` :
  A 2-transitive action is preprimitive

* `MulAction.isMultiplyPretransitive_of_le` :
  If an action is `n`-pretransitive, then it is `m`-pretransitive for all `m ≤ n`,
  provided `α` has at least `n` elements.

## Results for `SubMulAction`.

* `SubMulAction.ofStabilizer.isPretransitive_iff_conj` shows
  that for `a`, `b` and `g` such that `g • a = b`, the actions
  of `stabilizer G a` and of `stabilizer G b` are equivalently `n`-pretransitive for all `n : ℕ`.

* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff_conj hg` shows the
  same result for `n`-transitivity.


* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff` : if the action of `G` on `α`
  is pretransitive, then it is `n.succ` pretransitive if and only if
  the action of `stabilizer G a` on `ofStabilizer G a` is `n`-pretransitive.

## Results for permutation groups

* The permutation group is pretransitive, is multiply pretransitive,
  and is preprimitive (for its natural action)

* `Equiv.Perm.eq_top_if_isMultiplyPretransitive`:
  a subgroup of `Equiv.Perm α` which is `Nat.card α - 1` pretransitive is equal to `⊤`.

## Remarks on implementation

These results are results about actions on types `n ↪ α` induced by an action
on `α`, and some results are developed in this context.

-/

@[expose] public section

open MulAction MulActionHom Function.Embedding Fin Set Nat

section Functoriality

variable {G α : Type*} [Group G] [MulAction G α]
variable {H β : Type*} [Group H] [MulAction H β]
variable {σ : G -> H} {f : α ->ₑ[σ] β} {ι : Type*}

variable (ι) in
/-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`. -/
@[to_additive /-- An injective equivariant map `α →ₑ[σ] β` induces
an equivariant map on embedding types `(ι ↪ α) → (ι ↪ β)`. -/]
/--
Definition of `Function.Injective.mulActionHom_embedding` / `Function.Injective.mulActionHom_embedding` 的定义

English:
definition Function.Injective.mulActionHom_embedding
  signature: (hf : Function.Injective f)
  body: ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by ext; simp [f.map_smul']

@[to_additive (attr := simp)]

中文:
定义 函数.单射.mulActionHom_embedding
  签名: (hf : 函数.单射 f)
  定义体: ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by ext; simp [f.map_smul']

@[to_additive (attr := simp)]

Depends on / 依赖: _smul, f.toFun, hf.comp, toMatrix, x.inj, x.toFun
-/
def Function.Injective.mulActionHom_embedding (hf : Function.Injective f) :
    (ι ↪ α) ->ₑ[σ] (ι ↪ β) where
  toFun x := ⟨f.toFun ∘ x.toFun, hf.comp x.inj'⟩
  map_smul' m x := by ext; simp [f.map_smul']

@[to_additive (attr := simp)]
/--
theorem `Function.Injective.mulActionHom_embedding_apply` / 定理 `Function.Injective.mulActionHom_embedding_apply`

English:
theorem Function.Injective.mulActionHom_embedding_apply
  proof: rfl

@[to_additive]

中文:
定理 函数.单射.mulActionHom_embedding_apply
  证明: rfl

@[to_additive]

Depends on / 依赖: _comp, mul_comm, mul_left_comm, toMatrix
-/
theorem Function.Injective.mulActionHom_embedding_apply
    (hf : Function.Injective f) {x : ι ↪ α} {i : ι} :
    hf.mulActionHom_embedding ι x i = f (x i) := rfl

@[to_additive]
/--
theorem `Function.Injective.mulActionHom_embedding_isInjective` / 定理 `Function.Injective.mulActionHom_embedding_isInjective`

English:
theorem Function.Injective.mulActionHom_embedding_isInjective
  proof: by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

中文:
定理 函数.单射.mulActionHom_embedding_isInjective
  证明: by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

Depends on / 依赖: hf.mulActionHom_embedding_apply, mulActionHom_embedding_apply
-/
theorem Function.Injective.mulActionHom_embedding_isInjective
    (hf : Function.Injective f) :
    Function.Injective (hf.mulActionHom_embedding ι) := by
  intro _ _ hxy
  ext
  apply hf
  simp only [← hf.mulActionHom_embedding_apply, hxy]

variable (hf' : Function.Bijective f)

@[to_additive]
/--
theorem `Function.Bijective.mulActionHom_embedding_isBijective` / 定理 `Function.Bijective.mulActionHom_embedding_isBijective`

English:
theorem Function.Bijective.mulActionHom_embedding_isBijective
  given: (hf : Function.Bijective f)
  proof: by
  refine ⟨hf.injective.mulActionHom_embedding_isInjective, ?_⟩
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, hfg.injective.comp (EmbeddingLike.injective y)⟩
  ext
  simp only [hf.injective.mulActionHom_embedding_apply, coeFn_mk, comp_apply]
  exact hfg (y _)

中文:
定理 函数.双射.mulActionHom_embedding_isBijective
  条件: (hf : 函数.双射 f)
  证明: by
  refine ⟨hf.injective.mulActionHom_embedding_isInjective, ?_⟩
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, hfg.injective.comp (EmbeddingLike.injective y)⟩
  ext
  simp only [hf.injective.mulActionHom_embedding_apply, coeFn_mk, comp_apply]
  exact hfg (y _)

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, Function, Function.bijective_iff_has_inverse.mp, bijective_iff_has_inverse, coeFn_mk, comp_apply, hf.injective.mulActionHom_embedding_apply, hf.injective.mulActionHom_embedding_isInjective, hfg.injective.comp, injective, mulActionHom_embedding_apply, mulActionHom_embedding_isInjective
-/
theorem Function.Bijective.mulActionHom_embedding_isBijective (hf : Function.Bijective f) :
    Function.Bijective (hf.injective.mulActionHom_embedding ι) := by
  refine ⟨hf.injective.mulActionHom_embedding_isInjective, ?_⟩
  intro y
  obtain ⟨g, _, hfg⟩ := Function.bijective_iff_has_inverse.mp hf
  use ⟨g ∘ y, hfg.injective.comp (EmbeddingLike.injective y)⟩
  ext
  simp only [hf.injective.mulActionHom_embedding_apply, coeFn_mk, comp_apply]
  exact hfg (y _)

end Functoriality

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

variable (G α) in
/-- An action of a group on a type `α` is `n`-pretransitive
if the associated action on `Fin n ↪ α` is pretransitive. -/
@[to_additive /-- An additive action of an additive group on a type `α`
is `n`-pretransitive if the associated action on `Fin n ↪ α` is pretransitive. -/]
/--
Definition of `IsMultiplyPretransitive` / `IsMultiplyPretransitive` 的定义

English:
abbreviation IsMultiplyPretransitive
  signature: (n : Nat)
  body: IsPretransitive G (Fin n ↪ α)

@[to_additive]

中文:
缩写 IsMultiplyPretransitive
  签名: (n : 自然数)
  定义体: IsPretransitive G (Fin n ↪ α)

@[to_additive]

Depends on / 依赖: IsPretransitive
-/
abbrev IsMultiplyPretransitive (n : Nat) := IsPretransitive G (Fin n ↪ α)

@[to_additive]
/--
theorem `isMultiplyPretransitive_iff` / 定理 `isMultiplyPretransitive_iff`

English:
theorem isMultiplyPretransitive_iff
  given: {n : Nat}
  proof: isPretransitive_iff _ _

中文:
定理 isMultiplyPretransitive_iff
  条件: {n : 自然数}
  证明: isPretransitive_iff _ _

Depends on / 依赖: isPretransitive_iff
-/
theorem isMultiplyPretransitive_iff {n : Nat} :
    IsMultiplyPretransitive G α n ↔ forall x y : Fin n ↪ α, exists g : G, g • x = y :=
  isPretransitive_iff _ _

variable {H β : Type*} [Group H] [MulAction H β] {σ : G -> H}
  {f : α ->ₑ[σ] β} (hf : Function.Injective f)

/-- If there exists a surjective equivariant map `α →ₑ[σ] β`
then pretransitivity descends from `n ↪ α` to `n ↪ β`.

The subtlety is that if it is not injective, this map does not induce
an equivariant map from `n ↪ α` to `n ↪ β`. -/
@[to_additive]
/--
theorem `IsPretransitive.of_embedding` / 定理 `IsPretransitive.of_embedding`

English:
theorem IsPretransitive.of_embedding
  statement: {n : Type*}
  proof: by
    let aux (x : n ↪ β) : (n ↪ α) :=
      x.trans (Function.Embedding.ofSurjective (⇑f) hf)
    have aux_apply (x : n ↪ β) (i : n) : f.toFun (aux x i) = x i := by
      simp only [trans_apply, aux]
      apply Function.surjInv_eq
    obtain ⟨g, hg⟩ := exists_smul_eq (M := G) (aux x) (aux y)
    use σ g
    ext i
    rw [DFunLike.ext_iff] at hg
    rw [smul_apply]
    simp [← aux_apply, ← hg, MulActionHom.map_smul']

@[to_additive]

中文:
定理 是Pretransitive.of_embedding
  结论: {n : 类型}
  证明: by
    let aux (x : n ↪ β) : (n ↪ α) :=
      x.trans (Function.Embedding.ofSurjective (⇑f) hf)
    have aux_apply (x : n ↪ β) (i : n) : f.toFun (aux x i) = x i := by
      simp only [trans_apply, aux]
      apply Function.surjInv_eq
    obtain ⟨g, hg⟩ := exists_smul_eq (M := G) (aux x) (aux y)
    use σ g
    ext i
    rw [DFunLike.ext_iff] at hg
    rw [smul_apply]
    simp [← aux_apply, ← hg, MulActionHom.map_smul']

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Embedding, Function, Function.Embedding.ofSurjective, Function.surjInv_eq, MulActionHom, MulActionHom.map_smul, aux_apply, exists_smul_eq, ext_iff, f.toFun, map_smul, ofSurjective, smul_apply, surjInv_eq, trans_apply, x.trans
-/
theorem IsPretransitive.of_embedding {n : Type*}
    (hf : Function.Surjective f) [IsPretransitive G (n ↪ α)] :
    IsPretransitive H (n ↪ β) where
  exists_smul_eq x y := by
    let aux (x : n ↪ β) : (n ↪ α) :=
      x.trans (Function.Embedding.ofSurjective (⇑f) hf)
    have aux_apply (x : n ↪ β) (i : n) : f.toFun (aux x i) = x i := by
      simp only [trans_apply, aux]
      apply Function.surjInv_eq
    obtain ⟨g, hg⟩ := exists_smul_eq (M := G) (aux x) (aux y)
    use σ g
    ext i
    rw [DFunLike.ext_iff] at hg
    rw [smul_apply]
    simp [← aux_apply, ← hg, MulActionHom.map_smul']

@[to_additive]
/--
theorem `IsPretransitive.of_embedding_congr` / 定理 `IsPretransitive.of_embedding_congr`

English:
theorem IsPretransitive.of_embedding_congr
  statement: {n : Type*}
  proof: isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

中文:
定理 是Pretransitive.of_embedding_congr
  结论: {n : 类型}
  证明: isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

Depends on / 依赖: hf.mulActionHom_embedding_isBijective, isPretransitive_congr, mulActionHom_embedding_isBijective
-/
theorem IsPretransitive.of_embedding_congr {n : Type*}
    (hσ : Function.Surjective σ) (hf : Function.Bijective f) :
    IsPretransitive G (n ↪ α) ↔ IsPretransitive H (n ↪ β) :=
  isPretransitive_congr hσ hf.mulActionHom_embedding_isBijective

section Zero

/-- Any action is 0-pretransitive. -/
@[to_additive]
/--
theorem `is_zero_pretransitive` / 定理 `is_zero_pretransitive`

English:
theorem is_zero_pretransitive
  given: {n : Type*} [IsEmpty n]
  proof: inferInstance

中文:
定理 is_zero_pretransitive
  条件: {n : 类型} [是空 n]
  证明: inferInstance
-/
theorem is_zero_pretransitive {n : Type*} [IsEmpty n] :
    IsPretransitive G (n ↪ α) := inferInstance

/-- Any action is 0-pretransitive. -/
@[to_additive]
/--
theorem `is_zero_pretransitive'` / 定理 `is_zero_pretransitive'`

English:
theorem is_zero_pretransitive'
  proof: inferInstance

中文:
定理 is_zero_pretransitive'
  证明: inferInstance
-/
theorem is_zero_pretransitive' :
    IsMultiplyPretransitive G α 0 := inferInstance

end Zero

section One

variable {one : Type*} [Unique one]

/-- For `Unique one`, the equivariant map from `one ↪ α` to `α`. -/
@[to_additive /-- For `Unique one`, the equivariant map from `one ↪ α` to `α` -/]
/--
Definition of `_root_.MulActionHom.oneEmbeddingMap` / `_root_.MulActionHom.oneEmbeddingMap` 的定义

English:
definition _root_.MulActionHom.oneEmbeddingMap
  signature: :
  body: {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]

中文:
定义 _root_.乘法作用态射.oneEmbeddingMap
  签名: :
  定义体: {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]
-/
def _root_.MulActionHom.oneEmbeddingMap :
    (one ↪ α) ->[G] α := {
  oneEmbeddingEquiv with
  map_smul' _ _ := rfl }

@[to_additive]
/--
theorem `_root_.MulActionHom.oneEmbeddingMap_bijective` / 定理 `_root_.MulActionHom.oneEmbeddingMap_bijective`

English:
theorem _root_.MulActionHom.oneEmbeddingMap_bijective
  proof: oneEmbeddingEquiv.bijective

中文:
定理 _root_.乘法作用态射.oneEmbeddingMap_bijective
  证明: oneEmbeddingEquiv.bijective
-/
theorem _root_.MulActionHom.oneEmbeddingMap_bijective :
    Function.Bijective (oneEmbeddingMap (one := one) (G := G) (α := α)) :=
  oneEmbeddingEquiv.bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive /-- An additive action is `1`-pretransitive iff it is pretransitive. -/]
/--
theorem `oneEmbedding_isPretransitive_iff` / 定理 `oneEmbedding_isPretransitive_iff`

English:
theorem oneEmbedding_isPretransitive_iff
  proof: isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

中文:
定理 oneEmbedding_isPretransitive_iff
  证明: isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

Depends on / 依赖: Function, Function.surjective_id, isPretransitive_congr, oneEmbeddingMap_bijective, surjective_id
-/
theorem oneEmbedding_isPretransitive_iff :
    IsPretransitive G (one ↪ α) ↔ IsPretransitive G α :=
  isPretransitive_congr Function.surjective_id oneEmbeddingMap_bijective

/-- An action is `1`-pretransitive iff it is pretransitive. -/
@[to_additive /-- An additive action is `1`-pretransitive iff it is pretransitive. -/]
/--
theorem `is_one_pretransitive_iff` / 定理 `is_one_pretransitive_iff`

English:
theorem is_one_pretransitive_iff
  proof: oneEmbedding_isPretransitive_iff

中文:
定理 is_one_pretransitive_iff
  证明: oneEmbedding_isPretransitive_iff

Depends on / 依赖: oneEmbedding_isPretransitive_iff
-/
theorem is_one_pretransitive_iff :
    IsMultiplyPretransitive G α 1 ↔ IsPretransitive G α :=
  oneEmbedding_isPretransitive_iff

end One

section Two

/-- An action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/
@[to_additive /-- An additive action is `2`-pretransitive iff
it can move any two distinct elements to any two distinct elements. -/]
/--
theorem `is_two_pretransitive_iff` / 定理 `is_two_pretransitive_iff`

English:
theorem is_two_pretransitive_iff
  proof: by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']

中文:
定理 is_two_pretransitive_iff
  证明: by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']

Depends on / 依赖: Fin.zero_ne_one, embFinTwo, embFinTwo_apply_one, embFinTwo_apply_zero, eq_one_of_ne_zero, exists_smul_eq, injective, injective.ne_iff.mpr, j.injective.ne_iff.mpr, ne_iff, smul_apply, zero_ne_one
-/
theorem is_two_pretransitive_iff :
    IsMultiplyPretransitive G α 2 ↔
      forall {a b c d : α} (_ : a != b) (_ : c != d), exists g : G, g • a = c ∧ g • b = d := by
  constructor
  · intro _ a b c d h h'
    obtain ⟨m, e⟩ := exists_smul_eq (M := G) (embFinTwo h) (embFinTwo h')
    exact ⟨m,
      by rw [← embFinTwo_apply_zero h, ← smul_apply, e, embFinTwo_apply_zero],
      by rw [← embFinTwo_apply_one h, ← smul_apply, e, embFinTwo_apply_one]⟩
  · intro H
    constructor
    intro j j'
    obtain ⟨g, h, h'⟩ :=
      H (j.injective.ne_iff.mpr Fin.zero_ne_one) (j'.injective.ne_iff.mpr Fin.zero_ne_one)
    use g
    ext i
    by_cases hi : i = 0
    · simp [hi, h]
    · simp [eq_one_of_ne_zero i hi, h']

/-- A `2`-pretransitive action is pretransitive. -/
@[to_additive /-- A `2`-pretransitive additive action is pretransitive. -/]
/--
theorem `isPretransitive_of_is_two_pretransitive` / 定理 `isPretransitive_of_is_two_pretransitive`

English:
theorem isPretransitive_of_is_two_pretransitive
  proof: by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

中文:
定理 isPretransitive_of_is_two_pretransitive
  证明: by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

Depends on / 依赖: Ne.symm, is_two_pretransitive_iff
-/
theorem isPretransitive_of_is_two_pretransitive
    [h2 : IsMultiplyPretransitive G α 2] : IsPretransitive G α where
  exists_smul_eq a b := by
    by_cases h : a = b
    · exact ⟨1, by simp [h]⟩
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, h, _⟩ := h2 h (Ne.symm h)
      exact ⟨g, h⟩

/-- A `2`-transitive action is primitive. -/
@[to_additive /-- A `2`-transitive additive action is primitive. -/]
/--
theorem `isPreprimitive_of_is_two_pretransitive` / 定理 `isPreprimitive_of_is_two_pretransitive`

English:
theorem isPreprimitive_of_is_two_pretransitive
  proof: by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  apply IsPreprimitive.mk
  intro B hB
  rcases B.subsingleton_or_nontrivial with h | h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [← top_eq_univ]; rw [eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 h h'
      rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
      rw [← hB (g := g) ha (by rw [hga]; exact ha), ← hgb]
      exact smul_mem_smul_set hb

中文:
定理 isPreprimitive_of_is_two_pretransitive
  证明: by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  apply IsPreprimitive.mk
  intro B hB
  rcases B.subsingleton_or_nontrivial with h | h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [← top_eq_univ]; rw [eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 h h'
      rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
      rw [← hB (g := g) ha (by rw [hga]; exact ha), ← hgb]
      exact smul_mem_smul_set hb

Depends on / 依赖: B.subsingleton_or_nontrivial, IsPreprimitive, IsPreprimitive.mk, IsPretransitive, MulAction, MulAction.isBlock_iff_smul_eq_of_mem, eq_top_iff, isBlock_iff_smul_eq_of_mem, isPretransitive_of_is_two_pretransitive, is_two_pretransitive_iff, smul_mem_smul_set, subsingleton_or_nontrivial, top_eq_univ
-/
theorem isPreprimitive_of_is_two_pretransitive
    (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α := by
  have : IsPretransitive G α := isPretransitive_of_is_two_pretransitive
  apply IsPreprimitive.mk
  intro B hB
  rcases B.subsingleton_or_nontrivial with h | h
  · left
    exact h
  · right
    obtain ⟨a, ha, b, hb, h⟩ := h
    rw [← top_eq_univ]; rw [eq_top_iff]
    intro c _
    by_cases h' : a = c
    · rw [← h']; exact ha
    · rw [is_two_pretransitive_iff] at h2
      obtain ⟨g, hga, hgb⟩ := h2 h h'
      rw [MulAction.isBlock_iff_smul_eq_of_mem] at hB
      rw [← hB (g := g) ha (by rw [hga]; exact ha), ← hgb]
      exact smul_mem_smul_set hb

end Two

section Higher

variable (G α) in
/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding
`e : m ↪ n`. -/
@[to_additive
/-- The natural equivariant map from `n ↪ α` to `m ↪ α` given by an embedding `e : m ↪ n`. -/]
/--
Definition of `_root_.MulActionHom.embMap` / `_root_.MulActionHom.embMap` 的定义

English:
definition _root_.MulActionHom.embMap
  signature: {m n : Type*} (e : m ↪ n)
  body: e.trans i
  map_smul' _ _ := rfl

中文:
定义 _root_.乘法作用态射.embMap
  签名: {m n : 类型} (e : m ↪ n)
  定义体: e.trans i
  map_smul' _ _ := rfl

Depends on / 依赖: e.trans
-/
def _root_.MulActionHom.embMap {m n : Type*} (e : m ↪ n) :
    (n ↪ α) ->[G] (m ↪ α) where
  toFun i := e.trans i
  map_smul' _ _ := rfl

/-- If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `m`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `MulAction.isMultiplyPretransitive_of_le` -/
@[to_additive
/-- If `α` has at least `n` elements, then any `n`-pretransitive action on `α`
is `n`-pretransitive for any `m ≤ n`.

This version allows `α` to be infinite and uses `ENat.card`.
For `Finite α`, use `AddAction.isMultiplyPretransitive_of_le`. -/]
/--
theorem `isMultiplyPretransitive_of_le'` / 定理 `isMultiplyPretransitive_of_le'`

English:
theorem isMultiplyPretransitive_of_le'
  statement: {m n : Nat} [IsMultiplyPretransitive G α n]
  proof: by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

中文:
定理 isMultiplyPretransitive_of_le'
  结论: {m n : 自然数} [IsMultiplyPretransitive G α n]
  证明: by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

Depends on / 依赖: Embedding, Fin.Embedding.restrictSurjective_of_add_le_ENatCard, IsPretransitive, IsPretransitive.of_surjective_map, Nat.exists_eq_add_of_le, castAddEmb, embMap, exists_eq_add_of_le, of_surjective_map, restrictSurjective_of_add_le_ENatCard
-/
theorem isMultiplyPretransitive_of_le' {m n : Nat} [IsMultiplyPretransitive G α n]
    (hmn : m <= n) (hα : n <= ENat.card α) :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map
    (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_ENatCard hα) inferInstance

/-- If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/
@[to_additive
/-- If `α` has at least `n` elements, then an `n`-pretransitive action
is `m`-pretransitive for any `m ≤ n`.

For an infinite `α`, use `MulAction.isMultiplyPretransitive_of_le'`. -/]
/--
theorem `isMultiplyPretransitive_of_le` / 定理 `isMultiplyPretransitive_of_le`

English:
theorem isMultiplyPretransitive_of_le
  statement: {m n : Nat} [IsMultiplyPretransitive G α n]
  proof: by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

中文:
定理 isMultiplyPretransitive_of_le
  结论: {m n : 自然数} [IsMultiplyPretransitive G α n]
  证明: by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

Depends on / 依赖: Embedding, Fin.Embedding.restrictSurjective_of_add_le_natCard, IsPretransitive, IsPretransitive.of_surjective_map, Nat.exists_eq_add_of_le, castAddEmb, embMap, exists_eq_add_of_le, of_surjective_map, restrictSurjective_of_add_le_natCard
-/
theorem isMultiplyPretransitive_of_le {m n : Nat} [IsMultiplyPretransitive G α n]
    (hmn : m <= n) (hα : n <= Nat.card α) [Finite α] :
    IsMultiplyPretransitive G α m := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact IsPretransitive.of_surjective_map (f := embMap G α (castAddEmb p))
    (Fin.Embedding.restrictSurjective_of_add_le_natCard hα) inferInstance

end Higher

end MulAction

namespace SubMulAction.ofStabilizer

variable {G α : Type*} [Group G] [MulAction G α]

@[to_additive]
/--
theorem `isPretransitive_iff_of_conj` / 定理 `isPretransitive_iff_of_conj`

English:
theorem isPretransitive_iff_of_conj
  given: {a b : α} {g : G} (hg : b = g • a)
  proof: isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]

中文:
定理 isPretransitive_iff_of_conj
  条件: {a b : α} {g : G} (hg : b = g • a)
  证明: isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]

Depends on / 依赖: MulEquiv, MulEquiv.surjective, conjMap_bijective, isPretransitive_congr, ofStabilizer, ofStabilizer.conjMap_bijective, surjective
-/
theorem isPretransitive_iff_of_conj {a b : α} {g : G} (hg : b = g • a) :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
/--
theorem `isPretransitive_iff` / 定理 `isPretransitive_iff`

English:
theorem isPretransitive_iff
  given: [IsPretransitive G α] {a b : α}
  proof: let ⟨_, hg⟩ := exists_smul_eq G a b
  isPretransitive_iff_of_conj hg.symm

@[to_additive]

中文:
定理 isPretransitive_iff
  条件: [是Pretransitive G α] {a b : α}
  证明: let ⟨_, hg⟩ := exists_smul_eq G a b
  isPretransitive_iff_of_conj hg.symm

@[to_additive]

Depends on / 依赖: exists_smul_eq, hg.symm, isPretransitive_iff_of_conj
-/
theorem isPretransitive_iff [IsPretransitive G α] {a b : α} :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isPretransitive_iff_of_conj hg.symm

@[to_additive]
/--
theorem `isMultiplyPretransitive_iff_of_conj` / 定理 `isMultiplyPretransitive_iff_of_conj`

English:
theorem isMultiplyPretransitive_iff_of_conj
  proof: IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]

中文:
定理 isMultiplyPretransitive_iff_of_conj
  证明: IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]

Depends on / 依赖: IsPretransitive, IsPretransitive.of_embedding_congr, MulEquiv, MulEquiv.surjective, conjMap_bijective, ofStabilizer, ofStabilizer.conjMap_bijective, of_embedding_congr, surjective
-/
theorem isMultiplyPretransitive_iff_of_conj
    {n : Nat} {a b : α} {g : G} (hg : b = g • a) :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
/--
theorem `isMultiplyPretransitive_iff` / 定理 `isMultiplyPretransitive_iff`

English:
theorem isMultiplyPretransitive_iff
  given: [IsPretransitive G α] {n : Nat} {a b : α}
  proof: let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

中文:
定理 isMultiplyPretransitive_iff
  条件: [是Pretransitive G α] {n : 自然数} {a b : α}
  证明: let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

Depends on / 依赖: exists_smul_eq, hg.symm, isMultiplyPretransitive_iff_of_conj
-/
theorem isMultiplyPretransitive_iff [IsPretransitive G α] {n : Nat} {a b : α} :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

/-- Multiple transitivity of a pretransitive action
is equivalent to one less transitivity of stabilizer of a point
(Wielandt, th. 9.1, 1st part) -/
@[to_additive /-- Multiple transitivity of a pretransitive action
is equivalent to one less transitivity of stabilizer of a point
[Wielandt, th. 9.1, 1st part][Wielandt-1964]. -/]
/--
theorem `isMultiplyPretransitive` / 定理 `isMultiplyPretransitive`

English:
theorem isMultiplyPretransitive
  given: [IsPretransitive G α] {n : Nat} {a : α}
  proof: by
  refine ⟨fun hn => ⟨fun x y => ?_⟩, fun hn => ⟨fun x y => ?_⟩⟩
  · obtain ⟨g, hgxy⟩ := exists_smul_eq G (ofStabilizer.snoc x) (ofStabilizer.snoc y)
    have hg : g in stabilizer G a := by
      rw [DFunLike.ext_iff] at hgxy
      convert! hgxy (last n)
      simp [ofStabilizer.snoc_last]
    use ⟨g, hg⟩
    ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
    rw [← ofStabilizer.snoc_castSucc x]; rw [← smul_apply]; rw [hgxy]; rw [ofStabilizer.snoc_castSucc]
  · -- gx • x = x1 :: a
    obtain ⟨gx, x1, hgx⟩ := exists_smul_of_last_eq G a x
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy⟩ := exists_smul_of_last_eq G a y
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
    use gy⁻¹ * g * gx
    ext i
    simp only [mul_smul, smul_apply, inv_smul_eq_iff]
    simp only [← smul_apply _ _ i, hgy, hgx]
    simp only [smul_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · simp [ofStabilizer.snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
    · simp only [ofStabilizer.snoc_last, ← hg]
      exact g.prop

中文:
定理 isMultiplyPretransitive
  条件: [是Pretransitive G α] {n : 自然数} {a : α}
  证明: by
  refine ⟨fun hn => ⟨fun x y => ?_⟩, fun hn => ⟨fun x y => ?_⟩⟩
  · obtain ⟨g, hgxy⟩ := exists_smul_eq G (ofStabilizer.snoc x) (ofStabilizer.snoc y)
    have hg : g in stabilizer G a := by
      rw [DFunLike.ext_iff] at hgxy
      convert! hgxy (last n)
      simp [ofStabilizer.snoc_last]
    use ⟨g, hg⟩
    ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
    rw [← ofStabilizer.snoc_castSucc x]; rw [← smul_apply]; rw [hgxy]; rw [ofStabilizer.snoc_castSucc]
  · -- gx • x = x1 :: a
    obtain ⟨gx, x1, hgx⟩ := exists_smul_of_last_eq G a x
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy⟩ := exists_smul_of_last_eq G a y
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
    use gy⁻¹ * g * gx
    ext i
    simp only [mul_smul, smul_apply, inv_smul_eq_iff]
    simp only [← smul_apply _ _ i, hgy, hgx]
    simp only [smul_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · simp [ofStabilizer.snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
    · simp only [ofStabilizer.snoc_last, ← hg]
      exact g.prop

Depends on / 依赖: DFunLike, DFunLike.ext_iff, SubMulAction, SubMulAction.val_smul_of_tower, convert, exists_smul_eq, ext_iff, ofStabilizer, ofStabilizer.snoc, ofStabilizer.snoc_castSucc, ofStabilizer.snoc_last, smul_apply, snoc_castSucc, snoc_last, stabilizer, subgroup_smul_def, val_smul_of_tower
-/
theorem isMultiplyPretransitive [IsPretransitive G α] {n : Nat} {a : α} :
    IsMultiplyPretransitive G α n.succ ↔
      IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n := by
  refine ⟨fun hn => ⟨fun x y => ?_⟩, fun hn => ⟨fun x y => ?_⟩⟩
  · obtain ⟨g, hgxy⟩ := exists_smul_eq G (ofStabilizer.snoc x) (ofStabilizer.snoc y)
    have hg : g in stabilizer G a := by
      rw [DFunLike.ext_iff] at hgxy
      convert! hgxy (last n)
      simp [ofStabilizer.snoc_last]
    use ⟨g, hg⟩
    ext i
    simp only [smul_apply, SubMulAction.val_smul_of_tower, subgroup_smul_def]
    rw [← ofStabilizer.snoc_castSucc x]; rw [← smul_apply]; rw [hgxy]; rw [ofStabilizer.snoc_castSucc]
  · -- gx • x = x1 :: a
    obtain ⟨gx, x1, hgx⟩ := exists_smul_of_last_eq G a x
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy⟩ := exists_smul_of_last_eq G a y
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
    use gy⁻¹ * g * gx
    ext i
    simp only [mul_smul, smul_apply, inv_smul_eq_iff]
    simp only [← smul_apply _ _ i, hgy, hgx]
    simp only [smul_apply]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
    · simp [ofStabilizer.snoc_castSucc, ← hg, SetLike.val_smul, subgroup_smul_def]
    · simp only [ofStabilizer.snoc_last, ← hg]
      exact g.prop

end ofStabilizer

namespace ofFixingSubgroup

variable {G α : Type*} [Group G] [MulAction G α]

variable (G) in
/-- The `fixingSubgroup` of a finite subset of cardinal `d`
in an `n`-transitive action acts `n-d`-transitively on the complement. -/
@[to_additive /-- The `fixingSubgroup` of a finite subset of cardinal `d`
in an `n`-transitive additive action acts `n-d`-transitively on the complement. -/]
/--
theorem `isMultiplyPretransitive` / 定理 `isMultiplyPretransitive`

English:
theorem isMultiplyPretransitive
  statement: {m n : Nat} [Hn : IsMultiplyPretransitive G α n]
  proof: by
    have : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
    have Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    set x' := ofFixingSubgroup.append x with hx
    set y' := ofFixingSubgroup.append y with hy
    obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
    suffices g in fixingSubgroup G s by
      use ⟨g, this⟩
      ext i
      rw [smul_apply]; rw [SetLike.val_smul]; rw [Subgroup.mk_smul]
      simp [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
    intro a
    set i := (Classical.choice Hs).symm a
    have ha : (Classical.choice Hs) i = a := by simp [i]
    rw [← ha]
    nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
    rw [← ofFixingSubgroup.append_left y i]; rw [← hy]; rw [← hg]; rw [smul_apply]; rw [← hx]

中文:
定理 isMultiplyPretransitive
  结论: {m n : 自然数} [Hn : IsMultiplyPretransitive G α n]
  证明: by
    have : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
    have Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    set x' := ofFixingSubgroup.append x with hx
    set y' := ofFixingSubgroup.append y with hy
    obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
    suffices g in fixingSubgroup G s by
      use ⟨g, this⟩
      ext i
      rw [smul_apply]; rw [SetLike.val_smul]; rw [Subgroup.mk_smul]
      simp [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
    intro a
    set i := (Classical.choice Hs).symm a
    have ha : (Classical.choice Hs) i = a := by simp [i]
    rw [← ha]
    nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
    rw [← ofFixingSubgroup.append_left y i]; rw [← hy]; rw [← hg]; rw [smul_apply]; rw [← hx]

Depends on / 依赖: Finite, Finite.card_eq.mp, IsMultiplyPretransitive, Nat.card_coe_set_eq, Nonempty, SetLike, SetLike.val_smul, Subgroup, Subgroup.mk_smul, append, append_right, card_coe_set_eq, card_eq, exists_smul_eq, fixingSubgroup, infer_instance, mk_smul, ofFixingSubgroup, ofFixingSubgroup.append, ofFixingSubgroup.append_right
-/
theorem isMultiplyPretransitive {m n : Nat} [Hn : IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m = n) :
    IsMultiplyPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) m where
  exists_smul_eq x y := by
    have : IsMultiplyPretransitive G α (s.ncard + m) := by rw [hmn]; infer_instance
    have Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    set x' := ofFixingSubgroup.append x with hx
    set y' := ofFixingSubgroup.append y with hy
    obtain ⟨g, hg⟩ := exists_smul_eq G x' y'
    suffices g in fixingSubgroup G s by
      use ⟨g, this⟩
      ext i
      rw [smul_apply]; rw [SetLike.val_smul]; rw [Subgroup.mk_smul]
      simp [← ofFixingSubgroup.append_right, ← smul_apply, ← hx, ← hy, hg]
    intro a
    set i := (Classical.choice Hs).symm a
    have ha : (Classical.choice Hs) i = a := by simp [i]
    rw [← ha]
    nth_rewrite 1 [← ofFixingSubgroup.append_left x i]
    rw [← ofFixingSubgroup.append_left y i]; rw [← hy]; rw [← hg]; rw [smul_apply]; rw [← hx]

/-- The fixator of a finite subset of cardinal d in an n-transitive action
acts m transitively on the complement if d + m ≤ n. -/
@[to_additive /-- The fixator of a finite subset of cardinal d in an n-transitive additive action
acts m transitively on the complement if d + m ≤ n. -/]
/--
theorem `isMultiplyPretransitive'` / 定理 `isMultiplyPretransitive'`

English:
theorem isMultiplyPretransitive'
  proof: letI : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive G s rfl

中文:
定理 isMultiplyPretransitive'
  证明: letI : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive G s rfl

Depends on / 依赖: IsMultiplyPretransitive, isMultiplyPretransitive, isMultiplyPretransitive_of_le, s.ncard
-/
theorem isMultiplyPretransitive'
    {m n : Nat} [IsMultiplyPretransitive G α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m <= n) (hn : (n : ENat) <= ENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) m :=
  letI : IsMultiplyPretransitive G α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive G s rfl

end ofFixingSubgroup

end SubMulAction

namespace MulAction

section Index

open SubMulAction

variable {G : Type*} [Group G] {α : Type*} [MulAction G α]

/--
theorem `IsMultiplyPretransitive.index_of_fixingSubgroup_mul` / 定理 `IsMultiplyPretransitive.index_of_fixingSubgroup_mul`

English:
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_mul
  proof: by
  induction k generalizing G α with
  | zero =>
    rw [Set.ncard_eq_zero] at hs
    simp [hs]
  | succ k hrec =>
    have hGX : IsPretransitive G α := by
      rw [← is_one_pretransitive_iff]
      apply isMultiplyPretransitive_of_le (n := k + 1)
      · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
      · rw [← hs, ← Set.ncard_univ]
        exact ncard_le_ncard s.subset_univ finite_univ
    have : s.Nonempty := by
      rw [← Set.ncard_pos]; rw [hs]
      exact succ_pos k
    obtain ⟨a, has⟩ := this
    let t : Set (SubMulAction.ofStabilizer G a) := Subtype.val ⁻¹' s
    have hat : Subtype.val '' t = s \ {a} := by
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe_subtype]
      rw [Set.sdiff_eq_compl_inter]; rw [Set.inter_comm]
      congr
    have hat' : s = insert a (Subtype.val '' t) := by
      rw [hat]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem has]
    have hfs := SubMulAction.fixingSubgroup_of_insert a t
    rw [← hat'] at hfs
    rw [hfs]; rw [Subgroup.index_map]; rw [MonoidHom.ker_eq_bot (stabilizer G a).subtype
        (by simp only [Subgroup.coe_subtype]; rw [Subtype.coe_injective])]
    simp only [sup_bot_eq, Subgroup.range_subtype]
    have htcard : t.ncard = k := by
      rw [← Nat.succ_inj]; rw [Nat.succ_eq_add_one]; rw [Nat.succ_eq_add_one]; rw [← hs]; rw [hat']; rw [eq_comm]
      suffices ¬ a in (Subtype.val '' t) by
        convert! Set.ncard_insert_of_notMem this ?_
        · rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
        apply Set.toFinite
      intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [← hb', Set.mem_singleton_iff]
    suffices (fixingSubgroup (stabilizer G a) t).index *
      (Nat.card α - 1 - k).factorial =
        (Nat.card α - 1).factorial by
      rw [add_comm k]; rw [Nat.mul_right_comm]; rw [← Nat.sub_sub]; rw [this]; rw [mul_comm]; rw [index_stabilizer_of_transitive G a]
      exact Nat.mul_factorial_pred (card_ne_zero.mpr ⟨⟨a⟩, inferInstance⟩)
    convert! hrec (ofStabilizer.isMultiplyPretransitive.mp Hk) htcard
    all_goals { rw [nat_card_ofStabilizer_eq G a] }

中文:
定理 IsMultiplyPretransitive.index_of_fixingSubgroup_mul
  证明: by
  induction k generalizing G α with
  | zero =>
    rw [Set.ncard_eq_zero] at hs
    simp [hs]
  | succ k hrec =>
    have hGX : IsPretransitive G α := by
      rw [← is_one_pretransitive_iff]
      apply isMultiplyPretransitive_of_le (n := k + 1)
      · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
      · rw [← hs, ← Set.ncard_univ]
        exact ncard_le_ncard s.subset_univ finite_univ
    have : s.Nonempty := by
      rw [← Set.ncard_pos]; rw [hs]
      exact succ_pos k
    obtain ⟨a, has⟩ := this
    let t : Set (SubMulAction.ofStabilizer G a) := Subtype.val ⁻¹' s
    have hat : Subtype.val '' t = s \ {a} := by
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe_subtype]
      rw [Set.sdiff_eq_compl_inter]; rw [Set.inter_comm]
      congr
    have hat' : s = insert a (Subtype.val '' t) := by
      rw [hat]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem has]
    have hfs := SubMulAction.fixingSubgroup_of_insert a t
    rw [← hat'] at hfs
    rw [hfs]; rw [Subgroup.index_map]; rw [MonoidHom.ker_eq_bot (stabilizer G a).subtype
        (by simp only [Subgroup.coe_subtype]; rw [Subtype.coe_injective])]
    simp only [sup_bot_eq, Subgroup.range_subtype]
    have htcard : t.ncard = k := by
      rw [← Nat.succ_inj]; rw [Nat.succ_eq_add_one]; rw [Nat.succ_eq_add_one]; rw [← hs]; rw [hat']; rw [eq_comm]
      suffices ¬ a in (Subtype.val '' t) by
        convert! Set.ncard_insert_of_notMem this ?_
        · rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
        apply Set.toFinite
      intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [← hb', Set.mem_singleton_iff]
    suffices (fixingSubgroup (stabilizer G a) t).index *
      (Nat.card α - 1 - k).factorial =
        (Nat.card α - 1).factorial by
      rw [add_comm k]; rw [Nat.mul_right_comm]; rw [← Nat.sub_sub]; rw [this]; rw [mul_comm]; rw [index_stabilizer_of_transitive G a]
      exact Nat.mul_factorial_pred (card_ne_zero.mpr ⟨⟨a⟩, inferInstance⟩)
    convert! hrec (ofStabilizer.isMultiplyPretransitive.mp Hk) htcard
    all_goals { rw [nat_card_ofStabilizer_eq G a] }

Depends on / 依赖: IsPretransitive, Nat.succ_le_succ_iff, Nat.zero_le, Nonempty, Set.ncard_eq_zero, Set.ncard_pos, Set.ncard_univ, SubMulAction, SubMulAction.ofStabilizer, Subtype, Subtype.val, finite_univ, generalizing, isMultiplyPretransitive_of_le, is_one_pretransitive_iff, ncard_eq_zero, ncard_le_ncard, ncard_pos, ncard_univ, ofStabilizer
-/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_mul
    [Finite α]
    {k : Nat} (Hk : IsMultiplyPretransitive G α k)
    {s : Set α} (hs : s.ncard = k) :
    (fixingSubgroup G s).index * (Nat.card α - k).factorial =
      (Nat.card α).factorial := by
  induction k generalizing G α with
  | zero =>
    rw [Set.ncard_eq_zero] at hs
    simp [hs]
  | succ k hrec =>
    have hGX : IsPretransitive G α := by
      rw [← is_one_pretransitive_iff]
      apply isMultiplyPretransitive_of_le (n := k + 1)
      · rw [Nat.succ_le_succ_iff]; apply Nat.zero_le
      · rw [← hs, ← Set.ncard_univ]
        exact ncard_le_ncard s.subset_univ finite_univ
    have : s.Nonempty := by
      rw [← Set.ncard_pos]; rw [hs]
      exact succ_pos k
    obtain ⟨a, has⟩ := this
    let t : Set (SubMulAction.ofStabilizer G a) := Subtype.val ⁻¹' s
    have hat : Subtype.val '' t = s \ {a} := by
      rw [Set.image_preimage_eq_inter_range]
      simp only [Subtype.range_coe_subtype]
      rw [Set.sdiff_eq_compl_inter]; rw [Set.inter_comm]
      congr
    have hat' : s = insert a (Subtype.val '' t) := by
      rw [hat]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem has]
    have hfs := SubMulAction.fixingSubgroup_of_insert a t
    rw [← hat'] at hfs
    rw [hfs]; rw [Subgroup.index_map]; rw [MonoidHom.ker_eq_bot (stabilizer G a).subtype
        (by simp only [Subgroup.coe_subtype]; rw [Subtype.coe_injective])]
    simp only [sup_bot_eq, Subgroup.range_subtype]
    have htcard : t.ncard = k := by
      rw [← Nat.succ_inj]; rw [Nat.succ_eq_add_one]; rw [Nat.succ_eq_add_one]; rw [← hs]; rw [hat']; rw [eq_comm]
      suffices ¬ a in (Subtype.val '' t) by
        convert! Set.ncard_insert_of_notMem this ?_
        · rw [Set.ncard_image_of_injective _ Subtype.coe_injective]
        apply Set.toFinite
      intro h
      obtain ⟨⟨b, hb⟩, _, hb'⟩ := h
      apply hb
      simp only [← hb', Set.mem_singleton_iff]
    suffices (fixingSubgroup (stabilizer G a) t).index *
      (Nat.card α - 1 - k).factorial =
        (Nat.card α - 1).factorial by
      rw [add_comm k]; rw [Nat.mul_right_comm]; rw [← Nat.sub_sub]; rw [this]; rw [mul_comm]; rw [index_stabilizer_of_transitive G a]
      exact Nat.mul_factorial_pred (card_ne_zero.mpr ⟨⟨a⟩, inferInstance⟩)
    convert! hrec (ofStabilizer.isMultiplyPretransitive.mp Hk) htcard
    all_goals { rw [nat_card_ofStabilizer_eq G a] }

/--
theorem `IsMultiplyPretransitive.index_of_fixingSubgroup_eq` / 定理 `IsMultiplyPretransitive.index_of_fixingSubgroup_eq`

English:
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_eq
  proof: by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [hMk.index_of_fixingSubgroup_mul rfl]; rw [Nat.choose_mul_factorial_mul_factorial]
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ s)

中文:
定理 IsMultiplyPretransitive.index_of_fixingSubgroup_eq
  证明: by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [hMk.index_of_fixingSubgroup_mul rfl]; rw [Nat.choose_mul_factorial_mul_factorial]
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ s)

Depends on / 依赖: Nat.choose_mul_factorial_mul_factorial, Nat.eq_of_mul_eq_mul_right, Nat.factorial_pos, choose_mul_factorial_mul_factorial, eq_of_mul_eq_mul_right, factorial_pos, hMk.index_of_fixingSubgroup_mul, index_of_fixingSubgroup_mul, ncard_le_ncard, ncard_univ, subset_univ
-/
theorem IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    [Finite α] (s : Set α) (hMk : IsMultiplyPretransitive G α s.ncard) :
    (fixingSubgroup G s).index =
      Nat.choose (Nat.card α) s.ncard * s.ncard.factorial := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _)
  rw [hMk.index_of_fixingSubgroup_mul rfl]; rw [Nat.choose_mul_factorial_mul_factorial]
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ s)

end Index

end MulAction

namespace Equiv.Perm

variable {α : Type*}

/--
theorem `exists_smul_eq_embedding` / 定理 `exists_smul_eq_embedding`

English:
theorem exists_smul_eq_embedding
  statement: {ι : Type*} [Finite ι] {β : Type*}
  proof: by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair x y x.injective y.injective
  exact ⟨σ, Function.Embedding.ext fun i => by simp [Function.Embedding.smul_apply, hσ]⟩

中文:
定理 存在_smul_eq_embedding
  结论: {ι : 类型} [有限 ι] {β : 类型}
  证明: by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair x y x.injective y.injective
  exact ⟨σ, Function.Embedding.ext fun i => by simp [Function.Embedding.smul_apply, hσ]⟩

Depends on / 依赖: Embedding, Equiv.Perm.exists_extending_pair, Function, Function.Embedding.ext, Function.Embedding.smul_apply, exists_extending_pair, injective, smul_apply, x.injective, y.injective
-/
theorem exists_smul_eq_embedding {ι : Type*} [Finite ι] {β : Type*}
    (x y : ι ↪ β) : exists σ : Perm β, σ • x = y := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair x y x.injective y.injective
  exact ⟨σ, Function.Embedding.ext fun i => by simp [Function.Embedding.smul_apply, hσ]⟩

variable (α) in
/--
theorem `isMultiplyPretransitive` / 定理 `isMultiplyPretransitive`

English:
theorem isMultiplyPretransitive
  given: (n : Nat)
  proof: by
  rw [isMultiplyPretransitive_iff]
  exact exists_smul_eq_embedding

中文:
定理 isMultiplyPretransitive
  条件: (n : 自然数)
  证明: by
  rw [isMultiplyPretransitive_iff]
  exact exists_smul_eq_embedding

Depends on / 依赖: exists_smul_eq_embedding, isMultiplyPretransitive_iff
-/
theorem isMultiplyPretransitive (n : Nat) :
    IsMultiplyPretransitive (Perm α) α n := by
  rw [isMultiplyPretransitive_iff]
  exact exists_smul_eq_embedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsPreprimitive (Perm α) α
  body: isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive _ _)

中文:
实例 :
  签名: 是Preprimitive (置换 α) α
  定义体: isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive _ _)

Depends on / 依赖: isMultiplyPretransitive, isPreprimitive_of_is_two_pretransitive
-/
instance : IsPreprimitive (Perm α) α :=
  isPreprimitive_of_is_two_pretransitive (isMultiplyPretransitive _ _)

-- This is optimal, `AlternatingGroup α` is `Nat.card α - 2`-pretransitive.
/--
theorem `eq_top_of_isMultiplyPretransitive` / 定理 `eq_top_of_isMultiplyPretransitive`

English:
theorem eq_top_of_isMultiplyPretransitive
  statement: [Finite α] {G : Subgroup (Equiv.Perm α)}
  proof: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]
  intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx (x : Fin (Fintype.card α) ↪ α) : Function.Surjective x.toFun := by
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1) :
      (g • x) i = (k • x) i :=
    Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk (i : Fin (Fintype.card α)) : (g • x) i = (k • x) i := by
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · suffices i = j by
          rw [← this]; rw [← hi] at hj
          exact (lt_irrefl _ hj).elim
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj]; rw [hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff]; rw [hi]; rw [hj]
  ext a
  obtain ⟨i, rfl⟩ := (hx x) a
  specialize hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at hgk
  simp [← hgk, Subgroup.smul_def, Perm.smul_def]

中文:
定理 eq_top_of_isMultiplyPretransitive
  结论: [有限 α] {G : 子群 (等价.置换 α)}
  证明: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]
  intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx (x : Fin (Fintype.card α) ↪ α) : Function.Surjective x.toFun := by
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1) :
      (g • x) i = (k • x) i :=
    Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk (i : Fin (Fintype.card α)) : (g • x) i = (k • x) i := by
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · suffices i = j by
          rw [← this]; rw [← hi] at hj
          exact (lt_irrefl _ hj).elim
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj]; rw [hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff]; rw [hi]; rw [hj]
  ext a
  obtain ⟨i, rfl⟩ := (hx x) a
  specialize hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at hgk
  simp [← hgk, Subgroup.smul_def, Perm.smul_def]

Depends on / 依赖: Fin.castLEEmb, Fintype, Fintype.card, Fintype.equivFinOfCardEq, Fintype.ofFinite, Function, Function.Bi, Function.Surjective, Nat.card_eq_fintype_card, SetLike, SetLike.coe_mem, Surjective, card_eq_fintype_card, castLEEmb, coe_mem, eq_top_iff, equivFinOfCardEq, exists_smul_eq, j.trans, ofFinite
-/
theorem eq_top_of_isMultiplyPretransitive [Finite α] {G : Subgroup (Equiv.Perm α)}
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 1)) : G = ⊤ := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card] at hmt
  let j : Fin (Fintype.card α - 1) ↪ Fin (Fintype.card α) :=
    (Fin.castLEEmb ((Fintype.card α).sub_le 1))
  rw [eq_top_iff]
  intro k _
  let x : Fin (Fintype.card α) ↪ α := (Fintype.equivFinOfCardEq rfl).symm.toEmbedding
  let x' := j.trans x
  obtain ⟨g, hg'⟩ := exists_smul_eq G x' (k • x')
  suffices k = g by rw [this]; exact SetLike.coe_mem g
  have hx (x : Fin (Fintype.card α) ↪ α) : Function.Surjective x.toFun := by
    apply Function.Bijective.surjective
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨EmbeddingLike.injective x, Fintype.card_fin (Fintype.card α)⟩
  have hgk' (i : Fin (Fintype.card α)) (hi : i.val < Fintype.card α - 1) :
      (g • x) i = (k • x) i :=
    Function.Embedding.ext_iff.mp hg' ⟨i.val, hi⟩
  have hgk (i : Fin (Fintype.card α)) : (g • x) i = (k • x) i := by
    rcases lt_or_eq_of_le (le_sub_one_of_lt i.prop) with hi | hi
    · exact hgk' i hi
    · obtain ⟨j, hxj : (k • x) j = (g • x) i⟩ := hx (k • x) ((g • x) i)
      rcases lt_or_eq_of_le (le_sub_one_of_lt j.prop) with hj | hj
      · suffices i = j by
          rw [← this]; rw [← hi] at hj
          exact (lt_irrefl _ hj).elim
        apply EmbeddingLike.injective (g • x)
        rw [hgk' j hj]; rw [hxj]
      · rw [← hxj]
        apply congr_arg
        rw [Fin.ext_iff]; rw [hi]; rw [hj]
  ext a
  obtain ⟨i, rfl⟩ := (hx x) a
  specialize hgk i
  simp only [Function.Embedding.smul_apply, Equiv.Perm.smul_def] at hgk
  simp [← hgk, Subgroup.smul_def, Perm.smul_def]

end Equiv.Perm

namespace alternatingGroup

variable (α : Type*) [Fintype α] [DecidableEq α]

/--
theorem `isMultiplyPretransitive` / 定理 `isMultiplyPretransitive`

English:
theorem isMultiplyPretransitive
  proof: by
  rcases lt_or_ge (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have h2le : Nat.card α - 2 <= Nat.card α := sub_le (Nat.card α) 2
  have := Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
  have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α - 2) :=
    MulAction.isMultiplyPretransitive_of_le h2le le_rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm α) x y
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact ⟨⟨g, h⟩, hg⟩
  · have : (Finset.univ.image x)ᶜ.card = 2 := by
      rw [Finset.card_compl]; rw [Finset.univ.card_image_of_injective (by exact x.2)]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]; rw [Fintype.card_fin]; rw [tsub_tsub_cancel_of_le h2]
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp this
    refine ⟨⟨g * Equiv.swap a b, by simp [h, hab]⟩, ?_⟩
    ext i
    have h : x i in Finset.univ.image x := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [← Finset.notMem_compl]; rw [hs]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]; rw [not_or] at h
    simp [Equiv.swap_apply_of_ne_of_ne h.1 h.2, ← hg]

中文:
定理 isMultiplyPretransitive
  证明: by
  rcases lt_or_ge (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have h2le : Nat.card α - 2 <= Nat.card α := sub_le (Nat.card α) 2
  have := Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
  have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α - 2) :=
    MulAction.isMultiplyPretransitive_of_le h2le le_rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm α) x y
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact ⟨⟨g, h⟩, hg⟩
  · have : (Finset.univ.image x)ᶜ.card = 2 := by
      rw [Finset.card_compl]; rw [Finset.univ.card_image_of_injective (by exact x.2)]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]; rw [Fintype.card_fin]; rw [tsub_tsub_cancel_of_le h2]
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp this
    refine ⟨⟨g * Equiv.swap a b, by simp [h, hab]⟩, ?_⟩
    ext i
    have h : x i in Finset.univ.image x := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [← Finset.notMem_compl]; rw [hs]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]; rw [not_or] at h
    simp [Equiv.swap_apply_of_ne_of_ne h.1 h.2, ← hg]

Depends on / 依赖: Equiv.Perm, Equiv.Perm.isMultiplyPretransitive, Equiv.Perm.sign, Int.units_eq_one_or, IsMultiplyPretransitive, MulAction, MulAction.isMultiplyPretransitive_of_le, Nat.card, Nat.sub_eq_zero_of_le, exists_smul_eq, isMultiplyPretransitive, isMultiplyPretransitive_of_le, is_zero_pretransitive, le_of_lt, le_rfl, lt_or_ge, sub_eq_zero_of_le, sub_le, units_eq_one_or
-/
theorem isMultiplyPretransitive :
    IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) := by
  rcases lt_or_ge (Nat.card α) 2 with h2 | h2
  · rw [Nat.sub_eq_zero_of_le (le_of_lt h2)]
    apply is_zero_pretransitive
  have h2le : Nat.card α - 2 <= Nat.card α := sub_le (Nat.card α) 2
  have := Equiv.Perm.isMultiplyPretransitive α (Nat.card α)
  have : IsMultiplyPretransitive (Equiv.Perm α) α (Nat.card α - 2) :=
    MulAction.isMultiplyPretransitive_of_le h2le le_rfl
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := exists_smul_eq (Equiv.Perm α) x y
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
  · exact ⟨⟨g, h⟩, hg⟩
  · have : (Finset.univ.image x)ᶜ.card = 2 := by
      rw [Finset.card_compl]; rw [Finset.univ.card_image_of_injective (by exact x.2)]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]; rw [Fintype.card_fin]; rw [tsub_tsub_cancel_of_le h2]
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp this
    refine ⟨⟨g * Equiv.swap a b, by simp [h, hab]⟩, ?_⟩
    ext i
    have h : x i in Finset.univ.image x := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rw [← Finset.notMem_compl]; rw [hs]; rw [Finset.mem_insert]; rw [Finset.mem_singleton]; rw [not_or] at h
    simp [Equiv.swap_apply_of_ne_of_ne h.1 h.2, ← hg]

/--
theorem `_root_.IsMultiplyPretransitive.alternatingGroup_le` / 定理 `_root_.IsMultiplyPretransitive.alternatingGroup_le`

English:
theorem _root_.IsMultiplyPretransitive.alternatingGroup_le
  proof: by
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α < 2
    rw [eq_bot_of_card_le_two hα1.le]
    exact bot_le
  -- 2 ≤ Nat.card α
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  -- one picks up a set of cardinality (card α - 2)
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt
  -- The index of (fixingSubgroup G s) is (card α)!/2
  have := hmt.index_of_fixingSubgroup_mul rfl
  rw [hs]; rw [Nat.sub_sub_self hα]; rw [factorial_two] at this
  -- conclude
  rw [← mul_le_mul_iff_of_pos_left (a := Nat.card G) card_pos]; rw [Subgroup.card_mul_index]; rw [← (fixingSubgroup G s).index_mul_card]; rw [mul_assoc]; rw [mul_comm _ 2]; rw [← mul_assoc]
  rw [this]; rw [Nat.card_perm]
  refine Nat.le_mul_of_pos_right (Nat.card α)! card_pos

中文:
定理 _root_.IsMultiplyPretransitive.alternatingGroup_le
  证明: by
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α < 2
    rw [eq_bot_of_card_le_two hα1.le]
    exact bot_le
  -- 2 ≤ Nat.card α
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  -- one picks up a set of cardinality (card α - 2)
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt
  -- The index of (fixingSubgroup G s) is (card α)!/2
  have := hmt.index_of_fixingSubgroup_mul rfl
  rw [hs]; rw [Nat.sub_sub_self hα]; rw [factorial_two] at this
  -- conclude
  rw [← mul_le_mul_iff_of_pos_left (a := Nat.card G) card_pos]; rw [Subgroup.card_mul_index]; rw [← (fixingSubgroup G s).index_mul_card]; rw [mul_assoc]; rw [mul_comm _ 2]; rw [← mul_assoc]
  rw [this]; rw [Nat.card_perm]
  refine Nat.le_mul_of_pos_right (Nat.card α)! card_pos

Depends on / 依赖: Nat.card, Nat.lt_or_ge, bot_le, eq_bot_of_card_le_two, lt_or_ge
-/
theorem _root_.IsMultiplyPretransitive.alternatingGroup_le
    (G : Subgroup (Equiv.Perm α))
    (hmt : IsMultiplyPretransitive G α (Nat.card α - 2)) :
    alternatingGroup α <= G := by
  rcases Nat.lt_or_ge (Nat.card α) 2 with hα1 | hα
  · -- Nat.card α < 2
    rw [eq_bot_of_card_le_two hα1.le]
    exact bot_le
  -- 2 ≤ Nat.card α
  apply Equiv.Perm.alternatingGroup_le_of_index_le_two
  -- one picks up a set of cardinality (card α - 2)
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq (s := (Set.univ : Set α)) (n := Nat.card α - 2)
      (by rw [Set.ncard_univ]; exact sub_le (Nat.card α) 2)
  rw [← hs] at hmt
  -- The index of (fixingSubgroup G s) is (card α)!/2
  have := hmt.index_of_fixingSubgroup_mul rfl
  rw [hs]; rw [Nat.sub_sub_self hα]; rw [factorial_two] at this
  -- conclude
  rw [← mul_le_mul_iff_of_pos_left (a := Nat.card G) card_pos]; rw [Subgroup.card_mul_index]; rw [← (fixingSubgroup G s).index_mul_card]; rw [mul_assoc]; rw [mul_comm _ 2]; rw [← mul_assoc]
  rw [this]; rw [Nat.card_perm]
  refine Nat.le_mul_of_pos_right (Nat.card α)! card_pos

/--
theorem `isPretransitive_of_three_le_card` / 定理 `isPretransitive_of_three_le_card`

English:
theorem isPretransitive_of_three_le_card
  given: (h : 3 <= Nat.card α)
  proof: by
  rw [← is_one_pretransitive_iff]
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_trans (by norm_num) h)]

中文:
定理 isPretransitive_of_three_le_card
  条件: (h : 3 <= 自然数.card α)
  证明: by
  rw [← is_one_pretransitive_iff]
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_trans (by norm_num) h)]

Depends on / 依赖: Nat.card, Nat.sub_add_cancel, add_le_add_iff_right, isMultiplyPretransitive, isMultiplyPretransitive_of_le, is_one_pretransitive_iff, le_trans, sub_add_cancel, sub_le
-/
theorem isPretransitive_of_three_le_card (h : 3 <= Nat.card α) :
    IsPretransitive (alternatingGroup α) α := by
  rw [← is_one_pretransitive_iff]
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_trans (by norm_num) h)]

/--
theorem `isTrivialBlock_of_isBlock` / 定理 `isTrivialBlock_of_isBlock`

English:
theorem isTrivialBlock_of_isBlock
  given: {B : Set α} (hB : IsBlock (alternatingGroup α) B)
  proof: by
  rcases le_or_gt (Nat.card α) 2 with h2 | h2
  · exact isTrivialBlock_of_card_le_two h2 B
  rcases le_or_gt (Nat.card α) 3 with h3 | h4
  · replace h3 : Nat.card α = 3 := le_antisymm h3 h2
    have : IsPretransitive (alternatingGroup α) α := isPretransitive_of_three_le_card α h3.ge
    have : IsPreprimitive (alternatingGroup α) α := IsPreprimitive.of_prime_card (h3 ▸ prime_three)
    exact this.isTrivialBlock_of_isBlock hB
  -- IsTrivialBlock hB, for 4 ≤ Nat.card α
  suffices IsPreprimitive (alternatingGroup α) α by
    apply IsPreprimitive.isTrivialBlock_of_isBlock hB
  apply isPreprimitive_of_is_two_pretransitive
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_of_lt h2)]

中文:
定理 isTrivialBlock_of_isBlock
  条件: {B : 集合 α} (hB : IsBlock (alternatingGroup α) B)
  证明: by
  rcases le_or_gt (Nat.card α) 2 with h2 | h2
  · exact isTrivialBlock_of_card_le_two h2 B
  rcases le_or_gt (Nat.card α) 3 with h3 | h4
  · replace h3 : Nat.card α = 3 := le_antisymm h3 h2
    have : IsPretransitive (alternatingGroup α) α := isPretransitive_of_three_le_card α h3.ge
    have : IsPreprimitive (alternatingGroup α) α := IsPreprimitive.of_prime_card (h3 ▸ prime_three)
    exact this.isTrivialBlock_of_isBlock hB
  -- IsTrivialBlock hB, for 4 ≤ Nat.card α
  suffices IsPreprimitive (alternatingGroup α) α by
    apply IsPreprimitive.isTrivialBlock_of_isBlock hB
  apply isPreprimitive_of_is_two_pretransitive
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_of_lt h2)]

Depends on / 依赖: IsPreprimitive, IsPreprimitive.of_prime_card, IsPretransitive, Nat.card, alternatingGroup, h3.ge, isPretransitive_of_three_le_card, isTrivialBlock_of_card_le_two, isTrivialBlock_of_isBlock, le_antisymm, le_or_gt, of_prime_card, prime_three, replace, this.isTrivialBlock_of_isBlock
-/
theorem isTrivialBlock_of_isBlock {B : Set α} (hB : IsBlock (alternatingGroup α) B) :
    IsTrivialBlock B := by
  rcases le_or_gt (Nat.card α) 2 with h2 | h2
  · exact isTrivialBlock_of_card_le_two h2 B
  rcases le_or_gt (Nat.card α) 3 with h3 | h4
  · replace h3 : Nat.card α = 3 := le_antisymm h3 h2
    have : IsPretransitive (alternatingGroup α) α := isPretransitive_of_three_le_card α h3.ge
    have : IsPreprimitive (alternatingGroup α) α := IsPreprimitive.of_prime_card (h3 ▸ prime_three)
    exact this.isTrivialBlock_of_isBlock hB
  -- IsTrivialBlock hB, for 4 ≤ Nat.card α
  suffices IsPreprimitive (alternatingGroup α) α by
    apply IsPreprimitive.isTrivialBlock_of_isBlock hB
  apply isPreprimitive_of_is_two_pretransitive
  let := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (sub_le _ _)
  rwa [← add_le_add_iff_right 2, Nat.sub_add_cancel (le_of_lt h2)]

/--
theorem `isPreprimitive_of_three_le_card` / 定理 `isPreprimitive_of_three_le_card`

English:
theorem isPreprimitive_of_three_le_card
  given: (h : 3 <= Nat.card α)
  proof: letI := isPretransitive_of_three_le_card α h
  { isTrivialBlock_of_isBlock := isTrivialBlock_of_isBlock α }

中文:
定理 isPreprimitive_of_three_le_card
  条件: (h : 3 <= 自然数.card α)
  证明: letI := isPretransitive_of_three_le_card α h
  { isTrivialBlock_of_isBlock := isTrivialBlock_of_isBlock α }

Depends on / 依赖: isPretransitive_of_three_le_card, isTrivialBlock_of_isBlock
-/
theorem isPreprimitive_of_three_le_card (h : 3 <= Nat.card α) :
    IsPreprimitive (alternatingGroup α) α :=
  letI := isPretransitive_of_three_le_card α h
  { isTrivialBlock_of_isBlock := isTrivialBlock_of_isBlock α }

end alternatingGroup
