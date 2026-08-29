/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.Order.TransfiniteIteration

/-!
# Sharply smaller regular cardinals

In this file, we introduce the predicate `Cardinal.SharplyLT`. Given two regular
cardinals `κ₁ < κ₂`, this condition can be described in different ways:
(i) the category `CardinalDirectedPoset κ₁` (of `κ₁`-directed partially ordered
  types, with order embeddings as morphisms), is `κ₂`-accessible;
(ii) any `κ₁`-accessible category is `κ₂`-accessible.
(iii) for any type `X` of cardinality `< κ₂`, there exists a cofinal set of
  cardinality `< κ₂` in the subtype of subsets of `X` of cardinality `< κ₁`;
(iv) for any `κ₁`-directed partially ordered type `X` and any subset `A` of `X`
  of cardinality `< κ₂`, there exists a `κ₁`-directed subset `B` of `X` containing `A`
  that is of cardinality `< κ₂`.
The equivalence of these conditions (i)-(iv) is Theorem 2.11 in the book by Adámek and Rosický
((i) → (iii) is `exists_cofinal_of_isCardinalAccessibleCategory_cardinalDirectedPoset`,
(iii) → (iv) is `exists_isCardinalFiltered_set_of_exists_cofinal`, (ii) → (i) is obvious;
the rest is TODO @joelriou). Here, we take (i) as the definition.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v u

open CategoryTheory Limits

namespace Cardinal

variable {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]

variable (κ₁ κ₂) in
/-- If `κ₁ < κ₂` are two regular cardinals, we say that `κ₁` is sharply
smaller than `κ₂` if the category `CardinalDirectedPoset κ₁`
is `κ₂`-accessible. There are other characterizations (TODO @joelriou),
including the property that any `κ₁`-accessible category is
also `κ₂`-accessible. -/
public structure SharplyLT : Prop where
  lt : κ₁ < κ₂
  isCardinalAccessible_cardinalDirectedPoset :
    IsCardinalAccessibleCategory (CardinalDirectedPoset κ₁) κ₂

namespace SharplyLT

public lemma le (h : SharplyLT κ₁ κ₂) : κ₁ <= κ₂ := h.lt.le

set_option backward.defeqAttrib.useBackward true in
open CardinalDirectedPoset in
/-- This is the implication (i) → (iii) in the characterizations
of `SharplyLT κ₁ κ₂` in the docstring of this file. -/
public lemma exists_cofinal_of_isCardinalAccessibleCategory_cardinalDirectedPoset
    (h : κ₁ <= κ₂) [IsCardinalAccessibleCategory (CardinalDirectedPoset κ₁) κ₂]
    {X : Type w} (hX : HasCardinalLT X κ₂) :
    exists (Y : Set (SetCardinalLT κ₁ X)), HasCardinalLT Y κ₂ ∧ IsCofinal Y := by
  -- We write the partially ordered type `SetCardinalLT κ₁ X` of subsets
  -- of `X` of cardinality `< κ₁` as a `κ₂`-filtered colimit (with index
  -- category `J`) of `κ₂`-presentable objects (i.e. partially ordered
  -- types of cardinality `< κ₂`.)
  obtain ⟨J, _, _, ⟨p⟩⟩ := (isCardinalFilteredGenerator_isCardinalPresentable
    (CardinalDirectedPoset κ₁) κ₂).exists_colimitsOfShape (setCardinalLT κ₁ X)
  have : IsCardinalFiltered J κ₁ := .of_le _ h
  have hp (j : J) : HasCardinalLT (p.diag.obj j).obj κ₂ := by
    rw [← CardinalDirectedPoset.isCardinalPresentable_iff _ h]
    exact p.prop_diag_obj j
  -- For each `x : X`, we choose `j : J` in such a way that the singleton
  -- `{x}` belongs to the image of `p.diag.obj j` in `SetCardinalLT κ₁ X`.
  choose j y hy using fun x => Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CardinalDirectedPoset κ₁)) p.isColimit)
    (SetCardinalLT.singleton κ₁ x)
  dsimp at y hy
  -- The expected cofinal set `A` will be the range of `p.ι.app j'`
  -- where `j' : J` is such that for any `x : X`, there is a map `j x ⟶ j'`
  let j' := IsCardinalFiltered.max j hX
  let y' (x : X) : (p.diag.obj j').obj :=
    p.diag.map (IsCardinalFiltered.toMax j hX x) (y x)
  have hy' (x : X) : p.ι.app j' (y' x) = SetCardinalLT.singleton κ₁ x := by
    rw [← hy]; rw [← p.w (IsCardinalFiltered.toMax j hX x)]
    rfl
  refine ⟨Set.range (p.ι.app j'), (hp j').of_surjective _
    (Set.rangeFactorization_surjective (f := p.ι.app j')), fun ⟨B, hB⟩ => ?_⟩
  let j'' := IsCardinalFiltered.max (fun b => y' b.val) hB
  refine ⟨_, ⟨j'', rfl⟩, fun b hb => ?_⟩
  have : y' b <= j'' := (leOfHom (IsCardinalFiltered.toMax (fun b => y' b.val) hB ⟨b, hb⟩) :)
  refine (p.ι.app j').hom.hom.monotone this ?_
  convert Set.mem_singleton b
  exact Subtype.ext_iff.1 (hy' b)

section

open CardinalDirectedPoset

namespace existsIsCardinalFilteredSetOfExistsCofinal

/-! The definitions in this section are part of the proof of the
lemma `exists_isCardinalFiltered_set_of_exists_cofinal` below,
which is the implication (iii) → (iv) in the characterizations
of `SharplyLT κ₁ κ₂` which appear in the docstring of this file. -/

variable (h₀ : κ₁ < κ₂)
  {X : Type w} [PartialOrder X]
  -- The variables `Y`, `hY` and `hY'` below can be obtained by applying
  -- the `choose` tactic to an assumption of the form
  -- `∃ (Y : Set (SetCardinalLT κ₁ X)), HasCardinalLT Y κ₂ ∧ IsCofinal Y)`
  -- e.g. when the condition (iii) in the docstring of this file is satisfied
  (Y : forall (B : Set X) (_ : HasCardinalLT B κ₂), Set (SetCardinalLT κ₁ B))
  (hY : forall (B : Set X) (hB : HasCardinalLT B κ₂), HasCardinalLT (Y B hB) κ₂)
  (hY' : forall (B : Set X) (hB : HasCardinalLT B κ₂), IsCofinal (Y B hB))
  -- In the proof of `exists_isCardinalFiltered_set_of_exists_cofinal` below,
  -- we shall show that we can find such `m` and `hm`, i.e.
  -- for any `B : Set X`, `hB : HasCardinalLT B κ₂`, `C : SetCardinalLT κ₁ B`,
  -- if `C ∈ Y B hB`, then there exists `m : X` such that all the elements
  -- of `C` are less than or equal to `m`.
  (m : forall (B : Set X) (hB : HasCardinalLT B κ₂) (C : SetCardinalLT κ₁ B),
    C in Y B hB -> X)
  (hm : forall (B : Set X) (hB : HasCardinalLT B κ₂) (C : SetCardinalLT κ₁ B)
    (hC : C in Y B hB) (b : B), b in C.val -> b <= m B hB C hC)
  (A : Set X) (hA : HasCardinalLT A κ₂)

/--
Definition of `φ₀` / `φ₀` 的定义

English:
definition φ₀
  signature: (B : Set X) (hB : HasCardinalLT B κ₂)
  body: ⋃ (C : Y B hB), Subtype.val '' C.val.val union {m B hB C C.prop}

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] in
include hY' hm in

中文:
定义 φ₀
  签名: (B : 集合 X) (hB : HasCardinalLT B κ₂)
  定义体: ⋃ (C : Y B hB), Subtype.val '' C.val.val union {m B hB C C.prop}

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] in
include hY' hm in

Depends on / 依赖: C.prop, C.val.val, Subtype, Subtype.val
-/
def φ₀ (B : Set X) (hB : HasCardinalLT B κ₂) : Set X :=
    ⋃ (C : Y B hB), Subtype.val '' C.val.val union {m B hB C C.prop}

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] in
include hY' hm in
/--
lemma `hφ₀` / 引理 `hφ₀`

English:
lemma hφ₀
  statement: (B : Set X) (hB : HasCardinalLT B κ₂) {T : Type w} (f : T -> B)
  proof: by
  let C₀ : SetCardinalLT κ₁ B :=
    ⟨Set.range f, hT.of_surjective _ Set.rangeFactorization_surjective⟩
  obtain ⟨C, hC, hC'⟩ := hY' B hB C₀
  exact ⟨⟨m B hB C hC, Set.subset_iUnion _ ⟨C, hC⟩ (Or.inr (by simp))⟩,
    fun t => hm B hB C hC (f t) (hC' (by simp [C₀]))⟩

中文:
引理 hφ₀
  结论: (B : 集合 X) (hB : HasCardinalLT B κ₂) {T : 类型 w} (f : T -> B)
  证明: by
  let C₀ : SetCardinalLT κ₁ B :=
    ⟨Set.range f, hT.of_surjective _ Set.rangeFactorization_surjective⟩
  obtain ⟨C, hC, hC'⟩ := hY' B hB C₀
  exact ⟨⟨m B hB C hC, Set.subset_iUnion _ ⟨C, hC⟩ (Or.inr (by simp))⟩,
    fun t => hm B hB C hC (f t) (hC' (by simp [C₀]))⟩

Depends on / 依赖: Or.inr, Set.range, Set.rangeFactorization_surjective, Set.subset_iUnion, SetCardinalLT, hT.of_surjective, of_surjective, rangeFactorization_surjective, subset_iUnion
-/
lemma hφ₀ (B : Set X) (hB : HasCardinalLT B κ₂) {T : Type w} (f : T -> B)
    (hT : HasCardinalLT T κ₁) :
    exists (a : φ₀ Y m B hB), forall (t : T), f t <= a.val := by
  let C₀ : SetCardinalLT κ₁ B :=
    ⟨Set.range f, hT.of_surjective _ Set.rangeFactorization_surjective⟩
  obtain ⟨C, hC, hC'⟩ := hY' B hB C₀
  exact ⟨⟨m B hB C hC, Set.subset_iUnion _ ⟨C, hC⟩ (Or.inr (by simp))⟩,
    fun t => hm B hB C hC (f t) (hC' (by simp [C₀]))⟩

open scoped Classical in
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: (B : Set X)
  body: if hB : HasCardinalLT B κ₂ then φ₀ Y m B hB else B

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [PartialOrder X] in

中文:
定义 φ
  签名: (B : 集合 X)
  定义体: if hB : HasCardinalLT B κ₂ then φ₀ Y m B hB else B

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [PartialOrder X] in

Depends on / 依赖: HasCardinalLT
-/
noncomputable def φ (B : Set X) : Set X :=
  if hB : HasCardinalLT B κ₂ then φ₀ Y m B hB else B

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [PartialOrder X] in
/--
lemma `φ_eq` / 引理 `φ_eq`

English:
lemma φ_eq
  given: (B : Set X) (hB : HasCardinalLT B κ₂)
  proof: dif_pos hB

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in

中文:
引理 φ_eq
  条件: (B : 集合 X) (hB : HasCardinalLT B κ₂)
  证明: dif_pos hB

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in

Depends on / 依赖: dif_pos
-/
lemma φ_eq (B : Set X) (hB : HasCardinalLT B κ₂) :
  φ Y m B = φ₀ Y m B hB := dif_pos hB

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in
/--
lemma `le_φ` / 引理 `le_φ`

English:
lemma le_φ
  given: (B : Set X)
  statement: B <= φ Y m B
  proof: by
  dsimp [φ]
  split_ifs with hB
  · intro b hb
    obtain ⟨C, hC, hC'⟩ := hY' B hB ⟨{⟨b, hb⟩},
      hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩
    refine Set.subset_iUnion _ ⟨C, hC⟩ (Or.inl ?_)
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨hb, @hC' ⟨b, hb⟩ (by simp)⟩
  · simp

include h₀ hA hY in
omit [PartialOrder X] in

中文:
引理 le_φ
  条件: (B : 集合 X)
  结论: B <= φ Y m B
  证明: by
  dsimp [φ]
  split_ifs with hB
  · intro b hb
    obtain ⟨C, hC, hC'⟩ := hY' B hB ⟨{⟨b, hb⟩},
      hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩
    refine Set.subset_iUnion _ ⟨C, hC⟩ (Or.inl ?_)
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨hb, @hC' ⟨b, hb⟩ (by simp)⟩
  · simp

include h₀ hA hY in
omit [PartialOrder X] in

Depends on / 依赖: Fact.out, IsRegular, IsRegular.aleph0_le, Or.inl, Set.mem_image, Set.subset_iUnion, Subtype, Subtype.exists, aleph0_le, exists_and_right, exists_eq_right, hasCardinalLT_of_finite, mem_image, split_ifs, subset_iUnion
-/
lemma le_φ (B : Set X) : B <= φ Y m B := by
  dsimp [φ]
  split_ifs with hB
  · intro b hb
    obtain ⟨C, hC, hC'⟩ := hY' B hB ⟨{⟨b, hb⟩},
      hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩
    refine Set.subset_iUnion _ ⟨C, hC⟩ (Or.inl ?_)
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨hb, @hC' ⟨b, hb⟩ (by simp)⟩
  · simp

include h₀ hA hY in
omit [PartialOrder X] in
/--
lemma `hasCardinalLT_transfiniteIterate_φ` / 引理 `hasCardinalLT_transfiniteIterate_φ`

English:
lemma hasCardinalLT_transfiniteIterate_φ
  given: (j : κ₁.ord.ToType)
  proof: by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
    let := WellFoundedLT.toOrderBot κ₁.ord.ToType
    simpa [hj.eq_bot]
  | succ j hj hj' =>
    have hκ₂ : κ₂.IsRegular := Fact.out
    rw [transfiniteIterate_succ _ _ _ hj]; rw [φ_eq _ _ _ hj']
    refine hasCardinalLT_iUnion _ (hY _ _)
      (fun ⟨C, hC⟩ => hasCardinalLT_union hκ₂.aleph0_le ?_
        (hasCardinalLT_of_finite _ _ hκ₂.aleph0_le))
    refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ => ?_)
      (fun c₁ c₂ hc => ?_)
    · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
      exact ⟨⟨c, hc.choose⟩, hc.choose_spec⟩
    · simpa only [Subtype.ext_iff] using hc
  | isSuccLimit j hj hj' =>
    rw [transfiniteIterate_limit _ _ _ hj]; rw [Set.iSup_eq_iUnion]
    refine hasCardinalLT_iUnion _
      (HasCardinalLT.of_injective ?_ _ Subtype.val_injective) (fun ⟨k, hk⟩ => hj' _ hk)
    simpa [hasCardinalLT_iff_cardinal_mk_lt]

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in

中文:
引理 hasCardinalLT_transfiniteIterate_φ
  条件: (j : κ₁.ord.ToType)
  证明: by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
    let := WellFoundedLT.toOrderBot κ₁.ord.ToType
    simpa [hj.eq_bot]
  | succ j hj hj' =>
    have hκ₂ : κ₂.IsRegular := Fact.out
    rw [transfiniteIterate_succ _ _ _ hj]; rw [φ_eq _ _ _ hj']
    refine hasCardinalLT_iUnion _ (hY _ _)
      (fun ⟨C, hC⟩ => hasCardinalLT_union hκ₂.aleph0_le ?_
        (hasCardinalLT_of_finite _ _ hκ₂.aleph0_le))
    refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ => ?_)
      (fun c₁ c₂ hc => ?_)
    · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
      exact ⟨⟨c, hc.choose⟩, hc.choose_spec⟩
    · simpa only [Subtype.ext_iff] using hc
  | isSuccLimit j hj hj' =>
    rw [transfiniteIterate_limit _ _ _ hj]; rw [Set.iSup_eq_iUnion]
    refine hasCardinalLT_iUnion _
      (HasCardinalLT.of_injective ?_ _ Subtype.val_injective) (fun ⟨k, hk⟩ => hj' _ hk)
    simpa [hasCardinalLT_iff_cardinal_mk_lt]

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in

Depends on / 依赖: C.prop.of_le, Cardinal, Cardinal.nonempty_ord_toType, Fact.out, IsRegular, IsRegular.ne_zero, SuccOrder, SuccOrder.limitRecOn, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, aleph0_le, eq_bot, hasCardinalLT_iUnion, hasCardinalLT_of_finite, hasCardinalLT_union, hj.eq_bot, limitRecOn, ne_zero, nonempty_ord_toType
-/
lemma hasCardinalLT_transfiniteIterate_φ (j : κ₁.ord.ToType) :
    HasCardinalLT (transfiniteIterate (φ Y m) j A :) κ₂ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
    let := WellFoundedLT.toOrderBot κ₁.ord.ToType
    simpa [hj.eq_bot]
  | succ j hj hj' =>
    have hκ₂ : κ₂.IsRegular := Fact.out
    rw [transfiniteIterate_succ _ _ _ hj]; rw [φ_eq _ _ _ hj']
    refine hasCardinalLT_iUnion _ (hY _ _)
      (fun ⟨C, hC⟩ => hasCardinalLT_union hκ₂.aleph0_le ?_
        (hasCardinalLT_of_finite _ _ hκ₂.aleph0_le))
    refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ => ?_)
      (fun c₁ c₂ hc => ?_)
    · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
      exact ⟨⟨c, hc.choose⟩, hc.choose_spec⟩
    · simpa only [Subtype.ext_iff] using hc
  | isSuccLimit j hj hj' =>
    rw [transfiniteIterate_limit _ _ _ hj]; rw [Set.iSup_eq_iUnion]
    refine hasCardinalLT_iUnion _
      (HasCardinalLT.of_injective ?_ _ Subtype.val_injective) (fun ⟨k, hk⟩ => hj' _ hk)
    simpa [hasCardinalLT_iff_cardinal_mk_lt]

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in
/--
lemma `monotone_transfiniteIterate_φ` / 引理 `monotone_transfiniteIterate_φ`

English:
lemma monotone_transfiniteIterate_φ
  proof: have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ₁.ord.ToType
  monotone_transfiniteIterate _ _ (le_φ _ hY' _)

omit [PartialOrder X] [Fact κ₂.IsRegular] in

中文:
引理 monotone_transfiniteIterate_φ
  证明: have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ₁.ord.ToType
  monotone_transfiniteIterate _ _ (le_φ _ hY' _)

omit [PartialOrder X] [Fact κ₂.IsRegular] in

Depends on / 依赖: Cardinal, Cardinal.nonempty_ord_toType, Fact.out, IsRegular, IsRegular.ne_zero, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, monotone_transfiniteIterate, ne_zero, nonempty_ord_toType, ord.ToType, toOrderBot
-/
lemma monotone_transfiniteIterate_φ :
    Monotone (fun (j : κ₁.ord.ToType) => transfiniteIterate (φ Y m) j A) :=
  have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ₁.ord.ToType
  monotone_transfiniteIterate _ _ (le_φ _ hY' _)

omit [PartialOrder X] [Fact κ₂.IsRegular] in
/--
lemma `subset_iUnion` / 引理 `subset_iUnion`

English:
lemma subset_iUnion
  statement: A subseteq ⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A
  proof: by
  have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  let := WellFoundedLT.toOrderBot κ₁.ord.ToType
  exact subset_trans (by simp) (Set.subset_iUnion _ ⊥)

include h₀ hY hY' hm hA in

中文:
引理 subset_iUnion
  结论: A subseteq ⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A
  证明: by
  have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  let := WellFoundedLT.toOrderBot κ₁.ord.ToType
  exact subset_trans (by simp) (Set.subset_iUnion _ ⊥)

include h₀ hY hY' hm hA in

Depends on / 依赖: Cardinal, Cardinal.nonempty_ord_toType, Fact.out, IsRegular, IsRegular.ne_zero, Set.subset_iUnion, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, ne_zero, nonempty_ord_toType, ord.ToType, subset_iUnion, subset_trans, toOrderBot
-/
lemma subset_iUnion : A subseteq ⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A := by
  have := Cardinal.nonempty_ord_toType (c := κ₁) (IsRegular.ne_zero Fact.out)
  let := WellFoundedLT.toOrderBot κ₁.ord.ToType
  exact subset_trans (by simp) (Set.subset_iUnion _ ⊥)

include h₀ hY hY' hm hA in
/--
lemma `isCardinalFiltered_iUnion` / 引理 `isCardinalFiltered_iUnion`

English:
lemma isCardinalFiltered_iUnion
  proof: by
  suffices forall ⦃K : Type w⦄ (j : κ₁.ord.ToType) (f : K -> (transfiniteIterate (φ Y m) j A : Set _))
      (hK : HasCardinalLT K κ₁),
      exists (x : (transfiniteIterate (φ Y m) (Order.succ j) A : Set _)),
          forall (k : K), (f k).val <= x.val by
    refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have (k : K) : exists (j : κ₁.ord.ToType), (f k).val in transfiniteIterate (φ Y m) j A := by
      simpa only [Set.mem_iUnion] using (f k).prop
    choose a ha using this
    obtain ⟨⟨z, hz⟩, hz'⟩ := this (IsCardinalFiltered.max a hK) (fun k =>
      ⟨(f k).val, monotone_transfiniteIterate_φ Y hY' m A
          (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k)⟩) hK
    exact ⟨⟨z, Set.subset_iUnion _ _ hz⟩, hz'⟩
  intro K j f hK
  obtain ⟨⟨x, hx⟩, hx'⟩ := hφ₀ Y hY' m hm _
    (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _) f hK
  refine ⟨⟨x, ?_⟩, hx'⟩
  have : NoMaxOrder κ₁.ord.ToType := noMaxOrder (IsRegular.aleph0_le Fact.out)
  rwa [transfiniteIterate_succ _ _ _ (not_isMax j),
    φ_eq _ _ _ (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _)]

中文:
引理 isCardinalFiltered_iUnion
  证明: by
  suffices forall ⦃K : Type w⦄ (j : κ₁.ord.ToType) (f : K -> (transfiniteIterate (φ Y m) j A : Set _))
      (hK : HasCardinalLT K κ₁),
      exists (x : (transfiniteIterate (φ Y m) (Order.succ j) A : Set _)),
          forall (k : K), (f k).val <= x.val by
    refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have (k : K) : exists (j : κ₁.ord.ToType), (f k).val in transfiniteIterate (φ Y m) j A := by
      simpa only [Set.mem_iUnion] using (f k).prop
    choose a ha using this
    obtain ⟨⟨z, hz⟩, hz'⟩ := this (IsCardinalFiltered.max a hK) (fun k =>
      ⟨(f k).val, monotone_transfiniteIterate_φ Y hY' m A
          (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k)⟩) hK
    exact ⟨⟨z, Set.subset_iUnion _ _ hz⟩, hz'⟩
  intro K j f hK
  obtain ⟨⟨x, hx⟩, hx'⟩ := hφ₀ Y hY' m hm _
    (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _) f hK
  refine ⟨⟨x, ?_⟩, hx'⟩
  have : NoMaxOrder κ₁.ord.ToType := noMaxOrder (IsRegular.aleph0_le Fact.out)
  rwa [transfiniteIterate_succ _ _ _ (not_isMax j),
    φ_eq _ _ _ (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _)]

Depends on / 依赖: HasCardinalLT, Order.succ, Set.mem_iUnion, ToType, hasCardinalLT_iff_cardinal_mk_lt, isCardinalFiltered_preorder, mem_iUnion, ord.ToType, transfiniteIterate, x.val
-/
lemma isCardinalFiltered_iUnion :
    IsCardinalFiltered (⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A) κ₁ := by
  suffices forall ⦃K : Type w⦄ (j : κ₁.ord.ToType) (f : K -> (transfiniteIterate (φ Y m) j A : Set _))
      (hK : HasCardinalLT K κ₁),
      exists (x : (transfiniteIterate (φ Y m) (Order.succ j) A : Set _)),
          forall (k : K), (f k).val <= x.val by
    refine isCardinalFiltered_preorder _ _ (fun K f hK => ?_)
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have (k : K) : exists (j : κ₁.ord.ToType), (f k).val in transfiniteIterate (φ Y m) j A := by
      simpa only [Set.mem_iUnion] using (f k).prop
    choose a ha using this
    obtain ⟨⟨z, hz⟩, hz'⟩ := this (IsCardinalFiltered.max a hK) (fun k =>
      ⟨(f k).val, monotone_transfiniteIterate_φ Y hY' m A
          (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k)⟩) hK
    exact ⟨⟨z, Set.subset_iUnion _ _ hz⟩, hz'⟩
  intro K j f hK
  obtain ⟨⟨x, hx⟩, hx'⟩ := hφ₀ Y hY' m hm _
    (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _) f hK
  refine ⟨⟨x, ?_⟩, hx'⟩
  have : NoMaxOrder κ₁.ord.ToType := noMaxOrder (IsRegular.aleph0_le Fact.out)
  rwa [transfiniteIterate_succ _ _ _ (not_isMax j),
    φ_eq _ _ _ (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _)]

end existsIsCardinalFilteredSetOfExistsCofinal

open existsIsCardinalFilteredSetOfExistsCofinal in
/-- This is the implication (iii) → (iv) in the characterizations
of `SharplyLT κ₁ κ₂` in the docstring of this file. -/
public lemma exists_isCardinalFiltered_set_of_exists_cofinal (h₀ : κ₁ < κ₂)
    (h : forall (X : Type w) (_ : HasCardinalLT X κ₂),
      exists (Y : Set (SetCardinalLT κ₁ X)), HasCardinalLT Y κ₂ ∧ IsCofinal Y)
    {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (hA : HasCardinalLT A κ₂) :
    exists (B : Set X), A subseteq B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂ := by
  choose Y hY hY' using fun (B : Set X) hB => h B hB
  have hY'' (B : Set X) (hB : HasCardinalLT B κ₂)
      (C : SetCardinalLT κ₁ B) (hC : C in Y B hB) :
    exists (m : X), forall (b : B), b in C.val -> b <= m :=
      ⟨IsCardinalFiltered.max (fun (c : C.val) => c.val.val) C.prop,
        fun b hb => leOfHom (IsCardinalFiltered.toMax
          (fun (c : C.val) => c.val.val) C.prop ⟨_, hb⟩)⟩
  choose m hm using hY''
  -- The expected subset `B` is obtained as the union over
  -- all `j : κ₁.ord.ToType` of the transfinite iterations
  -- of the map `φ`
  exact ⟨⋃ j, transfiniteIterate (φ Y m) j A, subset_iUnion Y m A,
    isCardinalFiltered_iUnion h₀ Y hY hY' m hm A hA,
    hasCardinalLT_iUnion _ (by simpa [hasCardinalLT_iff_cardinal_mk_lt])
      (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA)⟩

end

end SharplyLT

end Cardinal
