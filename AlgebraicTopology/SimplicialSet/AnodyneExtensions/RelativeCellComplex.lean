/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
# The relative cell complex attached to a rank function for a pairing

Let `A` be a subcomplex of a simplicial set `X`. Let `P : A.Pairing`
be a proper pairing (in the sense of Moss) and `f : P.RankFunction ι`
be a rank function. We show that the inclusion `A.ι` is a relative
cell complex with basic cells given by horn inclusions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits Opposite

namespace SSet.Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}
  {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι)

/-- Given a rank function `f : P.RankFunction ι` for a
pairing `P` of a subcomplex `A` of `X : SSet`, and `i : ι`,
this is the type of type (II) simplices of rank `i`. -/
@[ext]
/--
Definition of `Cell` / `Cell` 的定义

English:
structure Cell
  parameters: (i : ι)
  axioms and operations (2):
    - s : P.II
    - rank_s : f.rank s = i

中文:
结构 Cell
  参数: (i : ι)
  公理与运算 (2 个):
    - s : P.II
    - rank_s : f.rank s = i
-/
structure Cell (i : ι) : Type u where
  /-- a type (II) simplex -/
  s : P.II
  rank_s : f.rank s = i

namespace Cell

variable {f} {i : ι} (c : f.Cell i)

/--
Definition of `dim` / `dim` 的定义

English:
abbreviation dim
  signature: : Nat
  body: c.s.val.dim

中文:
缩写 dim
  签名: : 自然数
  定义体: c.s.val.dim

Depends on / 依赖: c.s.val.dim
-/
abbrev dim : Nat := c.s.val.dim

variable [P.IsProper]

/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: : Fin (c.dim + 2)
  body: (P.isUniquelyCodimOneFace c.s).index rfl

中文:
定义 index
  签名: : 有限集 (c.dim + 2)
  定义体: (P.isUniquelyCodimOneFace c.s).index rfl

Depends on / 依赖: P.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
noncomputable def index : Fin (c.dim + 2) :=
  (P.isUniquelyCodimOneFace c.s).index rfl

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
abbreviation noncomputable
  signature: abbrev horn
  body: SSet.horn _ c.index

中文:
缩写 noncomputable
  签名: abbrev horn
  定义体: SSet.horn _ c.index
-/
protected noncomputable abbrev horn : (Δ[c.dim + 1] : SSet.{u}).Subcomplex :=
  SSet.horn _ c.index

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : Δ[c.dim + 1] ⟶ X
  body: yonedaEquiv.symm
    ((P.p c.s).val.cast (P.isUniquelyCodimOneFace c.s).dim_eq).simplex

中文:
缩写 map
  签名: : Δ[c.dim + 1] ⟶ X
  定义体: yonedaEquiv.symm
    ((P.p c.s).val.cast (P.isUniquelyCodimOneFace c.s).dim_eq).simplex

Depends on / 依赖: P.isUniquelyCodimOneFace, dim_eq, isUniquelyCodimOneFace, simplex, val.cast, yonedaEquiv, yonedaEquiv.symm
-/
abbrev map : Δ[c.dim + 1] ⟶ X :=
  yonedaEquiv.symm
    ((P.p c.s).val.cast (P.isUniquelyCodimOneFace c.s).dim_eq).simplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `range_map` / 引理 `range_map`

English:
lemma range_map
  statement: Subcomplex.range c.map = (P.p c.s).val.subcomplex
  proof: by
  rw [range_eq_ofSimplex]; rw [Equiv.apply_symm_apply]; rw [S.ofSimplex_eq_subcomplex_mk]; rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp [S.subcomplex]

中文:
引理 range_map
  结论: 子复形.range c.map = (P.p c.s).val.subcomplex
  证明: by
  rw [range_eq_ofSimplex]; rw [Equiv.apply_symm_apply]; rw [S.ofSimplex_eq_subcomplex_mk]; rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp [S.subcomplex]

Depends on / 依赖: Equiv.apply_symm_apply, P.dim_p, S.cast_eq_self, S.ofSimplex_eq_subcomplex_mk, S.subcomplex, apply_symm_apply, cast_eq_self, dim_p, ofSimplex_eq_subcomplex_mk, range_eq_ofSimplex, subcomplex
-/
lemma range_map : Subcomplex.range c.map = (P.p c.s).val.subcomplex := by
  rw [range_eq_ofSimplex]; rw [Equiv.apply_symm_apply]; rw [S.ofSimplex_eq_subcomplex_mk]; rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp [S.subcomplex]

/--
lemma `map_app_objEquiv_symm_δ_index` / 引理 `map_app_objEquiv_symm_δ_index`

English:
lemma map_app_objEquiv_symm_δ_index
  proof: (P.isUniquelyCodimOneFace c.s).δ_index rfl

中文:
引理 map_app_objEquiv_symm_δ_index
  证明: (P.isUniquelyCodimOneFace c.s).δ_index rfl

Depends on / 依赖: P.isUniquelyCodimOneFace, isUniquelyCodimOneFace
-/
lemma map_app_objEquiv_symm_δ_index :
    c.map.app (op ⦋c.dim⦌) (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index)) =
      c.s.val.simplex :=
  (P.isUniquelyCodimOneFace c.s).δ_index rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `subcomplex_not_le_image_horn` / 引理 `subcomplex_not_le_image_horn`

English:
lemma subcomplex_not_le_image_horn
  statement: ¬ c.s.val.subcomplex <= c.horn.image c.map
  proof: by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [← stdSimplex.map_objEquiv_op_apply]; rw [Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x := ⟨_, c.s.val.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.s).unique rfl _ h₂
  rw [← ofSimplex_le_iff]; rw [subcomplex_le_horn_iff]; rw [← stdSimplex.face_singleton_compl] at h₁
  tauto

中文:
引理 subcomplex_not_le_image_horn
  结论: ¬ c.s.val.subcomplex <= c.horn.像 c.map
  证明: by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [← stdSimplex.map_objEquiv_op_apply]; rw [Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x := ⟨_, c.s.val.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.s).unique rfl _ h₂
  rw [← ofSimplex_le_iff]; rw [subcomplex_le_horn_iff]; rw [← stdSimplex.face_singleton_compl] at h₁
  tauto

Depends on / 依赖: Equiv.apply_symm_apply, P.isUniquelyCodimOneFace, Set.mem_image, Subfunctor, Subfunctor.ofSection_le_iff, apply_symm_apply, c.s.val.nonDegenerate, face_singleton_compl, image_obj, isUniquelyCodimOneFace, map_objEquiv_op_apply, mem_image, mono_of_nonDegenerate, nonDegenerate, objEquiv, ofSection_le_iff, ofSimplex_le_iff, stdSimplex, stdSimplex.face_singleton_compl, stdSimplex.map_objEquiv_op_apply
-/
lemma subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex <= c.horn.image c.map := by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [← stdSimplex.map_objEquiv_op_apply]; rw [Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x := ⟨_, c.s.val.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.s).unique rfl _ h₂
  rw [← ofSimplex_le_iff]; rw [subcomplex_le_horn_iff]; rw [← stdSimplex.face_singleton_compl] at h₁
  tauto

/--
lemma `image_horn_lt_subcomplex` / 引理 `image_horn_lt_subcomplex`

English:
lemma image_horn_lt_subcomplex
  statement: c.horn.image c.map < (P.p c.s).val.subcomplex
  proof: by
  rw [lt_iff_le_and_ne]
  exact ⟨by simpa using! image_le_range c.horn c.map,
    fun h => c.subcomplex_not_le_image_horn (by simpa only [h] using! P.le c.s)⟩

@[simp]

中文:
引理 image_horn_lt_subcomplex
  结论: c.horn.像 c.map < (P.p c.s).val.subcomplex
  证明: by
  rw [lt_iff_le_and_ne]
  exact ⟨by simpa using! image_le_range c.horn c.map,
    fun h => c.subcomplex_not_le_image_horn (by simpa only [h] using! P.le c.s)⟩

@[simp]

Depends on / 依赖: I.upper, I.upper_mem_Icc, P.le, c.horn, c.map, c.subcomplex_not_le_image_horn, image_le_range, le_rfl, lt_iff_le_and_ne, single, subcomplex_not_le_image_horn, upper_mem_Icc
-/
lemma image_horn_lt_subcomplex : c.horn.image c.map < (P.p c.s).val.subcomplex := by
  rw [lt_iff_le_and_ne]
  exact ⟨by simpa using! image_le_range c.horn c.map,
    fun h => c.subcomplex_not_le_image_horn (by simpa only [h] using! P.le c.s)⟩

@[simp]
/--
lemma `image_face_index_compl` / 引理 `image_face_index_compl`

English:
lemma image_face_index_compl
  proof: by
  rw [stdSimplex.face_singleton_compl]; rw [image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.s).δ_index rfl

中文:
引理 image_face_index_compl
  证明: by
  rw [stdSimplex.face_singleton_compl]; rw [image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.s).δ_index rfl

Depends on / 依赖: P.isUniquelyCodimOneFace, face_singleton_compl, image_ofSimplex, isUniquelyCodimOneFace, stdSimplex, stdSimplex.face_singleton_compl
-/
lemma image_face_index_compl :
    (stdSimplex.face {c.index}ᶜ).image c.map = c.s.val.subcomplex := by
  rw [stdSimplex.face_singleton_compl]; rw [image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.s).δ_index rfl

end Cell

variable [P.IsProper] in
/--
Definition of `basicCell` / `basicCell` 的定义

English:
abbreviation basicCell
  signature: (i : ι) (c : f.Cell i)
  body: c.horn.ι

中文:
缩写 basicCell
  签名: (i : ι) (c : f.Cell i)
  定义体: c.horn.ι

Depends on / 依赖: c.horn
-/
noncomputable abbrev basicCell (i : ι) (c : f.Cell i) : (c.horn : SSet) ⟶ Δ[c.dim + 1] :=
  c.horn.ι

/--
Definition of `filtration` / `filtration` 的定义

English:
definition filtration
  signature: (i : ι)
  body: A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex

中文:
定义 filtration
  签名: (i : ι)
  定义体: A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex

Depends on / 依赖: f.Cell, subcomplex, val.subcomplex
-/
def filtration (i : ι) : X.Subcomplex :=
  A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex

/--
lemma `filtration_def` / 引理 `filtration_def`

English:
lemma filtration_def
  given: (i : ι)
  proof: rfl

中文:
引理 filtration_def
  条件: (i : ι)
  证明: rfl
-/
lemma filtration_def (i : ι) :
    f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex :=
  rfl

/--
lemma `subcomplex_le_filtration` / 引理 `subcomplex_le_filtration`

English:
lemma subcomplex_le_filtration
  given: {j : ι} (c : f.Cell j) {i : ι} (h : j < i)
  proof: by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]

中文:
引理 subcomplex_le_filtration
  条件: {j : ι} (c : f.Cell j) {i : ι} (h : j < i)
  证明: by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]

Depends on / 依赖: le_iSup, le_sup_right, le_trans
-/
lemma subcomplex_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) :
    (P.p c.s).val.subcomplex <= f.filtration i := by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]
/--
lemma `le_filtration` / 引理 `le_filtration`

English:
lemma le_filtration
  given: (i : ι)
  statement: A <= f.filtration i
  proof: le_sup_left

@[simp]

中文:
引理 le_filtration
  条件: (i : ι)
  结论: A <= f.filtration i
  证明: le_sup_left

@[simp]

Depends on / 依赖: le_sup_left
-/
lemma le_filtration (i : ι) : A <= f.filtration i := le_sup_left

@[simp]
/--
lemma `filtration_bot` / 引理 `filtration_bot`

English:
lemma filtration_bot
  given: [OrderBot ι]
  statement: f.filtration ⊥ = A
  proof: by
  simp [filtration_def]

中文:
引理 filtration_bot
  条件: [有底序 ι]
  结论: f.filtration ⊥ = A
  证明: by
  simp [filtration_def]

Depends on / 依赖: filtration_def
-/
lemma filtration_bot [OrderBot ι] : f.filtration ⊥ = A := by
  simp [filtration_def]

/--
lemma `filtration_monotone` / 引理 `filtration_monotone`

English:
lemma filtration_monotone
  statement: Monotone f.filtration
  proof: by
  intro i₁ i₂ h
  conv_lhs => rw [filtration_def]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)

中文:
引理 filtration_monotone
  结论: 递增 f.filtration
  证明: by
  intro i₁ i₂ h
  conv_lhs => rw [filtration_def]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)

Depends on / 依赖: conv_lhs, f.subcomplex_le_filtration, filtration_def, iSup_le_iff, le_filtration, lt_of_lt_of_le, subcomplex_le_filtration, sup_le_iff, true_and
-/
lemma filtration_monotone : Monotone f.filtration := by
  intro i₁ i₂ h
  conv_lhs => rw [filtration_def]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)

/--
lemma `filtration_succ` / 引理 `filtration_succ`

English:
lemma filtration_succ
  given: [SuccOrder ι] (i : ι) (hi : ¬ IsMax i)
  proof: by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c => ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c => f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

中文:
引理 filtration_succ
  条件: [Succ序 ι] (i : ι) (hi : ¬ IsMax i)
  证明: by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c => ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c => f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

Depends on / 依赖: Order.le_succ, Order.lt_succ_iff_of_not_isMax, Order.lt_succ_of_no, conv_lhs, f.filtration_monotone, f.le_filtration, f.subcomplex_le_filtration, filtration_def, filtration_monotone, hj.lt_or_eq, iSup_le_iff, le_antisymm, le_filtration, le_iSup, le_succ, le_sup_left, le_sup_right, le_trans, lt_or_eq, lt_succ_iff_of_not_isMax
-/
lemma filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) :
    f.filtration (Order.succ i) =
      f.filtration i ⊔ ⨆ (c : f.Cell i), (P.p c.s).val.subcomplex := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c => ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c => f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

/--
lemma `filtration_of_isSuccLimit` / 引理 `filtration_of_isSuccLimit`

English:
lemma filtration_of_isSuccLimit
  given: [OrderBot ι] [SuccOrder ι] (i : ι) (hi : Order.IsSuccLimit i)
  proof: by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c => ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

中文:
引理 filtration_of_isSuccLimit
  条件: [有底序 ι] [Succ序 ι] (i : ι) (hi : Order.是SuccLimit i)
  证明: by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c => ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

Depends on / 依赖: IsSuccLimit, Order.IsSuccLimit.succ_lt_iff, Order.lt_succ_of_not_isMax, Order.succ, bot_lt, conv_lhs, f.filtration_monotone, f.subcomplex_le_filtration, filtration_def, filtration_monotone, hi.bot_lt, hj.le, hj.not_isMax, iSup_le_iff, le_antisymm, le_iSup, le_trans, lt_succ_of_not_isMax, not_isMax, subcomplex_le_filtration
-/
lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι] (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c => ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

/--
lemma `iSup_filtration_iio` / 引理 `iSup_filtration_iio`

English:
lemma iSup_filtration_iio
  given: [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m)
  proof: by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c =>
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.mpr hj⟩))⟩

中文:
引理 iSup_filtration_iio
  条件: [有底序 ι] [Succ序 ι] (m : ι) (hm : Order.是SuccLimit m)
  证明: by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c =>
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.mpr hj⟩))⟩

Depends on / 依赖: Order.lt_succ_of_not_isMax, Order.succ, Set.mem_Iio, Subtype, Subtype.forall, bot_lt, conv_lhs, f.filtration_bot, f.filtration_monotone, f.subcomplex_le_filtration, filtration_bot, filtration_def, filtration_monotone, hj.le, hm.bot_lt, hm.succ_lt_iff.mpr, iSup_le_iff, le_antisymm, le_iSup, le_trans
-/
lemma iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m) :
    ⨆ (i : Set.Iio m), f.filtration i = f.filtration m := by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c =>
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.mpr hj⟩))⟩

variable {f} in
/--
lemma `Cell.subcomplex_not_le_filtration` / 引理 `Cell.subcomplex_not_le_filtration`

English:
lemma Cell.subcomplex_not_le_filtration
  given: {j : ι} (c : f.Cell j)
  proof: by
  simp only [ofSimplex_le_iff, filtration_def, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  refine ⟨c.s.val.notMem, fun i hi c' h => ?_⟩
  rw [← c.rank_s]; rw [← c'.rank_s] at hi
  refine lt_irrefl _ (hi.trans (f.lt ?_))
  refine ⟨fun hxy => ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
  · rw [hxy] at hi
    exact (lt_irrefl _ hi).elim
  · rw [← ofSimplex_le_iff] at h
    rwa [Subcomplex.N.le_iff, SSet.N.le_iff]

中文:
引理 Cell.subcomplex_not_le_filtration
  条件: {j : ι} (c : f.Cell j)
  证明: by
  simp only [ofSimplex_le_iff, filtration_def, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  refine ⟨c.s.val.notMem, fun i hi c' h => ?_⟩
  rw [← c.rank_s]; rw [← c'.rank_s] at hi
  refine lt_irrefl _ (hi.trans (f.lt ?_))
  refine ⟨fun hxy => ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
  · rw [hxy] at hi
    exact (lt_irrefl _ hi).elim
  · rw [← ofSimplex_le_iff] at h
    rwa [Subcomplex.N.le_iff, SSet.N.le_iff]

Depends on / 依赖: P.ne, SSet.N.le_iff, Set.mem_iUnion, Set.mem_union, Subcomplex, Subcomplex.N.le_iff, Subfunctor, Subfunctor.iSup_obj, Subfunctor.max_obj, c.rank_s, c.s.val.notMem, f.lt, filtration_def, hi.trans, iSup_obj, le_iff, lt_irrefl, lt_of_le_of_ne, max_obj, mem_iUnion
-/
lemma Cell.subcomplex_not_le_filtration {j : ι} (c : f.Cell j) :
    ¬ c.s.val.subcomplex <= f.filtration j := by
  simp only [ofSimplex_le_iff, filtration_def, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  refine ⟨c.s.val.notMem, fun i hi c' h => ?_⟩
  rw [← c.rank_s]; rw [← c'.rank_s] at hi
  refine lt_irrefl _ (hi.trans (f.lt ?_))
  refine ⟨fun hxy => ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
  · rw [hxy] at hi
    exact (lt_irrefl _ hi).elim
  · rw [← ofSimplex_le_iff] at h
    rwa [Subcomplex.N.le_iff, SSet.N.le_iff]

variable [P.IsProper]

/--
lemma `iSup_filtration` / 引理 `iSup_filtration`

English:
lemma iSup_filtration
  given: [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι]
  proof: by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  cases s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

中文:
引理 iSup_filtration
  条件: [有底序 ι] [Succ序 ι] [NoMax序 ι]
  证明: by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  cases s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

Depends on / 依赖: N.subcomplex_le_iff, Order.lt_succ, P.exists_or, P.le, SSet.Subcomplex.N.cases, Subcomplex, exists_or, f.subcomplex_le_filtration, hs.trans, le_antisymm, le_iSup, le_trans, lt_succ, notMem, subcomplex_le_filtration, subcomplex_le_iff
-/
lemma iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  cases s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

variable {f} in
/--
Definition of `Cell.mapToSucc` / `Cell.mapToSucc` 的定义

English:
definition Cell.mapToSucc
  signature: {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j)
  body: Subcomplex.lift c.map (by simpa using f.subcomplex_le_filtration c (Order.lt_succ _))

中文:
定义 Cell.mapToSucc
  签名: {j : ι} [Succ序 ι] [NoMax序 ι] (c : f.Cell j)
  定义体: Subcomplex.lift c.map (by simpa using f.subcomplex_le_filtration c (Order.lt_succ _))

Depends on / 依赖: Order.lt_succ, Subcomplex, Subcomplex.lift, c.map, f.subcomplex_le_filtration, lt_succ, subcomplex_le_filtration
-/
def Cell.mapToSucc {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by simpa using f.subcomplex_le_filtration c (Order.lt_succ _))

variable {f} in
@[reassoc (attr := simp)]
/--
lemma `Cell.mapToSucc_ι` / 引理 `Cell.mapToSucc_ι`

English:
lemma Cell.mapToSucc_ι
  given: {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j)
  proof: rfl

中文:
引理 Cell.mapToSucc_ι
  条件: {j : ι} [Succ序 ι] [NoMax序 ι] (c : f.Cell j)
  证明: rfl
-/
lemma Cell.mapToSucc_ι {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    c.mapToSucc ≫ (f.filtration (Order.succ j)).ι = c.map := rfl

section

/-!
The main technical result in this section is `SSet.Subcomplex.Pairing.RankFunction.isPushout`
which states that there is a pushout square:
```
                                      f.t j
∐ fun (c : f.Cell j) ↦ c.horn -------------> f.filtration j
               | |
         f.m j | |
               v f.b j v
∐ fun (c : f.Cell j) ↦ Δ[c.dim + 1] -------> f.filtration (Order.succ j)
```
The map on the left is a coproduct of horn inclusions (the source and target
of the morphism `f.m j` are denoted `f.sigmaHorn j` and `f.sigmaStdSimplex j`).

-/

/--
Definition of `sigmaHorn` / `sigmaHorn` 的定义

English:
abbreviation sigmaHorn
  signature: (j : ι)
  body: ∐ fun (c : f.Cell j) => c.horn

中文:
缩写 sigmaHorn
  签名: (j : ι)
  定义体: ∐ fun (c : f.Cell j) => c.horn

Depends on / 依赖: c.horn, f.Cell
-/
noncomputable abbrev sigmaHorn (j : ι) : SSet.{u} :=
  ∐ fun (c : f.Cell j) => c.horn

variable {f} in
/--
Definition of `Cell.ιSigmaHorn` / `Cell.ιSigmaHorn` 的定义

English:
abbreviation Cell.ιSigmaHorn
  signature: {j : ι} (c : f.Cell j)
  body: Sigma.ι (fun (c : f.Cell j) => (c.horn : SSet)) c

中文:
缩写 Cell.ιSigmaHorn
  签名: {j : ι} (c : f.Cell j)
  定义体: Sigma.ι (fun (c : f.Cell j) => (c.horn : SSet)) c

Depends on / 依赖: c.horn, f.Cell
-/
noncomputable abbrev Cell.ιSigmaHorn {j : ι} (c : f.Cell j) :
    (c.horn : SSet) ⟶ f.sigmaHorn j :=
  Sigma.ι (fun (c : f.Cell j) => (c.horn : SSet)) c

/--
Definition of `sigmaStdSimplex` / `sigmaStdSimplex` 的定义

English:
abbreviation sigmaStdSimplex
  signature: (j : ι)
  body: ∐ fun (i : f.Cell j) => Δ[i.dim + 1]

中文:
缩写 sigmaStdSimplex
  签名: (j : ι)
  定义体: ∐ fun (i : f.Cell j) => Δ[i.dim + 1]

Depends on / 依赖: f.Cell, i.dim
-/
noncomputable abbrev sigmaStdSimplex (j : ι) : SSet.{u} :=
  ∐ fun (i : f.Cell j) => Δ[i.dim + 1]

variable {f} in
/--
Definition of `Cell.ιSigmaStdSimplex` / `Cell.ιSigmaStdSimplex` 的定义

English:
abbreviation Cell.ιSigmaStdSimplex
  signature: {j : ι} (c : f.Cell j)
  body: Sigma.ι (fun (c : f.Cell j) => Δ[c.dim + 1]) c

中文:
缩写 Cell.ιSigmaStdSimplex
  签名: {j : ι} (c : f.Cell j)
  定义体: Sigma.ι (fun (c : f.Cell j) => Δ[c.dim + 1]) c

Depends on / 依赖: c.dim, f.Cell
-/
noncomputable abbrev Cell.ιSigmaStdSimplex {j : ι} (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.sigmaStdSimplex j :=
  Sigma.ι (fun (c : f.Cell j) => Δ[c.dim + 1]) c

/--
lemma `ιSigmaHorn_jointly_surjective` / 引理 `ιSigmaHorn_jointly_surjective`

English:
lemma ιSigmaHorn_jointly_surjective
  proof: Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in

中文:
引理 ιSigmaHorn_jointly_surjective
  证明: Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in

Depends on / 依赖: CategoryTheory, CategoryTheory.evaluation, Cofan.inj_jointly_surjective_of_isColimit, coproductIsCoproduct, evaluation, inj_jointly_surjective_of_isColimit, isColimitCofanMkObjOfIsColimit
-/
lemma ιSigmaHorn_jointly_surjective
    {d : Nat} {j : ι} (a : (f.sigmaHorn j) _⦋d⦌) :
    exists (c : f.Cell j) (x : (c.horn : SSet) _⦋d⦌), c.ιSigmaHorn.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
/--
lemma `ιSigmaStdSimplex_jointly_surjective` / 引理 `ιSigmaStdSimplex_jointly_surjective`

English:
lemma ιSigmaStdSimplex_jointly_surjective
  proof: Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in

中文:
引理 ιSigmaStdSimplex_jointly_surjective
  证明: Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in

Depends on / 依赖: CategoryTheory, CategoryTheory.evaluation, Cofan.inj_jointly_surjective_of_isColimit, coproductIsCoproduct, evaluation, inj_jointly_surjective_of_isColimit, isColimitCofanMkObjOfIsColimit
-/
lemma ιSigmaStdSimplex_jointly_surjective
    {d : Nat} {j : ι} (a : (f.sigmaStdSimplex j) _⦋d⦌) :
    exists (c : f.Cell j) (x : Δ[c.dim + 1] _⦋d⦌), c.ιSigmaStdSimplex.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
/--
lemma `ιSigmaStdSimplex_eq_iff` / 引理 `ιSigmaStdSimplex_eq_iff`

English:
lemma ιSigmaStdSimplex_eq_iff
  statement: {j : ι} {d : Nat}
  proof: Cofan.inj_apply_eq_iff_of_isColimit
    (((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _)))) _ _

中文:
引理 ιSigmaStdSimplex_eq_iff
  结论: {j : ι} {d : 自然数}
  证明: Cofan.inj_apply_eq_iff_of_isColimit
    (((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _)))) _ _

Depends on / 依赖: CategoryTheory, CategoryTheory.evaluation, Cofan.inj_apply_eq_iff_of_isColimit, coproductIsCoproduct, evaluation, inj_apply_eq_iff_of_isColimit, isColimitCofanMkObjOfIsColimit
-/
lemma ιSigmaStdSimplex_eq_iff {j : ι} {d : Nat}
    (x : f.Cell j) (s : (Δ[x.dim + 1] : SSet.{u}) _⦋d⦌)
    (y : f.Cell j) (t : (Δ[y.dim + 1] : SSet.{u}) _⦋d⦌) :
    x.ιSigmaStdSimplex.app (op ⦋d⦌) s = y.ιSigmaStdSimplex.app (op ⦋d⦌) t ↔
      exists (h : x = y), t = cast (by rw [h]) s :=
  Cofan.inj_apply_eq_iff_of_isColimit
    (((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _)))) _ _

instance {j : ι} (c : f.Cell j) : Mono c.ιSigmaStdSimplex := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro x y h
  simpa [f.ιSigmaStdSimplex_eq_iff] using h.symm

/--
Definition of `m` / `m` 的定义

English:
definition m
  signature: (j : ι)
  body: Limits.Sigma.map (basicCell _ _)

中文:
定义 m
  签名: (j : ι)
  定义体: Limits.Sigma.map (basicCell _ _)

Depends on / 依赖: Limits, Limits.Sigma.map, basicCell
-/
noncomputable def m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j :=
  Limits.Sigma.map (basicCell _ _)

instance (j : ι) : Mono (f.m j) := inferInstanceAs Mono (Limits.Sigma.map _)

@[reassoc (attr := simp)]
/--
lemma `Cell.ι_m` / 引理 `Cell.ι_m`

English:
lemma Cell.ι_m
  given: {j : ι} (c : f.Cell j)
  proof: by
  simp [m]

@[simp]

中文:
引理 Cell.ι_m
  条件: {j : ι} (c : f.Cell j)
  证明: by
  simp [m]

@[simp]
-/
lemma Cell.ι_m {j : ι} (c : f.Cell j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex := by
  simp [m]

@[simp]
/--
lemma `Cell.preimage_filtration_map` / 引理 `Cell.preimage_filtration_map`

English:
lemma Cell.preimage_filtration_map
  given: {j : ι} (c : f.Cell j)
  proof: by
  apply le_antisymm
  · simpa only [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cell.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    cases s using N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.rank_s]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.val.subcomplex <= c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

中文:
引理 Cell.preimage_filtration_map
  条件: {j : ι} (c : f.Cell j)
  证明: by
  apply le_antisymm
  · simpa only [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cell.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    cases s using N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.rank_s]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.val.subcomplex <= c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

Depends on / 依赖: Cell.image_face_index_compl, N.cases, N.subcomplex_le_iff, P.exists_or, P.le, Subcomplex, Subcomplex.image_le_iff, c.rank_s, c.subcomplex_not_le_filtration, exists_or, f.lt, f.subcomplex_le_filtration, image_face_index_compl, image_le_iff, le_antisymm, le_trans, notMem, rank_s, replace, subcomplex
-/
lemma Cell.preimage_filtration_map {j : ι} (c : f.Cell j) :
    (f.filtration j).preimage c.map = c.horn := by
  apply le_antisymm
  · simpa only [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cell.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    cases s using N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.rank_s]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.val.subcomplex <= c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

/--
Definition of `Cell.mapHorn` / `Cell.mapHorn` 的定义

English:
definition Cell.mapHorn
  signature: {j : ι} (c : f.Cell j)
  body: Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]

中文:
定义 Cell.mapHorn
  签名: {j : ι} (c : f.Cell j)
  定义体: Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]

Depends on / 依赖: Subcomplex, Subcomplex.lift, c.horn, c.map, c.preimage_filtration_map, image_le_iff, image_top, preimage_comp, preimage_filtration_map
-/
noncomputable def Cell.mapHorn {j : ι} (c : f.Cell j) : (c.horn : SSet) ⟶ f.filtration j :=
  Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]
/--
lemma `Cell.mapHorn_ι` / 引理 `Cell.mapHorn_ι`

English:
lemma Cell.mapHorn_ι
  given: {j : ι} (c : f.Cell j)
  proof: rfl

中文:
引理 Cell.mapHorn_ι
  条件: {j : ι} (c : f.Cell j)
  证明: rfl
-/
lemma Cell.mapHorn_ι {j : ι} (c : f.Cell j) :
    c.mapHorn ≫ (f.filtration j).ι = c.horn.ι ≫ c.map := rfl

/--
Definition of `t` / `t` 的定义

English:
definition t
  signature: (j : ι)
  body: Sigma.desc (fun c => c.mapHorn)

中文:
定义 t
  签名: (j : ι)
  定义体: Sigma.desc (fun c => c.mapHorn)

Depends on / 依赖: Sigma.desc, c.mapHorn, mapHorn
-/
noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  Sigma.desc (fun c => c.mapHorn)

variable {f} in
@[reassoc (attr := simp)]
/--
lemma `Cell.ι_t` / 引理 `Cell.ι_t`

English:
lemma Cell.ι_t
  given: {j : ι} (c : f.Cell j)
  statement: c.ιSigmaHorn ≫ f.t j = c.mapHorn
  proof: by
  simp [t]

中文:
引理 Cell.ι_t
  条件: {j : ι} (c : f.Cell j)
  结论: c.ιSigmaHorn ≫ f.t j = c.mapHorn
  证明: by
  simp [t]
-/
lemma Cell.ι_t {j : ι} (c : f.Cell j) : c.ιSigmaHorn ≫ f.t j = c.mapHorn := by
  simp [t]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `Cell.ι_t_app` / 引理 `Cell.ι_t_app`

English:
lemma Cell.ι_t_app
  given: {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ)
  proof: NatTrans.congr_app c.ι_t x

中文:
引理 Cell.ι_t_app
  条件: {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ)
  证明: NatTrans.congr_app c.ι_t x

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app
-/
lemma Cell.ι_t_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaHorn.app x ≫ (f.t j).app x = c.mapHorn.app x :=
  NatTrans.congr_app c.ι_t x

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to `c.ιSigmaStdSimplex`. -/
@[simps]
/--
Definition of `Cell.type₁` / `Cell.type₁` 的定义

English:
definition Cell.type₁
  signature: {j : ι} (c : f.Cell j)
  body: c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

中文:
定义 Cell.type₁
  签名: {j : ι} (c : f.Cell j)
  定义体: c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

Depends on / 依赖: SigmaStdSimplex.app, objEquiv, stdSimplex, stdSimplex.objEquiv.symm
-/
noncomputable def Cell.type₁ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to the `c.index`th-face of `c.type₁`. -/
@[simps]
/--
Definition of `Cell.type₂` / `Cell.type₂` 的定义

English:
definition Cell.type₂
  signature: {j : ι} (c : f.Cell j)
  body: c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).mp hy'

中文:
定义 Cell.type₂
  签名: {j : ι} (c : f.Cell j)
  定义体: c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).mp hy'

Depends on / 依赖: SigmaStdSimplex.app
-/
noncomputable def Cell.type₂ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply]; rw [ι_m]; rw [NatTrans.comp_app_apply]; rw [ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).mp hy'

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_or_of_range_m_N` / 引理 `exists_or_of_range_m_N`

English:
lemma exists_or_of_range_m_N
  given: {j : ι} (s : (Subcomplex.range (f.m j)).N)
  proof: by
  obtain ⟨d, s, hs, hs', rfl⟩ := s.mk_surjective
  obtain ⟨x, s, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective s
  replace hs' : s ∉ (horn _ x.index).obj _ :=
    fun h => hs' ⟨x.ιSigmaHorn.app _ ⟨_, h⟩, by rw [← NatTrans.comp_app_apply]; simp⟩
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective s
  rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply] at hs
  obtain hd | rfl := (SimplexCategory.le_of_mono g).lt_or_eq
  · rw [Nat.lt_succ_iff] at hd
    obtain hd | rfl := hd.lt_or_eq
    · exact (hs' (by simp [horn_obj_eq_univ x.index d (by lia)])).elim
    · obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono g
      obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).mp hs'
      exact ⟨x, Or.inr rfl⟩
  · obtain rfl := SimplexCategory.eq_id_of_mono g
    exact ⟨x, Or.inl rfl⟩

中文:
引理 存在_or_of_range_m_N
  条件: {j : ι} (s : (子复形.range (f.m j)).N)
  证明: by
  obtain ⟨d, s, hs, hs', rfl⟩ := s.mk_surjective
  obtain ⟨x, s, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective s
  replace hs' : s ∉ (horn _ x.index).obj _ :=
    fun h => hs' ⟨x.ιSigmaHorn.app _ ⟨_, h⟩, by rw [← NatTrans.comp_app_apply]; simp⟩
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective s
  rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply] at hs
  obtain hd | rfl := (SimplexCategory.le_of_mono g).lt_or_eq
  · rw [Nat.lt_succ_iff] at hd
    obtain hd | rfl := hd.lt_or_eq
    · exact (hs' (by simp [horn_obj_eq_univ x.index d (by lia)])).elim
    · obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono g
      obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).mp hs'
      exact ⟨x, Or.inr rfl⟩
  · obtain rfl := SimplexCategory.eq_id_of_mono g
    exact ⟨x, Or.inl rfl⟩

Depends on / 依赖: Equiv.apply_symm_apply, Nat.lt_succ_iff, NatTrans, NatTrans.comp_app_apply, SigmaHorn.app, SimplexCategory, SimplexCategory.le_of_mono, apply_symm_apply, comp_app_apply, le_of_mono, lt_or_eq, lt_succ_iff, mem_nonDegenerate_iff_mono, mk_surjective, nonDegenerate_iff_of_mono, objEquiv, replace, s.mk_surjective, stdSimplex, stdSimplex.mem_nonDegenerate_iff_mono
-/
lemma exists_or_of_range_m_N {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    exists (c : f.Cell j), s = c.type₁ ∨ s = c.type₂ := by
  obtain ⟨d, s, hs, hs', rfl⟩ := s.mk_surjective
  obtain ⟨x, s, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective s
  replace hs' : s ∉ (horn _ x.index).obj _ :=
    fun h => hs' ⟨x.ιSigmaHorn.app _ ⟨_, h⟩, by rw [← NatTrans.comp_app_apply]; simp⟩
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective s
  rw [nonDegenerate_iff_of_mono]; rw [stdSimplex.mem_nonDegenerate_iff_mono]; rw [Equiv.apply_symm_apply] at hs
  obtain hd | rfl := (SimplexCategory.le_of_mono g).lt_or_eq
  · rw [Nat.lt_succ_iff] at hd
    obtain hd | rfl := hd.lt_or_eq
    · exact (hs' (by simp [horn_obj_eq_univ x.index d (by lia)])).elim
    · obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono g
      obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).mp hs'
      exact ⟨x, Or.inr rfl⟩
  · obtain rfl := SimplexCategory.eq_id_of_mono g
    exact ⟨x, Or.inl rfl⟩

variable [SuccOrder ι] [NoMaxOrder ι]

/--
Definition of `b` / `b` 的定义

English:
definition b
  signature: (j : ι)
  body: Sigma.desc (fun c => c.mapToSucc)

中文:
定义 b
  签名: (j : ι)
  定义体: Sigma.desc (fun c => c.mapToSucc)

Depends on / 依赖: Sigma.desc, c.mapToSucc, mapToSucc
-/
noncomputable def b (j : ι) : f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c => c.mapToSucc)

variable {f} in
@[reassoc (attr := simp)]
/--
lemma `Cell.ι_b` / 引理 `Cell.ι_b`

English:
lemma Cell.ι_b
  given: {j : ι} (c : f.Cell j)
  statement: c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc
  proof: by
  simp [b]

中文:
引理 Cell.ι_b
  条件: {j : ι} (c : f.Cell j)
  结论: c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc
  证明: by
  simp [b]
-/
lemma Cell.ι_b {j : ι} (c : f.Cell j) : c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc := by
  simp [b]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `Cell.ι_b_app` / 引理 `Cell.ι_b_app`

English:
lemma Cell.ι_b_app
  given: {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ)
  proof: NatTrans.congr_app c.ι_b x

@[reassoc]

中文:
引理 Cell.ι_b_app
  条件: {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ)
  证明: NatTrans.congr_app c.ι_b x

@[reassoc]

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app
-/
lemma Cell.ι_b_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaStdSimplex.app x ≫ (f.b j).app x = c.mapToSucc.app x :=
  NatTrans.congr_app c.ι_b x

@[reassoc]
/--
lemma `w` / 引理 `w`

English:
lemma w
  given: (j : ι)
  proof: by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

中文:
引理 w
  条件: (j : ι)
  证明: by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

Depends on / 依赖: Subcomplex, cancel_mono
-/
lemma w (j : ι) :
    f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.m j ≫ f.b j := by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback` / 引理 `isPullback`

English:
lemma isPullback
  given: (j : ι)
  proof: f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isLimitMapConePullbackConeEquiv _ _).symm
      (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h => (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f.m j)).mp inferInstance _) h.2, fun y b h => ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b in Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [x.ι_b_app_apply] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, ?_⟩
    · simpa only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
        x.ι_b_app_apply, x.ι_t_app_apply] using! h.symm
    · rw [← NatTrans.comp_app_apply]
      simp)⟩

中文:
引理 isPullback
  条件: (j : ι)
  证明: f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isLimitMapConePullbackConeEquiv _ _).symm
      (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h => (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f.m j)).mp inferInstance _) h.2, fun y b h => ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b in Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [x.ι_b_app_apply] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, ?_⟩
    · simpa only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
        x.ι_b_app_apply, x.ι_t_app_apply] using! h.symm
    · rw [← NatTrans.comp_app_apply]
      simp)⟩
-/
lemma isPullback (j : ι) :
    IsPullback (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isLimitMapConePullbackConeEquiv _ _).symm
      (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h => (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f.m j)).mp inferInstance _) h.2, fun y b h => ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b in Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [x.ι_b_app_apply] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, ?_⟩
    · simpa only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
        x.ι_b_app_apply, x.ι_t_app_apply] using! h.symm
    · rw [← NatTrans.comp_app_apply]
      simp)⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_homOfLE_app_union_range_b_app` / 引理 `range_homOfLE_app_union_range_b_app`

English:
lemma range_homOfLE_app_union_range_b_app
  given: (j : ι) (d : SimplexCategoryᵒᵖ)
  proof: by
  ext ⟨x, hx⟩
  -- generated by `simp? [filtration_def, Subtype.ext_iff] at hx ⊢`
  simp only [filtration_def, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Subfunctor.homOfLe_app,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_range, Subtype.ext_iff,
    Subtype.exists, exists_eq_right, Set.mem_univ, iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩

中文:
引理 range_homOfLE_app_union_range_b_app
  条件: (j : ι) (d : SimplexCategoryᵒᵖ)
  证明: by
  ext ⟨x, hx⟩
  -- generated by `simp? [filtration_def, Subtype.ext_iff] at hx ⊢`
  simp only [filtration_def, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Subfunctor.homOfLe_app,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_range, Subtype.ext_iff,
    Subtype.exists, exists_eq_right, Set.mem_univ, iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩
-/
lemma range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) :
    Set.range ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) ⊔
      Set.range ((f.b j).app d) = Set.univ := by
  ext ⟨x, hx⟩
  -- generated by `simp? [filtration_def, Subtype.ext_iff] at hx ⊢`
  simp only [filtration_def, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Subfunctor.homOfLe_app,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_range, Subtype.ext_iff,
    Subtype.exists, exists_eq_right, Set.mem_univ, iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩

/--
Definition of `mapN` / `mapN` 的定义

English:
definition mapN
  signature: {j : ι} (x : (Subcomplex.range (f.m j)).N)
  body: S.mk ((f.b j).app _ x.simplex).val

中文:
定义 mapN
  签名: {j : ι} (x : (子复形.range (f.m j)).N)
  定义体: S.mk ((f.b j).app _ x.simplex).val

Depends on / 依赖: S.mk, simplex, x.simplex
-/
noncomputable def mapN {j : ι} (x : (Subcomplex.range (f.m j)).N) : X.S :=
  S.mk ((f.b j).app _ x.simplex).val

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapN_type₁` / 引理 `mapN_type₁`

English:
lemma mapN_type₁
  given: {j : ι} (c : f.Cell j)
  statement: f.mapN c.type₁ = S.mk (P.p c.s).val.simplex
  proof: by
  dsimp only [Cell.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp
  rw [S.ext_iff]; rw [c.ι_b_app_apply]
  apply yonedaEquiv_symm_app_id

中文:
引理 mapN_type₁
  条件: {j : ι} (c : f.Cell j)
  结论: f.mapN c.type₁ = S.mk (P.p c.s).val.simplex
  证明: by
  dsimp only [Cell.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp
  rw [S.ext_iff]; rw [c.ι_b_app_apply]
  apply yonedaEquiv_symm_app_id

Depends on / 依赖: Cell.type, P.dim_p, S.cast_eq_self, S.ext_iff, cast_eq_self, dim_p, ext_iff, yonedaEquiv_symm_app_id
-/
lemma mapN_type₁ {j : ι} (c : f.Cell j) : f.mapN c.type₁ = S.mk (P.p c.s).val.simplex := by
  dsimp only [Cell.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp
  rw [S.ext_iff]; rw [c.ι_b_app_apply]
  apply yonedaEquiv_symm_app_id

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `mapN_type₂` / 引理 `mapN_type₂`

English:
lemma mapN_type₂
  given: {j : ι} (c : f.Cell j)
  statement: f.mapN c.type₂ = S.mk c.s.val.simplex
  proof: by
  dsimp [mapN]
  rw [S.ext_iff]; rw [c.ι_b_app_apply]; rw [Cell.mapToSucc]
  exact c.map_app_objEquiv_symm_δ_index

中文:
引理 mapN_type₂
  条件: {j : ι} (c : f.Cell j)
  结论: f.mapN c.type₂ = S.mk c.s.val.simplex
  证明: by
  dsimp [mapN]
  rw [S.ext_iff]; rw [c.ι_b_app_apply]; rw [Cell.mapToSucc]
  exact c.map_app_objEquiv_symm_δ_index

Depends on / 依赖: Cell.mapToSucc, S.ext_iff, c.map_app_objEquiv_symm_, ext_iff, mapToSucc
-/
lemma mapN_type₂ {j : ι} (c : f.Cell j) : f.mapN c.type₂ = S.mk c.s.val.simplex := by
  dsimp [mapN]
  rw [S.ext_iff]; rw [c.ι_b_app_apply]; rw [Cell.mapToSucc]
  exact c.map_app_objEquiv_symm_δ_index

/--
lemma `isPushout_aux₁` / 引理 `isPushout_aux₁`

English:
lemma isPushout_aux₁
  given: {j : ι} (s : (Subcomplex.range (f.m j)).N)
  proof: by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.s).val.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.s.val.nonDegenerate

中文:
引理 isPushout_aux₁
  条件: {j : ι} (s : (子复形.range (f.m j)).N)
  证明: by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.s).val.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.s.val.nonDegenerate
-/
private lemma isPushout_aux₁ {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    (f.mapN s).simplex in SSet.nonDegenerate _ _ := by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.s).val.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.s.val.nonDegenerate

/--
lemma `isPushout_aux₂` / 引理 `isPushout_aux₂`

English:
lemma isPushout_aux₂
  given: {j : ι}
  statement: Function.Injective (f.mapN (j := j))
  proof: by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by ext : 1; exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · congr; aesop

中文:
引理 isPushout_aux₂
  条件: {j : ι}
  结论: 函数.单射 (f.mapN (j := j))
  证明: by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by ext : 1; exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · congr; aesop
-/
private lemma isPushout_aux₂ {j : ι} : Function.Injective (f.mapN (j := j)) := by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by ext : 1; exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · congr; aesop

/--
lemma `isPushout_aux₃` / 引理 `isPushout_aux₃`

English:
lemma isPushout_aux₃
  given: {j : ι}
  proof: fun _ _ h => f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)

中文:
引理 isPushout_aux₃
  条件: {j : ι}
  证明: fun _ _ h => f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)
-/
private lemma isPushout_aux₃ {j : ι} :
    Function.Injective fun (x : (Subcomplex.range (f.m j)).N) => S.mk ((f.b j).app _ x.simplex) :=
  fun _ _ h => f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  given: (j : ι)
  proof: f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h => ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq]; rw [← Subcomplex.ofSimplex_map_of_epi g₁]; rw [← Subcomplex.ofSimplex_map_of_epi g₂]
      · simp [← dsimp% (f.b j).naturality_apply, hg₁, hg₂, dsimp% h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).val)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, ← hg₁, dsimp% NatTrans.naturality_apply (f.b j)])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, dsimp% h, ← hg₂, dsimp% NatTrans.naturality_apply (f.b j)])
    rw [← hg₁]; rw [hg₂])⟩

中文:
引理 isPushout
  条件: (j : ι)
  证明: f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h => ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq]; rw [← Subcomplex.ofSimplex_map_of_epi g₁]; rw [← Subcomplex.ofSimplex_map_of_epi g₂]
      · simp [← dsimp% (f.b j).naturality_apply, hg₁, hg₂, dsimp% h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).val)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, ← hg₁, dsimp% NatTrans.naturality_apply (f.b j)])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, dsimp% h, ← hg₂, dsimp% NatTrans.naturality_apply (f.b j)])
    rw [← hg₁]; rw [hg₂])⟩
-/
lemma isPushout (j : ι) :
    IsPushout (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ => by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h => ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq]; rw [← Subcomplex.ofSimplex_map_of_epi g₁]; rw [← Subcomplex.ofSimplex_map_of_epi g₂]
      · simp [← dsimp% (f.b j).naturality_apply, hg₁, hg₂, dsimp% h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).val)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, ← hg₁, dsimp% NatTrans.naturality_apply (f.b j)])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, dsimp% h, ← hg₂, dsimp% NatTrans.naturality_apply (f.b j)])
    rw [← hg₁]; rw [hg₂])⟩

end

variable [SuccOrder ι] [OrderBot ι] [NoMaxOrder ι] [WellFoundedLT ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: f.filtration_monotone.functor.IsWellOrderContinuous
  body: ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

中文:
实例 :
  签名: f.filtration_monotone.functor.是WellOrderContinuous
  定义体: ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

Depends on / 依赖: Preorder, Preorder.isColimitOfIsLUB, f.iSup_filtration_iio, iSup_filtration_iio, isColimitOfIsLUB, isLUB_iSup
-/
instance : f.filtration_monotone.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

/--
Definition of `relativeCellComplex` / `relativeCellComplex` 的定义

English:
definition relativeCellComplex
  signature: :
  body: f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm => ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cell j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

中文:
定义 relativeCellComplex
  签名: :
  定义体: f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm => ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cell j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

Depends on / 依赖: Subcomplex, Subcomplex.toSSetFunctor, f.filtration_monotone.functor, filtration_monotone, functor, toSSetFunctor
-/
noncomputable def relativeCellComplex :
    RelativeCellComplex f.basicCell A.ι where
  F := f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm => ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cell j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

end SSet.Subcomplex.Pairing.RankFunction
