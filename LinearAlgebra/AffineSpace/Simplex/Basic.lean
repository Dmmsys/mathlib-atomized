/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Restrict

/-!
# Simplex in affine space

This file defines n-dimensional simplices in affine space.

## Main definitions

* `Simplex` is a bundled type with collection of `n + 1` points in affine space that are affinely
  independent, where `n` is the dimension of the simplex.

* `Triangle` is a simplex with three points, defined as an abbreviation for simplex with `n = 2`.

* `face` is a simplex with a subset of the points of the original simplex.

## References

* https://en.wikipedia.org/wiki/Simplex

-/

@[expose] public section

noncomputable section

open Finset Function Module
open scoped Affine

namespace Affine

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)
variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]
variable [Module k V] [Module k V₂] [Module k V₃]
variable [AffineSpace V P] [AffineSpace V₂ P₂] [AffineSpace V₃ P₃]

/--
Definition of `Simplex` / `Simplex` 的定义

English:
structure Simplex
  parameters: (n : Nat)
  axioms and operations (2):
    - points : Fin (n + 1) -> P
    - independent : AffineIndependent k points

中文:
结构 单纯形
  参数: (n : 自然数)
  公理与运算 (2 个):
    - points : 有限集 (n + 1) -> P
    - independent : AffineIndependent k points
-/
structure Simplex (n : Nat) where
  points : Fin (n + 1) -> P
  independent : AffineIndependent k points

/--
Definition of `Triangle` / `Triangle` 的定义

English:
abbreviation Triangle
  body: Simplex k P 2

中文:
缩写 Triangle
  定义体: Simplex k P 2

Depends on / 依赖: OpensMeasurableSpace, OpensMeasurableSpace.separatesPoints, Simplex, T0Space, separatesPoints
-/
abbrev Triangle :=
  Simplex k P 2

namespace Simplex

variable {P P₂ P₃}

/--
Definition of `mkOfPoint` / `mkOfPoint` 的定义

English:
definition mkOfPoint
  signature: (p : P)
  body: have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩

中文:
定义 mkOfPoint
  签名: (p : P)
  定义体: have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩

Depends on / 依赖: Subsingleton, add_zero, affineIndependent_of_subsingleton, infer_instance
-/
def mkOfPoint (p : P) : Simplex k P 0 :=
  have : Subsingleton (Fin (1 + 0)) := by rw [add_zero]; infer_instance
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mkOfPoint`. -/
@[simp]
/--
theorem `mkOfPoint_points` / 定理 `mkOfPoint_points`

English:
theorem mkOfPoint_points
  given: (p : P) (i : Fin 1)
  statement: (mkOfPoint k p).points i = p
  proof: rfl

中文:
定理 mkOfPoint_points
  条件: (p : P) (i : 有限集 1)
  结论: (mkOfPoint k p).points i = p
  证明: rfl

Depends on / 依赖: OpensMeasurableSpace, OpensMeasurableSpace.toMeasurableSingletonClass, T1Space, toMeasurableSingletonClass
-/
theorem mkOfPoint_points (p : P) (i : Fin 1) : (mkOfPoint k p).points i = p :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: P] : Inhabited (Simplex k P 0)
  body: ⟨mkOfPoint k default⟩

中文:
实例 [可居
  签名: P] : 可居 (单纯形 k P 0)
  定义体: ⟨mkOfPoint k default⟩

Depends on / 依赖: mkOfPoint
-/
instance [Inhabited P] : Inhabited (Simplex k P 0) :=
  ⟨mkOfPoint k default⟩

/--
Instance `nonempty` / 实例 `nonempty`

English:
instance nonempty
  signature: : Nonempty (Simplex k P 0)
  body: ⟨mkOfPoint k AddTorsor.nonempty.some⟩

中文:
实例 nonempty
  签名: : 非空 (单纯形 k P 0)
  定义体: ⟨mkOfPoint k AddTorsor.nonempty.some⟩

Depends on / 依赖: AddTorsor, AddTorsor.nonempty.some, mkOfPoint, nonempty
-/
instance nonempty : Nonempty (Simplex k P 0) :=
⟨mkOfPoint k AddTorsor.nonempty.some⟩

-- Although `simp` can prove this, it is still useful as a `simp` lemma, since the `simp`-generated
-- proof uses `range_eq_singleton_iff`, which does not apply when the LHS of this lemma appears
-- as part of a more complicated expression.
/--
lemma `range_mkOfPoint_points` / 引理 `range_mkOfPoint_points`

English:
lemma range_mkOfPoint_points
  given: (p : P)
  statement: Set.range (mkOfPoint k p).points = {p}
  proof: by
  simp

中文:
引理 range_mkOfPoint_points
  条件: (p : P)
  结论: 集合.range (mkOfPoint k p).points = {p}
  证明: by
  simp

Depends on / 依赖: TopologicalSpace, secondCountableTopologyEither_of_left
-/
@[simp] lemma range_mkOfPoint_points (p : P) : Set.range (mkOfPoint k p).points = {p} := by
  simp

variable {k}

/-- Two simplices are equal if they have the same points. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {n : Nat} {s1 s2 : Simplex k P n} (h : forall i, s1.points i = s2.points i)
  statement: s1 = s2
  proof: by
  cases s1
  cases s2
  congr with i
  exact h i

中文:
定理 ext
  条件: {n : 自然数} {s1 s2 : 单纯形 k P n} (h : 对任意 i, s1.points i = s2.points i)
  结论: s1 = s2
  证明: by
  cases s1
  cases s2
  congr with i
  exact h i

Depends on / 依赖: secondCountableTopologyEither_of_right
-/
theorem ext {n : Nat} {s1 s2 : Simplex k P n} (h : forall i, s1.points i = s2.points i) : s1 = s2 := by
  cases s1
  cases s2
  congr with i
  exact h i

/-- Two simplices are equal if and only if they have the same points. -/
add_decl_doc Affine.Simplex.ext_iff

/--
Definition of `face` / `face` 的定义

English:
definition face
  signature: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1)
  body: ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

中文:
定义 face
  签名: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数} (h : #fs = m + 1)
  定义体: ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

Depends on / 依赖: comp_embedding, fs.orderEmbOfFin, independent, orderEmbOfFin, points, s.independent.comp_embedding, s.points, toEmbedding
-/
def face {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) :
    Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩

/--
theorem `face_points` / 定理 `face_points`

English:
theorem face_points
  statement: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
  proof: rfl

中文:
定理 face_points
  结论: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数}
  证明: rfl
-/
theorem face_points {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) (i : Fin (m + 1)) :
    (s.face h).points i = s.points (fs.orderEmbOfFin h i) :=
  rfl

/--
theorem `face_points'` / 定理 `face_points'`

English:
theorem face_points'
  statement: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
  proof: rfl

中文:
定理 face_points'
  结论: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数}
  证明: rfl
-/
theorem face_points' {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) : (s.face h).points = s.points ∘ fs.orderEmbOfFin h :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mkOfPoint`. -/
@[simp]
/--
theorem `face_eq_mkOfPoint` / 定理 `face_eq_mkOfPoint`

English:
theorem face_eq_mkOfPoint
  given: {n : Nat} (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  ext
  simp [Affine.Simplex.mkOfPoint_points, Affine.Simplex.face_points, Finset.orderEmbOfFin_singleton]

中文:
定理 face_eq_mkOfPoint
  条件: {n : 自然数} (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  ext
  simp [Affine.Simplex.mkOfPoint_points, Affine.Simplex.face_points, Finset.orderEmbOfFin_singleton]

Depends on / 依赖: Affine, Affine.Simplex.face_points, Affine.Simplex.mkOfPoint_points, Finset, Finset.orderEmbOfFin_singleton, Simplex, face_points, mkOfPoint_points, orderEmbOfFin_singleton
-/
theorem face_eq_mkOfPoint {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.face (Finset.card_singleton i) = mkOfPoint k (s.points i) := by
  ext
  simp [Affine.Simplex.mkOfPoint_points, Affine.Simplex.face_points, Finset.orderEmbOfFin_singleton]

/-- The set of points of a face. -/
@[simp]
/--
theorem `range_face_points` / 定理 `range_face_points`

English:
theorem range_face_points
  statement: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
  proof: by
  rw [face_points']; rw [Set.range_comp]; rw [Finset.range_orderEmbOfFin]

中文:
定理 range_face_points
  结论: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数}
  证明: by
  rw [face_points']; rw [Set.range_comp]; rw [Finset.range_orderEmbOfFin]

Depends on / 依赖: Finset, Finset.range_orderEmbOfFin, Set.range_comp, face_points, range_comp, range_orderEmbOfFin
-/
theorem range_face_points {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) : Set.range (s.face h).points = s.points '' ↑fs := by
  rw [face_points']; rw [Set.range_comp]; rw [Finset.range_orderEmbOfFin]

/--
lemma `affineSpan_face_le` / 引理 `affineSpan_face_le`

English:
lemma affineSpan_face_le
  statement: {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
  proof: affineSpan_mono k (s.range_face_points h ▸ Set.image_subset_range _ _)

中文:
引理 affineSpan_face_le
  结论: {n : 自然数} (s : 单纯形 k P n) {fs : 有限集 (有限集 (n + 1))} {m : 自然数}
  证明: affineSpan_mono k (s.range_face_points h ▸ Set.image_subset_range _ _)

Depends on / 依赖: Set.image_subset_range, affineSpan_mono, image_subset_range, range_face_points, s.range_face_points
-/
lemma affineSpan_face_le {n : Nat} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) :
    affineSpan k (Set.range (s.face h).points) <= affineSpan k (Set.range s.points) :=
  affineSpan_mono k (s.range_face_points h ▸ Set.image_subset_range _ _)

/--
lemma `points_mem_affineSpan_face` / 引理 `points_mem_affineSpan_face`

English:
lemma points_mem_affineSpan_face
  statement: [Nontrivial k] {n : Nat} (s : Simplex k P n)
  proof: by
  rw [range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

中文:
引理 points_mem_affineSpan_face
  结论: [非平凡 k] {n : 自然数} (s : 单纯形 k P n)
  证明: by
  rw [range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

Depends on / 依赖: independent, mem_affineSpan_iff, range_face_points, s.independent.mem_affineSpan_iff
-/
lemma points_mem_affineSpan_face [Nontrivial k] {n : Nat} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {i : Fin (n + 1)} :
    s.points i in affineSpan k (Set.range (s.face h).points) ↔ i in fs := by
  rw [range_face_points]
  exact s.independent.mem_affineSpan_iff i fs

/--
Definition of `faceOpposite` / `faceOpposite` 的定义

English:
definition faceOpposite
  signature: {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1))
  body: s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

中文:
定义 faceOpposite
  签名: {n : 自然数} [NeZero n] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  定义体: s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

Depends on / 依赖: NeZero, NeZero.one_le, card_compl, one_le, s.face
-/
def faceOpposite {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) : Simplex k P (n - 1) :=
  s.face (fs := {i}ᶜ) (by simp [card_compl, NeZero.one_le])

/--
lemma `range_faceOpposite_points` / 引理 `range_faceOpposite_points`

English:
lemma range_faceOpposite_points
  given: {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  simp [faceOpposite]

中文:
引理 range_faceOpposite_points
  条件: {n : 自然数} [NeZero n] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  simp [faceOpposite]
-/
@[simp] lemma range_faceOpposite_points {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    Set.range (s.faceOpposite i).points = s.points '' {i}ᶜ := by
  simp [faceOpposite]

/--
lemma `affineSpan_faceOpposite_le` / 引理 `affineSpan_faceOpposite_le`

English:
lemma affineSpan_faceOpposite_le
  given: {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1))
  proof: s.affineSpan_face_le _

中文:
引理 affineSpan_faceOpposite_le
  条件: {n : 自然数} [NeZero n] (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: s.affineSpan_face_le _

Depends on / 依赖: affineSpan_face_le, s.affineSpan_face_le
-/
lemma affineSpan_faceOpposite_le {n : Nat} [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    affineSpan k (Set.range (s.faceOpposite i).points) <= affineSpan k (Set.range s.points) :=
  s.affineSpan_face_le _

/--
lemma `points_mem_affineSpan_faceOpposite` / 引理 `points_mem_affineSpan_faceOpposite`

English:
lemma points_mem_affineSpan_faceOpposite
  statement: [Nontrivial k] {n : Nat} [NeZero n] (s : Simplex k P n)
  proof: by
  rw [faceOpposite]; rw [s.points_mem_affineSpan_face]
  simp

中文:
引理 points_mem_affineSpan_faceOpposite
  结论: [非平凡 k] {n : 自然数} [NeZero n] (s : 单纯形 k P n)
  证明: by
  rw [faceOpposite]; rw [s.points_mem_affineSpan_face]
  simp

Depends on / 依赖: faceOpposite, points_mem_affineSpan_face, s.points_mem_affineSpan_face
-/
lemma points_mem_affineSpan_faceOpposite [Nontrivial k] {n : Nat} [NeZero n] (s : Simplex k P n)
    {i j : Fin (n + 1)} :
    s.points j in affineSpan k (Set.range (s.faceOpposite i).points) ↔ j != i := by
  rw [faceOpposite]; rw [s.points_mem_affineSpan_face]
  simp

/--
lemma `points_notMem_affineSpan_faceOpposite` / 引理 `points_notMem_affineSpan_faceOpposite`

English:
lemma points_notMem_affineSpan_faceOpposite
  statement: [Nontrivial k] {n : Nat} [NeZero n] (s : Simplex k P n)
  proof: by
  rw [points_mem_affineSpan_faceOpposite]
  simp

中文:
引理 points_notMem_affineSpan_faceOpposite
  结论: [非平凡 k] {n : 自然数} [NeZero n] (s : 单纯形 k P n)
  证明: by
  rw [points_mem_affineSpan_faceOpposite]
  simp

Depends on / 依赖: points_mem_affineSpan_faceOpposite
-/
lemma points_notMem_affineSpan_faceOpposite [Nontrivial k] {n : Nat} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) : s.points i ∉ affineSpan k (Set.range (s.faceOpposite i).points) := by
  rw [points_mem_affineSpan_faceOpposite]
  simp

/--
lemma `faceOpposite_point_eq_point_succAbove` / 引理 `faceOpposite_point_eq_point_succAbove`

English:
lemma faceOpposite_point_eq_point_succAbove
  statement: {n : Nat} [NeZero n] (s : Simplex k P n)
  proof: by
  simp_rw [faceOpposite, face, comp_apply, Finset.orderEmbOfFin_compl_singleton_apply]

中文:
引理 faceOpposite_point_eq_point_succAbove
  结论: {n : 自然数} [NeZero n] (s : 单纯形 k P n)
  证明: by
  simp_rw [faceOpposite, face, comp_apply, Finset.orderEmbOfFin_compl_singleton_apply]

Depends on / 依赖: Finset, Finset.orderEmbOfFin_compl_singleton_apply, comp_apply, faceOpposite, orderEmbOfFin_compl_singleton_apply, simp_rw
-/
lemma faceOpposite_point_eq_point_succAbove {n : Nat} [NeZero n] (s : Simplex k P n)
    (i : Fin (n + 1)) (j : Fin (n - 1 + 1)) :
    (s.faceOpposite i).points j =
      s.points (Fin.succAbove i (Fin.cast (Nat.sub_one_add_one (NeZero.ne _)) j)) := by
  simp_rw [faceOpposite, face, comp_apply, Finset.orderEmbOfFin_compl_singleton_apply]

/--
lemma `faceOpposite_point_eq_point_rev` / 引理 `faceOpposite_point_eq_point_rev`

English:
lemma faceOpposite_point_eq_point_rev
  given: (s : Simplex k P 1) (i : Fin 2) (n : Fin 1)
  proof: by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, faceOpposite_point_eq_point_succAbove]

中文:
引理 faceOpposite_point_eq_point_rev
  条件: (s : 单纯形 k P 1) (i : 有限集 2) (n : 有限集 1)
  证明: by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, faceOpposite_point_eq_point_succAbove]

Depends on / 依赖: Fin.succAbove, faceOpposite_point_eq_point_succAbove, i.rev, revert, succAbove
-/
lemma faceOpposite_point_eq_point_rev (s : Simplex k P 1) (i : Fin 2) (n : Fin 1) :
    (s.faceOpposite i).points n = s.points i.rev := by
  have h : i.rev = Fin.succAbove i n := by decide +revert
  simp [h, faceOpposite_point_eq_point_succAbove]

/--
lemma `faceOpposite_point_eq_point_one` / 引理 `faceOpposite_point_eq_point_one`

English:
lemma faceOpposite_point_eq_point_one
  given: (s : Simplex k P 1) (n : Fin 1)
  proof: s.faceOpposite_point_eq_point_rev _ _

中文:
引理 faceOpposite_point_eq_point_one
  条件: (s : 单纯形 k P 1) (n : 有限集 1)
  证明: s.faceOpposite_point_eq_point_rev _ _

Depends on / 依赖: ContinuousMul, ContinuousMul.measurableMul, SeparatelyContinuousMul, measurableMul
-/
@[simp] lemma faceOpposite_point_eq_point_one (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 0).points n = s.points 1 :=
  s.faceOpposite_point_eq_point_rev _ _

/--
lemma `faceOpposite_point_eq_point_zero` / 引理 `faceOpposite_point_eq_point_zero`

English:
lemma faceOpposite_point_eq_point_zero
  given: (s : Simplex k P 1) (n : Fin 1)
  proof: s.faceOpposite_point_eq_point_rev _ _

中文:
引理 faceOpposite_point_eq_point_zero
  条件: (s : 单纯形 k P 1) (n : 有限集 1)
  证明: s.faceOpposite_point_eq_point_rev _ _

Depends on / 依赖: ContinuousSub, ContinuousSub.measurableSub, measurableSub
-/
@[simp] lemma faceOpposite_point_eq_point_zero (s : Simplex k P 1) (n : Fin 1) :
    (s.faceOpposite 1).points n = s.points 0 :=
  s.faceOpposite_point_eq_point_rev _ _

/-- Needed to make `affineSpan (s.points '' {i}ᶜ)` nonempty. -/
instance {α} [Nontrivial α] (i : α) : Nonempty ({i}ᶜ : Set _) :=
  (Set.nonempty_compl_of_nontrivial i).to_subtype

/--
lemma `mem_affineSpan_image_iff` / 引理 `mem_affineSpan_image_iff`

English:
lemma mem_affineSpan_image_iff
  statement: [Nontrivial k] {n : Nat} (s : Simplex k P n)
  proof: s.independent.mem_affineSpan_iff _ _

中文:
引理 mem_affineSpan_image_iff
  结论: [非平凡 k] {n : 自然数} (s : 单纯形 k P n)
  证明: s.independent.mem_affineSpan_iff _ _

Depends on / 依赖: ContinuousInv, ContinuousInv.measurableInv, measurableInv
-/
@[simp] lemma mem_affineSpan_image_iff [Nontrivial k] {n : Nat} (s : Simplex k P n)
    {fs : Set (Fin (n + 1))} {i : Fin (n + 1)} :
    s.points i in affineSpan k (s.points '' fs) ↔ i in fs :=
  s.independent.mem_affineSpan_iff _ _

/--
lemma `affineCombination_mem_affineSpan_faceOpposite_iff` / 引理 `affineCombination_mem_affineSpan_faceOpposite_iff`

English:
lemma affineCombination_mem_affineSpan_faceOpposite_iff
  statement: {n : Nat} [NeZero n] {s : Simplex k P n}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

中文:
引理 affineCombination_mem_affineSpan_faceOpposite_iff
  结论: {n : 自然数} [NeZero n] {s : 单纯形 k P n}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

Depends on / 依赖: AddTorsor, AddTorsor.subsingleton_iff, ContinuousConstSMul, ContinuousConstSMul.toMeasurableConstSMul, Finset, Finset.mem_univ, Module, Module.subsingleton, Subsingleton, TopologicalSpace, affineCombination_mem_affineSpan_image, affineSpan_eq_top_iff_nonempty_of_subsingleton, eq_zero_of_affineCombination_mem_affineSpan, independent, mem_univ, range_faceOpposite_points, s.independent.eq_zero_of_affineCombination_mem_affineSpan, subsingleton, subsingleton_iff, subsingleton_or_nontrivial
-/
lemma affineCombination_mem_affineSpan_faceOpposite_iff {n : Nat} [NeZero n] {s : Simplex k P n}
    {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) {i : Fin (n + 1)} :
    Finset.univ.affineCombination k s.points w in
      affineSpan k (Set.range (s.faceOpposite i).points) ↔ w i = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [range_faceOpposite_points] at h
    exact s.independent.eq_zero_of_affineCombination_mem_affineSpan hw h (Finset.mem_univ i)
      (by simp)
  · rw [range_faceOpposite_points]
    rcases subsingleton_or_nontrivial k with hk | hk
    · have : Subsingleton V := Module.subsingleton k _
      have : Subsingleton P := (AddTorsor.subsingleton_iff V P).1 inferInstance
      rw [(affineSpan_eq_top_iff_nonempty_of_subsingleton k).2 (by simp)]
      simp
    · exact affineCombination_mem_affineSpan_image hw (by simpa using h) s.points

/-- Push forward an affine simplex under an injective affine map. -/
@[simps -fullyApplied]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
  body: f ∘ s.points
  independent := s.independent.map' f hf

@[simp]

中文:
定义 map
  签名: {n : 自然数} (s : 仿射.单纯形 k P n) (f : P ->ᵃ[k] P₂) (hf : 函数.单射 f)
  定义体: f ∘ s.points
  independent := s.independent.map' f hf

@[simp]

Depends on / 依赖: ContinuousSMul, ContinuousSMul.toMeasurableSMul, TopologicalSpace, points, s.points, toMeasurableSMul
-/
def map {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) :
    Affine.Simplex k P₂ n where
  points := f ∘ s.points
  independent := s.independent.map' f hf

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {n : Nat} (s : Affine.Simplex k P n)
  proof: ext fun _ => rfl

中文:
定理 map_id
  条件: {n : 自然数} (s : 仿射.单纯形 k P n)
  证明: ext fun _ => rfl
-/
theorem map_id {n : Nat} (s : Affine.Simplex k P n) :
    s.map (AffineMap.id _ _) Function.injective_id = s :=
  ext fun _ => rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {n : Nat} (s : Affine.Simplex k P n)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 map_comp
  结论: {n : 自然数} (s : 仿射.单纯形 k P n)
  证明: ext fun _ => rfl

@[simp]
-/
theorem map_comp {n : Nat} (s : Affine.Simplex k P n)
    (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
    (g : P₂ ->ᵃ[k] P₃) (hg : Function.Injective g) :
    s.map (g.comp f) (hg.comp hf) = (s.map f hf).map g hg :=
  ext fun _ => rfl

@[simp]
/--
theorem `face_map` / 定理 `face_map`

English:
theorem face_map
  statement: {n : Nat} (s : Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
  proof: rfl

@[simp]

中文:
定理 face_map
  结论: {n : 自然数} (s : 单纯形 k P n) (f : P ->ᵃ[k] P₂) (hf : 函数.单射 f)
  证明: rfl

@[simp]
-/
theorem face_map {n : Nat} (s : Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) :
    (s.map f hf).face h = (s.face h).map f hf :=
  rfl

@[simp]
/--
theorem `faceOpposite_map` / 定理 `faceOpposite_map`

English:
theorem faceOpposite_map
  statement: {n : Nat} [NeZero n] (s : Simplex k P n) (f : P ->ᵃ[k] P₂)
  proof: rfl

@[simp]

中文:
定理 faceOpposite_map
  结论: {n : 自然数} [NeZero n] (s : 单纯形 k P n) (f : P ->ᵃ[k] P₂)
  证明: rfl

@[simp]
-/
theorem faceOpposite_map {n : Nat} [NeZero n] (s : Simplex k P n) (f : P ->ᵃ[k] P₂)
    (hf : Function.Injective f) (i : Fin (n + 1)) :
    (s.map f hf).faceOpposite i = (s.faceOpposite i).map f hf :=
  rfl

@[simp]
/--
theorem `map_mkOfPoint` / 定理 `map_mkOfPoint`

English:
theorem map_mkOfPoint
  given: (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) (p : P)
  proof: rfl

中文:
定理 map_mkOfPoint
  条件: (f : P ->ᵃ[k] P₂) (hf : 函数.单射 f) (p : P)
  证明: rfl
-/
theorem map_mkOfPoint (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) (p : P) :
    (mkOfPoint k p).map f hf = mkOfPoint k (f p) :=
  rfl

/-- Remap a simplex along an `Equiv` of index types. -/
@[simps]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  body: ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩

中文:
定义 reindex
  签名: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (m + 1) ≃ 有限集 (n + 1))
  定义体: ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩

Depends on / 依赖: affineIndependent_equiv, e.symm, independent, points, s.independent, s.points
-/
def reindex {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Simplex k P n :=
  ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.independent⟩

/-- Reindexing by `Equiv.refl` yields the original simplex. -/
@[simp]
/--
theorem `reindex_refl` / 定理 `reindex_refl`

English:
theorem reindex_refl
  given: {n : Nat} (s : Simplex k P n)
  statement: s.reindex (Equiv.refl (Fin (n + 1))) = s
  proof: ext fun _ => rfl

中文:
定理 reindex_refl
  条件: {n : 自然数} (s : 单纯形 k P n)
  结论: s.reindex (等价.refl (有限集 (n + 1))) = s
  证明: ext fun _ => rfl
-/
theorem reindex_refl {n : Nat} (s : Simplex k P n) : s.reindex (Equiv.refl (Fin (n + 1))) = s :=
  ext fun _ => rfl

/-- Reindexing by the composition of two equivalences is the same as reindexing twice. -/
@[simp]
/--
theorem `reindex_trans` / 定理 `reindex_trans`

English:
theorem reindex_trans
  statement: {n₁ n₂ n₃ : Nat} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
  proof: rfl

中文:
定理 reindex_trans
  结论: {n₁ n₂ n₃ : 自然数} (e₁₂ : 有限集 (n₁ + 1) ≃ 有限集 (n₂ + 1))
  证明: rfl
-/
theorem reindex_trans {n₁ n₂ n₃ : Nat} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
    (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁) :
    s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ :=
  rfl

/-- Reindexing by an equivalence and its inverse yields the original simplex. -/
@[simp]
/--
theorem `reindex_reindex_symm` / 定理 `reindex_reindex_symm`

English:
theorem reindex_reindex_symm
  given: {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]

中文:
定理 reindex_reindex_symm
  条件: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (m + 1) ≃ 有限集 (n + 1))
  证明: by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]

Depends on / 依赖: Equiv.self_trans_symm, GroupWithZero, T1Space, measurableInv, reindex_refl, reindex_trans, self_trans_symm
-/
theorem reindex_reindex_symm {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).reindex e.symm = s := by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]

/-- Reindexing by the inverse of an equivalence and that equivalence yields the original simplex. -/
@[simp]
/--
theorem `reindex_symm_reindex` / 定理 `reindex_symm_reindex`

English:
theorem reindex_symm_reindex
  given: {m n : Nat} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]

中文:
定理 reindex_symm_reindex
  条件: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]

Depends on / 依赖: ContinuousMul, ContinuousMul.measurableMul, Equiv.symm_trans_self, SecondCountableTopology, reindex_refl, reindex_trans, symm_trans_self
-/
theorem reindex_symm_reindex {m n : Nat} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e.symm).reindex e = s := by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]

/-- Reindexing a simplex produces one with the same set of points. -/
@[simp]
/--
theorem `reindex_range_points` / 定理 `reindex_range_points`

English:
theorem reindex_range_points
  given: {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by
  rw [reindex]; rw [Set.range_comp]; rw [Equiv.range_eq_univ]; rw [Set.image_univ]

中文:
定理 reindex_range_points
  条件: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (m + 1) ≃ 有限集 (n + 1))
  证明: by
  rw [reindex]; rw [Set.range_comp]; rw [Equiv.range_eq_univ]; rw [Set.image_univ]

Depends on / 依赖: ContinuousSub, ContinuousSub.measurableSub, Equiv.range_eq_univ, SecondCountableTopology, Set.image_univ, Set.range_comp, image_univ, range_comp, range_eq_univ, reindex
-/
theorem reindex_range_points {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    Set.range (s.reindex e).points = Set.range s.points := by
  rw [reindex]; rw [Set.range_comp]; rw [Equiv.range_eq_univ]; rw [Set.image_univ]

/--
theorem `reindex_map` / 定理 `reindex_map`

English:
theorem reindex_map
  statement: {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: rfl

中文:
定理 reindex_map
  结论: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (m + 1) ≃ 有限集 (n + 1))
  证明: rfl

Depends on / 依赖: ContinuousSMul, ContinuousSMul.measurableSMul, TopologicalSpace
-/
theorem reindex_map {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).reindex e = (s.reindex e).map f hf :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_face_reindex` / 引理 `range_face_reindex`

English:
lemma range_face_reindex
  statement: {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
  proof: by
  simp only [range_face_points, reindex_points, Set.image_comp]
  simp

中文:
引理 range_face_reindex
  结论: {m n : 自然数} (s : 单纯形 k P m) (e : 有限集 (m + 1) ≃ 有限集 (n + 1))
  证明: by
  simp only [range_face_points, reindex_points, Set.image_comp]
  simp

Depends on / 依赖: Finset, Finset.card_map, Set.image_comp, card_map, e.symm.toEmbedding, fs.map, image_comp, isClosed_diagonal, isClosed_diagonal.measurableSet, measurableSet, points, range_face_points, reindex_points, toEmbedding
-/
lemma range_face_reindex {m n : Nat} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    {fs : Finset (Fin (n + 1))} {n' : Nat} (h : #fs = n' + 1) :
    Set.range ((s.reindex e).face h).points =
      Set.range (s.face (fs := fs.map e.symm.toEmbedding) (h ▸ Finset.card_map _)).points := by
  simp only [range_face_points, reindex_points, Set.image_comp]
  simp

/--
lemma `range_faceOpposite_reindex` / 引理 `range_faceOpposite_reindex`

English:
lemma range_faceOpposite_reindex
  statement: {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m)
  proof: by
  rw [faceOpposite]; rw [range_face_reindex]
  simp [Equiv.image_compl]

中文:
引理 range_faceOpposite_reindex
  结论: {m n : 自然数} [NeZero m] [NeZero n] (s : 单纯形 k P m)
  证明: by
  rw [faceOpposite]; rw [range_face_reindex]
  simp [Equiv.image_compl]

Depends on / 依赖: Equiv.image_compl, faceOpposite, image_compl, range_face_reindex
-/
lemma range_faceOpposite_reindex {m n : Nat} [NeZero m] [NeZero n] (s : Simplex k P m)
    (e : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    Set.range ((s.reindex e).faceOpposite i).points =
      Set.range (s.faceOpposite (e.symm i)).points := by
  rw [faceOpposite]; rw [range_face_reindex]
  simp [Equiv.image_compl]

section restrict

/-- Restrict an affine simplex to an affine subspace that contains it. -/
@[simps]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {n : Nat} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
  body: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    Affine.Simplex (V := S.direction) k S n :=
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  { points i := ⟨s.points i, hS <| mem_affineSpan _ <| Set.mem_range_self _⟩
    independent := AffineIndependent.of_comp S.subtype s.independent }

中文:
定义 restrict
  签名: {n : 自然数} (s : 仿射.单纯形 k P n) (S : 仿射子空间 k P)
  定义体: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    Affine.Simplex (V := S.direction) k S n :=
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  { points i := ⟨s.points i, hS <| mem_affineSpan _ <| Set.mem_range_self _⟩
    independent := AffineIndependent.of_comp S.subtype s.independent }

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
def restrict {n : Nat} (s : Affine.Simplex k P n) (S : AffineSubspace k P)
    (hS : affineSpan k (Set.range s.points) <= S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    Affine.Simplex (V := S.direction) k S n :=
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  { points i := ⟨s.points i, hS <| mem_affineSpan _ <| Set.mem_range_self _⟩
    independent := AffineIndependent.of_comp S.subtype s.independent }

/-- Restricting to `S₁` then mapping to a larger `S₂` is the same as restricting to `S₂`. -/
@[simp]
/--
theorem `restrict_map_inclusion` / 定理 `restrict_map_inclusion`

English:
theorem restrict_map_inclusion
  statement: {n : Nat} (s : Affine.Simplex k P n)
  proof: Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (Set.inclusion hS₂) ‹_›
    (s.restrict S₁ hS₁).map (AffineSubspace.inclusion hS₂) (Set.inclusion_injective hS₂) =
      s.restrict S₂ (hS₁.trans hS₂) :=
  rfl

@[simp]

中文:
定理 restrict_map_inclusion
  结论: {n : 自然数} (s : 仿射.单纯形 k P n)
  证明: Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (Set.inclusion hS₂) ‹_›
    (s.restrict S₁ hS₁).map (AffineSubspace.inclusion hS₂) (Set.inclusion_injective hS₂) =
      s.restrict S₂ (hS₁.trans hS₂) :=
  rfl

@[simp]

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem restrict_map_inclusion {n : Nat} (s : Affine.Simplex k P n)
    (S₁ S₂ : AffineSubspace k P) (hS₁) (hS₂ : S₁ <= S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (Set.inclusion hS₂) ‹_›
    (s.restrict S₁ hS₁).map (AffineSubspace.inclusion hS₂) (Set.inclusion_injective hS₂) =
      s.restrict S₂ (hS₁.trans hS₂) :=
  rfl

@[simp]
/--
theorem `map_subtype_restrict` / 定理 `map_subtype_restrict`

English:
theorem map_subtype_restrict
  proof: by
  rfl

中文:
定理 map_subtype_restrict
  证明: by
  rfl
-/
theorem map_subtype_restrict
    {n : Nat} (S : AffineSubspace k P) [Nonempty S] (s : Affine.Simplex k S n) :
    (s.map (AffineSubspace.subtype _) Subtype.coe_injective).restrict
      S (affineSpan_le.2 <| by rintro x ⟨y, rfl⟩; exact Subtype.prop _) = s := by
  rfl

/--
theorem `restrict_map_restrict` / 定理 `restrict_map_restrict`

English:
theorem restrict_map_restrict
  proof: Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
.trans hfS) := by (AffineSubspace.map_mono f hS₁)
  rfl

中文:
定理 restrict_map_restrict
  证明: Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
.trans hfS) := by (AffineSubspace.map_mono f hS₁)
  rfl

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
theorem restrict_map_restrict
    {n : Nat} (s : Affine.Simplex k P n) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f)
    (S₁ : AffineSubspace k P) (S₂ : AffineSubspace k P₂)
    (hS₁ : affineSpan k (Set.range s.points) <= S₁) (hfS : AffineSubspace.map f S₁ <= S₂) :
    letI := Nonempty.map (AffineSubspace.inclusion hS₁) inferInstance
    letI := Nonempty.map (AffineSubspace.inclusion hfS) inferInstance
    (s.restrict S₁ hS₁).map (f.restrict hfS) (AffineMap.restrict.injective hf _) =
      (s.map f hf).restrict S₂ (Eq.trans_le
          (by simp [AffineSubspace.map_span, Set.range_comp])
.trans hfS) := by (AffineSubspace.map_mono f hS₁)
  rfl

/-- Restricting to `affineSpan k (Set.range s.points)` can be reversed by mapping through
`AffineSubspace.subtype`. -/
@[simp]
/--
theorem `restrict_map_subtype` / 定理 `restrict_map_subtype`

English:
theorem restrict_map_subtype
  given: {n : Nat} (s : Affine.Simplex k P n)
  proof: rfl

中文:
定理 restrict_map_subtype
  条件: {n : 自然数} (s : 仿射.单纯形 k P n)
  证明: rfl
-/
theorem restrict_map_subtype {n : Nat} (s : Affine.Simplex k P n) :
    (s.restrict _ le_rfl).map (AffineSubspace.subtype _) Subtype.coe_injective = s :=
  rfl

/--
lemma `restrict_reindex` / 引理 `restrict_reindex`

English:
lemma restrict_reindex
  statement: {m n : Nat} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.reindex e).restrict S (s.reindex_range_points e ▸ hS) = (s.restrict S hS).reindex e :=
  rfl

中文:
引理 restrict_reindex
  结论: {m n : 自然数} (s : 仿射.单纯形 k P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.reindex e).restrict S (s.reindex_range_points e ▸ hS) = (s.restrict S hS).reindex e :=
  rfl

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma restrict_reindex {m n : Nat} (s : Affine.Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
    {S : AffineSubspace k P} (hS : affineSpan k (Set.range s.points) <= S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.reindex e).restrict S (s.reindex_range_points e ▸ hS) = (s.restrict S hS).reindex e :=
  rfl

/--
lemma `face_restrict` / 引理 `face_restrict`

English:
lemma face_restrict
  statement: {n : Nat} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp

中文:
引理 face_restrict
  结论: {n : 自然数} (s : 仿射.单纯形 k P n) {S : 仿射子空间 k P}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma face_restrict {n : Nat} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) <= S) {fs : Finset (Fin (n + 1))} {m : Nat}
    (h : #fs = m + 1) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).face h = (s.face h).restrict S ((s.affineSpan_face_le h).trans hS) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  ext i
  rw [restrict_points_coe]
  simp_rw [Affine.Simplex.face_points]
  simp

/--
lemma `faceOpposite_restrict` / 引理 `faceOpposite_restrict`

English:
lemma faceOpposite_restrict
  statement: {n : Nat} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((s.affineSpan_faceOpposite_le i).trans hS) :=
  s.face_restrict hS _

中文:
引理 faceOpposite_restrict
  结论: {n : 自然数} [NeZero n] (s : 仿射.单纯形 k P n) {S : 仿射子空间 k P}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((s.affineSpan_faceOpposite_le i).trans hS) :=
  s.face_restrict hS _

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma faceOpposite_restrict {n : Nat} [NeZero n] (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) <= S) (i : Fin (n + 1)) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).faceOpposite i = (s.faceOpposite i).restrict S
      ((s.affineSpan_faceOpposite_le i).trans hS) :=
  s.face_restrict hS _

end restrict

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]
variable [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/--
Definition of `setInterior` / `setInterior` 的定义

English:
definition setInterior
  signature: (I : Set k) {n : Nat} (s : Simplex k P n)
  body: {p | exists w : Fin (n + 1) -> k,
    (∑ i, w i = 1) ∧ (forall i, w i in I) ∧ Finset.univ.affineCombination k s.points w = p}

中文:
定义 set整数erior
  签名: (I : 集合 k) {n : 自然数} (s : 单纯形 k P n)
  定义体: {p | exists w : Fin (n + 1) -> k,
    (∑ i, w i = 1) ∧ (forall i, w i in I) ∧ Finset.univ.affineCombination k s.points w = p}
-/
protected def setInterior (I : Set k) {n : Nat} (s : Simplex k P n) : Set P :=
  {p | exists w : Fin (n + 1) -> k,
    (∑ i, w i = 1) ∧ (forall i, w i in I) ∧ Finset.univ.affineCombination k s.points w = p}

/--
lemma `affineCombination_mem_setInterior_iff` / 引理 `affineCombination_mem_setInterior_iff`

English:
lemma affineCombination_mem_setInterior_iff
  statement: {I : Set k} {n : Nat} {s : Simplex k P n}
  proof: by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ => ?_, fun h => ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

中文:
引理 affineCombination_mem_set整数erior_iff
  结论: {I : 集合 k} {n : 自然数} {s : 单纯形 k P n}
  证明: by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ => ?_, fun h => ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

Depends on / 依赖: affineIndependent_iff_eq_of_fintype_affineCombination_eq, independent, points, s.independent, s.points, simp_rw
-/
lemma affineCombination_mem_setInterior_iff {I : Set k} {n : Nat} {s : Simplex k P n}
    {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w in s.setInterior I ↔ forall i, w i in I := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ => ?_, fun h => ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

/--
lemma `setInterior_reindex` / 引理 `setInterior_reindex`

English:
lemma setInterior_reindex
  statement: (I : Set k) {m n : Nat} (s : Simplex k P n)
  proof: by
  ext p
  refine ⟨fun ⟨w, hw, hwI, h⟩ => ?_, fun ⟨w, hw, hwI, h⟩ => ?_⟩
  · subst h
    simp_rw [reindex]
    rw [← Function.comp_id w]; rw [← e.self_comp_symm]; rw [← Function.comp_assoc]; rw [← Equiv.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.symm.toEmbedding]; rw [map_univ_equiv]
    have hw' : ∑ i, (w ∘ e) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e i)
  · subst h
    rw [← Function.comp_id w]; rw [← Function.comp_id s.points]; rw [← e.symm_comp_self]; rw [← Function.comp_assoc]; rw [← Function.comp_assoc]; rw [← e.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.toEmbedding]; rw [map_univ_equiv]
    change Finset.univ.affineCombination k (s.reindex e).points _ in _
    have hw' : ∑ i, (w ∘ e.symm) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e.symm i)

中文:
引理 set整数erior_reindex
  结论: (I : 集合 k) {m n : 自然数} (s : 单纯形 k P n)
  证明: by
  ext p
  refine ⟨fun ⟨w, hw, hwI, h⟩ => ?_, fun ⟨w, hw, hwI, h⟩ => ?_⟩
  · subst h
    simp_rw [reindex]
    rw [← Function.comp_id w]; rw [← e.self_comp_symm]; rw [← Function.comp_assoc]; rw [← Equiv.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.symm.toEmbedding]; rw [map_univ_equiv]
    have hw' : ∑ i, (w ∘ e) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e i)
  · subst h
    rw [← Function.comp_id w]; rw [← Function.comp_id s.points]; rw [← e.symm_comp_self]; rw [← Function.comp_assoc]; rw [← Function.comp_assoc]; rw [← e.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.toEmbedding]; rw [map_univ_equiv]
    change Finset.univ.affineCombination k (s.reindex e).points _ in _
    have hw' : ∑ i, (w ∘ e.symm) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e.symm i)
-/
@[simp] lemma setInterior_reindex (I : Set k) {m n : Nat} (s : Simplex k P n)
    (e : Fin (n + 1) ≃ Fin (m + 1)) : (s.reindex e).setInterior I = s.setInterior I := by
  ext p
  refine ⟨fun ⟨w, hw, hwI, h⟩ => ?_, fun ⟨w, hw, hwI, h⟩ => ?_⟩
  · subst h
    simp_rw [reindex]
    rw [← Function.comp_id w]; rw [← e.self_comp_symm]; rw [← Function.comp_assoc]; rw [← Equiv.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.symm.toEmbedding]; rw [map_univ_equiv]
    have hw' : ∑ i, (w ∘ e) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e i)
  · subst h
    rw [← Function.comp_id w]; rw [← Function.comp_id s.points]; rw [← e.symm_comp_self]; rw [← Function.comp_assoc]; rw [← Function.comp_assoc]; rw [← e.coe_toEmbedding]; rw [← Finset.univ.affineCombination_map e.toEmbedding]; rw [map_univ_equiv]
    change Finset.univ.affineCombination k (s.reindex e).points _ in _
    have hw' : ∑ i, (w ∘ e.symm) i = 1 := by rwa [sum_comp_equiv, map_univ_equiv]
    rw [affineCombination_mem_setInterior_iff hw']
    exact fun i => hwI (e.symm i)

/--
lemma `setInterior_mono` / 引理 `setInterior_mono`

English:
lemma setInterior_mono
  given: {I J : Set k} (hij : I subseteq J) {n : Nat} (s : Simplex k P n)
  proof: fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => hij (hw01 i), hww⟩

中文:
引理 set整数erior_mono
  条件: {I J : 集合 k} (hij : I subseteq J) {n : 自然数} (s : 单纯形 k P n)
  证明: fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => hij (hw01 i), hww⟩
-/
lemma setInterior_mono {I J : Set k} (hij : I subseteq J) {n : Nat} (s : Simplex k P n) :
    s.setInterior I subseteq s.setInterior J :=
  fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => hij (hw01 i), hww⟩

/--
lemma `setInterior_subset_affineSpan` / 引理 `setInterior_subset_affineSpan`

English:
lemma setInterior_subset_affineSpan
  given: {I : Set k} {n : Nat} {s : Simplex k P n}
  proof: by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

中文:
引理 set整数erior_subset_affineSpan
  条件: {I : 集合 k} {n : 自然数} {s : 单纯形 k P n}
  证明: by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

Depends on / 依赖: affineCombination_mem_affineSpan_of_nonempty
-/
lemma setInterior_subset_affineSpan {I : Set k} {n : Nat} {s : Simplex k P n} :
    s.setInterior I subseteq affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

/--
lemma `setInterior_map` / 引理 `setInterior_map`

English:
lemma setInterior_map
  statement: (I : Set k) {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂}
  proof: by
  ext p
  rw [Set.mem_image]
  by_cases hp : p in affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw]; rw [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]; rw [Simplex.map_points]; rw [← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h => hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]; rw [AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq s.setInterior_subset_affineSpan), hqp⟩

中文:
引理 set整数erior_map
  结论: (I : 集合 k) {n : 自然数} (s : 单纯形 k P n) {f : P ->ᵃ[k] P₂}
  证明: by
  ext p
  rw [Set.mem_image]
  by_cases hp : p in affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw]; rw [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]; rw [Simplex.map_points]; rw [← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h => hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]; rw [AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq s.setInterior_subset_affineSpan), hqp⟩

Depends on / 依赖: Affine, Affine.Simplex.affineCombination_mem_setInterior_iff, Finset, Finset.map_affineCombination, Set.mem_image, Set.mem_of_mem_of_subset, Set.range, Simplex, Simplex.map_points, affineCombination_mem_setInterior_iff, affineSpan, eq_affineCombination_of_mem_affineSpan_of_fintype, eq_iff, hf.eq_iff, iff_of_false, map_affineCombination, map_points, mem_image, mem_of_mem_of_subset, points
-/
lemma setInterior_map (I : Set k) {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂}
    (hf : Function.Injective f) : (s.map f hf).setInterior I = f '' s.setInterior I := by
  ext p
  rw [Set.mem_image]
  by_cases hp : p in affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw]; rw [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]; rw [Simplex.map_points]; rw [← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h => hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points]; rw [Set.range_comp]; rw [← AffineSubspace.map_span]; rw [AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq s.setInterior_subset_affineSpan), hqp⟩

/--
lemma `setInterior_restrict` / 引理 `setInterior_restrict`

English:
lemma setInterior_restrict
  statement: (I : Set k) {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff]; rw [Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using! hS))]; rw [← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

中文:
引理 set整数erior_restrict
  结论: (I : 集合 k) {n : 自然数} (s : 单纯形 k P n) {S : 仿射子空间 k P}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff]; rw [Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using! hS))]; rw [← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma setInterior_restrict (I : Set k) {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) <= S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  let := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff]; rw [Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using! hS))]; rw [← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

section PartialOrder
variable [PartialOrder k]

/--
Definition of `interior` / `interior` 的定义

English:
definition interior
  signature: {n : Nat} (s : Simplex k P n)
  body: s.setInterior (Set.Ioo 0 1)

中文:
定义 interior
  签名: {n : 自然数} (s : 单纯形 k P n)
  定义体: s.setInterior (Set.Ioo 0 1)
-/
protected def interior {n : Nat} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Ioo 0 1)

/--
lemma `interior_reindex` / 引理 `interior_reindex`

English:
lemma interior_reindex
  given: {m n : Nat} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: s.setInterior_reindex _ _

中文:
引理 interior_reindex
  条件: {m n : 自然数} (s : 单纯形 k P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: s.setInterior_reindex _ _
-/
@[simp] lemma interior_reindex {m n : Nat} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).interior = s.interior :=
  s.setInterior_reindex _ _

/--
lemma `affineCombination_mem_interior_iff` / 引理 `affineCombination_mem_interior_iff`

English:
lemma affineCombination_mem_interior_iff
  statement: {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k}
  proof: affineCombination_mem_setInterior_iff hw

中文:
引理 affineCombination_mem_interior_iff
  结论: {n : 自然数} {s : 单纯形 k P n} {w : 有限集 (n + 1) -> k}
  证明: affineCombination_mem_setInterior_iff hw

Depends on / 依赖: affineCombination_mem_setInterior_iff
-/
lemma affineCombination_mem_interior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w in s.interior ↔ forall i, w i in Set.Ioo 0 1 :=
  affineCombination_mem_setInterior_iff hw

/--
Definition of `closedInterior` / `closedInterior` 的定义

English:
definition closedInterior
  signature: {n : Nat} (s : Simplex k P n)
  body: s.setInterior (Set.Icc 0 1)

中文:
定义 closed整数erior
  签名: {n : 自然数} (s : 单纯形 k P n)
  定义体: s.setInterior (Set.Icc 0 1)
-/
protected def closedInterior {n : Nat} (s : Simplex k P n) : Set P :=
  s.setInterior (Set.Icc 0 1)

/--
lemma `closedInterior_reindex` / 引理 `closedInterior_reindex`

English:
lemma closedInterior_reindex
  given: {m n : Nat} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1))
  proof: s.setInterior_reindex _ _

中文:
引理 closed整数erior_reindex
  条件: {m n : 自然数} (s : 单纯形 k P n) (e : 有限集 (n + 1) ≃ 有限集 (m + 1))
  证明: s.setInterior_reindex _ _
-/
@[simp] lemma closedInterior_reindex {m n : Nat} (s : Simplex k P n) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e).closedInterior = s.closedInterior :=
  s.setInterior_reindex _ _

/--
lemma `affineCombination_mem_closedInterior_iff` / 引理 `affineCombination_mem_closedInterior_iff`

English:
lemma affineCombination_mem_closedInterior_iff
  statement: {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k}
  proof: affineCombination_mem_setInterior_iff hw

中文:
引理 affineCombination_mem_closed整数erior_iff
  结论: {n : 自然数} {s : 单纯形 k P n} {w : 有限集 (n + 1) -> k}
  证明: affineCombination_mem_setInterior_iff hw

Depends on / 依赖: affineCombination_mem_setInterior_iff
-/
lemma affineCombination_mem_closedInterior_iff {n : Nat} {s : Simplex k P n} {w : Fin (n + 1) -> k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w in s.closedInterior ↔ forall i, w i in Set.Icc 0 1 :=
  affineCombination_mem_setInterior_iff hw

/--
lemma `interior_subset_closedInterior` / 引理 `interior_subset_closedInterior`

English:
lemma interior_subset_closedInterior
  given: {n : Nat} (s : Simplex k P n)
  proof: fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

中文:
引理 interior_subset_closed整数erior
  条件: {n : 自然数} (s : 单纯形 k P n)
  证明: fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

Depends on / 依赖: MeasurableSpace, RCLike, RCLike.measurableSpace, measurableSpace
-/
lemma interior_subset_closedInterior {n : Nat} (s : Simplex k P n) :
    s.interior subseteq s.closedInterior :=
  fun _ ⟨w, hw, hw01, hww⟩ => ⟨w, hw, fun i => ⟨(hw01 i).1.le, (hw01 i).2.le⟩, hww⟩

/--
lemma `point_notMem_interior` / 引理 `point_notMem_interior`

English:
lemma point_notMem_interior
  given: {n : Nat} (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_interior_iff (Fintype.sum_pi_single' _ _)]; rw [not_forall]
  exact ⟨i, by simp⟩

中文:
引理 point_notMem_interior
  条件: {n : 自然数} (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_interior_iff (Fintype.sum_pi_single' _ _)]; rw [not_forall]
  exact ⟨i, by simp⟩

Depends on / 依赖: BorelSpace, Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, RCLike, RCLike.borelSpace, affineCombination_mem_interior_iff, affineCombination_piSingle, borelSpace, mem_univ, not_forall, points, s.points, sum_pi_single
-/
lemma point_notMem_interior {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∉ s.interior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_interior_iff (Fintype.sum_pi_single' _ _)]; rw [not_forall]
  exact ⟨i, by simp⟩

/--
lemma `point_mem_closedInterior` / 引理 `point_mem_closedInterior`

English:
lemma point_mem_closedInterior
  given: [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1))
  proof: by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_closedInterior_iff (Fintype.sum_pi_single' _ _)]
  intro j
  obtain rfl | hj := eq_or_ne j i <;> simp_all

中文:
引理 point_mem_closed整数erior
  条件: [ZeroLEOne类 k] {n : 自然数} (s : 单纯形 k P n) (i : 有限集 (n + 1))
  证明: by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_closedInterior_iff (Fintype.sum_pi_single' _ _)]
  intro j
  obtain rfl | hj := eq_or_ne j i <;> simp_all

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ.affineCombination_piSingle, Fintype, Fintype.sum_pi_single, affineCombination_mem_closedInterior_iff, affineCombination_piSingle, eq_or_ne, mem_univ, points, s.points, sum_pi_single
-/
lemma point_mem_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.points i in s.closedInterior := by
  rw [← Finset.univ.affineCombination_piSingle k s.points (Finset.mem_univ i)]; rw [affineCombination_mem_closedInterior_iff (Fintype.sum_pi_single' _ _)]
  intro j
  obtain rfl | hj := eq_or_ne j i <;> simp_all

/--
lemma `nonempty_closedInterior` / 引理 `nonempty_closedInterior`

English:
lemma nonempty_closedInterior
  given: [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n)
  proof: ⟨s.points 0, s.point_mem_closedInterior 0⟩

中文:
引理 nonempty_closed整数erior
  条件: [ZeroLEOne类 k] {n : 自然数} (s : 单纯形 k P n)
  证明: ⟨s.points 0, s.point_mem_closedInterior 0⟩

Depends on / 依赖: point_mem_closedInterior, points, s.point_mem_closedInterior, s.points
-/
lemma nonempty_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) :
    s.closedInterior.Nonempty :=
  ⟨s.points 0, s.point_mem_closedInterior 0⟩

/--
lemma `interior_ssubset_closedInterior` / 引理 `interior_ssubset_closedInterior`

English:
lemma interior_ssubset_closedInterior
  given: [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n)
  proof: by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩

中文:
引理 interior_ssubset_closed整数erior
  条件: [ZeroLEOne类 k] {n : 自然数} (s : 单纯形 k P n)
  证明: by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩

Depends on / 依赖: Set.ssubset_iff_exists, interior_subset_closedInterior, point_mem_closedInterior, point_notMem_interior, points, s.interior_subset_closedInterior, s.point_mem_closedInterior, s.point_notMem_interior, s.points, ssubset_iff_exists
-/
lemma interior_ssubset_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n) :
    s.interior ⊂ s.closedInterior := by
  rw [Set.ssubset_iff_exists]
  exact ⟨s.interior_subset_closedInterior, s.points 0, s.point_mem_closedInterior 0,
    s.point_notMem_interior 0⟩

/--
lemma `closedInterior_subset_affineSpan` / 引理 `closedInterior_subset_affineSpan`

English:
lemma closedInterior_subset_affineSpan
  given: {n : Nat} {s : Simplex k P n}
  proof: by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

中文:
引理 closed整数erior_subset_affineSpan
  条件: {n : 自然数} {s : 单纯形 k P n}
  证明: by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

Depends on / 依赖: affineCombination_mem_affineSpan_of_nonempty
-/
lemma closedInterior_subset_affineSpan {n : Nat} {s : Simplex k P n} :
    s.closedInterior subseteq affineSpan k (Set.range s.points) := by
  rintro p ⟨w, hw, hi, rfl⟩
  exact affineCombination_mem_affineSpan_of_nonempty hw _

/--
lemma `interior_eq_empty` / 引理 `interior_eq_empty`

English:
lemma interior_eq_empty
  given: (s : Simplex k P 0)
  statement: s.interior = ∅
  proof: by
  ext p
  simp only [Simplex.interior, Simplex.setInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero,
    Fin.isValue, sum_singleton, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro w h hi
  simpa [h] using hi 0

中文:
引理 interior_eq_empty
  条件: (s : 单纯形 k P 0)
  结论: s.interior = ∅
  证明: by
  ext p
  simp only [Simplex.interior, Simplex.setInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero,
    Fin.isValue, sum_singleton, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro w h hi
  simpa [h] using hi 0
-/
@[simp] lemma interior_eq_empty (s : Simplex k P 0) : s.interior = ∅ := by
  ext p
  simp only [Simplex.interior, Simplex.setInterior, Nat.reduceAdd, univ_unique, Fin.default_eq_zero,
    Fin.isValue, sum_singleton, Set.mem_Ioo, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_exists, not_and]
  intro w h hi
  simpa [h] using hi 0

/--
lemma `closedInterior_eq_singleton` / 引理 `closedInterior_eq_singleton`

English:
lemma closedInterior_eq_singleton
  given: [ZeroLEOneClass k] (s : Simplex k P 0)
  proof: by
  ext p
  simp only [Simplex.closedInterior, Simplex.setInterior, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, sum_singleton, Set.mem_Icc, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

omit [PartialOrder k] in

中文:
引理 closed整数erior_eq_singleton
  条件: [ZeroLEOne类 k] (s : 单纯形 k P 0)
  证明: by
  ext p
  simp only [Simplex.closedInterior, Simplex.setInterior, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, sum_singleton, Set.mem_Icc, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

omit [PartialOrder k] in
-/
@[simp] lemma closedInterior_eq_singleton [ZeroLEOneClass k] (s : Simplex k P 0) :
    s.closedInterior = {s.points 0} := by
  ext p
  simp only [Simplex.closedInterior, Simplex.setInterior, Nat.reduceAdd, univ_unique,
    Fin.default_eq_zero, Fin.isValue, sum_singleton, Set.mem_Icc, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, h0, hi, rfl⟩
    simp [affineCombination_apply, h0]
  · rintro rfl
    exact ⟨1, by simp [affineCombination_apply]⟩

omit [PartialOrder k] in
/--
lemma `affineCombination_mem_setInterior_face_iff_mem` / 引理 `affineCombination_mem_setInterior_face_iff_mem`

English:
lemma affineCombination_mem_setInterior_face_iff_mem
  statement: (I : Set k) {n : Nat} (s : Simplex k P n)
  proof: by
  refine ⟨fun hi => ?_, fun ⟨hii, hi0⟩ => ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi setInterior_subset_affineSpan)
    rw [he]; rw [affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi => ?_, fun i hi => by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe]; rw [← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) -> k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi => hi0 _ (by simpa using hi)) (fun _ => rfl)]; rw [hw]
    have hw'01 (i) : w' i in I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert! hw'01
    convert! Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, mem_support]

中文:
引理 affineCombination_mem_set整数erior_face_iff_mem
  结论: (I : 集合 k) {n : 自然数} (s : 单纯形 k P n)
  证明: by
  refine ⟨fun hi => ?_, fun ⟨hii, hi0⟩ => ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi setInterior_subset_affineSpan)
    rw [he]; rw [affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi => ?_, fun i hi => by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe]; rw [← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) -> k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi => hi0 _ (by simpa using hi)) (fun _ => rfl)]; rw [hw]
    have hw'01 (i) : w' i in I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert! hw'01
    convert! Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, mem_support]

Depends on / 依赖: RelEmbedding, RelEmbedding.coe_toEmbedding, Set.mem_of_mem_of_subset, affineCombination_mem_setInterior_iff, coe_toEmbedding, eq_affineCombination_of_mem_affineSpan_of_fintype, fs.orderEmbOfFin, he.symm, independent, indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype, mem_of_mem_of_subset, orderEmbOfFin, s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype, setInterior_subset_affineSpan, simp_rw, toEmbedding
-/
lemma affineCombination_mem_setInterior_face_iff_mem (I : Set k) {n : Nat} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin (n + 1) -> k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w in (s.face h).setInterior I ↔
      (forall i in fs, w i in I) ∧ (forall i ∉ fs, w i = 0) := by
  refine ⟨fun hi => ?_, fun ⟨hii, hi0⟩ => ?_⟩
  · obtain ⟨w', hw', he⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype
      (Set.mem_of_mem_of_subset hi setInterior_subset_affineSpan)
    rw [he]; rw [affineCombination_mem_setInterior_iff hw'] at hi
    have he' := s.independent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
      hw hw' (fs.orderEmbOfFin h).toEmbedding he.symm
    simp_rw [he'.symm]
    refine ⟨fun i hi => ?_, fun i hi => by simp [hi]⟩
    simp only [RelEmbedding.coe_toEmbedding, range_orderEmbOfFin, mem_coe, hi, Set.indicator_of_mem]
    rw [← mem_coe]; rw [← fs.range_orderEmbOfFin h] at hi
    obtain ⟨j, rfl⟩ := hi
    simp [(fs.orderEmbOfFin h).injective.extend_apply, hi]
  · let w' : Fin (m + 1) -> k := w ∘ fs.orderEmbOfFin h
    have hw' : ∑ i, w' i = 1 := by
      rw [Fintype.sum_of_injective _ (fs.orderEmbOfFin h).injective w' w
        (fun i hi => hi0 _ (by simpa using hi)) (fun _ => rfl)]; rw [hw]
    have hw'01 (i) : w' i in I := hii (fs.orderEmbOfFin h i) (by simp)
    rw [← (s.face h).affineCombination_mem_setInterior_iff hw'] at hw'01
    convert! hw'01
    convert! Finset.univ.affineCombination_map (fs.orderEmbOfFin h).toEmbedding w s.points using 1
    simp only [map_orderEmbOfFin_univ, Finset.affineCombination_indicator_subset _ _ fs.subset_univ]
    congr
    grind [Set.indicator_eq_self, mem_support]

/--
lemma `affineCombination_mem_interior_face_iff_mem_Ioo` / 引理 `affineCombination_mem_interior_face_iff_mem_Ioo`

English:
lemma affineCombination_mem_interior_face_iff_mem_Ioo
  statement: {n : Nat} (s : Simplex k P n)
  proof: affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

中文:
引理 affineCombination_mem_interior_face_iff_mem_Ioo
  结论: {n : 自然数} (s : 单纯形 k P n)
  证明: affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

Depends on / 依赖: affineCombination_mem_setInterior_face_iff_mem
-/
lemma affineCombination_mem_interior_face_iff_mem_Ioo {n : Nat} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin (n + 1) -> k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w in (s.face h).interior ↔
      (forall i in fs, w i in Set.Ioo 0 1) ∧ (forall i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

/--
lemma `affineCombination_mem_closedInterior_face_iff_mem_Icc` / 引理 `affineCombination_mem_closedInterior_face_iff_mem_Icc`

English:
lemma affineCombination_mem_closedInterior_face_iff_mem_Icc
  statement: {n : Nat} (s : Simplex k P n)
  proof: affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

中文:
引理 affineCombination_mem_closed整数erior_face_iff_mem_Icc
  结论: {n : 自然数} (s : 单纯形 k P n)
  证明: affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

Depends on / 依赖: affineCombination_mem_setInterior_face_iff_mem
-/
lemma affineCombination_mem_closedInterior_face_iff_mem_Icc {n : Nat} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {w : Fin (n + 1) -> k}
    (hw : ∑ i, w i = 1) : Finset.univ.affineCombination k s.points w in (s.face h).closedInterior ↔
      (forall i in fs, w i in Set.Icc 0 1) ∧ (forall i ∉ fs, w i = 0) :=
  affineCombination_mem_setInterior_face_iff_mem _ _ _ hw

/--
lemma `affineCombination_mem_interior_face_iff_pos` / 引理 `affineCombination_mem_interior_face_iff_pos`

English:
lemma affineCombination_mem_interior_face_iff_pos
  statement: [IsOrderedAddMonoid k] {n : Nat}
  proof: by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [-> NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ => (hii t ht).le

中文:
引理 affineCombination_mem_interior_face_iff_pos
  结论: [是OrderedAdd幺半群 k] {n : 自然数}
  证明: by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [-> NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ => (hii t ht).le

Depends on / 依赖: Finset, Finset.single_lt_sum, Finset.subset_univ, Finset.sum_subset, NeZero, NeZero.ne, affineCombination_mem_interior_face_iff_mem_Ioo, exists_mem_ne, fs.exists_mem_ne, s.affineCombination_mem_interior_face_iff_mem_Ioo, single_lt_sum, subset_univ, sum_subset
-/
lemma affineCombination_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : Nat}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} [NeZero m] (h : #fs = m + 1)
    {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w in (s.face h).interior ↔
      (forall i in fs, 0 < w i) ∧ (forall i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_interior_face_iff_mem_Ioo h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  obtain ⟨j, hj, hji⟩ := fs.exists_mem_ne (by grind [-> NeZero.ne]) i
  exact Finset.single_lt_sum hji hi hj (hii j hj) fun t ht _ => (hii t ht).le

/--
lemma `affineCombination_mem_closedInterior_face_iff_nonneg` / 引理 `affineCombination_mem_closedInterior_face_iff_nonneg`

English:
lemma affineCombination_mem_closedInterior_face_iff_nonneg
  statement: [IsOrderedAddMonoid k] {n : Nat}
  proof: by
  rw [s.affineCombination_mem_closedInterior_face_iff_mem_Icc h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  exact Finset.single_le_sum (fun t ht => (hii t ht)) hi

中文:
引理 affineCombination_mem_closed整数erior_face_iff_nonneg
  结论: [是OrderedAdd幺半群 k] {n : 自然数}
  证明: by
  rw [s.affineCombination_mem_closedInterior_face_iff_mem_Icc h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  exact Finset.single_le_sum (fun t ht => (hii t ht)) hi

Depends on / 依赖: Finset, Finset.single_le_sum, Finset.subset_univ, Finset.sum_subset, affineCombination_mem_closedInterior_face_iff_mem_Icc, s.affineCombination_mem_closedInterior_face_iff_mem_Icc, single_le_sum, subset_univ, sum_subset
-/
lemma affineCombination_mem_closedInterior_face_iff_nonneg [IsOrderedAddMonoid k] {n : Nat}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1)
    {w : Fin (n + 1) -> k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w in (s.face h).closedInterior ↔
      (forall i in fs, 0 <= w i) ∧ (forall i ∉ fs, w i = 0) := by
  rw [s.affineCombination_mem_closedInterior_face_iff_mem_Icc h hw]
  refine ⟨by grind, fun ⟨hii, hi0⟩ => ⟨fun i hi => ⟨hii i hi, ?_⟩, hi0⟩⟩
  rw [← hw]; rw [← Finset.sum_subset (Finset.subset_univ fs) fun j _ => hi0 j]
  exact Finset.single_le_sum (fun t ht => (hii t ht)) hi

/--
lemma `interior_map` / 引理 `interior_map`

English:
lemma interior_map
  given: {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f)
  proof: s.setInterior_map _ hf

中文:
引理 interior_map
  条件: {n : 自然数} (s : 单纯形 k P n) {f : P ->ᵃ[k] P₂} (hf : 函数.单射 f)
  证明: s.setInterior_map _ hf

Depends on / 依赖: s.setInterior_map, setInterior_map
-/
lemma interior_map {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).interior = f '' s.interior :=
  s.setInterior_map _ hf

/--
lemma `closedInterior_map` / 引理 `closedInterior_map`

English:
lemma closedInterior_map
  given: {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f)
  proof: s.setInterior_map _ hf

中文:
引理 closed整数erior_map
  条件: {n : 自然数} (s : 单纯形 k P n) {f : P ->ᵃ[k] P₂} (hf : 函数.单射 f)
  证明: s.setInterior_map _ hf

Depends on / 依赖: s.setInterior_map, setInterior_map
-/
lemma closedInterior_map {n : Nat} (s : Simplex k P n) {f : P ->ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).closedInterior = f '' s.closedInterior :=
  s.setInterior_map _ hf

/--
lemma `interior_restrict` / 引理 `interior_restrict`

English:
lemma interior_restrict
  statement: {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).interior = S.subtype ⁻¹' s.interior :=
  s.setInterior_restrict _ hS

中文:
引理 interior_restrict
  结论: {n : 自然数} (s : 单纯形 k P n) {S : 仿射子空间 k P}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).interior = S.subtype ⁻¹' s.interior :=
  s.setInterior_restrict _ hS

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma interior_restrict {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) <= S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).interior = S.subtype ⁻¹' s.interior :=
  s.setInterior_restrict _ hS

/--
lemma `closedInterior_restrict` / 引理 `closedInterior_restrict`

English:
lemma closedInterior_restrict
  statement: {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
  proof: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS

中文:
引理 closed整数erior_restrict
  结论: {n : 自然数} (s : 单纯形 k P n) {S : 仿射子空间 k P}
  证明: Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS

Depends on / 依赖: AffineSubspace, AffineSubspace.inclusion, Nonempty, Nonempty.map, inclusion
-/
lemma closedInterior_restrict {n : Nat} (s : Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) <= S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS

/--
theorem `closedInterior_face_subset_closedInterior` / 定理 `closedInterior_face_subset_closedInterior`

English:
theorem closedInterior_face_subset_closedInterior
  statement: [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n)
  proof: by
  intro p hp
  have hp' : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hp
(s.face h).closedInterior_subset_affineSpan.trans
affineSpan_mono k by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i in fs <;> aesop

@[simp]

中文:
定理 closed整数erior_face_subset_closed整数erior
  结论: [ZeroLEOne类 k] {n : 自然数} (s : 单纯形 k P n)
  证明: by
  intro p hp
  have hp' : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hp
(s.face h).closedInterior_subset_affineSpan.trans
affineSpan_mono k by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i in fs <;> aesop

@[simp]

Depends on / 依赖: Set.mem_of_mem_of_subset, Set.range, affineCombination_mem_closedInterior_face_iff_mem_Icc, affineCombination_mem_closedInterior_iff, affineSpan, affineSpan_mono, closedInterior_subset_affineSpan, closedInterior_subset_affineSpan.trans, eq_affineCombination_of_mem_affineSpan_of_fintype, mem_of_mem_of_subset, points, s.face, s.points
-/
theorem closedInterior_face_subset_closedInterior [ZeroLEOneClass k] {n : Nat} (s : Simplex k P n)
    {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) :
    (s.face h).closedInterior subseteq s.closedInterior := by
  intro p hp
  have hp' : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hp
(s.face h).closedInterior_subset_affineSpan.trans
affineSpan_mono k by simp
  obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
  rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1] at hp
  rw [affineCombination_mem_closedInterior_iff hw1]
  intro i
  by_cases hi : i in fs <;> aesop

@[simp]
/--
theorem `point_mem_closedInterior_face_iff` / 定理 `point_mem_closedInterior_face_iff`

English:
theorem point_mem_closedInterior_face_iff
  statement: [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
  proof: by
  refine ⟨fun hj => ?_, fun hfs => ?_⟩
  · suffices s.points j in affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
.ge hfs · obtain ⟨i, rfl⟩ : exists i, fs.orderEmbOfFin h i = j := range_orderEmbOfFin fs h
    exact point_mem_closedInterior _ _

中文:
定理 point_mem_closed整数erior_face_iff
  结论: [非平凡 k] [ZeroLEOne类 k] {n : 自然数}
  证明: by
  refine ⟨fun hj => ?_, fun hfs => ?_⟩
  · suffices s.points j in affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
.ge hfs · obtain ⟨i, rfl⟩ : exists i, fs.orderEmbOfFin h i = j := range_orderEmbOfFin fs h
    exact point_mem_closedInterior _ _

Depends on / 依赖: Set.mem_of_mem_of_subset, affineCombination_mem_affineSpan, affineSpan, fs.orderEmbOfFin, mem_of_mem_of_subset, orderEmbOfFin, point_mem_closedInterior, points, range_orderEmbOfFin, s.points
-/
theorem point_mem_closedInterior_face_iff [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : Nat} (h : #fs = m + 1) {j : Fin (n + 1)} :
    s.points j in (s.face h).closedInterior ↔ j in fs := by
  refine ⟨fun hj => ?_, fun hfs => ?_⟩
  · suffices s.points j in affineSpan k (s.points '' fs) by simpa
    obtain ⟨w, hw, hw', hs⟩ := hj
    rw [← hs]
    exact Set.mem_of_mem_of_subset (affineCombination_mem_affineSpan hw _) (by simp)
.ge hfs · obtain ⟨i, rfl⟩ : exists i, fs.orderEmbOfFin h i = j := range_orderEmbOfFin fs h
    exact point_mem_closedInterior _ _

/--
theorem `closedInterior_face_ssubset_closedInterior` / 定理 `closedInterior_face_ssubset_closedInterior`

English:
theorem closedInterior_face_ssubset_closedInterior
  statement: [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
  proof: by
obtain ⟨a, ha⟩ := Classical.not_forall.mp Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a, fun hs => ha (by simpa using hs)⟩

中文:
定理 closed整数erior_face_ssubset_closed整数erior
  结论: [非平凡 k] [ZeroLEOne类 k] {n : 自然数}
  证明: by
obtain ⟨a, ha⟩ := Classical.not_forall.mp Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a, fun hs => ha (by simpa using hs)⟩

Depends on / 依赖: Classical, Classical.not_forall.mp, Finset, Finset.eq_univ_iff_forall.not.mp, Set.ssubset_iff_of_subset, closedInterior_face_subset_closedInterior, eq_univ_iff_forall, not_forall, point_mem_closedInterior, points, s.closedInterior_face_subset_closedInterior, s.point_mem_closedInterior, s.points, ssubset_iff_of_subset
-/
theorem closedInterior_face_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs != .univ) {m : Nat} (h : #fs = m + 1) :
    (s.face h).closedInterior ⊂ s.closedInterior := by
obtain ⟨a, ha⟩ := Classical.not_forall.mp Finset.eq_univ_iff_forall.not.mp hfs
  apply (Set.ssubset_iff_of_subset (s.closedInterior_face_subset_closedInterior h)).mpr
  exact ⟨s.points a, s.point_mem_closedInterior a, fun hs => ha (by simpa using hs)⟩

/--
theorem `disjoint_interior_closedInterior_face` / 定理 `disjoint_interior_closedInterior_face`

English:
theorem disjoint_interior_closedInterior_face
  statement: {n : Nat}
  proof: by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
  have hp : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hleft s.interior_subset_closedInterior.trans
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff, affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]

中文:
定理 disjoint_interior_closed整数erior_face
  结论: {n : 自然数}
  证明: by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
  have hp : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hleft s.interior_subset_closedInterior.trans
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff, affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]

Depends on / 依赖: Set.disjoint_left.mpr, Set.mem_of_mem_of_subset, Set.range, affineCombination_mem_closedInterior_face_iff_mem_Icc, affineCombination_mem_interior_iff, affineSpan, closedInterior_subset_affineSpan, disjoint_left, eq_affineCombination_of_mem_affineSpan_of_fintype, hright, interior_subset_closedInterior, mem_of_mem_of_subset, points, s.closedInterior_subset_affineSpan, s.interior_subset_closedInterior.trans, s.points
-/
theorem disjoint_interior_closedInterior_face {n : Nat}
    (s : Simplex k P n) {fs : Finset (Fin (n + 1))} (hfs : fs != .univ) {m : Nat} (h : #fs = m + 1) :
    Disjoint s.interior (s.face h).closedInterior := by
  refine Set.disjoint_left.mpr fun p hleft hright => ?_
  have hp : p in affineSpan k (Set.range s.points) :=
Set.mem_of_mem_of_subset hleft s.interior_subset_closedInterior.trans
      s.closedInterior_subset_affineSpan
  grind [affineCombination_mem_interior_iff, affineCombination_mem_closedInterior_face_iff_mem_Icc,
    eq_affineCombination_of_mem_affineSpan_of_fintype]

@[simp]
/--
theorem `point_mem_closedInterior_faceOpposite_iff` / 定理 `point_mem_closedInterior_faceOpposite_iff`

English:
theorem point_mem_closedInterior_faceOpposite_iff
  statement: [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
  proof: by
  simp [faceOpposite]

中文:
定理 point_mem_closed整数erior_faceOpposite_iff
  结论: [非平凡 k] [ZeroLEOne类 k] {n : 自然数}
  证明: by
  simp [faceOpposite]

Depends on / 依赖: faceOpposite
-/
theorem point_mem_closedInterior_faceOpposite_iff [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
    [NeZero n] (s : Simplex k P n) {i j : Fin (n + 1)} :
    s.points j in (s.faceOpposite i).closedInterior ↔ j != i := by
  simp [faceOpposite]

/--
theorem `closedInterior_faceOpposite_subset_closedInterior` / 定理 `closedInterior_faceOpposite_subset_closedInterior`

English:
theorem closedInterior_faceOpposite_subset_closedInterior
  statement: [ZeroLEOneClass k] {n : Nat} [NeZero n]
  proof: s.closedInterior_face_subset_closedInterior _

中文:
定理 closed整数erior_faceOpposite_subset_closed整数erior
  结论: [ZeroLEOne类 k] {n : 自然数} [NeZero n]
  证明: s.closedInterior_face_subset_closedInterior _

Depends on / 依赖: closedInterior_face_subset_closedInterior, s.closedInterior_face_subset_closedInterior
-/
theorem closedInterior_faceOpposite_subset_closedInterior [ZeroLEOneClass k] {n : Nat} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior subseteq s.closedInterior :=
  s.closedInterior_face_subset_closedInterior _

/--
theorem `closedInterior_faceOpposite_ssubset_closedInterior` / 定理 `closedInterior_faceOpposite_ssubset_closedInterior`

English:
theorem closedInterior_faceOpposite_ssubset_closedInterior
  statement: [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
  proof: s.closedInterior_face_ssubset_closedInterior (by simp) _

中文:
定理 closed整数erior_faceOpposite_ssubset_closed整数erior
  结论: [非平凡 k] [ZeroLEOne类 k] {n : 自然数}
  证明: s.closedInterior_face_ssubset_closedInterior (by simp) _

Depends on / 依赖: closedInterior_face_ssubset_closedInterior, s.closedInterior_face_ssubset_closedInterior
-/
theorem closedInterior_faceOpposite_ssubset_closedInterior [Nontrivial k] [ZeroLEOneClass k] {n : Nat}
    [NeZero n] (s : Simplex k P n) (i : Fin (n + 1)) :
    (s.faceOpposite i).closedInterior ⊂ s.closedInterior :=
  s.closedInterior_face_ssubset_closedInterior (by simp) _

/--
theorem `disjoint_interior_closedInterior_faceOpposite` / 定理 `disjoint_interior_closedInterior_faceOpposite`

English:
theorem disjoint_interior_closedInterior_faceOpposite
  statement: {n : Nat} [NeZero n]
  proof: s.disjoint_interior_closedInterior_face (by simp) _

中文:
定理 disjoint_interior_closed整数erior_faceOpposite
  结论: {n : 自然数} [NeZero n]
  证明: s.disjoint_interior_closedInterior_face (by simp) _

Depends on / 依赖: disjoint_interior_closedInterior_face, s.disjoint_interior_closedInterior_face
-/
theorem disjoint_interior_closedInterior_faceOpposite {n : Nat} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Disjoint s.interior (s.faceOpposite i).closedInterior :=
  s.disjoint_interior_closedInterior_face (by simp) _

end PartialOrder

section LinearOrder
variable [LinearOrder k]

/--
theorem `closedInterior_eq_interior_union` / 定理 `closedInterior_eq_interior_union`

English:
theorem closedInterior_eq_interior_union
  statement: [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n : Nat}
  proof: by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union]; rw [or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : exists j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1]; rw [← Finset.sum_erase_add _ _ (show i in Finset.univ by simp)]; rw [add_eq_right]; rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite]; rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ => hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior (Set.iUnion_subset fun i => ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i

中文:
定理 closed整数erior_eq_interior_union
  结论: [是OrderedAdd幺半群 k] [ZeroLEOne类 k] {n : 自然数}
  证明: by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union]; rw [or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : exists j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1]; rw [← Finset.sum_erase_add _ _ (show i in Finset.univ by simp)]; rw [add_eq_right]; rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite]; rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ => hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior (Set.iUnion_subset fun i => ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i

Depends on / 依赖: Set.Subset.antisymm, Set.mem_Ioo, Set.mem_of_mem_of_subset, Set.mem_union, Subset, affineCombination_mem_closedInterior_iff, affineCombination_mem_interior_iff, antisymm, closedInterior_subset_affineSpan, distrib, eq_affineCombination_of_mem_affineSpan_of_fintype, le_antisymm, mem_Ioo, mem_of_mem_of_subset, mem_union, or_iff_not_imp_left, s.closedInterior_subset_affineSpan, simp_rw
-/
theorem closedInterior_eq_interior_union [IsOrderedAddMonoid k] [ZeroLEOneClass k] {n : Nat}
    [NeZero n] (s : Simplex k P n) :
    s.closedInterior = s.interior union ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain hp' := Set.mem_of_mem_of_subset hp s.closedInterior_subset_affineSpan
    obtain ⟨w, hw1, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp'
    rw [Set.mem_union]; rw [or_iff_not_imp_left]
    intro h
    rw [affineCombination_mem_closedInterior_iff hw1] at hp
    simp_rw [affineCombination_mem_interior_iff hw1, Set.mem_Ioo] at h
    push +distrib Not at h
    obtain ⟨j, hj⟩ : exists j : Fin (n + 1), w j = 0 := by
      obtain ⟨i, hi | hi⟩ := h
      · exact ⟨i, le_antisymm hi (hp i).1⟩
      · have hi1 : w i = 1 := le_antisymm (hp i).2 hi
        rw [← hi1]; rw [← Finset.sum_erase_add _ _ (show i in Finset.univ by simp)]; rw [add_eq_right]; rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hp j).1)] at hw1
        exact ⟨i + 1, hw1 _ (by simp)⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    rw [faceOpposite]; rw [affineCombination_mem_closedInterior_face_iff_mem_Icc _ _ hw1]
    exact ⟨fun k _ => hp k, by simpa using hj⟩
  · refine Set.union_subset s.interior_subset_closedInterior (Set.iUnion_subset fun i => ?_)
    exact s.closedInterior_faceOpposite_subset_closedInterior i

/--
theorem `closedInterior_sdiff_interior` / 定理 `closedInterior_sdiff_interior`

English:
theorem closedInterior_sdiff_interior
  statement: [IsOrderedAddMonoid k] [ZeroLEOneClass k]
  proof: by
  simpa [closedInterior_eq_interior_union] using
    fun i => (s.disjoint_interior_closedInterior_faceOpposite i).symm

@[deprecated (since := "2026-06-03")]
alias closedInterior_diff_interior := closedInterior_sdiff_interior

中文:
定理 closed整数erior_sdiff_interior
  结论: [是OrderedAdd幺半群 k] [ZeroLEOne类 k]
  证明: by
  simpa [closedInterior_eq_interior_union] using
    fun i => (s.disjoint_interior_closedInterior_faceOpposite i).symm

@[deprecated (since := "2026-06-03")]
alias closedInterior_diff_interior := closedInterior_sdiff_interior

Depends on / 依赖: closedInterior_eq_interior_union, disjoint_interior_closedInterior_faceOpposite, s.disjoint_interior_closedInterior_faceOpposite
-/
theorem closedInterior_sdiff_interior [IsOrderedAddMonoid k] [ZeroLEOneClass k]
    {n : Nat} [NeZero n] (s : Simplex k P n) :
    s.closedInterior \ s.interior = ⋃ i : Fin (n + 1), (s.faceOpposite i).closedInterior := by
  simpa [closedInterior_eq_interior_union] using
    fun i => (s.disjoint_interior_closedInterior_faceOpposite i).symm

@[deprecated (since := "2026-06-03")]
alias closedInterior_diff_interior := closedInterior_sdiff_interior

end LinearOrder

end Simplex

end Affine
