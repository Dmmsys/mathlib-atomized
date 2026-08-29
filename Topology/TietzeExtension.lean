/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UrysohnsBounded

/-!
# Tietze extension theorem

In this file we prove a few version of the Tietze extension theorem. The theorem says that a
continuous function `s → ℝ` defined on a closed set in a normal topological space `Y` can be
extended to a continuous function on the whole space. Moreover, if all values of the original
function belong to some (finite or infinite, open or closed) interval, then the extension can be
chosen so that it takes values in the same interval. In particular, if the original function is a
bounded function, then there exists a bounded extension of the same norm.

The proof mostly follows <https://ncatlab.org/nlab/show/Tietze+extension+theorem>. We patch a small
gap in the proof for unbounded functions, see
`exists_extension_forall_exists_le_ge_of_isClosedEmbedding`.

In addition we provide a class `TietzeExtension` encoding the idea that a topological space
satisfies the Tietze extension theorem. This allows us to get a version of the Tietze extension
theorem that simultaneously applies to `ℝ`, `ℝ × ℝ`, `ℂ`, `ι → ℝ`, `ℝ≥0` et cetera. At some point
in the future, it may be desirable to provide instead a more general approach via
*absolute retracts*, but the current implementation covers the most common use cases easily.

## Implementation notes

We first prove the theorems for a closed embedding `e : X → Y` of a topological space into a normal
topological space, then specialize them to the case `X = s : Set Y`, `e = (↑)`.

## Tags

Tietze extension theorem, Urysohn's lemma, normal topological space
-/

public section

open Topology

/-! ### The `TietzeExtension` class -/

section TietzeExtensionClass

universe u u₁ u₂ v w

-- TODO: define *absolute retracts* and then prove they satisfy Tietze extension.
-- Then make instances of that instead and remove this class.
/--
Definition of `TietzeExtension` / `TietzeExtension` 的定义

English:
class TietzeExtension
  parameters: (Y : Type v) [TopologicalSpace Y]
  axioms and operations (1):
    - exists_restrict_eq'({X : Type u} [TopologicalSpace X] [NormalSpace X] (s : Set X) (hs : IsClosed s) (f : C(s, Y))) : exists (g : C(X, Y)), g.restrict s = f

中文:
类 TietzeExtension
  参数: (Y : 类型v) [TopologicalSpace Y]
  公理与运算 (1 个):
    - exists_restrict_eq'({X : 类型u} [TopologicalSpace X] [NormalSpace X] (s : Set X) (hs : IsClosed s) (f : C(s, Y))) : 存在 (g : C(X, Y)), g.restrict s = f
-/
class TietzeExtension (Y : Type v) [TopologicalSpace Y] : Prop where
  exists_restrict_eq' {X : Type u} [TopologicalSpace X] [NormalSpace X] (s : Set X)
    (hs : IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f

variable {X₁ : Type u₁} [TopologicalSpace X₁]
variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X}
variable {e : X₁ -> X}
variable {Y : Type v} [TopologicalSpace Y] [TietzeExtension.{u, v} Y]

/--
theorem `ContinuousMap.exists_restrict_eq` / 定理 `ContinuousMap.exists_restrict_eq`

English:
theorem ContinuousMap.exists_restrict_eq
  given: (hs : IsClosed s) (f : C(s, Y))
  proof: TietzeExtension.exists_restrict_eq' s hs f

中文:
定理 ContinuousMap.exists_restrict_eq
  条件: (hs : IsClosed s) (f : C(s, Y))
  证明: TietzeExtension.exists_restrict_eq' s hs f

Depends on / 依赖: TietzeExtension, TietzeExtension.exists_restrict_eq, exists_restrict_eq
-/
theorem ContinuousMap.exists_restrict_eq (hs : IsClosed s) (f : C(s, Y)) :
    exists (g : C(X, Y)), g.restrict s = f :=
  TietzeExtension.exists_restrict_eq' s hs f

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ContinuousMap.exists_extension` / 定理 `ContinuousMap.exists_extension`

English:
theorem ContinuousMap.exists_extension
  given: (he : IsClosedEmbedding e) (f : C(X₁, Y))
  proof: by
  let e' : X₁ ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ := (f.comp e'.symm).exists_restrict_eq he.isClosed_range
  exact ⟨g, by ext x; simpa using! congr($(hg) ⟨e' x, x, rfl⟩)⟩

中文:
定理 ContinuousMap.exists_extension
  条件: (he : IsClosedEmbedding e) (f : C(X₁, Y))
  证明: by
  let e' : X₁ ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ := (f.comp e'.symm).exists_restrict_eq he.isClosed_range
  exact ⟨g, by ext x; simpa using! congr($(hg) ⟨e' x, x, rfl⟩)⟩

Depends on / 依赖: Set.range, exists_restrict_eq, f.comp, he.isClosed_range, he.isEmbedding.toHomeomorph, isClosed_range, isEmbedding, toHomeomorph
-/
theorem ContinuousMap.exists_extension (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    exists (g : C(X, Y)), g.comp ⟨e, he.continuous⟩ = f := by
  let e' : X₁ ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ := (f.comp e'.symm).exists_restrict_eq he.isClosed_range
  exact ⟨g, by ext x; simpa using! congr($(hg) ⟨e' x, x, rfl⟩)⟩

/--
theorem `ContinuousMap.exists_extension'` / 定理 `ContinuousMap.exists_extension'`

English:
theorem ContinuousMap.exists_extension'
  given: (he : IsClosedEmbedding e) (f : C(X₁, Y))
  proof: .imp fun g hg => by ext x; congrm($(hg) x) f.exists_extension he

中文:
定理 ContinuousMap.exists_extension'
  条件: (he : IsClosedEmbedding e) (f : C(X₁, Y))
  证明: .imp fun g hg => by ext x; congrm($(hg) x) f.exists_extension he

Depends on / 依赖: congrm, exists_extension, f.exists_extension
-/
theorem ContinuousMap.exists_extension' (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    exists (g : C(X, Y)), g ∘ e = f :=
.imp fun g hg => by ext x; congrm($(hg) x) f.exists_extension he

/--
theorem `ContinuousMap.exists_forall_mem_restrict_eq` / 定理 `ContinuousMap.exists_forall_mem_restrict_eq`

English:
theorem ContinuousMap.exists_forall_mem_restrict_eq
  statement: (hs : IsClosed s)
  proof: by
.exists_restrict_eq hs obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

中文:
定理 ContinuousMap.exists_forall_mem_restrict_eq
  结论: (hs : IsClosed s)
  证明: by
.exists_restrict_eq hs obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

Depends on / 依赖: Subtype, Subtype.val, codRestrict, congrm, exists_restrict_eq, fun_prop, map_continuous
-/
theorem ContinuousMap.exists_forall_mem_restrict_eq (hs : IsClosed s)
    {Y : Type v} [TopologicalSpace Y] (f : C(s, Y))
    {t : Set Y} (hf : forall x, f x in t) [ht : TietzeExtension.{u, v} t] :
    exists (g : C(X, Y)), (forall x, g x in t) ∧ g.restrict s = f := by
.exists_restrict_eq hs obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

/--
theorem `ContinuousMap.exists_extension_forall_mem` / 定理 `ContinuousMap.exists_extension_forall_mem`

English:
theorem ContinuousMap.exists_extension_forall_mem
  statement: (he : IsClosedEmbedding e)
  proof: by
.exists_extension he obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

中文:
定理 ContinuousMap.exists_extension_forall_mem
  结论: (he : IsClosedEmbedding e)
  证明: by
.exists_extension he obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

Depends on / 依赖: Subtype, Subtype.val, codRestrict, congrm, exists_extension, fun_prop, map_continuous
-/
theorem ContinuousMap.exists_extension_forall_mem (he : IsClosedEmbedding e)
    {Y : Type v} [TopologicalSpace Y] (f : C(X₁, Y))
    {t : Set Y} (hf : forall x, f x in t) [ht : TietzeExtension.{u, v} t] :
    exists (g : C(X, Y)), (forall x, g x in t) ∧ g.comp ⟨e, he.continuous⟩ = f := by
.exists_extension he obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf)
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

/--
Instance `Pi.instTietzeExtension` / 实例 `Pi.instTietzeExtension`

English:
instance Pi.instTietzeExtension
  signature: {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
  body: by
obtain ⟨g', hg'⟩ := Classical.skolem.mp fun i =>
      ContinuousMap.exists_restrict_eq hs (ContinuousMap.piEquiv _ _ |>.symm f i)
    exact ⟨ContinuousMap.piEquiv _ _ g', by ext x i; congrm($(hg' i) x)⟩

中文:
实例 Pi.instTietzeExtension
  签名: {ι : 类型} {Y : ι -> 类型v} [对任意 i, TopologicalSpace (Y i)]
  定义体: by
obtain ⟨g', hg'⟩ := Classical.skolem.mp fun i =>
      ContinuousMap.exists_restrict_eq hs (ContinuousMap.piEquiv _ _ |>.symm f i)
    exact ⟨ContinuousMap.piEquiv _ _ g', by ext x i; congrm($(hg' i) x)⟩

Depends on / 依赖: Classical, Classical.skolem.mp, ContinuousMap, ContinuousMap.exists_restrict_eq, ContinuousMap.piEquiv, congrm, exists_restrict_eq, piEquiv, skolem
-/
instance Pi.instTietzeExtension {ι : Type*} {Y : ι -> Type v} [forall i, TopologicalSpace (Y i)]
    [forall i, TietzeExtension.{u} (Y i)] : TietzeExtension.{u} (forall i, Y i) where
  exists_restrict_eq' s hs f := by
obtain ⟨g', hg'⟩ := Classical.skolem.mp fun i =>
      ContinuousMap.exists_restrict_eq hs (ContinuousMap.piEquiv _ _ |>.symm f i)
    exact ⟨ContinuousMap.piEquiv _ _ g', by ext x i; congrm($(hg' i) x)⟩

/--
Instance `Prod.instTietzeExtension` / 实例 `Prod.instTietzeExtension`

English:
instance Prod.instTietzeExtension
  signature: {Y : Type v} {Z : Type w} [TopologicalSpace Y]
  body: by
    obtain ⟨g₁, hg₁⟩ := (ContinuousMap.fst.comp f).exists_restrict_eq hs
    obtain ⟨g₂, hg₂⟩ := (ContinuousMap.snd.comp f).exists_restrict_eq hs
    exact ⟨g₁.prodMk g₂, by ext1 x; congrm(($(hg₁) x), $(hg₂) x)⟩

中文:
实例 Prod.instTietzeExtension
  签名: {Y : 类型v} {Z : Type w} [TopologicalSpace Y]
  定义体: by
    obtain ⟨g₁, hg₁⟩ := (ContinuousMap.fst.comp f).exists_restrict_eq hs
    obtain ⟨g₂, hg₂⟩ := (ContinuousMap.snd.comp f).exists_restrict_eq hs
    exact ⟨g₁.prodMk g₂, by ext1 x; congrm(($(hg₁) x), $(hg₂) x)⟩

Depends on / 依赖: ContinuousMap, ContinuousMap.fst.comp, ContinuousMap.snd.comp, congrm, exists_restrict_eq, prodMk
-/
instance Prod.instTietzeExtension {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TietzeExtension.{u, v} Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] :
    TietzeExtension.{u, max w v} (Y × Z) where
  exists_restrict_eq' s hs f := by
    obtain ⟨g₁, hg₁⟩ := (ContinuousMap.fst.comp f).exists_restrict_eq hs
    obtain ⟨g₂, hg₂⟩ := (ContinuousMap.snd.comp f).exists_restrict_eq hs
    exact ⟨g₁.prodMk g₂, by ext1 x; congrm(($(hg₁) x), $(hg₂) x)⟩

/--
Instance `Unique.instTietzeExtension` / 实例 `Unique.instTietzeExtension`

English:
instance Unique.instTietzeExtension
  signature: {Y : Type v} [TopologicalSpace Y]
  body: ‹Nonempty Y›.elim fun y => ⟨.const _ y, by ext; subsingleton⟩

中文:
实例 Unique.instTietzeExtension
  签名: {Y : 类型v} [TopologicalSpace Y]
  定义体: ‹Nonempty Y›.elim fun y => ⟨.const _ y, by ext; subsingleton⟩

Depends on / 依赖: Nonempty, subsingleton
-/
instance Unique.instTietzeExtension {Y : Type v} [TopologicalSpace Y]
    [Nonempty Y] [Subsingleton Y] : TietzeExtension.{u, v} Y where
  exists_restrict_eq' _ _ f := ‹Nonempty Y›.elim fun y => ⟨.const _ y, by ext; subsingleton⟩

/--
theorem `TietzeExtension.of_retract` / 定理 `TietzeExtension.of_retract`

English:
theorem TietzeExtension.of_retract
  statement: {Y : Type v} {Z : Type w} [TopologicalSpace Y]
  proof: by
    obtain ⟨g, hg⟩ := (ι.comp f).exists_restrict_eq hs
    use r.comp g
    ext1 x
    have := congr(r.comp $(hg))
    rw [← r.comp_assoc ι]; rw [h]; rw [f.id_comp] at this
    congrm($this x)

中文:
定理 TietzeExtension.of_retract
  结论: {Y : 类型v} {Z : Type w} [TopologicalSpace Y]
  证明: by
    obtain ⟨g, hg⟩ := (ι.comp f).exists_restrict_eq hs
    use r.comp g
    ext1 x
    have := congr(r.comp $(hg))
    rw [← r.comp_assoc ι]; rw [h]; rw [f.id_comp] at this
    congrm($this x)

Depends on / 依赖: comp_assoc, congrm, exists_restrict_eq, f.id_comp, id_comp, r.comp, r.comp_assoc
-/
theorem TietzeExtension.of_retract {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι : C(Y, Z)) (r : C(Z, Y))
    (h : r.comp ι = .id Y) : TietzeExtension.{u, v} Y where
  exists_restrict_eq' s hs f := by
    obtain ⟨g, hg⟩ := (ι.comp f).exists_restrict_eq hs
    use r.comp g
    ext1 x
    have := congr(r.comp $(hg))
    rw [← r.comp_assoc ι]; rw [h]; rw [f.id_comp] at this
    congrm($this x)

/--
theorem `TietzeExtension.of_homeo` / 定理 `TietzeExtension.of_homeo`

English:
theorem TietzeExtension.of_homeo
  statement: {Y : Type v} {Z : Type w} [TopologicalSpace Y]
  proof: .of_retract (e : C(Y, Z)) (e.symm : C(Z, Y)) by simp

中文:
定理 TietzeExtension.of_homeo
  结论: {Y : 类型v} {Z : Type w} [TopologicalSpace Y]
  证明: .of_retract (e : C(Y, Z)) (e.symm : C(Z, Y)) by simp

Depends on / 依赖: e.symm, of_retract
-/
theorem TietzeExtension.of_homeo {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y ≃ₜ Z) :
    TietzeExtension.{u, v} Y :=
.of_retract (e : C(Y, Z)) (e.symm : C(Z, Y)) by simp

end TietzeExtensionClass

/-! The Tietze extension theorem for `ℝ`. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]

open Metric Set Filter

open BoundedContinuousFunction Topology

noncomputable section

namespace BoundedContinuousFunction

/--
theorem `tietze_extension_step` / 定理 `tietze_extension_step`

English:
theorem tietze_extension_step
  given: (f : X ->ᵇ Real) (e : C(X, Y)) (he : IsClosedEmbedding e)
  proof: by
  have h3 : (0 : Real) < 3 := by norm_num1
  have h23 : 0 < (2 / 3 : Real) := by norm_num1
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  /- Otherwise, the closed sets `e '' f ⁻¹' (Iic (-‖f‖ / 3))` and

中文:
定理 tietze_extension_step
  条件: (f : X ->ᵇ 实数) (e : C(X, Y)) (he : IsClosedEmbedding e)
  证明: by
  have h3 : (0 : Real) < 3 := by norm_num1
  have h23 : 0 < (2 / 3 : Real) := by norm_num1
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  /- Otherwise, the closed sets `e '' f ⁻¹' (Iic (-‖f‖ / 3))` and

Depends on / 依赖: norm_num1
-/
theorem tietze_extension_step (f : X ->ᵇ Real) (e : C(X, Y)) (he : IsClosedEmbedding e) :
    exists g : Y ->ᵇ Real, ‖g‖ <= ‖f‖ / 3 ∧ dist (g.compContinuous e) f <= 2 / 3 * ‖f‖ := by
  have h3 : (0 : Real) < 3 := by norm_num1
  have h23 : 0 < (2 / 3 : Real) := by norm_num1
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  /- Otherwise, the closed sets `e '' f ⁻¹' (Iic (-‖f‖ / 3))` and `e '' f ⁻¹' (Ici (‖f‖ / 3))`
    are disjoint, hence by Urysohn's lemma there exists a function `g` that is equal to `-‖f‖ / 3`
    on the former set and is equal to `‖f‖ / 3` on the latter set. This function `g` satisfies the
    assertions of the lemma. -/
  have hf3 : -‖f‖ / 3 < ‖f‖ / 3 := (div_lt_div_iff_of_pos_right h3).2 (Left.neg_lt_self hf)
  have hc₁ : IsClosed (e '' f ⁻¹' Iic (-‖f‖ / 3)) :=
    he.isClosedMap _ (isClosed_Iic.preimage f.continuous)
  have hc₂ : IsClosed (e '' f ⁻¹' Ici (‖f‖ / 3)) :=
    he.isClosedMap _ (isClosed_Ici.preimage f.continuous)
  have hd : Disjoint (e '' f ⁻¹' Iic (-‖f‖ / 3)) (e '' f ⁻¹' Ici (‖f‖ / 3)) := by
    refine disjoint_image_of_injective he.injective (Disjoint.preimage _ ?_)
    rwa [Iic_disjoint_Ici, not_le]
  rcases exists_bounded_mem_Icc_of_closed_of_le hc₁ hc₂ hd hf3.le with ⟨g, hg₁, hg₂, hgf⟩
  refine ⟨g, ?_, ?_⟩
  · refine (norm_le <| div_nonneg hf.le h3.le).mpr fun y => ?_
    simpa [abs_le, neg_div] using hgf y
  · refine (dist_le <| mul_nonneg h23.le hf.le).mpr fun x => ?_
    have hfx : -‖f‖ <= f x ∧ f x <= ‖f‖ := by
      simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x
    rcases le_total (f x) (-‖f‖ / 3) with hle₁ | hle₁
    · calc
        |g (e x) - f x| = -‖f‖ / 3 - f x := by
          rw [hg₁ (mem_image_of_mem _ hle₁)]; rw [Function.const_apply]; rw [abs_of_nonneg (sub_nonneg.2 hle₁)]
        _ <= 2 / 3 * ‖f‖ := by linarith
    · rcases le_total (f x) (‖f‖ / 3) with hle₂ | hle₂
      · simp only [neg_div] at *
        calc
          dist (g (e x)) (f x) <= |g (e x)| + |f x| := dist_le_norm_add_norm _ _
          _ <= ‖f‖ / 3 + ‖f‖ / 3 := (add_le_add (abs_le.2 <| hgf _) (abs_le.2 ⟨hle₁, hle₂⟩))
          _ = 2 / 3 * ‖f‖ := by linarith
      · calc
          |g (e x) - f x| = f x - ‖f‖ / 3 := by
            rw [hg₂ (mem_image_of_mem _ hle₂)]; rw [abs_sub_comm]; rw [Function.const_apply]; rw [abs_of_nonneg (sub_nonneg.2 hle₂)]
          _ <= 2 / 3 * ‖f‖ := by linarith

/--
theorem `exists_extension_norm_eq_of_isClosedEmbedding'` / 定理 `exists_extension_norm_eq_of_isClosedEmbedding'`

English:
theorem exists_extension_norm_eq_of_isClosedEmbedding'
  statement: (f : X ->ᵇ Real) (e : C(X, Y))
  proof: by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X ->ᵇ Real => tietze_extension_step f e he
  set g : Nat -> Y ->ᵇ Real := fun n => (fun g => g + F (f - g.com

中文:
定理 exists_extension_norm_eq_of_isClosedEmbedding'
  结论: (f : X ->ᵇ 实数) (e : C(X, Y))
  证明: by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X ->ᵇ Real => tietze_extension_step f e he
  set g : Nat -> Y ->ᵇ Real := fun n => (fun g => g + F (f - g.com
-/
theorem exists_extension_norm_eq_of_isClosedEmbedding' (f : X ->ᵇ Real) (e : C(X, Y))
    (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g.compContinuous e = f := by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X ->ᵇ Real => tietze_extension_step f e he
  set g : Nat -> Y ->ᵇ Real := fun n => (fun g => g + F (f - g.compContinuous e))^[n] 0
  have g0 : g 0 = 0 := rfl
  have g_succ : forall n, g (n + 1) = g n + F (f - (g n).compContinuous e) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hgf : forall n, dist ((g n).compContinuous e) f <= (2 / 3) ^ n * ‖f‖ := by
    intro n
    induction n with
    | zero => simp [g0]
    | succ n ihn =>
      rw [g_succ n]; rw [add_compContinuous]; rw [← dist_sub_right]; rw [add_sub_cancel_left]; rw [pow_succ']; rw [mul_assoc]
      refine (hF_dist _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num1))
      rwa [← dist_eq_norm']
  have hg_dist : forall n, dist (g n) (g (n + 1)) <= 1 / 3 * ‖f‖ * (2 / 3) ^ n := by
    intro n
    calc
      dist (g n) (g (n + 1)) = ‖F (f - (g n).compContinuous e)‖ := by
        rw [g_succ]; rw [dist_eq_norm']; rw [add_sub_cancel_left]
      _ <= ‖f - (g n).compContinuous e‖ / 3 := hF_norm _
      _ = 1 / 3 * dist ((g n).compContinuous e) f := by rw [dist_eq_norm', one_div, div_eq_inv_mul]
      _ <= 1 / 3 * ((2 / 3) ^ n * ‖f‖) := mul_le_mul_of_nonneg_left (hgf n) (by norm_num1)
      _ = 1 / 3 * ‖f‖ * (2 / 3) ^ n := by ac_rfl
  have hg_cau : CauchySeq g := cauchySeq_of_le_geometric _ _ (by norm_num1) hg_dist
  have :
    Tendsto (fun n => (g n).compContinuous e) atTop
      (𝓝 <| (limUnder atTop g).compContinuous e) :=
    ((continuous_compContinuous e).tendsto _).comp hg_cau.tendsto_limUnder
  have hge : (limUnder atTop g).compContinuous e = f := by
    refine tendsto_nhds_unique this (tendsto_iff_dist_tendsto_zero.2 ?_)
    refine squeeze_zero (fun _ => dist_nonneg) hgf ?_
    rw [← zero_mul ‖f‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num1
  refine ⟨limUnder atTop g, le_antisymm ?_ ?_, hge⟩
  · rw [← dist_zero_left, ← g0]
    refine
      (dist_le_of_le_geometric_of_tendsto₀ _ _ (by norm_num1)
        hg_dist hg_cau.tendsto_limUnder).trans_eq ?_
    ring
  · rw [← hge]
    exact norm_compContinuous_le _ _

/--
theorem `exists_extension_norm_eq_of_isClosedEmbedding` / 定理 `exists_extension_norm_eq_of_isClosedEmbedding`

English:
theorem exists_extension_norm_eq_of_isClosedEmbedding
  statement: (f : X ->ᵇ Real) {e : X -> Y}
  proof: by
  rcases exists_extension_norm_eq_of_isClosedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

中文:
定理 exists_extension_norm_eq_of_isClosedEmbedding
  结论: (f : X ->ᵇ 实数) {e : X -> Y}
  证明: by
  rcases exists_extension_norm_eq_of_isClosedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

Depends on / 依赖: continuous, exists_extension_norm_eq_of_isClosedEmbedding, he.continuous
-/
theorem exists_extension_norm_eq_of_isClosedEmbedding (f : X ->ᵇ Real) {e : X -> Y}
    (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

/--
theorem `exists_norm_eq_domRestrict_eq_of_closed` / 定理 `exists_norm_eq_domRestrict_eq_of_closed`

English:
theorem exists_norm_eq_domRestrict_eq_of_closed
  given: {s : Set Y} (f : s ->ᵇ Real) (hs : IsClosed s)
  proof: exists_extension_norm_eq_of_isClosedEmbedding' f ((ContinuousMap.id _).restrict s)
    hs.isClosedEmbedding_subtypeVal

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq_of_closed := exists_norm_eq_domRestrict_eq_of_closed

中文:
定理 exists_norm_eq_domRestrict_eq_of_closed
  条件: {s : Set Y} (f : s ->ᵇ 实数) (hs : IsClosed s)
  证明: exists_extension_norm_eq_of_isClosedEmbedding' f ((ContinuousMap.id _).restrict s)
    hs.isClosedEmbedding_subtypeVal

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq_of_closed := exists_norm_eq_domRestrict_eq_of_closed

Depends on / 依赖: ContinuousMap, ContinuousMap.id, exists_extension_norm_eq_of_isClosedEmbedding, hs.isClosedEmbedding_subtypeVal, isClosedEmbedding_subtypeVal, restrict
-/
theorem exists_norm_eq_domRestrict_eq_of_closed {s : Set Y} (f : s ->ᵇ Real) (hs : IsClosed s) :
    exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f :=
  exists_extension_norm_eq_of_isClosedEmbedding' f ((ContinuousMap.id _).restrict s)
    hs.isClosedEmbedding_subtypeVal

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq_of_closed := exists_norm_eq_domRestrict_eq_of_closed

/--
theorem `exists_extension_forall_mem_Icc_of_isClosedEmbedding` / 定理 `exists_extension_forall_mem_Icc_of_isClosedEmbedding`

English:
theorem exists_extension_forall_mem_Icc_of_isClosedEmbedding
  statement: (f : X ->ᵇ Real) {a b : Real} {e : X -> Y}
  proof: by
  rcases exists_extension_norm_eq_of_isClosedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine ⟨const Y ((a + b) / 2) + g, fun y => ?_, ?_⟩
  · suffices ‖f - const X ((a + b) / 2)‖ <= (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
   

中文:
定理 exists_extension_forall_mem_Icc_of_isClosedEmbedding
  结论: (f : X ->ᵇ 实数) {a b : 实数} {e : X -> Y}
  证明: by
  rcases exists_extension_norm_eq_of_isClosedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine ⟨const Y ((a + b) / 2) + g, fun y => ?_, ?_⟩
  · suffices ‖f - const X ((a + b) / 2)‖ <= (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
   

Depends on / 依赖: Icc_eq_closedBall, Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm, div_nonneg, exists_extension_norm_eq_of_isClosedEmbedding, hgf.trans_le, norm_coe_le_norm, norm_le, sub_nonneg, trans_le, zero_le_two
-/
theorem exists_extension_forall_mem_Icc_of_isClosedEmbedding (f : X ->ᵇ Real) {a b : Real} {e : X -> Y}
    (hf : forall x, f x in Icc a b) (hle : a <= b) (he : IsClosedEmbedding e) :
    exists g : Y ->ᵇ Real, (forall y, g y in Icc a b) ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine ⟨const Y ((a + b) / 2) + g, fun y => ?_, ?_⟩
  · suffices ‖f - const X ((a + b) / 2)‖ <= (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
        (norm_coe_le_norm g y).trans (hgf.trans_le this)
    refine (norm_le <| div_nonneg (sub_nonneg.2 hle) zero_le_two).2 fun x => ?_
    simpa only [Real.Icc_eq_closedBall] using! hf x
  · ext x
    have : g (e x) = f x - (a + b) / 2 := congr_fun hge x
    simp [this]

/--
theorem `exists_extension_forall_exists_le_ge_of_isClosedEmbedding` / 定理 `exists_extension_forall_exists_le_ge_of_isClosedEmbedding`

English:
theorem exists_extension_forall_exists_le_ge_of_isClosedEmbedding
  statement: [Nonempty X] (f : X ->ᵇ Real)
  proof: by
  inhabit X
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : exists a, IsGLB (range f) a := ⟨_, isGLB_ciInf f.isBounded_range.bddBelow⟩
  obtain ⟨b, hb⟩ : exists b, IsLUB (range f) b := ⟨_, isLUB_ciSup f.isBounded_range.bddAbove⟩
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : for

中文:
定理 exists_extension_forall_exists_le_ge_of_isClosedEmbedding
  结论: [Nonempty X] (f : X ->ᵇ 实数)
  证明: by
  inhabit X
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : exists a, IsGLB (range f) a := ⟨_, isGLB_ciInf f.isBounded_range.bddBelow⟩
  obtain ⟨b, hb⟩ : exists b, IsLUB (range f) b := ⟨_, isLUB_ciSup f.isBounded_range.bddAbove⟩
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : for

Depends on / 依赖: inhabit
-/
theorem exists_extension_forall_exists_le_ge_of_isClosedEmbedding [Nonempty X] (f : X ->ᵇ Real)
    {e : X -> Y} (he : IsClosedEmbedding e) :
    exists g : Y ->ᵇ Real, (forall y, exists x₁ x₂, g y in Icc (f x₁) (f x₂)) ∧ g ∘ e = f := by
  inhabit X
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : exists a, IsGLB (range f) a := ⟨_, isGLB_ciInf f.isBounded_range.bddBelow⟩
  obtain ⟨b, hb⟩ : exists b, IsLUB (range f) b := ⟨_, isLUB_ciSup f.isBounded_range.bddAbove⟩
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : forall x, f x in Icc a b := fun x => ⟨ha.1 ⟨x, rfl⟩, hb.1 ⟨x, rfl⟩⟩
  -- Rule out the trivial case `a = b`
  have hle : a <= b := (hmem default).1.trans (hmem default).2
  rcases hle.eq_or_lt with (rfl | hlt)
  · have : forall x, f x = a := by simpa using hmem
    use const Y a
    simp [this, funext_iff]
  -- Put `c = (a + b) / 2`. Then `a < c < b` and `c - a = b - c`.
  set c := (a + b) / 2
  have hac : a < c := left_lt_add_div_two.2 hlt
  have hcb : c < b := add_div_two_lt_right.2 hlt
  have hsub : c - a = b - c := by
    simp [c]
    ring
  /- Due to `exists_extension_forall_mem_Icc_of_isClosedEmbedding`, there exists an extension `g`
    such that `g y ∈ [a, b]` for all `y`. However, if `a` and/or `b` do not belong to the range of
    `f`, then we need to ensure that these points do not belong to the range of `g`. This is done
    in two almost identical steps. First we deal with the case `∀ x, f x ≠ a`. -/
  obtain ⟨g, hg_mem, hgf⟩ : exists g : Y ->ᵇ Real, (forall y, exists x, g y in Icc (f x) b) ∧ g ∘ e = f := by
    rcases exists_extension_forall_mem_Icc_of_isClosedEmbedding f hmem hle he with ⟨g, hg_mem, hgf⟩
    -- If `a ∈ range f`, then we are done.
    rcases em (exists x, f x = a) with (⟨x, rfl⟩ | ha')
    · exact ⟨g, fun y => ⟨x, hg_mem _⟩, hgf⟩
    /- Otherwise, `g ⁻¹' {a}` is disjoint with `range e ∪ g ⁻¹' (Ici c)`, hence there exists a
        function `dg : Y → ℝ` such that `dg ∘ e = 0`, `dg y = 0` whenever `c ≤ g y`, `dg y = c - a`
        whenever `g y = a`, and `0 ≤ dg y ≤ c - a` for all `y`. -/
    have hd : Disjoint (range e union g ⁻¹' Ici c) (g ⁻¹' {a}) := by
      refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨x, rfl⟩ (rfl : g (e x) = a)
        exact ha' ⟨x, (congr_fun hgf x).symm⟩
      · exact Set.disjoint_singleton_right.2 hac.not_ge
    rcases exists_bounded_mem_Icc_of_closed_of_le
        (he.isClosed_range.union <| isClosed_Ici.preimage g.continuous)
        (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hac.le) with
      ⟨dg, dg0, dga, dgmem⟩
    replace hgf : forall x, (g + dg) (e x) = f x := by
      intro x
      simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
    refine ⟨g + dg, fun y => ?_, funext hgf⟩
    have hay : a < (g + dg) y := by
      rcases (hg_mem y).1.eq_or_lt with (rfl | hlt)
      · refine (lt_add_iff_pos_right _).2 ?_
        calc
          0 < c - g y := sub_pos.2 hac
          _ = dg y := (dga rfl).symm
      · exact hlt.trans_le (le_add_of_nonneg_right (dgmem y).1)
    rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
    refine ⟨x, hxy.le, ?_⟩
    rcases le_total c (g y) with hc | hc
    · simp [dg0 (Or.inr hc), (hg_mem y).2]
    · calc
        g y + dg y <= c + (c - a) := add_le_add hc (dgmem _).2
        _ = b := by rw [hsub, add_sub_cancel]
  /- Now we deal with the case `∀ x, f x ≠ b`. The proof is the same as in the first case, with
    minor modifications that make it hard to deduplicate code. -/
  choose xl hxl hgb using hg_mem
  rcases em (exists x, f x = b) with (⟨x, rfl⟩ | hb')
  · exact ⟨g, fun y => ⟨xl y, x, hxl y, hgb y⟩, hgf⟩
  have hd : Disjoint (range e union g ⁻¹' Iic c) (g ⁻¹' {b}) := by
    refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ (rfl : g (e x) = b)
      exact hb' ⟨x, (congr_fun hgf x).symm⟩
    · exact Set.disjoint_singleton_right.2 hcb.not_ge
  rcases exists_bounded_mem_Icc_of_closed_of_le
      (he.isClosed_range.union <| isClosed_Iic.preimage g.continuous)
      (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hcb.le) with
    ⟨dg, dg0, dgb, dgmem⟩
  replace hgf : forall x, (g - dg) (e x) = f x := by
    intro x
    simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
  refine ⟨g - dg, fun y => ?_, funext hgf⟩
  have hyb : (g - dg) y < b := by
    rcases (hgb y).eq_or_lt with (rfl | hlt)
    · refine (sub_lt_self_iff _).2 ?_
      calc
        0 < g y - c := sub_pos.2 hcb
        _ = dg y := (dgb rfl).symm
    · exact ((sub_le_self_iff _).2 (dgmem _).1).trans_lt hlt
  rcases hb.exists_between hyb with ⟨_, ⟨xu, rfl⟩, hyxu, _⟩
  rcases lt_or_ge c (g y) with hc | hc
  · rcases em (a in range f) with (⟨x, rfl⟩ | _)
    · refine ⟨x, xu, ?_, hyxu.le⟩
      calc
        f x = c - (b - c) := by rw [← hsub, sub_sub_cancel]
        _ <= g y - dg y := sub_le_sub hc.le (dgmem _).2
    · have hay : a < (g - dg) y := by
        calc
          a = c - (b - c) := by rw [← hsub, sub_sub_cancel]
          _ < g y - (b - c) := sub_lt_sub_right hc _
          _ <= g y - dg y := sub_le_sub_left (dgmem _).2 _
      rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
      exact ⟨x, xu, hxy.le, hyxu.le⟩
  · refine ⟨xl y, xu, ?_, hyxu.le⟩
    simp [dg0 (Or.inr hc), hxl]

/--
theorem `exists_extension_forall_mem_of_isClosedEmbedding` / 定理 `exists_extension_forall_mem_of_isClosedEmbedding`

English:
theorem exists_extension_forall_mem_of_isClosedEmbedding
  statement: (f : X ->ᵇ Real) {t : Set Real} {e : X -> Y}
  proof: by
  cases isEmpty_or_nonempty X
  · rcases hne with ⟨c, hc⟩
    exact ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
  rcases exists_extension_forall_exists_le_ge_of_isClosedEmbedding f he with ⟨g, hg, hgf⟩
  refine ⟨g, fun y => ?_, hgf⟩
  rcases hg y with ⟨xl, xu, h⟩
  exact hs.out (hf _)

中文:
定理 exists_extension_forall_mem_of_isClosedEmbedding
  结论: (f : X ->ᵇ 实数) {t : Set 实数} {e : X -> Y}
  证明: by
  cases isEmpty_or_nonempty X
  · rcases hne with ⟨c, hc⟩
    exact ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
  rcases exists_extension_forall_exists_le_ge_of_isClosedEmbedding f he with ⟨g, hg, hgf⟩
  refine ⟨g, fun y => ?_, hgf⟩
  rcases hg y with ⟨xl, xu, h⟩
  exact hs.out (hf _)

Depends on / 依赖: exists_extension_forall_exists_le_ge_of_isClosedEmbedding, hs.out, isEmptyElim, isEmpty_or_nonempty
-/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : X ->ᵇ Real) {t : Set Real} {e : X -> Y}
    [hs : OrdConnected t] (hf : forall x, f x in t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    exists g : Y ->ᵇ Real, (forall y, g y in t) ∧ g ∘ e = f := by
  cases isEmpty_or_nonempty X
  · rcases hne with ⟨c, hc⟩
    exact ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
  rcases exists_extension_forall_exists_le_ge_of_isClosedEmbedding f he with ⟨g, hg, hgf⟩
  refine ⟨g, fun y => ?_, hgf⟩
  rcases hg y with ⟨xl, xu, h⟩
  exact hs.out (hf _) (hf _) h

/--
theorem `exists_forall_mem_domRestrict_eq_of_closed` / 定理 `exists_forall_mem_domRestrict_eq_of_closed`

English:
theorem exists_forall_mem_domRestrict_eq_of_closed
  statement: {s : Set Y} (f : s ->ᵇ Real) (hs : IsClosed s)
  proof: by
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f hf hne hs.isClosedEmbedding_subtypeVal
  exact ⟨g, hg, DFunLike.coe_injective hgf⟩

@[deprecated (since := "2026-07-19")]
alias exists_forall_mem_restrict_eq_of_closed := exists_forall_mem_domRestrict_eq_of_closed

中文:
定理 exists_forall_mem_domRestrict_eq_of_closed
  结论: {s : Set Y} (f : s ->ᵇ 实数) (hs : IsClosed s)
  证明: by
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f hf hne hs.isClosedEmbedding_subtypeVal
  exact ⟨g, hg, DFunLike.coe_injective hgf⟩

@[deprecated (since := "2026-07-19")]
alias exists_forall_mem_restrict_eq_of_closed := exists_forall_mem_domRestrict_eq_of_closed

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, exists_extension_forall_mem_of_isClosedEmbedding, hs.isClosedEmbedding_subtypeVal, isClosedEmbedding_subtypeVal
-/
theorem exists_forall_mem_domRestrict_eq_of_closed {s : Set Y} (f : s ->ᵇ Real) (hs : IsClosed s)
    {t : Set Real} [OrdConnected t] (hf : forall x, f x in t) (hne : t.Nonempty) :
    exists g : Y ->ᵇ Real, (forall y, g y in t) ∧ g.domRestrict s = f := by
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f hf hne hs.isClosedEmbedding_subtypeVal
  exact ⟨g, hg, DFunLike.coe_injective hgf⟩

@[deprecated (since := "2026-07-19")]
alias exists_forall_mem_restrict_eq_of_closed := exists_forall_mem_domRestrict_eq_of_closed

end BoundedContinuousFunction

namespace ContinuousMap

/--
theorem `exists_extension_forall_mem_of_isClosedEmbedding` / 定理 `exists_extension_forall_mem_of_isClosedEmbedding`

English:
theorem exists_extension_forall_mem_of_isClosedEmbedding
  statement: (f : C(X, Real)) {t : Set Real} {e : X -> Y}
  proof: by
  have h : Real ≃o Ioo (-1 : Real) 1 := orderIsoIooNegOneOne Real
  let F : X ->ᵇ Real :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := by fun_prop
      map_bounded' := isBounded_range_iff.1
        ((isBounded_Ioo (-1 : Real) 1).subset <| range_subset_iff.2 fun x => (h (f x)).2) }
  let 

中文:
定理 exists_extension_forall_mem_of_isClosedEmbedding
  结论: (f : C(X, 实数)) {t : Set 实数} {e : X -> Y}
  证明: by
  have h : Real ≃o Ioo (-1 : Real) 1 := orderIsoIooNegOneOne Real
  let F : X ->ᵇ Real :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := by fun_prop
      map_bounded' := isBounded_range_iff.1
        ((isBounded_Ioo (-1 : Real) 1).subset <| range_subset_iff.2 fun x => (h (f x)).2) }
  let 

Depends on / 依赖: OrdConnected, continuous_toFun, fun_prop, ht_sub, image_subset_iff, isBounded_Ioo, isBounded_range_iff, map_bounded, orderIsoIooNegOneOne, range_subset_iff, subset, subseteq
-/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : C(X, Real)) {t : Set Real} {e : X -> Y}
    [hs : OrdConnected t] (hf : forall x, f x in t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    exists g : C(Y, Real), (forall y, g y in t) ∧ g ∘ e = f := by
  have h : Real ≃o Ioo (-1 : Real) 1 := orderIsoIooNegOneOne Real
  let F : X ->ᵇ Real :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := by fun_prop
      map_bounded' := isBounded_range_iff.1
        ((isBounded_Ioo (-1 : Real) 1).subset <| range_subset_iff.2 fun x => (h (f x)).2) }
  let t' : Set Real := (↑) ∘ h '' t
  have ht_sub : t' subseteq Ioo (-1 : Real) 1 := image_subset_iff.2 fun x _ => (h x).2
  have : OrdConnected t' := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    lift z to Ioo (-1 : Real) 1 using Icc_subset_Ioo (h x).2.1 (h y).2.2 hz
    change z in Icc (h x) (h y) at hz
    rw [← h.image_Icc] at hz
    rcases hz with ⟨z, hz, rfl⟩
    exact ⟨z, hs.out hx hy hz, rfl⟩
  have hFt : forall x, F x in t' := fun x => mem_image_of_mem _ (hf x)
  rcases F.exists_extension_forall_mem_of_isClosedEmbedding hFt (hne.image _) he with ⟨G, hG, hGF⟩
  let g : C(Y, Real) :=
    ⟨h.symm ∘ codRestrict G _ fun y => ht_sub (hG y),
h.symm.continuous.comp G.continuous.subtype_mk _⟩
  have hgG : forall {y a}, g y = a ↔ G y = h a := @fun y a =>
    h.toEquiv.symm_apply_eq.trans Subtype.ext_iff
  refine ⟨g, fun y => ?_, ?_⟩
  · rcases hG y with ⟨a, ha, hay⟩
    convert! ha
    exact hgG.2 hay.symm
  · ext x
    exact hgG.2 (congr_fun hGF _)

/--
theorem `exists_restrict_eq_forall_mem_of_closed` / 定理 `exists_restrict_eq_forall_mem_of_closed`

English:
theorem exists_restrict_eq_forall_mem_of_closed
  statement: {s : Set Y} (f : C(s, Real)) {t : Set Real}
  proof: let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f ht hne hs.isClosedEmbedding_subtypeVal
  ⟨g, hgt, coe_injective hgf⟩

中文:
定理 exists_restrict_eq_forall_mem_of_closed
  结论: {s : Set Y} (f : C(s, 实数)) {t : Set 实数}
  证明: let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f ht hne hs.isClosedEmbedding_subtypeVal
  ⟨g, hgt, coe_injective hgf⟩

Depends on / 依赖: coe_injective, exists_extension_forall_mem_of_isClosedEmbedding, hs.isClosedEmbedding_subtypeVal, isClosedEmbedding_subtypeVal
-/
theorem exists_restrict_eq_forall_mem_of_closed {s : Set Y} (f : C(s, Real)) {t : Set Real}
    [OrdConnected t] (ht : forall x, f x in t) (hne : t.Nonempty) (hs : IsClosed s) :
    exists g : C(Y, Real), (forall y, g y in t) ∧ g.restrict s = f :=
  let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f ht hne hs.isClosedEmbedding_subtypeVal
  ⟨g, hgt, coe_injective hgf⟩

end ContinuousMap

/--
Instance `Real.instTietzeExtension` / 实例 `Real.instTietzeExtension`

English:
instance Real.instTietzeExtension
  signature: : TietzeExtension Real where
  body: .imp f.exists_restrict_eq_forall_mem_of_closed (fun _ => mem_univ _) univ_nonempty hs
      fun _ => (And.right ·)

中文:
实例 Real.instTietzeExtension
  签名: : TietzeExtension 实数 where
  定义体: .imp f.exists_restrict_eq_forall_mem_of_closed (fun _ => mem_univ _) univ_nonempty hs
      fun _ => (And.right ·)

Depends on / 依赖: And.right, exists_restrict_eq_forall_mem_of_closed, f.exists_restrict_eq_forall_mem_of_closed, mem_univ, univ_nonempty
-/
instance Real.instTietzeExtension : TietzeExtension Real where
  exists_restrict_eq' _s hs f :=
.imp f.exists_restrict_eq_forall_mem_of_closed (fun _ => mem_univ _) univ_nonempty hs
      fun _ => (And.right ·)

set_option backward.isDefEq.respectTransparency false in
open NNReal in
/--
Instance `NNReal.instTietzeExtension` / 实例 `NNReal.instTietzeExtension`

English:
instance NNReal.instTietzeExtension
  signature: : TietzeExtension Real>=0
  body: .of_retract ⟨((↑) : Real>=0 -> Real), by fun_prop⟩ ⟨Real.toNNReal, continuous_real_toNNReal⟩ by
    ext; simp

中文:
实例 NNReal.instTietzeExtension
  签名: : TietzeExtension 实数>=0
  定义体: .of_retract ⟨((↑) : Real>=0 -> Real), by fun_prop⟩ ⟨Real.toNNReal, continuous_real_toNNReal⟩ by
    ext; simp

Depends on / 依赖: Real.toNNReal, continuous_real_toNNReal, fun_prop, of_retract, toNNReal
-/
instance NNReal.instTietzeExtension : TietzeExtension Real>=0 :=
.of_retract ⟨((↑) : Real>=0 -> Real), by fun_prop⟩ ⟨Real.toNNReal, continuous_real_toNNReal⟩ by
    ext; simp
