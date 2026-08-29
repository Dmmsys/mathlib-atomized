/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Centroid
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Pointwise
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Affine bases and barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

* `fintypeAffineCoords`: the `AffineSubspace` of `ι → k` (for `Fintype ι`) where coordinates sum
  to `1`.
* `finsuppAffineCoords`: the `AffineSubspace` of `ι →₀ k` where coordinates sum to `1`.
* `AffineBasis`: a structure representing an affine basis of an affine space.
* `AffineBasis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
* `AffineBasis.coord_apply_eq`: the behaviour of `AffineBasis.coord i` on `p i`.
* `AffineBasis.coord_apply_ne`: the behaviour of `AffineBasis.coord i` on `p j` when `j ≠ i`.
* `AffineBasis.coord_apply`: the behaviour of `AffineBasis.coord i` on `p j` for general `j`.
* `AffineBasis.coord_apply_combination`: the characterisation of `AffineBasis.coord i` in terms
  of affine combinations, i.e., `AffineBasis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

* Construct the affine equivalence between `P` and `finsuppAffineCoords ι k`.

-/

@[expose] public section

open Affine Module Set
open scoped Pointwise

section Coordinates

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

variable (ι k) in
/--
Definition of `fintypeAffineCoords` / `fintypeAffineCoords` 的定义

English:
definition fintypeAffineCoords
  signature: [Fintype ι]
  body: (affineSpan k {(1 : k)}).comap (Fintype.linearCombination k (1 : ι -> k)).toAffineMap

中文:
定义 fintypeAffineCoords
  签名: [有限类型 ι]
  定义体: (affineSpan k {(1 : k)}).comap (Fintype.linearCombination k (1 : ι -> k)).toAffineMap

Depends on / 依赖: Fintype, Fintype.linearCombination, affineSpan, linearCombination, toAffineMap
-/
def fintypeAffineCoords [Fintype ι] : AffineSubspace k (ι -> k) :=
  (affineSpan k {(1 : k)}).comap (Fintype.linearCombination k (1 : ι -> k)).toAffineMap

/--
lemma `mem_fintypeAffineCoords_iff_sum` / 引理 `mem_fintypeAffineCoords_iff_sum`

English:
lemma mem_fintypeAffineCoords_iff_sum
  given: [Fintype ι] {w : ι -> k}
  proof: by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]

中文:
引理 mem_fintypeAffineCoords_iff_sum
  条件: [有限类型 ι] {w : ι -> k}
  证明: by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, fintypeAffineCoords, linearCombination_apply
-/
lemma mem_fintypeAffineCoords_iff_sum [Fintype ι] {w : ι -> k} :
    w in fintypeAffineCoords ι k ↔ ∑ i, w i = 1 := by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]

/--
lemma `AffineIndependent.injOn_affineCombination_fintypeAffineCoords` / 引理 `AffineIndependent.injOn_affineCombination_fintypeAffineCoords`

English:
lemma AffineIndependent.injOn_affineCombination_fintypeAffineCoords
  statement: [Fintype ι] {p : ι -> P}
  proof: fun w₁ hw₁ w₂ hw₂ he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

中文:
引理 AffineIndependent.injOn_affineCombination_fintypeAffineCoords
  结论: [有限类型 ι] {p : ι -> P}
  证明: fun w₁ hw₁ w₂ hw₂ he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

Depends on / 依赖: affineIndependent_iff_eq_of_fintype_affineCombination_eq, mem_fintypeAffineCoords_iff_sum
-/
lemma AffineIndependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] {p : ι -> P}
    (h : AffineIndependent k p) :
    InjOn (Finset.univ.affineCombination k p) (fintypeAffineCoords ι k) :=
  fun w₁ hw₁ w₂ hw₂ he => (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

variable (ι k) in
/--
Definition of `finsuppAffineCoords` / `finsuppAffineCoords` 的定义

English:
definition finsuppAffineCoords
  signature: : AffineSubspace k (ι ->₀ k)
  body: (affineSpan k {(1 : k)}).comap (Finsupp.linearCombination k (1 : ι -> k)).toAffineMap

中文:
定义 finsuppAffineCoords
  签名: : 仿射子空间 k (ι ->₀ k)
  定义体: (affineSpan k {(1 : k)}).comap (Finsupp.linearCombination k (1 : ι -> k)).toAffineMap

Depends on / 依赖: Finsupp, Finsupp.linearCombination, affineSpan, linearCombination, toAffineMap
-/
noncomputable def finsuppAffineCoords : AffineSubspace k (ι ->₀ k) :=
  (affineSpan k {(1 : k)}).comap (Finsupp.linearCombination k (1 : ι -> k)).toAffineMap

/--
lemma `mem_finsuppAffineCoords_iff_linearCombination` / 引理 `mem_finsuppAffineCoords_iff_linearCombination`

English:
lemma mem_finsuppAffineCoords_iff_linearCombination
  given: {w : ι ->₀ k}
  proof: by
  simp [finsuppAffineCoords]

中文:
引理 mem_finsuppAffineCoords_iff_linearCombination
  条件: {w : ι ->₀ k}
  证明: by
  simp [finsuppAffineCoords]

Depends on / 依赖: finsuppAffineCoords
-/
lemma mem_finsuppAffineCoords_iff_linearCombination {w : ι ->₀ k} :
    w in finsuppAffineCoords ι k ↔ Finsupp.linearCombination k (1 : ι -> k) w = 1 := by
  simp [finsuppAffineCoords]

end Coordinates

universe u₁ u₂ u₃ u₄

/--
Definition of `AffineBasis` / `AffineBasis` 的定义

English:
structure AffineBasis
  parameters: (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  axioms and operations (3):
    - toFun : ι -> P
    - ind' : AffineIndependent k toFun
    - tot' : affineSpan k (range toFun) = ⊤

中文:
结构 仿射基
  参数: (ι : 类型u₁) (k : 类型u₂) {V : 类型u₃} (P : 类型u₄) [加法交换群 V]
  公理与运算 (3 个):
    - toFun : ι -> P
    - ind' : AffineIndependent k toFun
    - tot' : affineSpan k (range toFun) = ⊤
-/
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [AffineSpace V P] [Ring k] [Module k V] where
  /-- The underlying family of points.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : ι -> P
  protected ind' : AffineIndependent k toFun
  protected tot' : affineSpan k (range toFun) = ⊤

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (AffineBasis PUnit k PUnit)
  body: ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩

中文:
实例 :
  签名: 可居 (仿射基 命题单元 k 命题单元)
  定义体: ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩

Depends on / 依赖: affineIndependent_of_subsingleton
-/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (AffineBasis ι k P) ι P where
  body: AffineBasis.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]

中文:
实例 instFunLike
  签名: : 函数状 (仿射基 ι k P) ι P where
  定义体: AffineBasis.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]

Depends on / 依赖: AffineBasis, AffineBasis.toFun
-/
instance instFunLike : FunLike (AffineBasis ι k P) ι P where
  coe := AffineBasis.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι -> P) = b₂)
  statement: b₁ = b₂
  proof: DFunLike.coe_injective h

中文:
定理 ext
  条件: {b₁ b₂ : 仿射基 ι k P} (h : (b₁ : ι -> P) = b₂)
  结论: b₁ = b₂
  证明: DFunLike.coe_injective h

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι -> P) = b₂) : b₁ = b₂ :=
  DFunLike.coe_injective h

/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  statement: AffineIndependent k b
  proof: b.ind'

中文:
定理 ind
  结论: AffineIndependent k b
  证明: b.ind'

Depends on / 依赖: b.ind
-/
theorem ind : AffineIndependent k b :=
  b.ind'

/--
theorem `tot` / 定理 `tot`

English:
theorem tot
  statement: affineSpan k (range b) = ⊤
  proof: b.tot'

include b in

中文:
定理 tot
  结论: affineSpan k (range b) = ⊤
  证明: b.tot'

include b in

Depends on / 依赖: b.tot
-/
theorem tot : affineSpan k (range b) = ⊤ :=
  b.tot'

include b in
/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  statement: Nonempty ι
  proof: not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot

中文:
定理 nonempty
  结论: 非空 ι
  证明: not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot
-/
protected theorem nonempty : Nonempty ι :=
  not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (e : ι ≃ ι')
  body: ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩

@[simp, norm_cast]

中文:
定义 reindex
  签名: (e : ι ≃ ι')
  定义体: ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩

@[simp, norm_cast]

Depends on / 依赖: b.ind.comp_embedding, comp_embedding, e.symm, e.symm.surjective.range_comp, e.symm.toEmbedding, range_comp, surjective, toEmbedding
-/
def reindex (e : ι ≃ ι') : AffineBasis ι' k P :=
  ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding, by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩

@[simp, norm_cast]
/--
theorem `coe_reindex` / 定理 `coe_reindex`

English:
theorem coe_reindex
  statement: ⇑(b.reindex e) = b ∘ e.symm
  proof: rfl

@[simp]

中文:
定理 coe_reindex
  结论: ⇑(b.reindex e) = b ∘ e.symm
  证明: rfl

@[simp]
-/
theorem coe_reindex : ⇑(b.reindex e) = b ∘ e.symm :=
  rfl

@[simp]
/--
theorem `reindex_apply` / 定理 `reindex_apply`

English:
theorem reindex_apply
  given: (i' : ι')
  statement: b.reindex e i' = b (e.symm i')
  proof: rfl

@[simp]

中文:
定理 reindex_apply
  条件: (i' : ι')
  结论: b.reindex e i' = b (e.symm i')
  证明: rfl

@[simp]
-/
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  rfl

@[simp]
/--
theorem `reindex_refl` / 定理 `reindex_refl`

English:
theorem reindex_refl
  statement: b.reindex (Equiv.refl _) = b
  proof: ext rfl

中文:
定理 reindex_refl
  结论: b.reindex (等价.refl _) = b
  证明: ext rfl
-/
theorem reindex_refl : b.reindex (Equiv.refl _) = b :=
  ext rfl

/--
Definition of `basisOf` / `basisOf` 的定义

English:
definition basisOf
  signature: (i : ι)
  body: Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x != i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this]; rw [← direction_affineSpan]; rw [b.tot]; rw [AffineSubspace.direction_top]
      conv

中文:
定义 basisOf
  签名: (i : ι)
  定义体: Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x != i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this]; rw [← direction_affineSpan]; rw [b.tot]; rw [AffineSubspace.direction_top]
      conv

Depends on / 依赖: AffineSubspace, AffineSubspace.direction_top, Basis.mk, Submodule, Submodule.span, affineIndependent_iff_linearIndependent_vsub, b.ind, b.tot, conv_rhs, direction_affineSpan, direction_top, image_univ, mem_univ, vectorSpan, vectorSpan_image_eq_span_vsub_set_right_ne
-/
noncomputable def basisOf (i : ι) : Basis { j : ι // j != i } k V :=
  Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x != i } => b ↑j -ᵥ b i) = vectorSpan k (range b) by
        rw [this]; rw [← direction_affineSpan]; rw [b.tot]; rw [AffineSubspace.direction_top]
      conv_rhs => rw [← image_univ]
      rw [vectorSpan_image_eq_span_vsub_set_right_ne k b (mem_univ i)]
      congr
      ext v
      simp)

@[simp]
/--
theorem `basisOf_apply` / 定理 `basisOf_apply`

English:
theorem basisOf_apply
  given: (i : ι) (j : { j : ι // j != i })
  statement: b.basisOf i j = b ↑j -ᵥ b i
  proof: by
  simp [basisOf]

@[simp]

中文:
定理 basisOf_apply
  条件: (i : ι) (j : { j : ι // j != i })
  结论: b.basisOf i j = b ↑j -ᵥ b i
  证明: by
  simp [basisOf]

@[simp]

Depends on / 依赖: basisOf
-/
theorem basisOf_apply (i : ι) (j : { j : ι // j != i }) : b.basisOf i j = b ↑j -ᵥ b i := by
  simp [basisOf]

@[simp]
/--
theorem `basisOf_reindex` / 定理 `basisOf_reindex`

English:
theorem basisOf_reindex
  given: (i : ι')
  proof: by
  ext j
  simp

中文:
定理 basisOf_reindex
  条件: (i : ι')
  证明: by
  ext j
  simp
-/
theorem basisOf_reindex (i : ι') :
    (b.reindex e).basisOf i =
      (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.not) := by
  ext j
  simp

/--
Definition of `coord` / `coord` 的定义

English:
definition coord
  signature: (i : ι)
  body: 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc]; rw [map_add]; rw [vadd_eq_add]; rw [LinearMap.neg_apply]; rw [sub_add_eq_sub_sub_swap]; rw [add_comm]; rw [sub_eq_add_neg]

@[simp]

中文:
定义 coord
  签名: (i : ι)
  定义体: 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc]; rw [map_add]; rw [vadd_eq_add]; rw [LinearMap.neg_apply]; rw [sub_add_eq_sub_sub_swap]; rw [add_comm]; rw [sub_eq_add_neg]

@[simp]

Depends on / 依赖: b.basisOf, basisOf, sumCoords
-/
noncomputable def coord (i : ι) : P ->ᵃ[k] k where
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc]; rw [map_add]; rw [vadd_eq_add]; rw [LinearMap.neg_apply]; rw [sub_add_eq_sub_sub_swap]; rw [add_comm]; rw [sub_eq_add_neg]

@[simp]
/--
theorem `linear_eq_sumCoords` / 定理 `linear_eq_sumCoords`

English:
theorem linear_eq_sumCoords
  given: (i : ι)
  statement: (b.coord i).linear = -(b.basisOf i).sumCoords
  proof: rfl

@[simp]

中文:
定理 linear_eq_sumCoords
  条件: (i : ι)
  结论: (b.coord i).linear = -(b.basisOf i).sumCoords
  证明: rfl

@[simp]
-/
theorem linear_eq_sumCoords (i : ι) : (b.coord i).linear = -(b.basisOf i).sumCoords :=
  rfl

@[simp]
/--
theorem `coord_reindex` / 定理 `coord_reindex`

English:
theorem coord_reindex
  given: (i : ι')
  statement: (b.reindex e).coord i = b.coord (e.symm i)
  proof: by
  ext
  simp [AffineBasis.coord]

@[simp]

中文:
定理 coord_reindex
  条件: (i : ι')
  结论: (b.reindex e).coord i = b.coord (e.symm i)
  证明: by
  ext
  simp [AffineBasis.coord]

@[simp]

Depends on / 依赖: AffineBasis, AffineBasis.coord
-/
theorem coord_reindex (i : ι') : (b.reindex e).coord i = b.coord (e.symm i) := by
  ext
  simp [AffineBasis.coord]

@[simp]
/--
theorem `coord_apply_eq` / 定理 `coord_apply_eq`

English:
theorem coord_apply_eq
  given: (i : ι)
  statement: b.coord i (b i) = 1
  proof: by
  simp only [coord, Basis.coe_sumCoords, map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]

中文:
定理 coord_apply_eq
  条件: (i : ι)
  结论: b.coord i (b i) = 1
  证明: by
  simp only [coord, Basis.coe_sumCoords, map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]

Depends on / 依赖: AffineMap, AffineMap.coe_mk, Basis.coe_sumCoords, Finsupp, Finsupp.sum_zero_index, coe_mk, coe_sumCoords, map_zero, sub_zero, sum_zero_index, vsub_self
-/
theorem coord_apply_eq (i : ι) : b.coord i (b i) = 1 := by
  simp only [coord, Basis.coe_sumCoords, map_zero, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]
/--
theorem `coord_apply_ne` / 定理 `coord_apply_ne`

English:
theorem coord_apply_ne
  given: (h : i != j)
  statement: b.coord i (b j) = 0
  proof: by
  rw [coord]; rw [AffineMap.coe_mk]; rw [← Subtype.coe_mk (p := (· != i)) j h.symm]; rw [← b.basisOf_apply]; rw [Basis.sumCoords_self_apply]; rw [sub_self]

中文:
定理 coord_apply_ne
  条件: (h : i != j)
  结论: b.coord i (b j) = 0
  证明: by
  rw [coord]; rw [AffineMap.coe_mk]; rw [← Subtype.coe_mk (p := (· != i)) j h.symm]; rw [← b.basisOf_apply]; rw [Basis.sumCoords_self_apply]; rw [sub_self]

Depends on / 依赖: AffineMap, AffineMap.coe_mk, Basis.sumCoords_self_apply, Subtype, Subtype.coe_mk, b.basisOf_apply, basisOf_apply, coe_mk, h.symm, sub_self, sumCoords_self_apply
-/
theorem coord_apply_ne (h : i != j) : b.coord i (b j) = 0 := by
  rw [coord]; rw [AffineMap.coe_mk]; rw [← Subtype.coe_mk (p := (· != i)) j h.symm]; rw [← b.basisOf_apply]; rw [Basis.sumCoords_self_apply]; rw [sub_self]

/--
theorem `coord_apply` / 定理 `coord_apply`

English:
theorem coord_apply
  given: [DecidableEq ι] (i j : ι)
  statement: b.coord i (b j) = if i = j then 1 else 0
  proof: by
  rcases eq_or_ne i j with h | h <;> simp [h]

@[simp]

中文:
定理 coord_apply
  条件: [DecidableEq ι] (i j : ι)
  结论: b.coord i (b j) = if i = j then 1 else 0
  证明: by
  rcases eq_or_ne i j with h | h <;> simp [h]

@[simp]

Depends on / 依赖: eq_or_ne
-/
theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b j) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with h | h <;> simp [h]

@[simp]
/--
theorem `coord_apply_combination_of_mem` / 定理 `coord_apply_combination_of_mem`

English:
theorem coord_apply_combination_of_mem
  given: (hi : i in s) {w : ι -> k} (hw : s.sum w = 1)
  proof: by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]

中文:
定理 coord_apply_combination_of_mem
  条件: (hi : i in s) {w : ι -> k} (hw : s.求和 w = 1)
  证明: by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]

Depends on / 依赖: Finset, Finset.affineCombination_eq_linear_combination, Function, Function.comp_apply, affineCombination_eq_linear_combination, classical, comp_apply, coord_apply, if_true, map_affineCombination, mul_boole, s.map_affineCombination, s.sum_ite_eq, smul_eq_mul, sum_ite_eq
-/
theorem coord_apply_combination_of_mem (hi : i in s) {w : ι -> k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = w i := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]
/--
theorem `coord_apply_combination_of_notMem` / 定理 `coord_apply_combination_of_notMem`

English:
theorem coord_apply_combination_of_notMem
  given: (hi : i ∉ s) {w : ι -> k} (hw : s.sum w = 1)
  proof: by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]

中文:
定理 coord_apply_combination_of_notMem
  条件: (hi : i ∉ s) {w : ι -> k} (hw : s.求和 w = 1)
  证明: by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]

Depends on / 依赖: Finset, Finset.affineCombination_eq_linear_combination, Function, Function.comp_apply, affineCombination_eq_linear_combination, classical, comp_apply, coord_apply, if_false, map_affineCombination, mul_boole, s.map_affineCombination, s.sum_ite_eq, smul_eq_mul, sum_ite_eq
-/
theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι -> k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affineCombination b w hw]

@[simp]
/--
theorem `sum_coord_apply_eq_one` / 定理 `sum_coord_apply_eq_one`

English:
theorem sum_coord_apply_eq_one
  given: [Fintype ι] (q : P)
  statement: ∑ i, b.coord i q = 1
  proof: by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert! hw
  exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

@[simp]

中文:
定理 sum_coord_apply_eq_one
  条件: [有限类型 ι] (q : P)
  结论: ∑ i, b.coord i q = 1
  证明: by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert! hw
  exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

@[simp]

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_top, Finset, Finset.mem_univ, affineSpan, b.coord_apply_combination_of_mem, b.tot, convert, coord_apply_combination_of_mem, eq_affineCombination_of_mem_affineSpan_of_fintype, mem_top, mem_univ
-/
theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : ∑ i, b.coord i q = 1 := by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert! hw
  exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

@[simp]
/--
theorem `affineCombination_coord_eq_self` / 定理 `affineCombination_coord_eq_self`

English:
theorem affineCombination_coord_eq_self
  given: [Fintype ι] (q : P)
  proof: by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

中文:
定理 affineCombination_coord_eq_self
  条件: [有限类型 ι] (q : P)
  证明: by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

Depends on / 依赖: AffineSubspace, AffineSubspace.mem_top, Finset, Finset.mem_univ, affineSpan, b.coord_apply_combination_of_mem, b.tot, coord_apply_combination_of_mem, eq_affineCombination_of_mem_affineSpan_of_fintype, mem_top, mem_univ
-/
theorem affineCombination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination k b fun i => b.coord i q) = q := by
  have hq : q in affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw

/-- A variant of `AffineBasis.affineCombination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp]
/--
theorem `linear_combination_coord_eq_self` / 定理 `linear_combination_coord_eq_self`

English:
theorem linear_combination_coord_eq_self
  given: [Fintype ι] (b : AffineBasis ι k V) (v : V)
  proof: by
  have hb := b.affineCombination_coord_eq_self v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb

中文:
定理 linear_combination_coord_eq_self
  条件: [有限类型 ι] (b : 仿射基 ι k V) (v : V)
  证明: by
  have hb := b.affineCombination_coord_eq_self v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb

Depends on / 依赖: Finset, Finset.univ.affineCombination_eq_linear_combination, affineCombination_coord_eq_self, affineCombination_eq_linear_combination, b.affineCombination_coord_eq_self, b.sum_coord_apply_eq_one, sum_coord_apply_eq_one
-/
theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    ∑ i, b.coord i v • b i = v := by
  have hb := b.affineCombination_coord_eq_self v
  rwa [Finset.univ.affineCombination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb

/--
theorem `ext_elem` / 定理 `ext_elem`

English:
theorem ext_elem
  given: [Finite ι] {q₁ q₂ : P} (h : forall i, b.coord i q₁ = b.coord i q₂)
  statement: q₁ = q₂
  proof: by
  cases nonempty_fintype ι
  rw [← b.affineCombination_coord_eq_self q₁]; rw [← b.affineCombination_coord_eq_self q₂]
  simp only [h]

@[simp]

中文:
定理 ext_elem
  条件: [有限 ι] {q₁ q₂ : P} (h : 对任意 i, b.coord i q₁ = b.coord i q₂)
  结论: q₁ = q₂
  证明: by
  cases nonempty_fintype ι
  rw [← b.affineCombination_coord_eq_self q₁]; rw [← b.affineCombination_coord_eq_self q₂]
  simp only [h]

@[simp]

Depends on / 依赖: affineCombination_coord_eq_self, b.affineCombination_coord_eq_self, nonempty_fintype
-/
theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : forall i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ := by
  cases nonempty_fintype ι
  rw [← b.affineCombination_coord_eq_self q₁]; rw [← b.affineCombination_coord_eq_self q₂]
  simp only [h]

@[simp]
/--
theorem `coe_coord_of_subsingleton_eq_one` / 定理 `coe_coord_of_subsingleton_eq_one`

English:
theorem coe_coord_of_subsingleton_eq_one
  given: [Subsingleton ι] (i : ι)
  statement: (b.coord i : P -> k) = 1
  proof: by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply Subsingleton.image
    apply subsingleton_of_subsingleton
  have := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i in s := by simp [s]
  have hw : s.sum (Func

中文:
定理 coe_coord_of_subsingleton_eq_one
  条件: [子单例 ι] (i : ι)
  结论: (b.coord i : P -> k) = 1
  证明: by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply Subsingleton.image
    apply subsingleton_of_subsingleton
  have := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i in s := by simp [s]
  have hw : s.sum (Func

Depends on / 依赖: AffineSubspace, AffineSubspace.subsingleton_of_subsingleton_span_eq_top, Finset, Function, Function.const, Pi.one_apply, Subsingleton, Subsingleton.image, affineCombination, b.coord_apply_combination_of_mem, b.tot, coord_apply_combination_of_mem, eq_iff_true_of_subsingleton, image_univ, one_apply, s.affineCombination, s.sum, subsingleton_of_subsingleton, subsingleton_of_subsingleton_span_eq_top
-/
theorem coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.coord i : P -> k) = 1 := by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply Subsingleton.image
    apply subsingleton_of_subsingleton
  have := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i in s := by simp [s]
  have hw : s.sum (Function.const ι (1 : k)) = 1 := by simp [s]
  have hq : q = s.affineCombination k b (Function.const ι (1 : k)) := by
    simp [eq_iff_true_of_subsingleton]
  rw [Pi.one_apply]; rw [hq]; rw [b.coord_apply_combination_of_mem hi hw]; rw [Function.const_apply]

/--
theorem `surjective_coord` / 定理 `surjective_coord`

English:
theorem surjective_coord
  given: [Nontrivial ι] (i : ι)
  statement: Function.Surjective b.coord i
  proof: by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i in s := by simp [s]
    let w : ι -> k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true

中文:
定理 surjective_coord
  条件: [非平凡 ι] (i : ι)
  结论: 函数.满射 b.coord i
  证明: by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i in s := by simp [s]
    let w : ι -> k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true

Depends on / 依赖: Finset, Finset.filter_false_of_mem, Finset.filter_insert, Finset.filter_true_of_mem, Finset.sum_ite, affineCombination, b.coord_apply_combination_of_mem, classical, coord_apply_combination_of_mem, exists_ne, filter_false_of_mem, filter_insert, filter_true_of_mem, s.affineCombination, s.sum, sum_ite
-/
theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective b.coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i in s := by simp [s]
    let w : ι -> k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [s, w, Finset.sum_ite, Finset.filter_insert, hij,
      Finset.filter_true_of_mem, Finset.filter_false_of_mem]
    use s.affineCombination k b w
    simp [w, b.coord_apply_combination_of_mem hi hw]

/--
Definition of `coords` / `coords` 的定义

English:
definition coords
  signature: : P ->ᵃ[k] ι -> k where
  body: b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp

@[simp]

中文:
定义 coords
  签名: : P ->ᵃ[k] ι -> k where
  定义体: b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp

@[simp]

Depends on / 依赖: b.coord
-/
noncomputable def coords : P ->ᵃ[k] ι -> k where
  toFun q i := b.coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by ext; simp only [map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by ext; simp }
  map_vadd' p v := by ext; simp

@[simp]
/--
theorem `coords_apply` / 定理 `coords_apply`

English:
theorem coords_apply
  given: (q : P) (i : ι)
  statement: b.coords q i = b.coord i q
  proof: rfl

中文:
定理 coords_apply
  条件: (q : P) (i : ι)
  结论: b.coords q i = b.coord i q
  证明: rfl
-/
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.coord i q :=
  rfl

/--
Instance `instVAdd` / 实例 `instVAdd`

English:
instance instVAdd
  signature: : VAdd V (AffineBasis ι k P) where
  body: { toFun := x +ᵥ ⇑b,
      ind' := b.ind'.vadd,
      tot' := by rw [Pi.vadd_def, ← vadd_set_range, ← AffineSubspace.pointwise_vadd_span, b.tot,
        AffineSubspace.pointwise_vadd_top] }

中文:
实例 instVAdd
  签名: : 向量加法 V (仿射基 ι k P) where
  定义体: { toFun := x +ᵥ ⇑b,
      ind' := b.ind'.vadd,
      tot' := by rw [Pi.vadd_def, ← vadd_set_range, ← AffineSubspace.pointwise_vadd_span, b.tot,
        AffineSubspace.pointwise_vadd_top] }

Depends on / 依赖: AffineSubspace, AffineSubspace.pointwise_vadd_span, AffineSubspace.pointwise_vadd_top, Pi.vadd_def, b.ind, b.tot, pointwise_vadd_span, pointwise_vadd_top, vadd_def, vadd_set_range
-/
instance instVAdd : VAdd V (AffineBasis ι k P) where
  vadd x b :=
    { toFun := x +ᵥ ⇑b,
      ind' := b.ind'.vadd,
      tot' := by rw [Pi.vadd_def, ← vadd_set_range, ← AffineSubspace.pointwise_vadd_span, b.tot,
        AffineSubspace.pointwise_vadd_top] }

/--
lemma `coe_vadd` / 引理 `coe_vadd`

English:
lemma coe_vadd
  given: (v : V) (b : AffineBasis ι k P)
  statement: ⇑(v +ᵥ b) = v +ᵥ ⇑b
  proof: rfl

中文:
引理 coe_vadd
  条件: (v : V) (b : 仿射基 ι k P)
  结论: ⇑(v +ᵥ b) = v +ᵥ ⇑b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_vadd (v : V) (b : AffineBasis ι k P) : ⇑(v +ᵥ b) = v +ᵥ ⇑b := rfl

/--
lemma `basisOf_vadd` / 引理 `basisOf_vadd`

English:
lemma basisOf_vadd
  given: (v : V) (b : AffineBasis ι k P)
  statement: (v +ᵥ b).basisOf = b.basisOf
  proof: by
  ext
  simp

中文:
引理 basisOf_vadd
  条件: (v : V) (b : 仿射基 ι k P)
  结论: (v +ᵥ b).basisOf = b.basisOf
  证明: by
  ext
  simp
-/
@[simp] lemma basisOf_vadd (v : V) (b : AffineBasis ι k P) : (v +ᵥ b).basisOf = b.basisOf := by
  ext
  simp

/--
Instance `instAddAction` / 实例 `instAddAction`

English:
instance instAddAction
  signature: : AddAction V (AffineBasis ι k P)
  body: DFunLike.coe_injective.addAction _ coe_vadd

中文:
实例 instAddAction
  签名: : 加法作用 V (仿射基 ι k P)
  定义体: DFunLike.coe_injective.addAction _ coe_vadd

Depends on / 依赖: DFunLike, DFunLike.coe_injective.addAction, addAction, coe_injective, coe_vadd
-/
instance instAddAction : AddAction V (AffineBasis ι k P) :=
  DFunLike.coe_injective.addAction _ coe_vadd

/--
lemma `coord_vadd` / 引理 `coord_vadd`

English:
lemma coord_vadd
  given: (v : V) (b : AffineBasis ι k P)
  proof: by
  ext p
  simp only [coord, ne_eq, basisOf_vadd, coe_vadd, Pi.vadd_apply, Basis.coe_sumCoords,
    AffineMap.coe_mk, AffineEquiv.constVAdd_symm, AffineMap.coe_comp, AffineEquiv.coe_toAffineMap,
    Function.comp_apply, AffineEquiv.constVAdd_apply, sub_right_inj]
  congr! 1
  rw [vadd_vsub_assoc];

中文:
引理 coord_vadd
  条件: (v : V) (b : 仿射基 ι k P)
  证明: by
  ext p
  simp only [coord, ne_eq, basisOf_vadd, coe_vadd, Pi.vadd_apply, Basis.coe_sumCoords,
    AffineMap.coe_mk, AffineEquiv.constVAdd_symm, AffineMap.coe_comp, AffineEquiv.coe_toAffineMap,
    Function.comp_apply, AffineEquiv.constVAdd_apply, sub_right_inj]
  congr! 1
  rw [vadd_vsub_assoc];
-/
@[simp] lemma coord_vadd (v : V) (b : AffineBasis ι k P) :
    (v +ᵥ b).coord i = (b.coord i).comp (AffineEquiv.constVAdd k P v).symm := by
  ext p
  simp only [coord, ne_eq, basisOf_vadd, coe_vadd, Pi.vadd_apply, Basis.coe_sumCoords,
    AffineMap.coe_mk, AffineEquiv.constVAdd_symm, AffineMap.coe_comp, AffineEquiv.coe_toAffineMap,
    Function.comp_apply, AffineEquiv.constVAdd_apply, sub_right_inj]
  congr! 1
  rw [vadd_vsub_assoc]; rw [neg_add_eq_sub]; rw [vsub_vadd_eq_vsub_sub]

section SMul
variable [Group G] [Group G']
variable [DistribMulAction G V] [DistribMulAction G' V]
variable [SMulCommClass G k V] [SMulCommClass G' k V]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul G (AffineBasis ι k V) where
  body: { toFun := a • ⇑b,
      ind' := b.ind'.smul,
      tot' := by
        rw [Pi.smul_def]; rw [← smul_set_range]; rw [← AffineSubspace.smul_span]; rw [b.tot]; rw [AffineSubspace.smul_top (Group.isUnit a)] }

中文:
实例 instSMul
  签名: : 标量乘法 G (仿射基 ι k V) where
  定义体: { toFun := a • ⇑b,
      ind' := b.ind'.smul,
      tot' := by
        rw [Pi.smul_def]; rw [← smul_set_range]; rw [← AffineSubspace.smul_span]; rw [b.tot]; rw [AffineSubspace.smul_top (Group.isUnit a)] }

Depends on / 依赖: AffineSubspace, AffineSubspace.smul_span, AffineSubspace.smul_top, Group.isUnit, Pi.smul_def, b.ind, b.tot, isUnit, smul_def, smul_set_range, smul_span, smul_top
-/
instance instSMul : SMul G (AffineBasis ι k V) where
  smul a b :=
    { toFun := a • ⇑b,
      ind' := b.ind'.smul,
      tot' := by
        rw [Pi.smul_def]; rw [← smul_set_range]; rw [← AffineSubspace.smul_span]; rw [b.tot]; rw [AffineSubspace.smul_top (Group.isUnit a)] }

/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (a : G) (b : AffineBasis ι k V)
  statement: ⇑(a • b) = a • ⇑b
  proof: rfl

中文:
引理 coe_smul
  条件: (a : G) (b : 仿射基 ι k V)
  结论: ⇑(a • b) = a • ⇑b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_smul (a : G) (b : AffineBasis ι k V) : ⇑(a • b) = a • ⇑b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: G G' V] : SMulCommClass G G' (AffineBasis ι k V) where
  body: DFunLike.ext _ _ fun _ => smul_comm _ _ _

中文:
实例 [标量交换类
  签名: G G' V] : 标量交换类 G G' (仿射基 ι k V) where
  定义体: DFunLike.ext _ _ fun _ => smul_comm _ _ _

Depends on / 依赖: DFunLike, DFunLike.ext, smul_comm
-/
instance [SMulCommClass G G' V] : SMulCommClass G G' (AffineBasis ι k V) where
  smul_comm _g _g' _b := DFunLike.ext _ _ fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: G G'] [IsScalarTower G G' V] : IsScalarTower G G' (AffineBasis ι k V) where
  body: DFunLike.ext _ _ fun _ => smul_assoc _ _ _

中文:
实例 [标量乘法
  签名: G G'] [标量塔 G G' V] : 标量塔 G G' (仿射基 ι k V) where
  定义体: DFunLike.ext _ _ fun _ => smul_assoc _ _ _

Depends on / 依赖: DFunLike, DFunLike.ext, smul_assoc
-/
instance [SMul G G'] [IsScalarTower G G' V] : IsScalarTower G G' (AffineBasis ι k V) where
  smul_assoc _g _g' _b := DFunLike.ext _ _ fun _ => smul_assoc _ _ _

/--
lemma `basisOf_smul` / 引理 `basisOf_smul`

English:
lemma basisOf_smul
  given: (a : G) (b : AffineBasis ι k V) (i : ι)
  proof: by ext j; simp [smul_sub]

中文:
引理 basisOf_smul
  条件: (a : G) (b : 仿射基 ι k V) (i : ι)
  证明: by ext j; simp [smul_sub]
-/
@[simp] lemma basisOf_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).basisOf i = a • b.basisOf i := by ext j; simp [smul_sub]

/--
lemma `reindex_smul` / 引理 `reindex_smul`

English:
lemma reindex_smul
  given: (a : G) (b : AffineBasis ι k V) (e : ι ≃ ι')
  proof: rfl

中文:
引理 reindex_smul
  条件: (a : G) (b : 仿射基 ι k V) (e : ι ≃ ι')
  证明: rfl
-/
@[simp] lemma reindex_smul (a : G) (b : AffineBasis ι k V) (e : ι ≃ ι') :
    (a • b).reindex e = a • b.reindex e :=
  rfl

/--
lemma `coord_smul` / 引理 `coord_smul`

English:
lemma coord_smul
  given: (a : G) (b : AffineBasis ι k V) (i : ι)
  proof: by
  ext v; simp [map_sub, coord]

中文:
引理 coord_smul
  条件: (a : G) (b : 仿射基 ι k V) (i : ι)
  证明: by
  ext v; simp [map_sub, coord]
-/
@[simp] lemma coord_smul (a : G) (b : AffineBasis ι k V) (i : ι) :
    (a • b).coord i = (b.coord i).comp (DistribMulAction.toLinearEquiv _ _ a).symm.toAffineMap := by
  ext v; simp [map_sub, coord]

/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: : MulAction G (AffineBasis ι k V)
  body: DFunLike.coe_injective.mulAction _ coe_smul

中文:
实例 instMulAction
  签名: : 乘法作用 G (仿射基 ι k V)
  定义体: DFunLike.coe_injective.mulAction _ coe_smul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, coe_smul, mulAction
-/
instance instMulAction : MulAction G (AffineBasis ι k V) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end SMul
end Ring

section DivisionRing

variable [DivisionRing k] [Module k V]

@[simp]
/--
theorem `coord_apply_centroid` / 定理 `coord_apply_centroid`

English:
theorem coord_apply_centroid
  statement: [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
  proof: by
  rw [Finset.centroid]; rw [b.coord_apply_combination_of_mem hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i]; rw [hi⟩)]; rw [Finset.centroidWeights]; rw [Function.const_apply]

中文:
定理 coord_apply_centroid
  结论: [特征零 k] (b : 仿射基 ι k P) {s : 有限集 ι} {i : ι}
  证明: by
  rw [Finset.centroid]; rw [b.coord_apply_combination_of_mem hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i]; rw [hi⟩)]; rw [Finset.centroidWeights]; rw [Function.const_apply]

Depends on / 依赖: Finset, Finset.centroid, Finset.centroidWeights, Function, Function.const_apply, b.coord_apply_combination_of_mem, centroid, centroidWeights, const_apply, coord_apply_combination_of_mem, s.sum_centroidWeights_eq_one_of_nonempty, sum_centroidWeights_eq_one_of_nonempty
-/
theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i in s) : b.coord i (s.centroid k b) = (s.card : k)⁻¹ := by
  rw [Finset.centroid]; rw [b.coord_apply_combination_of_mem hi (s.sum_centroidWeights_eq_one_of_nonempty _ ⟨i]; rw [hi⟩)]; rw [Finset.centroidWeights]; rw [Function.const_apply]

/--
theorem `exists_affine_subbasis` / 定理 `exists_affine_subbasis`

English:
theorem exists_affine_subbasis
  given: {t : Set P} (ht : affineSpan k t = ⊤)
  proof: by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe]; rw [h_tot]; rw [ht]

中文:
定理 存在_affine_subbasis
  条件: {t : 集合 P} (ht : affineSpan k t = ⊤)
  证明: by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe]; rw [h_tot]; rw [ht]

Depends on / 依赖: Subtype, Subtype.range_coe, exists_affineIndependent, h_ind, h_tot, range_coe
-/
theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    exists s subseteq t, exists b : AffineBasis s k P, ⇑b = ((↑) : s -> P) := by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine ⟨s, hst, ⟨(↑), h_ind, ?_⟩, rfl⟩
  rw [Subtype.range_coe]; rw [h_tot]; rw [ht]

variable (k V P)

/--
theorem `exists_affineBasis` / 定理 `exists_affineBasis`

English:
theorem exists_affineBasis
  statement: exists (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s -> P)
  proof: let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

中文:
定理 存在_affineBasis
  结论: 存在 (s : 集合 P) (b : 仿射基 (↥s) k P), ⇑b = ((↑) : s -> P)
  证明: let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

Depends on / 依赖: AffineSubspace, AffineSubspace.span_univ, exists_affine_subbasis, span_univ
-/
theorem exists_affineBasis : exists (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s -> P) :=
  let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩

end DivisionRing

end AffineBasis
