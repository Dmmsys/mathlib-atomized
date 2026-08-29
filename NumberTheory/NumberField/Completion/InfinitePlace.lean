/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# The completion of a number field at an infinite place

This file contains the completion of a number field at an infinite place. This is ultimately
achieved by applying the `UniformSpace.Completion` functor, however each infinite place induces
its own `UniformSpace` instance on the number field, so the inference system cannot automatically
infer these. A common approach to handle the ambiguity that arises from having multiple sources
of instances is through the use of type synonyms. In this case, we use the type synonym `WithAbs`
of a semiring. In particular this type synonym depends on an absolute value, which provides a
systematic way of assigning and inferring instances of the semiring that also depend on an absolute
value. The completion of a field at multiple absolute values is defined in
`Mathlib/Analysis/Normed/Field/WithAbs.lean` as `AbsoluteValue.Completion`. The completion of a
number field at an infinite place is then derived in this file, as `InfinitePlace` is a subtype of
`AbsoluteValue`.

## Main definitions
- `NumberField.InfinitePlace.Completion` : the completion of a number field `K` at an infinite
  place, obtained by completing `K` with respect to the absolute value associated to the infinite
  place.
- `NumberField.InfinitePlace.Completion.extensionEmbedding` : the embedding `v.embedding : K →+* ℂ`
  extended to `v.Completion →+* ℂ`.
- `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal` : if the infinite place `v`
  is real, then this extends the embedding `v.embedding_of_isReal : K →+* ℝ` to
  `v.Completion →+* ℝ`.
- `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` : the ring isomorphism
  `v.Completion ≃+* ℝ` when `v` is a real infinite place; the forward direction of this is
  `extensionEmbeddingOfIsReal`.
- `NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex` : the ring isomorphism
  `v.Completion ≃+* ℂ` when `v` is a complex infinite place; the forward direction of this is
  `extensionEmbedding`.

## Main results
- `NumberField.Completion.locallyCompactSpace` : the completion of a number field at
  an infinite place is locally compact.
- `NumberField.Completion.isometry_extensionEmbedding` : the embedding `v.Completion →+* ℂ` is
  an isometry. See also `isometry_extensionEmbeddingOfIsReal` for the corresponding result on
  `v.Completion →+* ℝ` when `v` is real.
- `NumberField.Completion.bijective_extensionEmbedding_of_isComplex` : the embedding
  `v.Completion →+* ℂ` is bijective when `v` is complex. See also
  `bijective_extensionEmbeddingOfIsReal` for the corresponding result for `v.Completion →+* ℝ`
  when `v` is real.

## Tags
number field, embeddings, infinite places, completion, absolute value
-/

@[expose] public section
noncomputable section

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion UniformSpace.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] (v : InfinitePlace K)

/--
theorem `isometry_embedding` / 定理 `isometry_embedding`

English:
theorem isometry_embedding
  statement: Isometry (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
  proof: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)

中文:
定理 isometry_embedding
  结论: 等距 (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
  证明: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, WithAbs, WithAbs.equiv, isometry_of_norm, norm_embedding_eq, v.norm_embedding_eq
-/
theorem isometry_embedding : Isometry (v.embedding.comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)

/--
theorem `isometry_embedding_of_isReal` / 定理 `isometry_embedding_of_isReal`

English:
theorem isometry_embedding_of_isReal
  given: (hv : v.IsReal)
  proof: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

中文:
定理 isometry_embedding_of_is实数
  条件: (hv : v.Is实数)
  证明: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, WithAbs, WithAbs.equiv, isometry_of_norm, norm_embedding_of_isReal, v.norm_embedding_of_isReal
-/
theorem isometry_embedding_of_isReal (hv : v.IsReal) :
    Isometry ((v.embedding_of_isReal hv).comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompletableTopField (WithAbs v.1)
  body: v.isometry_embedding.isUniformInducing.completableTopField

中文:
实例 :
  签名: 余mpletableTopField (WithAbs v.1)
  定义体: v.isometry_embedding.isUniformInducing.completableTopField

Depends on / 依赖: completableTopField, isUniformInducing, isometry_embedding, v.isometry_embedding.isUniformInducing.completableTopField
-/
instance : CompletableTopField (WithAbs v.1) :=
  v.isometry_embedding.isUniformInducing.completableTopField

/--
Definition of `Completion` / `Completion` 的定义

English:
structure Completion
  parameters: where
  axioms and operations (2):
    - ofCompletion : :
    - toCompletion : v.1.Completion

中文:
结构 完备化
  参数: where
  公理与运算 (2 个):
    - ofCompletion : :
    - toCompletion : v.1.完备化
-/
structure Completion where
  /-- Wrap an element of `v.1.Completion` into `v.Completion`. -/
  ofCompletion ::
  /-- The underlying element of `v.1.Completion`. -/
  toCompletion : v.1.Completion

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
@[simps]
/--
Definition of `equivCompletion` / `equivCompletion` 的定义

English:
definition equivCompletion
  signature: : v.Completion ≃ v.1.Completion where
  body: toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 equivCompletion
  签名: : v.完备化 ≃ v.1.完备化 where
  定义体: toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: toCompletion
-/
def equivCompletion : v.Completion ≃ v.1.Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedField v.Completion
  body: fast_instance% (equivCompletion v).normedField

中文:
实例 :
  签名: 赋范域 v.完备化
  定义体: fast_instance% (equivCompletion v).normedField

Depends on / 依赖: equivCompletion, fast_instance, normedField
-/
instance : NormedField v.Completion := fast_instance% (equivCompletion v).normedField

/-- `Completion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : v.Completion ≃+* v.1.Completion where
  body: equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 equiv
  签名: : v.完备化 ≃+* v.1.完备化 where
  定义体: equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: Countable, Countable.of_equiv, countable_of_linear_succ_pred_arch, equivCompletion, infer_instance, isEmpty_or_nonempty, of_equiv, orderIsoRangeToZOfLinearSuccPredArch, orderIsoRangeToZOfLinearSuccPredArch.symm.toEquiv, toEquiv
-/
def equiv : v.Completion ≃+* v.1.Completion where
  toEquiv := equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/--
lemma `toCompletion_ofCompletion` / 引理 `toCompletion_ofCompletion`

English:
lemma toCompletion_ofCompletion
  given: (x : v.1.Completion)
  proof: rfl

中文:
引理 toCompletion_ofCompletion
  条件: (x : v.1.完备化)
  证明: rfl
-/
@[simp] lemma toCompletion_ofCompletion (x : v.1.Completion) :
    toCompletion (ofCompletion x : v.Completion) = x := rfl
/--
lemma `ofCompletion_toCompletion` / 引理 `ofCompletion_toCompletion`

English:
lemma ofCompletion_toCompletion
  given: (x : v.Completion)
  proof: rfl

中文:
引理 ofCompletion_toCompletion
  条件: (x : v.完备化)
  证明: rfl
-/
@[simp] lemma ofCompletion_toCompletion (x : v.Completion) :
    ofCompletion x.toCompletion = x := rfl

/--
lemma `toCompletion_zero` / 引理 `toCompletion_zero`

English:
lemma toCompletion_zero
  statement: (0 : v.Completion).toCompletion = 0
  proof: rfl

中文:
引理 toCompletion_zero
  结论: (0 : v.完备化).toCompletion = 0
  证明: rfl
-/
@[simp] lemma toCompletion_zero : (0 : v.Completion).toCompletion = 0 := rfl
/--
lemma `toCompletion_one` / 引理 `toCompletion_one`

English:
lemma toCompletion_one
  statement: (1 : v.Completion).toCompletion = 1
  proof: rfl

中文:
引理 toCompletion_one
  结论: (1 : v.完备化).toCompletion = 1
  证明: rfl

Depends on / 依赖: Countable, Countable.of_linearOrder_locallyFiniteOrder, LocallyFiniteOrder, of_linearOrder_locallyFiniteOrder
-/
@[simp] lemma toCompletion_one : (1 : v.Completion).toCompletion = 1 := rfl
/--
lemma `toCompletion_add` / 引理 `toCompletion_add`

English:
lemma toCompletion_add
  given: (x y : v.Completion)
  proof: rfl

中文:
引理 toCompletion_add
  条件: (x y : v.完备化)
  证明: rfl
-/
@[simp] lemma toCompletion_add (x y : v.Completion) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
/--
lemma `toCompletion_mul` / 引理 `toCompletion_mul`

English:
lemma toCompletion_mul
  given: (x y : v.Completion)
  proof: rfl

中文:
引理 toCompletion_mul
  条件: (x y : v.完备化)
  证明: rfl
-/
@[simp] lemma toCompletion_mul (x y : v.Completion) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {v : InfinitePlace K} {x y : v.Completion}
  proof: by
  cases x; cases y; exact congrArg ofCompletion h

中文:
定理 ext
  结论: {v : InfinitePlace K} {x y : v.完备化}
  证明: by
  cases x; cases y; exact congrArg ofCompletion h
-/
@[ext] theorem ext {v : InfinitePlace K} {x y : v.Completion}
    (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h

/--
theorem `toCompletion_surjective` / 定理 `toCompletion_surjective`

English:
theorem toCompletion_surjective
  statement: Function.Surjective (toCompletion (v := v))
  proof: (equivCompletion v).surjective

中文:
定理 toCompletion_surjective
  结论: 函数.满射 (toCompletion (v := v))
  证明: (equivCompletion v).surjective
-/
theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equivCompletion v).surjective

/--
theorem `ofCompletion_surjective` / 定理 `ofCompletion_surjective`

English:
theorem ofCompletion_surjective
  statement: Function.Surjective (ofCompletion (v := v))
  proof: (equivCompletion v).symm.surjective

中文:
定理 ofCompletion_surjective
  结论: 函数.满射 (ofCompletion (v := v))
  证明: (equivCompletion v).symm.surjective
-/
theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equivCompletion v).symm.surjective

/--
lemma `norm_toCompletion` / 引理 `norm_toCompletion`

English:
lemma norm_toCompletion
  given: (x : v.Completion)
  statement: ‖x.toCompletion‖ = ‖x‖
  proof: rfl

中文:
引理 norm_toCompletion
  条件: (x : v.完备化)
  结论: ‖x.toCompletion‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_toCompletion (x : v.Completion) : ‖x.toCompletion‖ = ‖x‖ := rfl

/--
lemma `norm_ofCompletion` / 引理 `norm_ofCompletion`

English:
lemma norm_ofCompletion
  given: (x : v.1.Completion)
  proof: rfl

中文:
引理 norm_ofCompletion
  条件: (x : v.1.完备化)
  证明: rfl
-/
@[simp] lemma norm_ofCompletion (x : v.1.Completion) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl

/--
theorem `isometry_toCompletion` / 定理 `isometry_toCompletion`

English:
theorem isometry_toCompletion
  statement: Isometry (toCompletion (v := v))
  proof: Isometry.of_dist_eq fun _ _ => rfl

中文:
定理 isometry_toCompletion
  结论: 等距 (toCompletion (v := v))
  证明: Isometry.of_dist_eq fun _ _ => rfl
-/
theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ => rfl

/--
Definition of `isometryEquivCompletion` / `isometryEquivCompletion` 的定义

English:
definition isometryEquivCompletion
  signature: : v.Completion ≃ᵢ v.1.Completion where
  body: equivCompletion v
  isometry_toFun := isometry_toCompletion v

中文:
定义 isometryEquivCompletion
  签名: : v.完备化 ≃ᵢ v.1.完备化 where
  定义体: equivCompletion v
  isometry_toFun := isometry_toCompletion v

Depends on / 依赖: equivCompletion
-/
def isometryEquivCompletion : v.Completion ≃ᵢ v.1.Completion where
  toEquiv := equivCompletion v
  isometry_toFun := isometry_toCompletion v

/--
theorem `continuous_toCompletion` / 定理 `continuous_toCompletion`

English:
theorem continuous_toCompletion
  statement: Continuous (toCompletion (v := v))
  proof: (isometry_toCompletion v).continuous

中文:
定理 continuous_toCompletion
  结论: 连续 (toCompletion (v := v))
  证明: (isometry_toCompletion v).continuous
-/
theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous

/--
theorem `continuous_ofCompletion` / 定理 `continuous_ofCompletion`

English:
theorem continuous_ofCompletion
  statement: Continuous (ofCompletion (v := v))
  proof: (isometryEquivCompletion v).symm.continuous

中文:
定理 continuous_ofCompletion
  结论: 连续 (ofCompletion (v := v))
  证明: (isometryEquivCompletion v).symm.continuous
-/
theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometryEquivCompletion v).symm.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace v.Completion
  body: ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

中文:
实例 :
  签名: 完备空间 v.完备化
  定义体: ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

Depends on / 依赖: completeSpace_congr, isUniformInducing, isUniformInducing.completeSpace_congr, isometry_toCompletion, toCompletion_surjective
-/
instance : CompleteSpace v.Completion :=
  ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited v.Completion
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 v.完备化
  定义体: ⟨0⟩
-/
instance : Inhabited v.Completion := ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (WithAbs v.1) v.Completion
  body: ofCompletion (x : v.1.Completion)

中文:
实例 :
  签名: Coe (WithAbs v.1) v.完备化
  定义体: ofCompletion (x : v.1.Completion)

Depends on / 依赖: Completion, ofCompletion
-/
instance : Coe (WithAbs v.1) v.Completion where
  coe x := ofCompletion (x : v.1.Completion)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe K v.Completion
  body: ofCompletion (k : v.1.Completion)

中文:
实例 :
  签名: Coe K v.完备化
  定义体: ofCompletion (k : v.1.Completion)

Depends on / 依赖: Completion, ofCompletion
-/
instance : Coe K v.Completion where
  coe k := ofCompletion (k : v.1.Completion)

/--
lemma `coe_toCompletion` / 引理 `coe_toCompletion`

English:
lemma coe_toCompletion
  given: (x : WithAbs v.1)
  proof: rfl

中文:
引理 coe_toCompletion
  条件: (x : WithAbs v.1)
  证明: rfl
-/
@[simp] lemma coe_toCompletion (x : WithAbs v.1) :
    (x : v.Completion).toCompletion = (x : v.1.Completion) := rfl

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : K) : v.Completion) = 0
  proof: by ext; simp

中文:
引理 coe_zero
  结论: ((0 : K) : v.完备化) = 0
  证明: by ext; simp
-/
@[norm_cast] lemma coe_zero : ((0 : K) : v.Completion) = 0 := by ext; simp
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : K) : v.Completion) = 1
  proof: by ext; simp

中文:
引理 coe_one
  结论: ((1 : K) : v.完备化) = 1
  证明: by ext; simp
-/
@[norm_cast] lemma coe_one : ((1 : K) : v.Completion) = 1 := by ext; simp
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (x y : K)
  statement: ((x + y : K) : v.Completion) = ↑x + ↑y
  proof: by
  ext; simp [UniformSpace.Completion.coe_add]

中文:
引理 coe_add
  条件: (x y : K)
  结论: ((x + y : K) : v.完备化) = ↑x + ↑y
  证明: by
  ext; simp [UniformSpace.Completion.coe_add]
-/
@[norm_cast] lemma coe_add (x y : K) : ((x + y : K) : v.Completion) = ↑x + ↑y := by
  ext; simp [UniformSpace.Completion.coe_add]
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (x y : K)
  statement: ((x * y : K) : v.Completion) = ↑x * ↑y
  proof: by
  ext; simp [UniformSpace.Completion.coe_mul]

中文:
引理 coe_mul
  条件: (x y : K)
  结论: ((x * y : K) : v.完备化) = ↑x * ↑y
  证明: by
  ext; simp [UniformSpace.Completion.coe_mul]
-/
@[norm_cast] lemma coe_mul (x y : K) : ((x * y : K) : v.Completion) = ↑x * ↑y := by
  ext; simp [UniformSpace.Completion.coe_mul]

/--
theorem `continuous_coe` / 定理 `continuous_coe`

English:
theorem continuous_coe
  statement: Continuous ((↑) : WithAbs v.1 -> v.Completion)
  proof: (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

中文:
定理 continuous_coe
  结论: 连续 ((↑) : WithAbs v.1 -> v.完备化)
  证明: (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.continuous_coe, continuous_coe, continuous_ofCompletion
-/
theorem continuous_coe : Continuous ((↑) : WithAbs v.1 -> v.Completion) :=
  (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

/--
theorem `denseRange_coe` / 定理 `denseRange_coe`

English:
theorem denseRange_coe
  statement: DenseRange ((↑) : WithAbs v.1 -> v.Completion)
  proof: (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

中文:
定理 denseRange_coe
  结论: DenseRange ((↑) : WithAbs v.1 -> v.完备化)
  证明: (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.denseRange_coe, continuous_ofCompletion, denseRange, denseRange.comp, denseRange_coe, ofCompletion_surjective
-/
theorem denseRange_coe : DenseRange ((↑) : WithAbs v.1 -> v.Completion) :=
  (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

/-- Induction on the completion of a number field at an infinite place: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {p : v.Completion -> Prop} (x : v.Completion) (hp : IsClosed {x | p x})
  proof: UniformSpace.Completion.induction_on (p := fun y => p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

中文:
定理 induction_on
  结论: {p : v.完备化 -> 命题} (x : v.完备化) (hp : 是闭集 {x | p x})
  证明: UniformSpace.Completion.induction_on (p := fun y => p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.induction_on, continuous_ofCompletion, hp.preimage, induction_on, ofCompletion, preimage, toCompletion, x.toCompletion
-/
theorem induction_on {p : v.Completion -> Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : forall a : WithAbs v.1, p a) : p x :=
  UniformSpace.Completion.induction_on (p := fun y => p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R (WithAbs v.1)]
  [UniformContinuousConstSMul R (WithAbs v.1)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R v.Completion
  body: fast_instance% (equivCompletion v).algebra R

中文:
实例 :
  签名: 代数 R v.完备化
  定义体: fast_instance% (equivCompletion v).algebra R

Depends on / 依赖: algebra, equivCompletion, fast_instance
-/
instance : Algebra R v.Completion := fast_instance% (equivCompletion v).algebra R

/--
theorem `algebraMap_toCompletion` / 定理 `algebraMap_toCompletion`

English:
theorem algebraMap_toCompletion
  given: (r : R)
  proof: rfl

中文:
定理 algebraMap_toCompletion
  条件: (r : R)
  证明: rfl
-/
theorem algebraMap_toCompletion (r : R) :
    (algebraMap R v.Completion r).toCompletion = algebraMap R v.1.Completion r := rfl

end Algebra

/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (k : K)
  statement: algebraMap K v.Completion k = (k : v.Completion)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (k : K)
  结论: algebraMap K v.完备化 k = (k : v.完备化)
  证明: rfl
-/
@[simp] theorem algebraMap_apply (k : K) : algebraMap K v.Completion k = (k : v.Completion) := rfl

/--
lemma `norm_coe` / 引理 `norm_coe`

English:
lemma norm_coe
  given: (x : WithAbs v.1)
  proof: UniformSpace.Completion.norm_coe x

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

中文:
引理 norm_coe
  条件: (x : WithAbs v.1)
  证明: UniformSpace.Completion.norm_coe x

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.norm_coe, norm_coe
-/
lemma norm_coe (x : WithAbs v.1) :
    ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x) :=
  UniformSpace.Completion.norm_coe x

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

/--
lemma `WithAbs.ratCast_equiv` / 引理 `WithAbs.ratCast_equiv`

English:
lemma WithAbs.ratCast_equiv
  given: (v : InfinitePlace Rat) (x : WithAbs v.1)
  proof: (eq_ratCast ((equiv v).symm.toRingHom.comp (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom)) _).symm

中文:
引理 WithAbs.ratCast_equiv
  条件: (v : InfinitePlace 有理数) (x : WithAbs v.1)
  证明: (eq_ratCast ((equiv v).symm.toRingHom.comp (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom)) _).symm

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.coeRingHom.comp, WithAbs, WithAbs.equiv, coeRingHom, eq_ratCast, symm.toRingHom, symm.toRingHom.comp, toRingHom
-/
lemma WithAbs.ratCast_equiv (v : InfinitePlace Rat) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast ((equiv v).symm.toRingHom.comp (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom)) _).symm

/--
lemma `Rat.norm_infinitePlace_completion` / 引理 `Rat.norm_infinitePlace_completion`

English:
lemma Rat.norm_infinitePlace_completion
  given: (v : InfinitePlace Rat) (x : Rat)
  proof: by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x]; rw [WithAbs.ratCast_equiv]; rw [norm_coe]; rw [(WithAbs.equiv v.1).apply_symm_apply]; rw [Rat.infinitePlace_apply]

中文:
引理 有理数.norm_infinitePlace_completion
  条件: (v : InfinitePlace 有理数) (x : 有理数)
  证明: by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x]; rw [WithAbs.ratCast_equiv]; rw [norm_coe]; rw [(WithAbs.equiv v.1).apply_symm_apply]; rw [Rat.infinitePlace_apply]

Depends on / 依赖: Rat.infinitePlace_apply, WithAbs, WithAbs.equiv, WithAbs.ratCast_equiv, apply_symm_apply, infinitePlace_apply, norm_coe, ratCast_equiv
-/
lemma Rat.norm_infinitePlace_completion (v : InfinitePlace Rat) (x : Rat) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x]; rw [WithAbs.ratCast_equiv]; rw [norm_coe]; rw [(WithAbs.equiv v.1).apply_symm_apply]; rw [Rat.infinitePlace_apply]

/--
Instance `locallyCompactSpace` / 实例 `locallyCompactSpace`

English:
instance locallyCompactSpace
  signature: : LocallyCompactSpace (v.Completion)
  body: letI := AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding
  (isometryEquivCompletion v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

中文:
实例 locallyCompactSpace
  签名: : 局部紧空间 (v.完备化)
  定义体: letI := AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding
  (isometryEquivCompletion v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

Depends on / 依赖: AbsoluteValue, AbsoluteValue.Completion.locallyCompactSpace, Completion, isClosedEmbedding, isometryEquivCompletion, isometry_embedding, locallyCompactSpace, toHomeomorph, toHomeomorph.isClosedEmbedding.locallyCompactSpace, v.isometry_embedding
-/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  letI := AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding
  (isometryEquivCompletion v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/--
Definition of `extensionEmbedding` / `extensionEmbedding` 的定义

English:
definition extensionEmbedding
  signature: : v.Completion ->+* Complex
  body: v.isometry_embedding.extensionHom.comp (equiv v).toRingHom

中文:
定义 extensionEmbedding
  签名: : v.完备化 ->+* 复形
  定义体: v.isometry_embedding.extensionHom.comp (equiv v).toRingHom

Depends on / 依赖: Set.Ici, extensionHom, isometry_embedding, toRingHom, v.isometry_embedding.extensionHom.comp, v.root
-/
def extensionEmbedding : v.Completion ->+* Complex :=
  v.isometry_embedding.extensionHom.comp (equiv v).toRingHom

/--
Definition of `extensionEmbeddingOfIsReal` / `extensionEmbeddingOfIsReal` 的定义

English:
definition extensionEmbeddingOfIsReal
  signature: {v : InfinitePlace K} (hv : IsReal v)
  body: (v.isometry_embedding_of_isReal hv).extensionHom.comp (equiv v).toRingHom

@[simp]

中文:
定义 extensionEmbeddingOfIs实数
  签名: {v : InfinitePlace K} (hv : Is实数 v)
  定义体: (v.isometry_embedding_of_isReal hv).extensionHom.comp (equiv v).toRingHom

@[simp]

Depends on / 依赖: extensionHom, extensionHom.comp, isometry_embedding_of_isReal, toRingHom, v.isometry_embedding_of_isReal
-/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ->+* Real :=
  (v.isometry_embedding_of_isReal hv).extensionHom.comp (equiv v).toRingHom

@[simp]
/--
theorem `extensionEmbedding_coe` / 定理 `extensionEmbedding_coe`

English:
theorem extensionEmbedding_coe
  given: (x : WithAbs v.1)
  proof: v.isometry_embedding.extensionHom_coe _

@[simp]

中文:
定理 extensionEmbedding_coe
  条件: (x : WithAbs v.1)
  证明: v.isometry_embedding.extensionHom_coe _

@[simp]

Depends on / 依赖: extensionHom_coe, isometry_embedding, v.isometry_embedding.extensionHom_coe
-/
theorem extensionEmbedding_coe (x : WithAbs v.1) :
    extensionEmbedding v x = v.embedding (WithAbs.equiv v.1 x) :=
  v.isometry_embedding.extensionHom_coe _

@[simp]
/--
theorem `extensionEmbeddingOfIsReal_coe` / 定理 `extensionEmbeddingOfIsReal_coe`

English:
theorem extensionEmbeddingOfIsReal_coe
  given: {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1)
  proof: (v.isometry_embedding_of_isReal hv).extensionHom_coe _

中文:
定理 extensionEmbeddingOfIs实数_coe
  条件: {v : InfinitePlace K} (hv : Is实数 v) (x : WithAbs v.1)
  证明: (v.isometry_embedding_of_isReal hv).extensionHom_coe _

Depends on / 依赖: SubRootedTree, SubRootedTree.coeTree, coeTree, extensionHom_coe, isometry_embedding_of_isReal, v.isometry_embedding_of_isReal
-/
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs.equiv v.1 x) :=
  (v.isometry_embedding_of_isReal hv).extensionHom_coe _

/--
theorem `isometry_extensionEmbedding` / 定理 `isometry_extensionEmbedding`

English:
theorem isometry_extensionEmbedding
  statement: Isometry (extensionEmbedding v)
  proof: v.isometry_embedding.completion_extension.comp (isometry_toCompletion v)

中文:
定理 isometry_extensionEmbedding
  结论: 等距 (extensionEmbedding v)
  证明: v.isometry_embedding.completion_extension.comp (isometry_toCompletion v)

Depends on / 依赖: completion_extension, isometry_embedding, isometry_toCompletion, v.isometry_embedding.completion_extension.comp
-/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  v.isometry_embedding.completion_extension.comp (isometry_toCompletion v)

/--
theorem `isometry_extensionEmbeddingOfIsReal` / 定理 `isometry_extensionEmbeddingOfIsReal`

English:
theorem isometry_extensionEmbeddingOfIsReal
  given: {v : InfinitePlace K} (hv : IsReal v)
  proof: (v.isometry_embedding_of_isReal hv).completion_extension.comp (isometry_toCompletion v)

@[simp]

中文:
定理 isometry_extensionEmbeddingOfIs实数
  条件: {v : InfinitePlace K} (hv : Is实数 v)
  证明: (v.isometry_embedding_of_isReal hv).completion_extension.comp (isometry_toCompletion v)

@[simp]

Depends on / 依赖: completion_extension, completion_extension.comp, isometry_embedding_of_isReal, isometry_toCompletion, v.isometry_embedding_of_isReal
-/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  (v.isometry_embedding_of_isReal hv).completion_extension.comp (isometry_toCompletion v)

@[simp]
/--
theorem `extensionEmbeddingOfIsReal_apply` / 定理 `extensionEmbeddingOfIsReal_apply`

English:
theorem extensionEmbeddingOfIsReal_apply
  given: {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion)
  proof: by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hv).continuous)
      (isometry_extensionEmbedding v).continuous
  | ih a => simp

中文:
定理 extensionEmbeddingOfIs实数_apply
  条件: {v : InfinitePlace K} (hv : Is实数 v) (x : v.完备化)
  证明: by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hv).continuous)
      (isometry_extensionEmbedding v).continuous
  | ih a => simp

Depends on / 依赖: Complex.continuous_ofReal.comp, continuous, continuous_ofReal, induction_on, isClosed_eq, isometry_extensionEmbedding, isometry_extensionEmbeddingOfIsReal
-/
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : Complex) = extensionEmbedding v x := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hv).continuous)
      (isometry_extensionEmbedding v).continuous
  | ih a => simp

/--
theorem `isClosed_image_extensionEmbedding` / 定理 `isClosed_image_extensionEmbedding`

English:
theorem isClosed_image_extensionEmbedding
  statement: IsClosed (Set.range (extensionEmbedding v))
  proof: (isometry_extensionEmbedding v).isClosedEmbedding.isClosed_range

中文:
定理 isClosed_image_extensionEmbedding
  结论: 是闭集 (集合.range (extensionEmbedding v))
  证明: (isometry_extensionEmbedding v).isClosedEmbedding.isClosed_range

Depends on / 依赖: isClosedEmbedding, isClosedEmbedding.isClosed_range, isClosed_range, isometry_extensionEmbedding
-/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  (isometry_extensionEmbedding v).isClosedEmbedding.isClosed_range

/--
theorem `isClosed_image_extensionEmbeddingOfIsReal` / 定理 `isClosed_image_extensionEmbeddingOfIsReal`

English:
theorem isClosed_image_extensionEmbeddingOfIsReal
  given: {v : InfinitePlace K} (hv : IsReal v)
  proof: (isometry_extensionEmbeddingOfIsReal hv).isClosedEmbedding.isClosed_range

中文:
定理 isClosed_image_extensionEmbeddingOfIs实数
  条件: {v : InfinitePlace K} (hv : Is实数 v)
  证明: (isometry_extensionEmbeddingOfIsReal hv).isClosedEmbedding.isClosed_range

Depends on / 依赖: isClosedEmbedding, isClosedEmbedding.isClosed_range, isClosed_range, isometry_extensionEmbeddingOfIsReal
-/
theorem isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbeddingOfIsReal hv)) :=
  (isometry_extensionEmbeddingOfIsReal hv).isClosedEmbedding.isClosed_range

/--
theorem `subfield_ne_real_of_isComplex` / 定理 `subfield_ne_real_of_isComplex`

English:
theorem subfield_ne_real_of_isComplex
  given: {v : InfinitePlace K} (hv : IsComplex v)
  proof: by
  contrapose hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ RingHom.mem_fieldRange_self (extensionEmbedding v) (x : v.Completion)
  rw [extensionEmbedding_coe]; rw [← WithAbs.equiv_symm_apply]; rw [RingEquiv.apply_symm_apply] at hr
  simp [ComplexEmbedding.

中文:
定理 subfield_ne_real_of_isComplex
  条件: {v : InfinitePlace K} (hv : 是复形 v)
  证明: by
  contrapose hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ RingHom.mem_fieldRange_self (extensionEmbedding v) (x : v.Completion)
  rw [extensionEmbedding_coe]; rw [← WithAbs.equiv_symm_apply]; rw [RingEquiv.apply_symm_apply] at hr
  simp [ComplexEmbedding.

Depends on / 依赖: Completion, Complex.conj_ofReal, ComplexEmbedding, ComplexEmbedding.conjugate_coe_eq, RingEquiv, RingEquiv.apply_symm_apply, RingHom, RingHom.mem_fieldRange_self, WithAbs, WithAbs.equiv_symm_apply, apply_symm_apply, conj_ofReal, conjugate_coe_eq, contrapose, equiv_symm_apply, extensionEmbedding, extensionEmbedding_coe, isReal_iff, mem_fieldRange_self, not_isComplex_iff_isReal
-/
theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    (extensionEmbedding v).fieldRange != Complex.ofRealHom.fieldRange := by
  contrapose hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ RingHom.mem_fieldRange_self (extensionEmbedding v) (x : v.Completion)
  rw [extensionEmbedding_coe]; rw [← WithAbs.equiv_symm_apply]; rw [RingEquiv.apply_symm_apply] at hr
  simp [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.conj_ofReal]

/--
theorem `surjective_extensionEmbedding_of_isComplex` / 定理 `surjective_extensionEmbedding_of_isComplex`

English:
theorem surjective_extensionEmbedding_of_isComplex
  given: {v : InfinitePlace K} (hv : IsComplex v)
  proof: by
  rw [← RingHom.fieldRange_eq_top_iff]
exact (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding v).resolve_left
    subfield_ne_real_of_isComplex hv

中文:
定理 surjective_extensionEmbedding_of_isComplex
  条件: {v : InfinitePlace K} (hv : 是复形 v)
  证明: by
  rw [← RingHom.fieldRange_eq_top_iff]
exact (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding v).resolve_left
    subfield_ne_real_of_isComplex hv

Depends on / 依赖: Complex.subfield_eq_of_closed, RingHom, RingHom.fieldRange_eq_top_iff, fieldRange_eq_top_iff, isClosed_image_extensionEmbedding, resolve_left, subfield_eq_of_closed, subfield_ne_real_of_isComplex
-/
theorem surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Surjective (extensionEmbedding v) := by
  rw [← RingHom.fieldRange_eq_top_iff]
exact (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding v).resolve_left
    subfield_ne_real_of_isComplex hv

/--
theorem `bijective_extensionEmbedding_of_isComplex` / 定理 `bijective_extensionEmbedding_of_isComplex`

English:
theorem bijective_extensionEmbedding_of_isComplex
  given: {v : InfinitePlace K} (hv : IsComplex v)
  proof: ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

中文:
定理 bijective_extensionEmbedding_of_isComplex
  条件: {v : InfinitePlace K} (hv : 是复形 v)
  证明: ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

Depends on / 依赖: extensionEmbedding, injective, surjective_extensionEmbedding_of_isComplex
-/
theorem bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Bijective (extensionEmbedding v) :=
  ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

/--
Definition of `ringEquivComplexOfIsComplex` / `ringEquivComplexOfIsComplex` 的定义

English:
definition ringEquivComplexOfIsComplex
  signature: {v : InfinitePlace K} (hv : IsComplex v)
  body: RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

中文:
定义 ringEquivComplexOfIsComplex
  签名: {v : InfinitePlace K} (hv : 是复形 v)
  定义体: RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective_extensionEmbedding_of_isComplex, ofBijective
-/
def ringEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃+* Complex := RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

/--
theorem `ringEquivComplexOfIsComplex_apply` / 定理 `ringEquivComplexOfIsComplex_apply`

English:
theorem ringEquivComplexOfIsComplex_apply
  statement: {v : InfinitePlace K} (hv : IsComplex v)
  proof: rfl

中文:
定理 ringEquivComplexOfIsComplex_apply
  结论: {v : InfinitePlace K} (hv : 是复形 v)
  证明: rfl
-/
@[simp] theorem ringEquivComplexOfIsComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.Completion) : ringEquivComplexOfIsComplex hv x = extensionEmbedding v x := rfl

/--
Definition of `isometryEquivComplexOfIsComplex` / `isometryEquivComplexOfIsComplex` 的定义

English:
definition isometryEquivComplexOfIsComplex
  signature: {v : InfinitePlace K} (hv : IsComplex v)
  body: ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

中文:
定义 isometryEquivComplexOfIsComplex
  签名: {v : InfinitePlace K} (hv : 是复形 v)
  定义体: ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

Depends on / 依赖: ringEquivComplexOfIsComplex
-/
def isometryEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃ᵢ Complex where
  toEquiv := ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

/--
theorem `surjective_extensionEmbeddingOfIsReal` / 定理 `surjective_extensionEmbeddingOfIsReal`

English:
theorem surjective_extensionEmbeddingOfIsReal
  given: {v : InfinitePlace K} (hv : IsReal v)
  proof: by
  rw [← RingHom.fieldRange_eq_top_iff]; rw [← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

中文:
定理 surjective_extensionEmbeddingOfIs实数
  条件: {v : InfinitePlace K} (hv : Is实数 v)
  证明: by
  rw [← RingHom.fieldRange_eq_top_iff]; rw [← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

Depends on / 依赖: Real.subfield_eq_of_closed, RingHom, RingHom.fieldRange_eq_top_iff, fieldRange_eq_top_iff, isClosed_image_extensionEmbeddingOfIsReal, subfield_eq_of_closed
-/
theorem surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbeddingOfIsReal hv) := by
  rw [← RingHom.fieldRange_eq_top_iff]; rw [← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

/--
theorem `bijective_extensionEmbeddingOfIsReal` / 定理 `bijective_extensionEmbeddingOfIsReal`

English:
theorem bijective_extensionEmbeddingOfIsReal
  given: {v : InfinitePlace K} (hv : IsReal v)
  proof: ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

中文:
定理 bijective_extensionEmbeddingOfIs实数
  条件: {v : InfinitePlace K} (hv : Is实数 v)
  证明: ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

Depends on / 依赖: extensionEmbeddingOfIsReal, injective, surjective_extensionEmbeddingOfIsReal
-/
theorem bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbeddingOfIsReal hv) :=
  ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

/--
Definition of `ringEquivRealOfIsReal` / `ringEquivRealOfIsReal` 的定义

English:
definition ringEquivRealOfIsReal
  signature: {v : InfinitePlace K} (hv : IsReal v)
  body: RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)

中文:
定义 ringEquiv实数OfIs实数
  签名: {v : InfinitePlace K} (hv : Is实数 v)
  定义体: RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)

Depends on / 依赖: RingEquiv, RingEquiv.ofBijective, bijective_extensionEmbeddingOfIsReal, ofBijective
-/
def ringEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃+* Real :=
  RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)

/--
theorem `ringEquivRealOfIsReal_apply` / 定理 `ringEquivRealOfIsReal_apply`

English:
theorem ringEquivRealOfIsReal_apply
  statement: {v : InfinitePlace K} (hv : IsReal v)
  proof: rfl

中文:
定理 ringEquiv实数OfIs实数_apply
  结论: {v : InfinitePlace K} (hv : Is实数 v)
  证明: rfl

Depends on / 依赖: OrderType
-/
@[simp] theorem ringEquivRealOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v)
    (x : v.Completion) : ringEquivRealOfIsReal hv x = extensionEmbeddingOfIsReal hv x := rfl

/--
Definition of `isometryEquivRealOfIsReal` / `isometryEquivRealOfIsReal` 的定义

English:
definition isometryEquivRealOfIsReal
  signature: {v : InfinitePlace K} (hv : IsReal v)
  body: ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

中文:
定义 isometryEquiv实数OfIs实数
  签名: {v : InfinitePlace K} (hv : Is实数 v)
  定义体: ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

Depends on / 依赖: ringEquivRealOfIsReal
-/
def isometryEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃ᵢ Real where
  toEquiv := ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) {v}

/--
theorem `algebraMap_eq_coe` / 定理 `algebraMap_eq_coe`

English:
theorem algebraMap_eq_coe
  given: (x : WithAbs v.1)
  proof: by
  apply ext
  rw [algebraMap_toCompletion]
  exact UniformSpace.Completion.algebraMap_def (WithAbs w.1) (WithAbs v.1) x

中文:
定理 algebraMap_eq_coe
  条件: (x : WithAbs v.1)
  证明: by
  apply ext
  rw [algebraMap_toCompletion]
  exact UniformSpace.Completion.algebraMap_def (WithAbs w.1) (WithAbs v.1) x

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.algebraMap_def, WithAbs, algebraMap_def, algebraMap_toCompletion
-/
theorem algebraMap_eq_coe (x : WithAbs v.1) :
    algebraMap (WithAbs v.1) w.Completion x = (algebraMap (WithAbs v.1) (WithAbs w.1) x) := by
  apply ext
  rw [algebraMap_toCompletion]
  exact UniformSpace.Completion.algebraMap_def (WithAbs w.1) (WithAbs v.1) x

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

@[simp]
/--
theorem `algebraMap_coe` / 定理 `algebraMap_coe`

English:
theorem algebraMap_coe
  given: (x : WithAbs v.1)
  proof: (IsScalarTower.algebraMap_apply (WithAbs v.1) v.Completion w.Completion x).symm.trans
    (algebraMap_eq_coe w x)

中文:
定理 algebraMap_coe
  条件: (x : WithAbs v.1)
  证明: (IsScalarTower.algebraMap_apply (WithAbs v.1) v.Completion w.Completion x).symm.trans
    (algebraMap_eq_coe w x)

Depends on / 依赖: Completion, IsScalarTower, IsScalarTower.algebraMap_apply, WithAbs, algebraMap_apply, algebraMap_eq_coe, symm.trans, v.Completion, w.Completion
-/
theorem algebraMap_coe (x : WithAbs v.1) :
    algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1) (WithAbs w.1) x :=
  (IsScalarTower.algebraMap_apply (WithAbs v.1) v.Completion w.Completion x).symm.trans
    (algebraMap_eq_coe w x)

end Completion

section LiesOver

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) (v : InfinitePlace K)

namespace Completion

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

/--
theorem `liesOver_extensionEmbedding` / 定理 `liesOver_extensionEmbedding`

English:
theorem liesOver_extensionEmbedding
  statement: [ContinuousSMul v.Completion w.Completion]
  proof: by
    ext x
    induction x using induction_on
    · exact isClosed_eq
        ((isometry_extensionEmbedding w).continuous.comp
          (continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraM

中文:
定理 liesOver_extensionEmbedding
  结论: [连续标量乘法 v.完备化 w.完备化]
  证明: by
    ext x
    induction x using induction_on
    · exact isClosed_eq
        ((isometry_extensionEmbedding w).continuous.comp
          (continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraM

Depends on / 依赖: Completion, ComplexEmbedding, ComplexEmbedding.LiesOver.over, LiesOver, OrderType, WithAbs, WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply, algebraMap_left_apply, algebraMap_right_apply, continuous, continuous.comp, continuous_algebraMap, embedding, induction_on, isClosed_eq, isometry_extensionEmbedding, v.Completion, v.embedding, w.Completion
-/
theorem liesOver_extensionEmbedding [ContinuousSMul v.Completion w.Completion]
    [ComplexEmbedding.LiesOver w.embedding v.embedding] :
    ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) where
  over := by
    ext x
    induction x using induction_on
    · exact isClosed_eq
        ((isometry_extensionEmbedding w).continuous.comp
          (continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
        ← ComplexEmbedding.LiesOver.over w.embedding v.embedding]

/--
theorem `liesOver_conjugate_extensionEmbedding` / 定理 `liesOver_conjugate_extensionEmbedding`

English:
theorem liesOver_conjugate_extensionEmbedding
  statement: [ContinuousSMul v.Completion w.Completion]
  proof: by
    ext x
    induction x using induction_on
    · simpa using! isClosed_eq (.comp (by fun_prop)
          ((isometry_extensionEmbedding w).continuous.comp <|
            continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algeb

中文:
定理 liesOver_conjugate_extensionEmbedding
  结论: [连续标量乘法 v.完备化 w.完备化]
  证明: by
    ext x
    induction x using induction_on
    · simpa using! isClosed_eq (.comp (by fun_prop)
          ((isometry_extensionEmbedding w).continuous.comp <|
            continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algeb

Depends on / 依赖: Completion, ComplexEmbedding, ComplexEmbedding.LiesOver.over, LiesOver, WithAbs, WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply, algebraMap_left_apply, algebraMap_right_apply, conjugate, continuous, continuous.comp, continuous_algebraMap, embedding, fun_prop, induction_on, isClosed_eq, isometry_extensionEmbedding, v.Completion, v.embedding
-/
theorem liesOver_conjugate_extensionEmbedding [ContinuousSMul v.Completion w.Completion]
    [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding] :
    ComplexEmbedding.LiesOver (conjugate (extensionEmbedding w)) (extensionEmbedding v) where
  over := by
    ext x
    induction x using induction_on
    · simpa using! isClosed_eq (.comp (by fun_prop)
          ((isometry_extensionEmbedding w).continuous.comp <|
            continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
        ← ComplexEmbedding.LiesOver.over (conjugate w.embedding) v.embedding]

omit [Algebra K L] in
@[simp]
/--
theorem `liesOver_extensionEmbedding_apply` / 定理 `liesOver_extensionEmbedding_apply`

English:
theorem liesOver_extensionEmbedding_apply
  statement: {φ : w.Completion ->+* Complex}
  proof: by
  simp_all [liesOver_iff, RingHom.ext_iff]

中文:
定理 liesOver_extensionEmbedding_apply
  结论: {φ : w.完备化 ->+* 复形}
  证明: by
  simp_all [liesOver_iff, RingHom.ext_iff]

Depends on / 依赖: RingHom, RingHom.ext_iff, ext_iff, liesOver_iff
-/
theorem liesOver_extensionEmbedding_apply {φ : w.Completion ->+* Complex}
    [ComplexEmbedding.LiesOver φ (extensionEmbedding v)] {x : v.Completion} :
    φ (algebraMap v.Completion w.Completion x) = (extensionEmbedding v) x := by
  simp_all [liesOver_iff, RingHom.ext_iff]

end Completion

namespace LiesOver

open Completion

variable [w.LiesOver v]

/--
theorem `isometry_algebraMap` / 定理 `isometry_algebraMap`

English:
theorem isometry_algebraMap
  statement: Isometry (algebraMap (WithAbs v.1) (WithAbs w.1))
  proof: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa [WithAbs.norm_eq_apply_ofAbs] using
      WithAbs.ofAbs_algebraMap v.1 w.1 x ▸ comp_of_comap_eq (comap_eq w v) x.ofAbs

中文:
定理 isometry_algebraMap
  结论: 等距 (algebraMap (WithAbs v.1) (WithAbs w.1))
  证明: AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa [WithAbs.norm_eq_apply_ofAbs] using
      WithAbs.ofAbs_algebraMap v.1 w.1 x ▸ comp_of_comap_eq (comap_eq w v) x.ofAbs

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, WithAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_algebraMap, comap_eq, comp_of_comap_eq, isometry_of_norm, norm_eq_apply_ofAbs, ofAbs_algebraMap, x.ofAbs
-/
theorem isometry_algebraMap : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1)) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    simpa [WithAbs.norm_eq_apply_ofAbs] using
      WithAbs.ofAbs_algebraMap v.1 w.1 x ▸ comp_of_comap_eq (comap_eq w v) x.ofAbs

variable {v}

/--
theorem `embedding_liesOver_of_isReal` / 定理 `embedding_liesOver_of_isReal`

English:
theorem embedding_liesOver_of_isReal
  given: (h : v.IsReal)
  proof: (comap_eq w v ▸ comap_embedding_of_isReal _ (comap_eq w v ▸ h)).symm

中文:
定理 embedding_liesOver_of_is实数
  条件: (h : v.Is实数)
  证明: (comap_eq w v ▸ comap_embedding_of_isReal _ (comap_eq w v ▸ h)).symm

Depends on / 依赖: comap_embedding_of_isReal, comap_eq
-/
theorem embedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver w.embedding v.embedding where
  over := (comap_eq w v ▸ comap_embedding_of_isReal _ (comap_eq w v ▸ h)).symm

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

/--
theorem `extensionEmbedding_liesOver_of_isReal` / 定理 `extensionEmbedding_liesOver_of_isReal`

English:
theorem extensionEmbedding_liesOver_of_isReal
  given: (h : v.IsReal)
  proof: let := embedding_liesOver_of_isReal w h; liesOver_extensionEmbedding w v

中文:
定理 extensionEmbedding_liesOver_of_is实数
  条件: (h : v.Is实数)
  证明: let := embedding_liesOver_of_isReal w h; liesOver_extensionEmbedding w v

Depends on / 依赖: embedding_liesOver_of_isReal, liesOver_extensionEmbedding
-/
theorem extensionEmbedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) :=
  let := embedding_liesOver_of_isReal w h; liesOver_extensionEmbedding w v

end LiesOver

end NumberField.InfinitePlace.LiesOver
