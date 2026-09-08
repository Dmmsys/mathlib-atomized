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

/-
**NumberField.InfinitePlace.isometry_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace`。
形式化陈述：isometry_embedding : Isometry (v.embedding.comp (WithAbs.equiv v.1).toRing
Hom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
-/
theorem isometry_embedding : Isometry (v.embedding.comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)
/-
**NumberField.InfinitePlace.isometry_embedding_of_isReal** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace`。
形式化陈述：isometry_embedding_of_isReal (hv : v.IsReal) : Isometry ((v.embedding_of_i
sReal hv).comp (WithAbs.equiv v.1).toRingHom)
参数：hv : v.IsReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.InfinitePlace.norm_embedding_of_isReal`：norm_embedding_of_is
Real {w : InfinitePlace K} (hw : IsReal w) (x : K) : ‖embedding_of_isReal hw x‖ 
= w x
-/
theorem isometry_embedding_of_isReal (hv : v.IsReal) :
    Isometry ((v.embedding_of_isReal hv).comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)
/-
**NumberField.InfinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.InfinitePlac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompletableTopField (WithAbs v.1) :=
  v.isometry_embedding.isUniformInducing.completableTopField

/-- The completion of a number field at an infinite place, as a one-field structure wrapping the
completion `v.1.Completion` of `K` at the underlying absolute value. -/
/-
**NumberField.InfinitePlace.Completion** 是 Mathlib 中的一个归纳类型，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：{K : Type u_1} → [inst : Field K] → NumberField.InfinitePlace K → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of a number field at an infinite place, as a one-field structure 
wrapping the
completion `v.1.Completion` of `K` at the underlying absolute value.
-/
structure Completion where
  /-- Wrap an element of `v.1.Completion` into `v.Completion`. -/
  ofCompletion ::
  /-- The underlying element of `v.1.Completion`. -/
  toCompletion : v.1.Completion

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
@[simps]
/-
**NumberField.InfinitePlace.Completion.equivCompletion** 是 Mathlib 中的一个定义，位于命名空间
 `NumberField.InfinitePlace.Completion`。
形式化陈述：equivCompletion : v.Completion ≃ v.1.Completion where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Completion.toCompletion` and `Completion.ofCompletion` as an equivalence.
-/
def equivCompletion : v.Completion ≃ v.1.Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedField v.Completion := fast_instance% (equivCompletion v).normedField

/-- `Completion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
/-
**NumberField.InfinitePlace.Completion.equiv** 是 Mathlib 中的一个定义，位于命名空间 `NumberFi
eld.InfinitePlace.Completion`。
形式化陈述：equiv : v.Completion ≃+* v.1.Completion where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Completion.toCompletion` as a ring isomorphism onto the underlying completion.
-/
def equiv : v.Completion ≃+* v.1.Completion where
  toEquiv := equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
/-
**NumberField.InfinitePlace.Completion.toCompletion_ofCompletion** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : (
↑v).Completion),   { toCompletion := x }.toCompletion = x
参数：v : NumberField.InfinitePlace K；x : (↑v).Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_ofCompletion (x : v.1.Completion) :
    toCompletion (ofCompletion x : v.Completion) = x := rfl
/-
**NumberField.InfinitePlace.Completion.ofCompletion_toCompletion** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : v
.Completion),   { toCompletion := x.toCompletion } = x
参数：v : NumberField.InfinitePlace K；x : v.Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofCompletion_toCompletion (x : v.Completion) :
    ofCompletion x.toCompletion = x := rfl
/-
**NumberField.InfinitePlace.Completion.toCompletion_zero** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K),   Num
berField.InfinitePlace.Completion.toCompletion 0 = 0
参数：v : NumberField.InfinitePlace K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_zero : (0 : v.Completion).toCompletion = 0 := rfl
/-
**NumberField.InfinitePlace.Completion.toCompletion_one** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K),   Num
berField.InfinitePlace.Completion.toCompletion 1 = 1
参数：v : NumberField.InfinitePlace K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_one : (1 : v.Completion).toCompletion = 1 := rfl
/-
**NumberField.InfinitePlace.Completion.toCompletion_add** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x y :
 v.Completion),   (x + y).toCompletion = x.toCompletion + y.toCompletion
参数：v : NumberField.InfinitePlace K；x y : v.Completion；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_add (x y : v.Completion) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
/-
**NumberField.InfinitePlace.Completion.toCompletion_mul** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x y :
 v.Completion),   (x * y).toCompletion = x.toCompletion * y.toCompletion
参数：v : NumberField.InfinitePlace K；x y : v.Completion；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toCompletion_mul (x y : v.Completion) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl
/-
**NumberField.InfinitePlace.Completion.ext** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {v : NumberField.InfinitePlace K} {x y :
 v.Completion},   x.toCompletion = y.toCompletion → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem ext {v : InfinitePlace K} {x y : v.Completion}
    (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h
/-
**NumberField.InfinitePlace.Completion.toCompletion_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：toCompletion_surjective : Function.Surjective (toCompletion (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equivCompletion v).surjective
/-
**NumberField.InfinitePlace.Completion.ofCompletion_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：ofCompletion_surjective : Function.Surjective (ofCompletion (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equivCompletion v).symm.surjective
/-
**NumberField.InfinitePlace.Completion.norm_toCompletion** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : v
.Completion), ‖x.toCompletion‖ = ‖x‖
参数：v : NumberField.InfinitePlace K；x : v.Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_toCompletion (x : v.Completion) : ‖x.toCompletion‖ = ‖x‖ := rfl
/-
**NumberField.InfinitePlace.Completion.norm_ofCompletion** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : (
↑v).Completion), ‖{ toCompletion := x }‖ = ‖x‖
参数：v : NumberField.InfinitePlace K；x : (↑v).Completion。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_ofCompletion (x : v.1.Completion) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl
/-
**NumberField.InfinitePlace.Completion.isometry_toCompletion** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometry_toCompletion : Isometry (toCompletion (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
-/
theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

/-- `Completion.toCompletion` as an isometry equivalence onto the underlying completion. -/
/-
**NumberField.InfinitePlace.Completion.isometryEquivCompletion** 是 Mathlib 中的一个定
义，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometryEquivCompletion : v.Completion ≃ᵢ v.1.Completion where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_toCompletion`：isometry_toC
ompletion : Isometry (toCompletion (v

--- 原说明 ---
`Completion.toCompletion` as an isometry equivalence onto the underlying complet
ion.
-/
def isometryEquivCompletion : v.Completion ≃ᵢ v.1.Completion where
  toEquiv := equivCompletion v
  isometry_toFun := isometry_toCompletion v
/-
**NumberField.InfinitePlace.Completion.continuous_toCompletion** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：continuous_toCompletion : Continuous (toCompletion (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_toCompletion`：isometry_toC
ompletion : Isometry (toCompletion (v
-/
theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous
/-
**NumberField.InfinitePlace.Completion.continuous_ofCompletion** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：continuous_ofCompletion : Continuous (ofCompletion (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Continuous ⇑h
-/
theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometryEquivCompletion v).symm.continuous
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace v.Completion :=
  ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited v.Completion := ⟨0⟩

/-- Coercion of an element of `WithAbs v.1` into the completion. -/
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an element of `WithAbs v.1` into the completion.
-/
instance : Coe (WithAbs v.1) v.Completion where
  coe x := ofCompletion (x : v.1.Completion)

/-- Coercion of an element of `K` into the completion. -/
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion of an element of `K` into the completion.
-/
instance : Coe K v.Completion where
  coe k := ofCompletion (k : v.1.Completion)
/-
**NumberField.InfinitePlace.Completion.coe_toCompletion** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : W
ithAbs ↑v),   { toCompletion := ↑x }.toCompletion = ↑x
参数：v : NumberField.InfinitePlace K；x : WithAbs ↑v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toCompletion (x : WithAbs v.1) :
    (x : v.Completion).toCompletion = (x : v.1.Completion) := rfl
/-
**NumberField.InfinitePlace.Completion.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K), { toC
ompletion := ↑(WithAbs.toAbs (↑v) 0) } = 0
参数：v : NumberField.InfinitePlace K；WithAbs.toAbs (↑v) 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_zero : ((0 : K) : v.Completion) = 0 := by ext; simp
/-
**NumberField.InfinitePlace.Completion.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K), { toC
ompletion := ↑(WithAbs.toAbs (↑v) 1) } = 1
参数：v : NumberField.InfinitePlace K；WithAbs.toAbs (↑v) 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_one : ((1 : K) : v.Completion) = 1 := by ext; simp
/-
**NumberField.InfinitePlace.Completion.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x y :
 K),   { toCompletion := ↑(WithAbs.toAbs (↑v) (x + y)) } =     { toCompletion :=
 ↑(WithAbs.toAbs (↑v) x) } + { toCompletion := ↑(WithAbs.toAbs (↑v) y) }
参数：v : NumberField.InfinitePlace K；x y : K；WithAbs.toAbs (↑v) (x + y)；WithAbs.to
Abs (↑v) x；WithAbs.toAbs (↑v) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.coe_add`：coe_add (a b : α) : ((a + b : α) : Comp
letion α) = a + b
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_add (x y : K) : ((x + y : K) : v.Completion) = ↑x + ↑y := by
  ext; simp [UniformSpace.Completion.coe_add]
/-
**NumberField.InfinitePlace.Completion.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x y :
 K),   { toCompletion := ↑(WithAbs.toAbs (↑v) (x * y)) } =     { toCompletion :=
 ↑(WithAbs.toAbs (↑v) x) } * { toCompletion := ↑(WithAbs.toAbs (↑v) y) }
参数：v : NumberField.InfinitePlace K；x y : K；WithAbs.toAbs (↑v) (x * y)；WithAbs.to
Abs (↑v) x；WithAbs.toAbs (↑v) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[norm_cast] lemma coe_mul (x y : K) : ((x * y : K) : v.Completion) = ↑x * ↑y := by
  ext; simp [UniformSpace.Completion.coe_mul]
/-
**NumberField.InfinitePlace.Completion.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace.Completion`。
形式化陈述：continuous_coe : Continuous ((↑) : WithAbs v.1 -> v.Completion)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_ofCompletion`：continuous
_ofCompletion : Continuous (ofCompletion (v
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
-/
theorem continuous_coe : Continuous ((↑) : WithAbs v.1 → v.Completion) :=
  (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)
/-
**NumberField.InfinitePlace.Completion.denseRange_coe** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace.Completion`。
形式化陈述：denseRange_coe : DenseRange ((↑) : WithAbs v.1 -> v.Completion)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.comp`：DenseRange.comp {g : Y -> Z} {f : α -> Y} (hg : DenseRa
nge g) (hf : DenseRange f) (cg : Continuous g) : DenseRange (g ∘ f)
· 使用定理 `Function.Surjective.denseRange`：Function.Surjective.denseRange (hf : Fun
ction.Surjective f) : DenseRange f
· 使用定理 `NumberField.InfinitePlace.Completion.ofCompletion_surjective`：ofCompleti
on_surjective : Function.Surjective (ofCompletion (v
· 使用定理 `UniformSpace.Completion.denseRange_coe`：denseRange_coe : DenseRange ((↑)
 : α -> Completion α)
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_ofCompletion`：continuous
_ofCompletion : Continuous (ofCompletion (v
-/
theorem denseRange_coe : DenseRange ((↑) : WithAbs v.1 → v.Completion) :=
  (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

/-- Induction on the completion of a number field at an infinite place: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
/-
**NumberField.InfinitePlace.Completion.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.InfinitePlace.Completion`。
形式化陈述：induction_on {p : v.Completion -> Prop} (x : v.Completion) (hp : IsClosed 
{x | p x}) (ih : forall a : WithAbs v.1, p a) : p x
参数：x : v.Completion；hp : IsClosed {x | p x}；ih : forall a : WithAbs v.1, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `NumberField.InfinitePlace.Completion.continuous_ofCompletion`：continuous
_ofCompletion : Continuous (ofCompletion (v

--- 原说明 ---
Induction on the completion of a number field at an infinite place: a closed pro
perty that
holds on the image of `K` holds everywhere.
-/
theorem induction_on {p : v.Completion → Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : ∀ a : WithAbs v.1, p a) : p x :=
  UniformSpace.Completion.induction_on (p := fun y ↦ p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R (WithAbs v.1)]
  [UniformContinuousConstSMul R (WithAbs v.1)]

/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R v.Completion := fast_instance% (equivCompletion v).algebra R
/-
**NumberField.InfinitePlace.Completion.algebraMap_toCompletion** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：algebraMap_toCompletion (r : R) : (algebraMap R v.Completion r).toCompleti
on = algebraMap R v.1.Completion r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_toCompletion (r : R) :
    (algebraMap R v.Completion r).toCompletion = algebraMap R v.1.Completion r := rfl

end Algebra

/-
**NumberField.InfinitePlace.Completion.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (k : K
),   (algebraMap K v.Completion) k = { toCompletion := ↑(WithAbs.toAbs (↑v) k) }
参数：v : NumberField.InfinitePlace K；k : K；algebraMap K v.Completion；WithAbs.toAbs
 (↑v) k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
-/
@[simp] theorem algebraMap_apply (k : K) : algebraMap K v.Completion k = (k : v.Completion) := rfl
/-
**NumberField.InfinitePlace.Completion.norm_coe** 是 Mathlib 中的一个引理，位于命名空间 `Numbe
rField.InfinitePlace.Completion`。
形式化陈述：norm_coe (x : WithAbs v.1) : ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x
)
参数：x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
-/
lemma norm_coe (x : WithAbs v.1) :
    ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x) :=
  UniformSpace.Completion.norm_coe x
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个示例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : NormedField v.Completion := inferInstance
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个示例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Algebra K v.Completion := inferInstance
/-
**NumberField.InfinitePlace.Completion.** 是 Mathlib 中的一个示例，位于命名空间 `NumberField.I
nfinitePlace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsTopologicalRing v.Completion := inferInstance

/-- The coercion from the rationals to its completion along an infinite place is `Rat.cast`. -/
/-
**NumberField.InfinitePlace.Completion.WithAbs.ratCast_equiv** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.InfinitePlace.Completion.WithAbs`。
形式化陈述：∀ (v : NumberField.InfinitePlace ℚ) (x : WithAbs ↑v), ↑((WithAbs.equiv ↑v)
 x) = { toCompletion := ↑x }
参数：v : NumberField.InfinitePlace ℚ；x : WithAbs ↑v；(WithAbs.equiv ↑v) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q

--- 原说明 ---
The coercion from the rationals to its completion along an infinite place is `Ra
t.cast`.
-/
lemma WithAbs.ratCast_equiv (v : InfinitePlace ℚ) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast ((equiv v).symm.toRingHom.comp (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom)) _).symm
/-
**NumberField.InfinitePlace.Completion.Rat.norm_infinitePlace_completion** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion.Rat`。
形式化陈述：∀ (v : NumberField.InfinitePlace ℚ) (x : ℚ), ‖↑x‖ = ↑|x|
参数：v : NumberField.InfinitePlace ℚ；x : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `NumberField.InfinitePlace.Completion.WithAbs.ratCast_equiv`：∀ (v : Numbe
rField.InfinitePlace ℚ) (x : WithAbs ↑v), ↑((WithAbs.equiv ↑v) x) = { toCompleti
on := ↑x }
· 使用引理 `NumberField.InfinitePlace.Completion.norm_coe`：norm_coe (x : WithAbs v.1
) : ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x)
· 使用定理 `Rat.infinitePlace_apply`：∀ (v : NumberField.InfinitePlace ℚ) (x : ℚ), v 
x = ↑|x|
-/
lemma Rat.norm_infinitePlace_completion (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x, WithAbs.ratCast_equiv,
    norm_coe, (WithAbs.equiv v.1).apply_symm_apply,
    Rat.infinitePlace_apply]

/-- The completion of a number field at an infinite place is locally compact. -/
/-
**NumberField.InfinitePlace.Completion.locallyCompactSpace** 是 Mathlib 中的一个实例，位于
命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：locallyCompactSpace : LocallyCompactSpace (v.Completion)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompac
tSpace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `AbsoluteValue.Completion.locallyCompactSpace`：locallyCompactSpace [Local
lyCompactSpace L] (h : Isometry f) : LocallyCompactSpace v.Completion
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `NumberField.InfinitePlace.isometry_embedding`：isometry_embedding : Isome
try (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h

--- 原说明 ---
The completion of a number field at an infinite place is locally compact.
-/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  letI := AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding
  (isometryEquivCompletion v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- The embedding associated to an infinite place extended to an embedding `v.Completion →+* ℂ`. -/
/-
**NumberField.InfinitePlace.Completion.extensionEmbedding** 是 Mathlib 中的一个定义，位于命
名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：extensionEmbedding : v.Completion ->+* Complex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `NumberField.InfinitePlace.isometry_embedding`：isometry_embedding : Isome
try (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)

--- 原说明 ---
The embedding associated to an infinite place extended to an embedding `v.Comple
tion →+* ℂ`.
-/
def extensionEmbedding : v.Completion →+* ℂ :=
  v.isometry_embedding.extensionHom.comp (equiv v).toRingHom

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Completion →+* ℝ`. -/
/-
**NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal** 是 Mathlib 中的
一个定义，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Compl
etion ->+* Real
参数：hv : IsReal v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `NumberField.InfinitePlace.isometry_embedding_of_isReal`：isometry_embeddi
ng_of_isReal (hv : v.IsReal) : Isometry ((v.embedding_of_isReal hv).comp (WithAb
s.equiv v.1).toRingHom)
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)

--- 原说明 ---
The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Compl
etion →+* ℝ`.
-/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion →+* ℝ :=
  (v.isometry_embedding_of_isReal hv).extensionHom.comp (equiv v).toRingHom

@[simp]
/-
**NumberField.InfinitePlace.Completion.extensionEmbedding_coe** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：extensionEmbedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embe
dding (WithAbs.equiv v.1 x)
参数：x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.extensionHom_coe`：Isometry.extensionHom_coe [CompleteSpace β] [
T0Space β] {f : α ->+* β} (h : Isometry f) (x : α) : h.extensionHom x = f x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.InfinitePlace.isometry_embedding`：isometry_embedding : Isome
try (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
-/
theorem extensionEmbedding_coe (x : WithAbs v.1) :
    extensionEmbedding v x = v.embedding (WithAbs.equiv v.1 x) :=
  v.isometry_embedding.extensionHom_coe _

@[simp]
/-
**NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : 
WithAbs v.1) : extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs
.equiv v.1 x)
参数：hv : IsReal v；x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.extensionHom_coe`：Isometry.extensionHom_coe [CompleteSpace β] [
T0Space β] {f : α ->+* β} (h : Isometry f) (x : α) : h.extensionHom x = f x
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.InfinitePlace.isometry_embedding_of_isReal`：isometry_embeddi
ng_of_isReal (hv : v.IsReal) : Isometry ((v.embedding_of_isReal hv).comp (WithAb
s.equiv v.1).toRingHom)
-/
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs.equiv v.1 x) :=
  (v.isometry_embedding_of_isReal hv).extensionHom_coe _

/-- The embedding `v.Completion →+* ℂ` is an isometry. -/
/-
**NumberField.InfinitePlace.Completion.isometry_extensionEmbedding** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometry_extensionEmbedding : Isometry (extensionEmbedding v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)
· 使用定理 `Isometry.completion_extension`：Isometry.completion_extension [PseudoMetr
icSpace β] [CompleteSpace β] [T0Space β] {f : α -> β} (h : Isometry f) : Isometr
y (Completion.exten…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.InfinitePlace.isometry_embedding`：isometry_embedding : Isome
try (v.embedding.comp (WithAbs.equiv v.1).toRingHom)
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_toCompletion`：isometry_toC
ompletion : Isometry (toCompletion (v

--- 原说明 ---
The embedding `v.Completion →+* ℂ` is an isometry.
-/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  v.isometry_embedding.completion_extension.comp (isometry_toCompletion v)

/-- The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry. -/
/-
**NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) 
: Isometry (extensionEmbeddingOfIsReal hv)
参数：hv : IsReal v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `NumberField.InfinitePlace.instCompletableTopFieldWithAbsRealValAbsoluteV
alueExistsRingHomComplexEqPlace`：∀ {K : Type u_1} [inst : Field K] (v : NumberFi
eld.InfinitePlace K), CompletableTopField (WithAbs ↑v)
· 使用定理 `Isometry.completion_extension`：Isometry.completion_extension [PseudoMetr
icSpace β] [CompleteSpace β] [T0Space β] {f : α -> β} (h : Isometry f) : Isometr
y (Completion.exten…
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NumberField.InfinitePlace.isometry_embedding_of_isReal`：isometry_embeddi
ng_of_isReal (hv : v.IsReal) : Isometry ((v.embedding_of_isReal hv).comp (WithAb
s.equiv v.1).toRingHom)
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_toCompletion`：isometry_toC
ompletion : Isometry (toCompletion (v

--- 原说明 ---
The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry.
-/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  (v.isometry_embedding_of_isReal hv).completion_extension.comp (isometry_toCompletion v)

@[simp]
/-
**NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply** 是 Math
lib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x 
: v.Completion) : (extensionEmbeddingOfIsReal hv x : Complex) = extensionEmbeddi
ng v x
参数：hv : IsReal v；x : v.Completion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.induction_on`：induction_on {p : v.C
ompletion -> Prop} (x : v.Completion) (hp : IsClosed {x | p x}) (ih : forall a :
 WithAbs v.1, p a) : p x
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
`：isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : Is
ometry (extensionEmbeddingOfIsReal hv)
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`：isomet
ry_extensionEmbedding : Isometry (extensionEmbedding v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe`：ext
ensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v
.1) : extensionEmbeddingOfIsReal hv x = embedding_of_isRe…
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `NumberField.InfinitePlace.embedding_of_isReal_apply`：embedding_of_isReal
_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) : ((embedding_of_isReal hw)
 x : Complex) = (embedding w) x
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbedding_coe`：extensionEm
bedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embedding (WithAbs.eq
uiv v.1 x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : ℂ) = extensionEmbedding v x := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hv).continuous)
      (isometry_extensionEmbedding v).continuous
  | ih a => simp

/-- The embedding `v.Completion →+* ℂ` has closed image inside `ℂ`. -/
/-
**NumberField.InfinitePlace.Completion.isClosed_image_extensionEmbedding** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbeddin
g v))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `NumberField.InfinitePlace.Completion.instCompleteSpace`：∀ {K : Type u_1}
 [inst : Field K] (v : NumberField.InfinitePlace K), CompleteSpace v.Completion
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`：isomet
ry_extensionEmbedding : Isometry (extensionEmbedding v)

--- 原说明 ---
The embedding `v.Completion →+* ℂ` has closed image inside `ℂ`.
-/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  (isometry_extensionEmbedding v).isClosedEmbedding.isClosed_range

/-- The embedding `v.Completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
/-
**NumberField.InfinitePlace.Completion.isClosed_image_extensionEmbeddingOfIsReal
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsRe
al v) : IsClosed (Set.range (extensionEmbeddingOfIsReal hv))
参数：hv : IsReal v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `NumberField.InfinitePlace.Completion.instCompleteSpace`：∀ {K : Type u_1}
 [inst : Field K] (v : NumberField.InfinitePlace K), CompleteSpace v.Completion
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
`：isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : Is
ometry (extensionEmbeddingOfIsReal hv)

--- 原说明 ---
The embedding `v.Completion →+* ℝ` associated to a real infinite place has close
d image
inside `ℝ`.
-/
theorem isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbeddingOfIsReal hv)) :=
  (isometry_extensionEmbeddingOfIsReal hv).isClosedEmbedding.isClosed_range
/-
**NumberField.InfinitePlace.Completion.subfield_ne_real_of_isComplex** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) : (
extensionEmbedding v).fieldRange != Complex.ofRealHom.fieldRange
参数：hv : IsComplex v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingHom.mem_fieldRange_self`：mem_fieldRange_self (x : K) : f x in f.fiel
dRange
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `WithAbs.equiv_symm_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng S] [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) 
(ofAbs : R), (…
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbedding_coe`：extensionEm
bedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embedding (WithAbs.eq
uiv v.1 x)
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    (extensionEmbedding v).fieldRange ≠ Complex.ofRealHom.fieldRange := by
  contrapose hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ RingHom.mem_fieldRange_self (extensionEmbedding v) (x : v.Completion)
  rw [extensionEmbedding_coe, ← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply] at hr
  simp [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.conj_ofReal]

/-- If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is surjective. -/
/-
**NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_isComple
x** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsC
omplex v) : Function.Surjective (extensionEmbedding v)
参数：hv : IsComplex v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.fieldRange_eq_top_iff`：fieldRange_eq_top_iff {f : K ->+* L} : f.
fieldRange = ⊤ ↔ Function.Surjective f
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Complex.subfield_eq_of_closed`：Complex.subfield_eq_of_closed {K : Subfie
ld Complex} (hc : IsClosed (K : Set Complex)) : K = ofRealHom.fieldRange ∨ K = ⊤
· 使用定理 `NumberField.InfinitePlace.Completion.isClosed_image_extensionEmbedding`：
isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v))
· 使用定理 `NumberField.InfinitePlace.Completion.subfield_ne_real_of_isComplex`：subf
ield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) : (extensionE
mbedding v).fieldRange != Complex.ofRealHom.fieldRange

--- 原说明 ---
If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is s
urjective.
-/
theorem surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Surjective (extensionEmbedding v) := by
  rw [← RingHom.fieldRange_eq_top_iff]
  exact (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding v).resolve_left <|
    subfield_ne_real_of_isComplex hv

/-- If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is bijective. -/
/-
**NumberField.InfinitePlace.Completion.bijective_extensionEmbedding_of_isComplex
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsCo
mplex v) : Function.Bijective (extensionEmbedding v)
参数：hv : IsComplex v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_is
Complex`：surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : 
IsComplex v) : Function.Surjective (extensionEmbedding v)

--- 原说明 ---
If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is b
ijective.
-/
theorem bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Bijective (extensionEmbedding v) :=
  ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

/-- The ring isomorphism `v.Completion ≃+* ℂ`, when `v` is complex, given by the bijection
`v.Completion →+* ℂ`. -/
/-
**NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex** 是 Mathlib 中
的一个定义，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：ringEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) : v.C
ompletion ≃+* Complex
参数：hv : IsComplex v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.bijective_extensionEmbedding_of_isC
omplex`：bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : Is
Complex v) : Function.Bijective (extensionEmbedding v)

--- 原说明 ---
The ring isomorphism `v.Completion ≃+* ℂ`, when `v` is complex, given by the bij
ection
`v.Completion →+* ℂ`.
-/
def ringEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃+* ℂ := RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)
/-
**NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {v : NumberField.InfinitePlace K} (hv : 
v.IsComplex) (x : v.Completion),   (NumberField.InfinitePlace.Completion.ringEqu
ivComplexOfIsComplex hv) x =     (NumberField.InfinitePlace.Completion.extension
Embedding v) x
参数：hv : v.IsComplex；x : v.Completion；NumberField.InfinitePlace.Completion.ringEq
uivComplexOfIsComplex hv；NumberField.InfinitePlace.Completion.extensionEmbedding
 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ringEquivComplexOfIsComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.Completion) : ringEquivComplexOfIsComplex hv x = extensionEmbedding v x := rfl

/-- If the infinite place `v` is complex, then `v.Completion` is isometric to `ℂ`. -/
/-
**NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex** 是 Mathl
ib 中的一个定义，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometryEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
 v.Completion ≃ᵢ Complex where toEquiv
参数：hv : IsComplex v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`：isomet
ry_extensionEmbedding : Isometry (extensionEmbedding v)

--- 原说明 ---
If the infinite place `v` is complex, then `v.Completion` is isometric to `ℂ`.
-/
def isometryEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃ᵢ ℂ where
  toEquiv := ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is surjective. -/
/-
**NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v
) : Function.Surjective (extensionEmbeddingOfIsReal hv)
参数：hv : IsReal v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.fieldRange_eq_top_iff`：fieldRange_eq_top_iff {f : K ->+* L} : f.
fieldRange = ⊤ ↔ Function.Surjective f
· 使用定理 `Real.subfield_eq_of_closed`：Real.subfield_eq_of_closed {K : Subfield Rea
l} (hc : IsClosed (K : Set Real)) : K = ⊤
· 使用定理 `NumberField.InfinitePlace.Completion.isClosed_image_extensionEmbeddingOf
IsReal`：isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : Is
Real v) : IsClosed (Set.range (extensionEmbeddingOfIsReal hv))

--- 原说明 ---
If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is surj
ective.
-/
theorem surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbeddingOfIsReal hv) := by
  rw [← RingHom.fieldRange_eq_top_iff, ← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is bijective. -/
/-
**NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal** 是 
Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v)
 : Function.Bijective (extensionEmbeddingOfIsReal hv)
参数：hv : IsReal v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `NumberField.InfinitePlace.Completion.surjective_extensionEmbeddingOfIsRe
al`：surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) 
: Function.Surjective (extensionEmbeddingOfIsReal hv)

--- 原说明 ---
If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is bije
ctive.
-/
theorem bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbeddingOfIsReal hv) :=
  ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

/-- The ring isomorphism `v.Completion ≃+* ℝ`, when `v` is real, given by the bijection
`v.Completion →+* ℝ`. -/
/-
**NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal** 是 Mathlib 中的一个定义，
位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：ringEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion
 ≃+* Real
参数：hv : IsReal v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsRea
l`：bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : 
Function.Bijective (extensionEmbeddingOfIsReal hv)

--- 原说明 ---
The ring isomorphism `v.Completion ≃+* ℝ`, when `v` is real, given by the biject
ion
`v.Completion →+* ℝ`.
-/
def ringEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃+* ℝ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)
/-
**NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {v : NumberField.InfinitePlace K} (hv : 
v.IsReal) (x : v.Completion),   (NumberField.InfinitePlace.Completion.ringEquivR
ealOfIsReal hv) x =     (NumberField.InfinitePlace.Completion.extensionEmbedding
OfIsReal hv) x
参数：hv : v.IsReal；x : v.Completion；NumberField.InfinitePlace.Completion.ringEquiv
RealOfIsReal hv；NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal 
hv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ringEquivRealOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v)
    (x : v.Completion) : ringEquivRealOfIsReal hv x = extensionEmbeddingOfIsReal hv x := rfl

/-- If the infinite place `v` is real, then `v.Completion` is isometric to `ℝ`. -/
/-
**NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal** 是 Mathlib 中的一
个定义，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：isometryEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Comple
tion ≃ᵢ Real where toEquiv
参数：hv : IsReal v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
`：isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : Is
ometry (extensionEmbeddingOfIsReal hv)

--- 原说明 ---
If the infinite place `v` is real, then `v.Completion` is isometric to `ℝ`.
-/
def isometryEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃ᵢ ℝ where
  toEquiv := ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) {v}
/-
**NumberField.InfinitePlace.Completion.algebraMap_eq_coe** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：algebraMap_eq_coe (x : WithAbs v.1) : algebraMap (WithAbs v.1) w.Completio
n x = (algebraMap (WithAbs v.1) (WithAbs w.1) x)
参数：x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.Completion.algebraMap_toCompletion`：algebraMap
_toCompletion (r : R) : (algebraMap R v.Completion r).toCompletion = algebraMap 
R v.1.Completion r
· 使用定理 `UniformSpace.Completion.algebraMap_def`：algebraMap_def (r : R) : algebra
Map R (Completion A) r = (algebraMap R A r : Completion A)
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
-/
theorem algebraMap_eq_coe (x : WithAbs v.1) :
    algebraMap (WithAbs v.1) w.Completion x = (algebraMap (WithAbs v.1) (WithAbs w.1) x) := by
  apply ext
  rw [algebraMap_toCompletion]
  exact UniformSpace.Completion.algebraMap_def (WithAbs w.1) (WithAbs v.1) x

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

@[simp]
/-
**NumberField.InfinitePlace.Completion.algebraMap_coe** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace.Completion`。
形式化陈述：algebraMap_coe (x : WithAbs v.1) : algebraMap v.Completion w.Completion x 
= algebraMap (WithAbs v.1) (WithAbs w.1) x
参数：x : WithAbs v.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `WithAbs.instIsScalarTower`：∀ {S : Type u_2} [inst : Semiring S] [inst_1 
: PartialOrder S] {R : Type u_3} {T : Type u_4} [inst_2 : Semiring R]   (v : Abs
oluteValue R S)…
· 使用定理 `NumberField.InfinitePlace.Completion.algebraMap_eq_coe`：algebraMap_eq_co
e (x : WithAbs v.1) : algebraMap (WithAbs v.1) w.Completion x = (algebraMap (Wit
hAbs v.1) (WithAbs w.1) x)
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

/-- Assume that `w.Completion` forms an algebra over `v.Completion` with continuous scalar action,
such that `IsScalarTower K v.Completion w.Completion`.
If `w.embedding : L →+* ℂ` extends `v.embedding : K →+* ℂ`, then the corresponding embeddings
to completions are also extensions. -/
/-
**NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：liesOver_extensionEmbedding [ContinuousSMul v.Completion w.Completion] [Co
mplexEmbedding.LiesOver w.embedding v.embedding] : ComplexEmbedding.LiesOver (ex
tensionEmbedding w) (extensionEmbedding v) where over
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `NumberField.InfinitePlace.Completion.induction_on`：induction_on {p : v.C
ompletion -> Prop} (x : v.Completion) (hp : IsClosed {x | p x}) (ih : forall a :
 WithAbs v.1, p a) : p x
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`：isomet
ry_extensionEmbedding : Isometry (extensionEmbedding v)
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.Completion.algebraMap_coe`：algebraMap_coe (x :
 WithAbs v.1) : algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1
) (WithAbs w.1) x
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbedding_coe`：extensionEm
bedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embedding (WithAbs.eq
uiv v.1 x)
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Assume that `w.Completion` forms an algebra over `v.Completion` with continuous 
scalar action,
such that `IsScalarTower K v.Completion w.Completion`.
If `w.embedding : L →+* ℂ` extends `v.embedding : K →+* ℂ`, then the correspondi
ng embeddings
to completions are also extensions.
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
/-
**NumberField.InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：liesOver_conjugate_extensionEmbedding [ContinuousSMul v.Completion w.Compl
etion] [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding] : Complex
Embedding.LiesOver (conjugate (extensionEmbedding w)) (extensionEmbedding v) whe
re over
参数：conjugate w.embedding。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `NumberField.InfinitePlace.Completion.induction_on`：induction_on {p : v.C
ompletion -> Prop} (x : v.Completion) (hp : IsClosed {x | p x}) (ih : forall a :
 WithAbs v.1, p a) : p x
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_conj`：Continuous ⇑(starRingEnd ℂ)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `NumberField.InfinitePlace.Completion.isometry_extensionEmbedding`：isomet
ry_extensionEmbedding : Isometry (extensionEmbedding v)
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.Completion.algebraMap_coe`：algebraMap_coe (x :
 WithAbs v.1) : algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1
) (WithAbs w.1) x
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbedding_coe`：extensionEm
bedding_coe (x : WithAbs v.1) : extensionEmbedding v x = v.embedding (WithAbs.eq
uiv v.1 x)
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding_apply** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.Completion`。
形式化陈述：liesOver_extensionEmbedding_apply {φ : w.Completion ->+* Complex} [Complex
Embedding.LiesOver φ (extensionEmbedding v)] {x : v.Completion} : φ (algebraMap 
v.Completion w.Completion x) = (extensionEmbedding v) x
参数：extensionEmbedding v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liesOver_extensionEmbedding_apply {φ : w.Completion →+* ℂ}
    [ComplexEmbedding.LiesOver φ (extensionEmbedding v)] {x : v.Completion} :
    φ (algebraMap v.Completion w.Completion x) = (extensionEmbedding v) x := by
  simp_all [liesOver_iff, RingHom.ext_iff]

end Completion

namespace LiesOver

open Completion

variable [w.LiesOver v]

/-
**NumberField.InfinitePlace.LiesOver.isometry_algebraMap** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：isometry_algebraMap : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `NumberField.InfinitePlace.comp_of_comap_eq`：comp_of_comap_eq {v : Infini
tePlace k} {w : InfinitePlace K} {f : k ->+* K} (h : w.comap f = v) (x : k) : w 
(f x) = v x
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithAbs.ofAbs_algebraMap`：ofAbs_algebraMap (v : AbsoluteValue R S) (w : 
AbsoluteValue T S) (x : WithAbs v) : (algebraMap (WithAbs v) (WithAbs w) x).ofAb
s = algebraMap…
-/
theorem isometry_algebraMap : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1)) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa [WithAbs.norm_eq_apply_ofAbs] using
      WithAbs.ofAbs_algebraMap v.1 w.1 x ▸ comp_of_comap_eq (comap_eq w v) x.ofAbs

variable {v}
/-
**NumberField.InfinitePlace.LiesOver.embedding_liesOver_of_isReal** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：embedding_liesOver_of_isReal (h : v.IsReal) : ComplexEmbedding.LiesOver w.
embedding v.embedding where over
参数：h : v.IsReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.comap_embedding_of_isReal`：comap_embedding_of_
isReal (f : k ->+* K) {w : InfinitePlace K} (h : (w.comap f).IsReal) : (w.comap 
f).embedding = w.embedding.comp f
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
-/
theorem embedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver w.embedding v.embedding where
  over := (comap_eq w v ▸ comap_embedding_of_isReal _ (comap_eq w v ▸ h)).symm

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]
/-
**NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.LiesOver`。
形式化陈述：extensionEmbedding_liesOver_of_isReal (h : v.IsReal) : ComplexEmbedding.Li
esOver (extensionEmbedding w) (extensionEmbedding v)
参数：h : v.IsReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.instUniformContinuousConstSMulReal`：∀ {R : Type u_1} [inst : Com
mRing R] {T : Type u_3} [inst_1 : Field T] [inst_2 : Algebra R T] (w : AbsoluteV
alue T ℝ),   UniformContinuousCo…
· 使用定理 `NumberField.InfinitePlace.LiesOver.embedding_liesOver_of_isReal`：embeddi
ng_liesOver_of_isReal (h : v.IsReal) : ComplexEmbedding.LiesOver w.embedding v.e
mbedding where over
· 使用定理 `NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding`：liesOv
er_extensionEmbedding [ContinuousSMul v.Completion w.Completion] [ComplexEmbeddi
ng.LiesOver w.embedding v.embedding] : ComplexEmbeddin…
-/
theorem extensionEmbedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) :=
  let := embedding_liesOver_of_isReal w h; liesOver_extensionEmbedding w v

end LiesOver

end NumberField.InfinitePlace.LiesOver

