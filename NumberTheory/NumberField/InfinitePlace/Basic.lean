/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Instances.Complex

/-!
# Infinite places of a number field

This file defines the infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace`: the type of infinite places of a number field `K`.
* `NumberField.InfinitePlace.mk_eq_iff`: two complex embeddings define the same infinite place iff
  they are equal or complex conjugates.
* `NumberField.InfinitePlace.IsReal`: The predicate on infinite places saying
  that a place is real, i.e., defined by a real embedding.
* `NumberField.InfinitePlace.IsComplex`: The predicate on infinite places saying
  that a place is complex, i.e., defined by a complex embedding that is not real.
* `NumberField.InfinitePlace.mult`: the multiplicity of an infinite place, that is the number of
  distinct complex embeddings that define it. So it is equal to `1` if the place is real and `2`
  if the place is complex.
* `NumberField.InfinitePlace.prod_eq_abs_norm`: the infinite part of the product formula, that is
  for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where the product is over the infinite place `w` and
  `‖·‖_w` is the normalized absolute value for `w`.
* `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`: the degree of `K` is equal to the
  number of real places plus twice the number of complex places.
* `NumberField.InfinitePlace.denseRange_algebraMap_pi`: the image of `K` by the diagonal embedding
  into the product of its infinite completions is dense.

## Tags

number field, infinite places
-/

@[expose] public section


open scoped Finset Topology

namespace NumberField

open Fintype Module

variable (K : Type*) [Field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
/-
**NumberField.InfinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：InfinitePlace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place of a number field `K` is a place associated to a complex embed
ding.
-/
def InfinitePlace := { w : AbsoluteValue K ℝ // ∃ φ : K →+* ℂ, place φ = w }
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty (K →+* ℂ)] : Nonempty (InfinitePlace K) := Set.instNonemptyRange _

variable {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
/-
**NumberField.InfinitePlace.mk** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.InfinitePl
ace`。
形式化陈述：{K : Type u_1} → [inst : Field K] → (K →+* ℂ) → NumberField.InfinitePlace 
K
参数：K →+* ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Return the infinite place defined by a complex embedding `φ`.
-/
noncomputable def InfinitePlace.mk (φ : K →+* ℂ) : InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩

/-- A predicate singling out infinite places among the absolute values on a number field `K`. -/
/-
**NumberField.IsInfinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：IsInfinitePlace (w : AbsoluteValue K Real) : Prop
参数：w : AbsoluteValue K Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate singling out infinite places among the absolute values on a number f
ield `K`.
-/
def IsInfinitePlace (w : AbsoluteValue K ℝ) : Prop :=
  ∃ φ : K →+* ℂ, place φ = w
/-
**NumberField.InfinitePlace.isInfinitePlace** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.InfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K), Numbe
rField.IsInfinitePlace ↑v
参数：v : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma InfinitePlace.isInfinitePlace (v : InfinitePlace K) : IsInfinitePlace v.val := by
  simp [IsInfinitePlace, v.prop]
/-
**NumberField.isInfinitePlace_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：isInfinitePlace_iff (v : AbsoluteValue K Real) : IsInfinitePlace v ↔ exist
s w : InfinitePlace K, w.val = v
参数：v : AbsoluteValue K Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.isInfinitePlace`：∀ {K : Type u_1} [inst : Fiel
d K] (v : NumberField.InfinitePlace K), NumberField.IsInfinitePlace ↑v
-/
lemma isInfinitePlace_iff (v : AbsoluteValue K ℝ) :
    IsInfinitePlace v ↔ ∃ w : InfinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isInfinitePlace⟩

namespace InfinitePlace

/-
**NumberField.InfinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.InfinitePlac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (InfinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext fun x => congr_fun h x)
/-
**NumberField.InfinitePlace.coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：coe_apply (v : InfinitePlace K) (x : K) : v x = v.1 x
参数：v : InfinitePlace K；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_apply (v : InfinitePlace K) (x : K) : v x = v.1 x := rfl

@[ext]
/-
**NumberField.InfinitePlace.ext** 是 Mathlib 中的一个引理，位于命名空间 `NumberField.InfiniteP
lace`。
形式化陈述：ext (v₁ v₂ : InfinitePlace K) (h : forall k, v₁ k = v₂ k) : v₁ = v₂
参数：v₁ v₂ : InfinitePlace K；h : forall k, v₁ k = v₂ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AbsoluteValue.ext`：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x)
 -> f = g
-/
lemma ext (v₁ v₂ : InfinitePlace K) (h : ∀ k, v₁ k = v₂ k) : v₁ = v₂ :=
  Subtype.ext <| AbsoluteValue.ext h
/-
**NumberField.InfinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.InfinitePlac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZeroHomClass (InfinitePlace K) K ℝ where
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero
/-
**NumberField.InfinitePlace.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.InfinitePlac
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonnegHomClass (InfinitePlace K) K ℝ where
  apply_nonneg w _ := w.1.nonneg _

@[simp]
/-
**NumberField.InfinitePlace.apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Infinit
ePlace`。
形式化陈述：apply (φ : K ->+* Complex) (x : K) : (mk φ) x = ‖φ x‖
参数：φ : K ->+* Complex；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply (φ : K →+* ℂ) (x : K) : (mk φ) x = ‖φ x‖ := rfl

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
/-
**NumberField.InfinitePlace.embedding** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：embedding (w : InfinitePlace K) : K ->+* Complex
参数：w : InfinitePlace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an infinite place `w`, return an embedding `φ` such that `w = infinite_place
 φ` .
-/
noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ := w.2.choose

@[simp]
/-
**NumberField.InfinitePlace.mk_embedding** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：mk_embedding (w : InfinitePlace K) : mk (embedding w) = w
参数：w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w := Subtype.ext w.2.choose_spec

@[simp]
/-
**NumberField.InfinitePlace.mk_conjugate_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.InfinitePlace`。
形式化陈述：mk_conjugate_eq (φ : K ->+* Complex) : mk (ComplexEmbedding.conjugate φ) =
 mk φ
参数：φ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.apply`：apply (φ : K ->+* Complex) (x : K) : (m
k φ) x = ‖φ x‖
· 使用定理 `NumberField.ComplexEmbedding.conjugate_coe_eq`：conjugate_coe_eq (φ : K -
>+* Complex) (x : K) : (conjugate φ) x = conj (φ x)
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
-/
theorem mk_conjugate_eq (φ : K →+* ℂ) : mk (ComplexEmbedding.conjugate φ) = mk φ := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [apply, apply, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
/-
**NumberField.InfinitePlace.norm_embedding_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：norm_embedding_eq (w : InfinitePlace K) (x : K) : ‖(embedding w) x‖ = w x
参数：w : InfinitePlace K；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
-/
theorem norm_embedding_eq (w : InfinitePlace K) (x : K) :
    ‖(embedding w) x‖ = w x := by
  nth_rewrite 2 [← mk_embedding w]
  rfl

variable (K) in
/-
**NumberField.InfinitePlace.embedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.InfinitePlace`。
形式化陈述：embedding_injective : (embedding (K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem embedding_injective : (embedding (K := K)).Injective :=
  fun _ _ h ↦ by simpa using congr_arg mk h

@[simp]
/-
**NumberField.InfinitePlace.embedding_inj** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：embedding_inj {v₁ v₂ : InfinitePlace K} : v₁.embedding = v₂.embedding ↔ v₁
 = v₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.InfinitePlace.embedding_injective`：embedding_injective : (em
bedding (K
-/
theorem embedding_inj {v₁ v₂ : InfinitePlace K} : v₁.embedding = v₂.embedding ↔ v₁ = v₂ :=
  (embedding_injective _).eq_iff

variable (K) in
/-
**NumberField.InfinitePlace.conjugate_embedding_injective** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.InfinitePlace`。
形式化陈述：conjugate_embedding_injective : (fun (v : InfinitePlace K) => ComplexEmbed
ding.conjugate v.embedding).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `star_injective`：star_injective [InvolutiveStar R] : Function.Injective (
star : R -> R)
· 使用定理 `NumberField.InfinitePlace.embedding_injective`：embedding_injective : (em
bedding (K
-/
theorem conjugate_embedding_injective :
    (fun (v : InfinitePlace K) ↦ ComplexEmbedding.conjugate v.embedding).Injective :=
  star_injective.comp <| embedding_injective K

variable (K) in
/-
**NumberField.InfinitePlace.eq_of_embedding_eq_conjugate** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.InfinitePlace`。
形式化陈述：eq_of_embedding_eq_conjugate {v₁ v₂ : InfinitePlace K} (h : v₁.embedding =
 ComplexEmbedding.conjugate v₂.embedding) : v₁ = v₂
参数：h : v₁.embedding = ComplexEmbedding.conjugate v₂.embedding。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.InfinitePlace.mk_conjugate_eq`：mk_conjugate_eq (φ : K ->+* C
omplex) : mk (ComplexEmbedding.conjugate φ) = mk φ
-/
theorem eq_of_embedding_eq_conjugate {v₁ v₂ : InfinitePlace K}
    (h : v₁.embedding = ComplexEmbedding.conjugate v₂.embedding) : v₁ = v₂ := by
  rw [← mk_embedding v₁, h, mk_conjugate_eq, mk_embedding]
/-
**NumberField.InfinitePlace.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：eq_iff_eq (x : K) (r : Real) : (forall w : InfinitePlace K, w x = r) ↔ for
all φ : K ->+* Complex, ‖φ x‖ = r
参数：x : K；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x = r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ = r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
/-
**NumberField.InfinitePlace.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：le_iff_le (x : K) (r : Real) : (forall w : InfinitePlace K, w x <= r) ↔ fo
rall φ : K ->+* Complex, ‖φ x‖ <= r
参数：x : K；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_iff_le (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x ≤ r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
/-
**NumberField.InfinitePlace.pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Infin
itePlace`。
形式化陈述：pos_iff {w : InfinitePlace K} {x : K} : 0 < w x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.pos_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {
x : R}, 0 <…
-/
theorem pos_iff {w : InfinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1

@[simp]
/-
**NumberField.InfinitePlace.mk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：mk_eq_iff {φ ψ : K ->+* Complex} : mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.
conjugate φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.hasLeftInverse`：∀ {α : Sort u_1} {β : Sort u_2} [None
mpty α] {f : α → β}, Function.Injective f → Function.HasLeftInverse f
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `RingEquiv.ofLeftInverse_apply`：ofLeftInverse_apply {g : S -> R} {f : R -
>+* S} (h : Function.LeftInverse g f) (x : R) : ↑(ofLeftInverse h x) = f x
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Complex.uniformContinuous_ringHom_eq_id_or_conj`：Complex.uniformContinuo
us_ringHom_eq_id_or_conj (K : Subfield Complex) {ψ : K ->+* Complex} (hc : Unifo
rmContinuous ψ) : ψ.toFun = K.subtype…
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mk_conjugate_eq`：mk_conjugate_eq (φ : K ->+* C
omplex) : mk (ComplexEmbedding.conjugate φ) = mk φ
-/
theorem mk_eq_iff {φ ψ : K →+* ℂ} : mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ := by
  constructor
  · -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using `Complex.uniformContinuous_ringHom_eq_id_or_conj`
    intro h₀
    obtain ⟨j, hiφ⟩ := (φ.injective).hasLeftInverse
    let ι := RingEquiv.ofLeftInverse hiφ
    have hlip : LipschitzWith 1 (RingHom.comp ψ ι.symm.toRingHom) := by
      change LipschitzWith 1 (ψ ∘ ι.symm)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, dist_eq_norm, Function.comp_apply, Function.comp_apply,
        ← map_sub, ← map_sub]
      apply le_of_eq
      suffices ‖φ (ι.symm (x - y))‖ = ‖ψ (ι.symm (x - y))‖ by
        rw [← this, ← RingEquiv.ofLeftInverse_apply hiφ _, RingEquiv.apply_symm_apply ι _,
          dist_eq_norm]
        rfl
      exact congrFun (congrArg (↑) h₀) _
    cases
      Complex.uniformContinuous_ringHom_eq_id_or_conj φ.fieldRange hlip.uniformContinuous with
    | inl h =>
        left; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
    | inr h =>
        right; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
  · rintro (⟨h⟩ | ⟨h⟩)
    · exact congr_arg mk h
    · rw [← mk_conjugate_eq]
      exact congr_arg mk h

/-- An infinite place `w` of `L / K` lies over the infinite place `v` of `K` if `v` is the
restriction of `w` to `K`. -/
/-
**NumberField.InfinitePlace.LiesOver** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infi
nitePlace`。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     {L : Type u_2} →       [inst_1 :
 Field L] → [Algebra K L] → NumberField.InfinitePlace L → NumberField.InfinitePl
ace K → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place `w` of `L / K` lies over the infinite place `v` of `K` if `v` 
is the
restriction of `w` to `K`.
-/
protected abbrev LiesOver {L : Type*} [Field L] [Algebra K L]
    (w : InfinitePlace L) (v : InfinitePlace K) :=
  w.val.LiesOver v.val

/-- An infinite place is real if it is defined by a real embedding. -/
/-
**NumberField.InfinitePlace.IsReal** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infini
tePlace`。
形式化陈述：IsReal (w : InfinitePlace K) : Prop
参数：w : InfinitePlace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place is real if it is defined by a real embedding.
-/
def IsReal (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ComplexEmbedding.IsReal φ ∧ mk φ = w

/-- An infinite place is complex if it is defined by a complex (i.e. not real) embedding. -/
/-
**NumberField.InfinitePlace.IsComplex** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：IsComplex (w : InfinitePlace K) : Prop
参数：w : InfinitePlace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An infinite place is complex if it is defined by a complex (i.e. not real) embed
ding.
-/
def IsComplex (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w
/-
**NumberField.InfinitePlace.embedding_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.InfinitePlace`。
形式化陈述：embedding_mk_eq (φ : K ->+* Complex) : embedding (mk φ) = φ ∨ embedding (m
k φ) = ComplexEmbedding.conjugate φ
参数：φ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_eq_iff`：mk_eq_iff {φ ψ : K ->+* Complex} : 
mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
-/
theorem embedding_mk_eq (φ : K →+* ℂ) :
    embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ := by
  rw [@eq_comm _ _ φ, @eq_comm _ _ (ComplexEmbedding.conjugate φ), ← mk_eq_iff, mk_embedding]

@[simp]
/-
**NumberField.InfinitePlace.embedding_mk_eq_of_isReal** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：embedding_mk_eq_of_isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsRea
l φ) : embedding (mk φ) = φ
参数：h : ComplexEmbedding.IsReal φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq`：embedding_mk_eq (φ : K ->+* C
omplex) : embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
-/
theorem embedding_mk_eq_of_isReal {φ : K →+* ℂ} (h : ComplexEmbedding.IsReal φ) :
    embedding (mk φ) = φ := by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this
/-
**NumberField.InfinitePlace.isReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：isReal_iff {w : InfinitePlace K} : IsReal w ↔ ComplexEmbedding.IsReal (emb
edding w)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.embedding_mk_eq_of_isReal`：embedding_mk_eq_of_
isReal {φ : K ->+* Complex} (h : ComplexEmbedding.IsReal φ) : embedding (mk φ) =
 φ
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
-/
theorem isReal_iff {w : InfinitePlace K} :
    IsReal w ↔ ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]
/-
**NumberField.InfinitePlace.isComplex_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：isComplex_iff {w : InfinitePlace K} : IsComplex w ↔ ¬ComplexEmbedding.IsRe
al (embedding w)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.mk_eq_iff`：mk_eq_iff {φ ψ : K ->+* Complex} : 
mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.isReal_conjugate_iff`：isReal_conjugate_iff 
{φ : K ->+* Complex} : IsReal (conjugate φ) ↔ IsReal φ
-/
theorem isComplex_iff {w : InfinitePlace K} :
    IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ

@[simp]
/-
**NumberField.InfinitePlace.conjugate_embedding_eq_of_isReal** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：conjugate_embedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) : Co
mplexEmbedding.conjugate (embedding w) = embedding w
参数：h : IsReal w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
-/
theorem conjugate_embedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) :
    ComplexEmbedding.conjugate (embedding w) = embedding w :=
  ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]
/-
**NumberField.InfinitePlace.not_isReal_iff_isComplex** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：not_isReal_iff_isComplex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_isReal_iff_isComplex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w := by
  rw [isComplex_iff, isReal_iff]

@[simp]
/-
**NumberField.InfinitePlace.not_isComplex_iff_isReal** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：not_isComplex_iff_isReal {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.isComplex_iff`：isComplex_iff {w : InfinitePlac
e K} : IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w)
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_isComplex_iff_isReal {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w := by
  rw [isComplex_iff, isReal_iff, not_not]
/-
**NumberField.InfinitePlace.isReal_or_isComplex** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.InfinitePlace`。
形式化陈述：isReal_or_isComplex (w : InfinitePlace K) : IsReal w ∨ IsComplex w
参数：w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem isReal_or_isComplex (w : InfinitePlace K) : IsReal w ∨ IsComplex w := by
  rw [← not_isReal_iff_isComplex]; exact em _
/-
**NumberField.InfinitePlace.ne_of_isReal_isComplex** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.InfinitePlace`。
形式化陈述：ne_of_isReal_isComplex {w w' : InfinitePlace K} (h : IsReal w) (h' : IsCom
plex w') : w != w'
参数：h : IsReal w；h' : IsComplex w'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
-/
theorem ne_of_isReal_isComplex {w w' : InfinitePlace K} (h : IsReal w) (h' : IsComplex w') :
    w ≠ w' := fun h_eq ↦ not_isReal_iff_isComplex.mpr h' (h_eq ▸ h)

variable (K) in
/-
**NumberField.InfinitePlace.disjoint_isReal_isComplex** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：disjoint_isReal_isComplex : Disjoint {(w : InfinitePlace K) | IsReal w} {(
w : InfinitePlace K) | IsComplex w}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem disjoint_isReal_isComplex :
    Disjoint {(w : InfinitePlace K) | IsReal w} {(w : InfinitePlace K) | IsComplex w} :=
  Set.disjoint_iff.2 <| fun _ hw ↦ not_isReal_iff_isComplex.2 hw.2 hw.1

/-- The real embedding associated to a real infinite place. -/
/-
**NumberField.InfinitePlace.embedding_of_isReal** 是 Mathlib 中的一个定义，位于命名空间 `Numbe
rField.InfinitePlace`。
形式化陈述：embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) : K ->+* Real
参数：hw : IsReal w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real embedding associated to a real infinite place.
-/
noncomputable def embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) : K →+* ℝ :=
  ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)

@[simp]
/-
**NumberField.InfinitePlace.embedding_of_isReal_apply** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：embedding_of_isReal_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) : 
((embedding_of_isReal hw) x : Complex) = (embedding w) x
参数：hw : IsReal w；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.IsReal.coe_embedding_apply`：∀ {K : Type u_1
} [inst : Field K] {φ : K →+* ℂ} (hφ : NumberField.ComplexEmbedding.IsReal φ) (x
 : K),   ↑(hφ.embedding x) = φ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
-/
theorem embedding_of_isReal_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ((embedding_of_isReal hw) x : ℂ) = (embedding w) x :=
  ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x
/-
**NumberField.InfinitePlace.norm_embedding_of_isReal** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：norm_embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : K) : ‖
embedding_of_isReal hw x‖ = w x
参数：hw : IsReal w；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `NumberField.InfinitePlace.embedding_of_isReal_apply`：embedding_of_isReal
_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) : ((embedding_of_isReal hw)
 x : Complex) = (embedding w) x
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
theorem norm_embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ‖embedding_of_isReal hw x‖ = w x := by
  rw [← norm_embedding_eq, ← embedding_of_isReal_apply hw, Complex.norm_real]

@[simp]
/-
**NumberField.InfinitePlace.isReal_of_mk_isReal** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.InfinitePlace`。
形式化陈述：isReal_of_mk_isReal {φ : K ->+* Complex} (h : IsReal (mk φ)) : ComplexEmbe
dding.IsReal φ
参数：h : IsReal (mk φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
-/
theorem isReal_of_mk_isReal {φ : K →+* ℂ} (h : IsReal (mk φ)) :
    ComplexEmbedding.IsReal φ := by
  contrapose h
  rw [not_isReal_iff_isComplex]
  exact ⟨φ, h, rfl⟩
/-
**NumberField.InfinitePlace.isReal_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：isReal_mk_iff {φ : K ->+* Complex} : IsReal (mk φ) ↔ ComplexEmbedding.IsRe
al φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.isReal_of_mk_isReal`：isReal_of_mk_isReal {φ : 
K ->+* Complex} (h : IsReal (mk φ)) : ComplexEmbedding.IsReal φ
-/
lemma isReal_mk_iff {φ : K →+* ℂ} :
    IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ :=
  ⟨isReal_of_mk_isReal, fun H ↦ ⟨_, H, rfl⟩⟩
/-
**NumberField.InfinitePlace.isComplex_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：isComplex_mk_iff {φ : K ->+* Complex} : IsComplex (mk φ) ↔ ¬ ComplexEmbedd
ing.IsReal φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `NumberField.InfinitePlace.isReal_mk_iff`：isReal_mk_iff {φ : K ->+* Compl
ex} : IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ
-/
lemma isComplex_mk_iff {φ : K →+* ℂ} :
    IsComplex (mk φ) ↔ ¬ ComplexEmbedding.IsReal φ :=
  not_isReal_iff_isComplex.symm.trans isReal_mk_iff.not

@[simp]
/-
**NumberField.InfinitePlace.not_isReal_of_mk_isComplex** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.InfinitePlace`。
形式化陈述：not_isReal_of_mk_isComplex {φ : K ->+* Complex} (h : IsComplex (mk φ)) : ¬
 ComplexEmbedding.IsReal φ
参数：h : IsComplex (mk φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NumberField.InfinitePlace.isComplex_mk_iff`：isComplex_mk_iff {φ : K ->+*
 Complex} : IsComplex (mk φ) ↔ ¬ ComplexEmbedding.IsReal φ
-/
theorem not_isReal_of_mk_isComplex {φ : K →+* ℂ} (h : IsComplex (mk φ)) :
    ¬ ComplexEmbedding.IsReal φ := by rwa [← isComplex_mk_iff]

open scoped Classical in
/-- The multiplicity of an infinite place, that is the number of distinct complex embeddings that
define it, see `card_filter_mk_eq`. -/
/-
**NumberField.InfinitePlace.mult** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infinite
Place`。
形式化陈述：mult (w : InfinitePlace K) : Nat
参数：w : InfinitePlace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicity of an infinite place, that is the number of distinct complex em
beddings that
define it, see `card_filter_mk_eq`.
-/
noncomputable def mult (w : InfinitePlace K) : ℕ := if (IsReal w) then 1 else 2
/-
**NumberField.InfinitePlace.IsReal.mult_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.InfinitePlace.IsReal`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {w : NumberField.InfinitePlace K}, w.IsR
eal → w.mult = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem IsReal.mult_eq_one {w : InfinitePlace K} (hw : IsReal w) : mult w = 1 :=
  if_pos hw
/-
**NumberField.InfinitePlace.IsComplex.mult_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.InfinitePlace.IsComplex`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {w : NumberField.InfinitePlace K}, w.IsC
omplex → w.mult = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
-/
theorem IsComplex.mult_eq_two {w : InfinitePlace K} (hw : IsComplex w) : mult w = 2 :=
  if_neg (not_isReal_iff_isComplex.mpr hw)

@[simp]
/-
**NumberField.InfinitePlace.mult_isReal** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：mult_isReal (w : {w : InfinitePlace K // IsReal w}) : mult w.1 = 1
参数：w : {w : InfinitePlace K // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.IsReal.mult_eq_one`：∀ {K : Type u_1} [inst : F
ield K] {w : NumberField.InfinitePlace K}, w.IsReal → w.mult = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mult_isReal (w : {w : InfinitePlace K // IsReal w}) :
    mult w.1 = 1 :=
  w.2.mult_eq_one

@[simp]
/-
**NumberField.InfinitePlace.mult_isComplex** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.InfinitePlace`。
形式化陈述：mult_isComplex (w : {w : InfinitePlace K // IsComplex w}) : mult w.1 = 2
参数：w : {w : InfinitePlace K // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.IsComplex.mult_eq_two`：∀ {K : Type u_1} [inst 
: Field K] {w : NumberField.InfinitePlace K}, w.IsComplex → w.mult = 2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mult_isComplex (w : {w : InfinitePlace K // IsComplex w}) :
    mult w.1 = 2 :=
  w.2.mult_eq_two
/-
**NumberField.InfinitePlace.mult_pos** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Infi
nitePlace`。
形式化陈述：mult_pos {w : InfinitePlace K} : 0 < mult w
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem mult_pos {w : InfinitePlace K} : 0 < mult w := by
  rw [mult]
  split_ifs <;> norm_num

@[simp]
/-
**NumberField.InfinitePlace.mult_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：mult_ne_zero {w : InfinitePlace K} : mult w != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
-/
theorem mult_ne_zero {w : InfinitePlace K} : mult w ≠ 0 := ne_of_gt mult_pos
/-
**NumberField.InfinitePlace.mult_coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：mult_coe_ne_zero {w : InfinitePlace K} : (mult w : Real) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NumberField.InfinitePlace.mult_ne_zero`：mult_ne_zero {w : InfinitePlace 
K} : mult w != 0
-/
theorem mult_coe_ne_zero {w : InfinitePlace K} : (mult w : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr mult_ne_zero
/-
**NumberField.InfinitePlace.one_le_mult** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：one_le_mult {w : InfinitePlace K} : (1 : Real) <= mult w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
-/
theorem one_le_mult {w : InfinitePlace K} : (1 : ℝ) ≤ mult w := by
  rw [← Nat.cast_one, Nat.cast_le]
  exact mult_pos

open scoped Classical in
/-
**NumberField.InfinitePlace.card_filter_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：card_filter_mk_eq [NumberField K] (w : InfinitePlace K) : #{φ | mk φ = w} 
= mult w
参数：w : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.mk_embedding`：mk_embedding (w : InfinitePlace 
K) : mk (embedding w) = w
· 使用定理 `NumberField.InfinitePlace.mk_eq_iff`：mk_eq_iff {φ ψ : K ->+* Complex} : 
mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ
· 使用定理 `NumberField.ComplexEmbedding.conjugate.eq_1`：∀ {K : Type u_1} [inst : Fi
eld K] (φ : K →+* ℂ), NumberField.ComplexEmbedding.conjugate φ = star φ
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `InvolutiveStar.star_involutive`：∀ {R : Type u} [self : InvolutiveStar R]
, Function.Involutive star
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.ComplexEmbedding.isReal_iff`：isReal_iff {φ : K ->+* Complex}
 : IsReal φ ↔ conjugate φ = φ
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem card_filter_mk_eq [NumberField K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w := by
  conv_lhs =>
    congr; congr; ext
    rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate, star_involutive.eq_iff]
  simp_rw [Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w)),
    Finset.mem_univ, ite_true, mult]
  split_ifs with hw
  · rw [ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw), Finset.union_idempotent,
      Finset.card_singleton]
  · refine Finset.card_pair ?_
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

open scoped Classical in
/-
**NumberField.InfinitePlace.fintype** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infin
itePlace`。
形式化陈述：{K : Type u_1} → [inst : Field K] → [NumberField K] → Fintype (NumberField
.InfinitePlace K)
参数：NumberField.InfinitePlace K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable instance fintype [NumberField K] :
    Fintype (InfinitePlace K) := Set.fintypeRange _

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias NumberField.InfinitePlace.fintype := InfinitePlace.fintype

open scoped Classical in
@[to_additive]
/-
**NumberField.InfinitePlace.prod_eq_prod_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.InfinitePlace`。
形式化陈述：prod_eq_prod_mul_prod {α : Type*} [CommMonoid α] [NumberField K] (f : Infi
nitePlace K -> α) : ∏ w, f w = (∏ w : {w // IsReal w}, f w.1) * (∏ w : {w // IsC
omplex w}, f w.1)
参数：f : InfinitePlace K -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Equiv.subtypeEquivRight_apply_coe`：∀ {α : Sort u_1} {p q : α → Prop} (e 
: ∀ (x : α), p x ↔ q x) (a : { a // p a }), ↑((Equiv.subtypeEquivRight e) a) = ↑
a
· 使用定理 `Fintype.prod_subtype_mul_prod_subtype`：prod_subtype_mul_prod_subtype (p 
: ι -> Prop) (f : ι -> M) [DecidablePred p] : (∏ i : { x // p x }, f i) * ∏ i : 
{ x // ¬p x }, f i = ∏ i, f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_eq_prod_mul_prod {α : Type*} [CommMonoid α] [NumberField K] (f : InfinitePlace K → α) :
    ∏ w, f w = (∏ w : {w // IsReal w}, f w.1) * (∏ w : {w // IsComplex w}, f w.1) := by
  rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex))]
  simp [Fintype.prod_subtype_mul_prod_subtype]
/-
**NumberField.InfinitePlace.sum_mult_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：sum_mult_eq [NumberField K] : ∑ w : InfinitePlace K, mult w = Module.finra
nk Rat K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_fiberwise`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [in
st : AddCommMonoid M] [inst_1 : DecidableEq κ] [inst_2 : Fintype κ]   (s : Finse
t ι) (g : …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NumberField.InfinitePlace.card_filter_mk_eq`：card_filter_mk_eq [NumberFi
eld K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w
-/
theorem sum_mult_eq [NumberField K] :
    ∑ w : InfinitePlace K, mult w = Module.finrank ℚ K := by
  classical
  rw [← Embeddings.card K ℂ, Fintype.card, Finset.card_eq_sum_ones, ← Finset.univ.sum_fiberwise
    (fun φ => InfinitePlace.mk φ)]
  exact Finset.sum_congr rfl
    (fun _ _ => by rw [Finset.sum_const, smul_eq_mul, mul_one, card_filter_mk_eq])

set_option backward.isDefEq.respectTransparency.types false in
/-- The map from real embeddings to real infinite places as an equiv -/
/-
**NumberField.InfinitePlace.mkReal** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Infini
tePlace`。
形式化陈述：mkReal : { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } ≃ { w : Infin
itePlace K // IsReal w }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from real embeddings to real infinite places as an equiv
-/
noncomputable def mkReal :
    { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } ≃ { w : InfinitePlace K // IsReal w } := by
  refine (Equiv.ofBijective (fun φ => ⟨mk φ, ?_⟩) ⟨fun φ ψ h => ?_, fun w => ?_⟩)
  · exact ⟨φ, φ.prop, rfl⟩
  · rwa [Subtype.mk.injEq, mk_eq_iff, ComplexEmbedding.isReal_iff.mp φ.prop, or_self,
      ← Subtype.ext_iff] at h
  · exact ⟨⟨embedding w, isReal_iff.mp w.prop⟩, by simp⟩

/-- The map from nonreal embeddings to complex infinite places -/
/-
**NumberField.InfinitePlace.mkComplex** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Inf
initePlace`。
形式化陈述：mkComplex : { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ } -> { w : 
InfinitePlace K // IsComplex w }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from nonreal embeddings to complex infinite places
-/
noncomputable def mkComplex :
    { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } → { w : InfinitePlace K // IsComplex w } :=
  Subtype.map mk fun φ hφ => ⟨φ, hφ, rfl⟩

@[simp]
/-
**NumberField.InfinitePlace.mkReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：mkReal_coe (φ : { φ : K ->+* Complex // ComplexEmbedding.IsReal φ }) : (mk
Real φ : InfinitePlace K) = mk (φ : K ->+* Complex)
参数：φ : { φ : K ->+* Complex // ComplexEmbedding.IsReal φ }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkReal_coe (φ : { φ : K →+* ℂ // ComplexEmbedding.IsReal φ }) :
    (mkReal φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl

@[simp]
/-
**NumberField.InfinitePlace.mkComplex_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.InfinitePlace`。
形式化陈述：mkComplex_coe (φ : { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ }) :
 (mkComplex φ : InfinitePlace K) = mk (φ : K ->+* Complex)
参数：φ : { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkComplex_coe (φ : { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ }) :
    (mkComplex φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl

variable [NumberField K]

/-- The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`. -/
/-
**NumberField.InfinitePlace.prod_eq_abs_norm** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：prod_eq_abs_norm (x : K) : ∏ w : InfinitePlace K, w x ^ mult w = abs (Alge
bra.norm Rat x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_prod`：norm_prod (s : Finset β) (f : β -> α) : ‖∏ b in s, f b‖ = ∏ b
 in s, ‖f b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.equivRatAlgHom_apply`：∀ (R : Type u_1) (S : Type u_2) [inst : Ri
ng R] [inst_1 : Ring S] [inst_2 : Algebra ℚ R] [inst_3 : Algebra ℚ S]   (f : R →
+* S), (RingHom.eq…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.prod_fiberwise`：prod_fiberwise (s : Finset ι) (g : ι -> κ) (f : ι
 -> M) : ∏ j, ∏ i in s with g i = j, f i = ∏ i in s, f i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `NumberField.InfinitePlace.apply`：apply (φ : K ->+* Complex) (x : K) : (m
k φ) x = ‖φ x‖
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `NumberField.InfinitePlace.card_filter_mk_eq`：card_filter_mk_eq [NumberFi
eld K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.ofReal_ratCast`：∀ (q : ℚ), ↑↑q = ↑q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_prod_embeddings`：norm_eq_prod_embeddings [Algebra.IsSepa
rable K L] [IsAlgClosed E] (x : L) : algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] 
E, σ x

--- 原说明 ---
The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |no
rm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`.
-/
theorem prod_eq_abs_norm (x : K) :
    ∏ w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm ℚ x) := by
  classical
  convert! (congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
    rw [← Finset.prod_fiberwise Finset.univ mk (fun φ => ‖φ x‖)]
    have (w : InfinitePlace K) (φ) (hφ : φ ∈ ({φ | mk φ = w} : Finset _)) :
        ‖φ x‖ = w x := by rw [← (Finset.mem_filter.mp hφ).2, apply]
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]
/-
**NumberField.InfinitePlace.one_le_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：one_le_of_lt_one {w : InfinitePlace K} {a : (𝓞 K)} (ha : a != 0) (h : fora
ll ⦃z⦄, z != w -> z a < 1) : 1 <= w a
参数：𝓞 K；ha : a != 0；h : forall ⦃z⦄, z != w -> z a < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.coe_norm_int`：Algebra.coe_norm_int : (Algebra.norm Int x : Rat) 
= Algebra.norm Rat (x : K)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.one_le_abs`：one_le_abs {z : Int} (h₀ : z != 0) : 1 <= |z|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.norm_ne_zero_iff`：norm_ne_zero_iff [IsDomain R] [IsDomain S] [Mo
dule.Free R S] [Module.Finite R S] {x : S} : norm R x != 0 ↔ x != 0
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `NumberField.InfinitePlace.prod_eq_abs_norm`：prod_eq_abs_norm (x : K) : ∏
 w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x)
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `Finset.prod_lt_prod_of_nonempty`：prod_lt_prod_of_nonempty (hf : forall i
 in s, 0 < f i) (hfg : forall i in s, f i < g i) (h_ne : s.Nonempty) : ∏ i in s,
 f i < ∏ i in s, g i
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `NumberField.InfinitePlace.pos_iff`：pos_iff {w : InfinitePlace K} {x : K}
 : 0 < w x ↔ x != 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
（共 44 条，此处仅展示前 30 条）
-/
theorem one_le_of_lt_one {w : InfinitePlace K} {a : (𝓞 K)} (ha : a ≠ 0)
    (h : ∀ ⦃z⦄, z ≠ w → z a < 1) : 1 ≤ w a := by
  suffices (1 : ℝ) ≤ |Algebra.norm ℚ (a : K)| by
    contrapose! this
    rw [← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_const_one]
    refine Finset.prod_lt_prod_of_nonempty (fun _ _ ↦ ?_) (fun z _ ↦ ?_) Finset.univ_nonempty
    · exact pow_pos (pos_iff.mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)) _
    · refine pow_lt_one₀ (apply_nonneg _ _) ?_ (by rw [mult]; split_ifs <;> norm_num)
      by_cases hz : z = w
      · rwa [hz]
      · exact h hz
  rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

open scoped IntermediateField in
/-
**NumberField.InfinitePlace._root_.NumberField.is_primitive_element_of_infiniteP
lace_lt** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.is_primitive_element_of_infinitePlace_lt {x : 𝓞 K}
    {w : InfinitePlace K} (h₁ : x ≠ 0) (h₂ : ∀ ⦃w'⦄, w' ≠ w → w' x < 1)
    (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) : ℚ⟮(x : K)⟯ = ⊤ := by
  rw [Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 ≤ w x := one_le_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      simp only [RingHom.toRatAlgHom_apply] at hψ
      rw [← norm_embedding_eq, hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm, mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw, or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' ↦ hw.not_ge ?_)
      have : (embedding w x).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        have := RingHom.congr_fun h' x
        simp only [ComplexEmbedding.conjugate_coe_eq, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe] at this
        rw [this]
        exact hψ.symm
      rwa [← norm_embedding_eq, ← Complex.re_add_im (embedding w x), this, Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real] at h
  · exact fun x ↦ IsAlgClosed.splits _
/-
**NumberField.InfinitePlace._root_.NumberField.adjoin_eq_top_of_infinitePlace_lt
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NumberField.adjoin_eq_top_of_infinitePlace_lt {x : 𝓞 K} {w : InfinitePlace K}
    (h₁ : x ≠ 0) (h₂ : ∀ ⦃w'⦄, w' ≠ w → w' x < 1) (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) :
    Algebra.adjoin ℚ {(x : K)} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite ℚ _)]
  exact congr_arg IntermediateField.toSubalgebra <|
    NumberField.is_primitive_element_of_infinitePlace_lt h₁ h₂ h₃

variable (K)

open scoped Classical in
/-- The number of infinite real places of the number field `K`. -/
/-
**NumberField.InfinitePlace.nrRealPlaces** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFiel
d.InfinitePlace`。
形式化陈述：nrRealPlaces
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of infinite real places of the number field `K`.
-/
noncomputable abbrev nrRealPlaces := card { w : InfinitePlace K // IsReal w }

open scoped Classical in
/-- The number of infinite complex places of the number field `K`. -/
/-
**NumberField.InfinitePlace.nrComplexPlaces** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：nrComplexPlaces
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of infinite complex places of the number field `K`.
-/
noncomputable abbrev nrComplexPlaces := card { w : InfinitePlace K // IsComplex w }

open scoped Classical in
/-
**NumberField.InfinitePlace.card_real_embeddings** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.InfinitePlace`。
形式化陈述：card_real_embeddings : card { φ : K ->+* Complex // ComplexEmbedding.IsRea
l φ } = nrRealPlaces K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_real_embeddings :
    card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = nrRealPlaces K := Fintype.card_congr mkReal
/-
**NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：card_eq_nrRealPlaces_add_nrComplexPlaces : Fintype.card (InfinitePlace K) 
= nrRealPlaces K + nrComplexPlaces K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fintype.card_subtype_or_disjoint`：Fintype.card_subtype_or_disjoint (p q 
: α -> Prop) (h : Disjoint p q) [Fintype { x // p x }] [Fintype { x // q x }] [F
intype { x // p x ∨ q …
· 使用定理 `NumberField.InfinitePlace.disjoint_isReal_isComplex`：disjoint_isReal_isC
omplex : Disjoint {(w : InfinitePlace K) | IsReal w} {(w : InfinitePlace K) | Is
Complex w}
-/
theorem card_eq_nrRealPlaces_add_nrComplexPlaces :
    Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K := by
  classical
  convert!
    Fintype.card_subtype_or_disjoint (IsReal (K := K)) (IsComplex (K := K))
      (disjoint_isReal_isComplex K) using 1
  exact (Fintype.card_of_subtype _ (fun w ↦ ⟨fun _ ↦ isReal_or_isComplex w, fun _ ↦ by simp⟩)).symm

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-
**NumberField.InfinitePlace.card_complex_embeddings** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.InfinitePlace`。
形式化陈述：card_complex_embeddings : card { φ : K ->+* Complex // ¬ComplexEmbedding.I
sReal φ } = 2 * nrComplexPlaces K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_subtype`：Fintype.card_subtype [Fintype α] (p : α -> Prop) [
Fintype {a // p a}] [DecidablePred p] : Fintype.card { x // p x } = #{x | p x}
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `NumberField.InfinitePlace.not_isReal_of_mk_isComplex`：not_isReal_of_mk_i
sComplex {φ : K ->+* Complex} (h : IsComplex (mk φ)) : ¬ ComplexEmbedding.IsReal
 φ
· 使用定理 `NumberField.InfinitePlace.mkComplex_coe`：mkComplex_coe (φ : { φ : K ->+*
 Complex // ¬ComplexEmbedding.IsReal φ }) : (mkComplex φ : InfinitePlace K) = mk
 (φ : K ->+* Complex)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.InfinitePlace.card_filter_mk_eq`：card_filter_mk_eq [NumberFi
eld K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_fiberwise`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [in
st : AddCommMonoid M] [inst_1 : DecidableEq κ] [inst_2 : Fintype κ]   (s : Finse
t ι) (g : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem card_complex_embeddings :
    card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K := by
  suffices ∀ w : { w : InfinitePlace K // IsComplex w },
     #{φ : {φ //¬ ComplexEmbedding.IsReal φ} | mkComplex φ = w} = 2 by
    rw [Fintype.card, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
  rintro ⟨w, hw⟩
  convert! card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]
/-
**NumberField.InfinitePlace.card_add_two_mul_card_eq_rank** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.InfinitePlace`。
形式化陈述：card_add_two_mul_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = f
inrank Rat K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.card_real_embeddings`：card_real_embeddings : c
ard { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } = nrRealPlaces K
· 使用定理 `NumberField.InfinitePlace.card_complex_embeddings`：card_complex_embeddin
gs : card { φ : K ->+* Complex // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPl
aces K
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `Fintype.card_subtype_le`：Fintype.card_subtype_le [Fintype α] (p : α -> P
rop) [Fintype {a // p a}] : Fintype.card { x // p x } <= Fintype.card α
-/
theorem card_add_two_mul_card_eq_rank :
    nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K := by
  classical
  rw [← card_real_embeddings, ← card_complex_embeddings, Fintype.card_subtype_compl,
    ← Embeddings.card K ℂ, Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
The signature of the permutation on the complex embeddings of `K` defined by sending an embedding
to its conjugate has signature `(-1) ^ nrComplexPlaces K`.
-/
/-
**NumberField.InfinitePlace.ComplexEmbedding.conjugate_sign** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.InfinitePlace.ComplexEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K],   Equiv.Perm.s
ign (Function.Involutive.toPerm NumberField.ComplexEmbedding.conjugate ⋯) =     
(-1) ^ NumberField.InfinitePlace.nrComplexPlaces K
参数：K : Type u_1；Function.Involutive.toPerm NumberField.ComplexEmbedding.conjugat
e ⋯；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.involutive_conjugate`：involutive_conjugate 
: Function.Involutive (conjugate : (K ->+* Complex) -> (K ->+* Complex))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sign_of_pow_two_eq_one`：sign_of_pow_two_eq_one {σ : Perm α} (
hσ : σ ^ 2 = 1) : sign σ = (-1) ^ ((Fintype.card α - Fintype.card (Function.fixe
dPoints σ)) / 2)
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Function.Involutive.toPerm_involutive`：toPerm_involutive {f : α -> α} (h
 : Involutive f) : Involutive (h.toPerm f)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.Embeddings.card`：card : Fintype.card (K ->+* A) = finrank Ra
t K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `NumberField.InfinitePlace.card_real_embeddings`：card_real_embeddings : c
ard { φ : K ->+* Complex // ComplexEmbedding.IsReal φ } = nrRealPlaces K
· 使用定理 `Fintype.card.eq_1`：∀ (α : Type u_4) [inst : Fintype α], Fintype.card α =
 Finset.univ.card
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The signature of the permutation on the complex embeddings of `K` defined by sen
ding an embedding
to its conjugate has signature `(-1) ^ nrComplexPlaces K`.
-/
theorem ComplexEmbedding.conjugate_sign :
    (ComplexEmbedding.involutive_conjugate K).toPerm.sign = (-1) ^ nrComplexPlaces K := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one, Embeddings.card, ← card_add_two_mul_card_eq_rank,
    ← card_real_embeddings, Fintype.card, Fintype.card, Nat.add_sub_cancel_left,
    Nat.mul_div_cancel_left _ zero_lt_two]
  exact Equiv.ext (ComplexEmbedding.involutive_conjugate K).toPerm_involutive

variable {K}
/-
**NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：nrComplexPlaces_eq_zero_of_finrank_eq_one (h : finrank Rat K = 1) : nrComp
lexPlaces K = 0
参数：h : finrank Rat K = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 63 条，此处仅展示前 30 条）
-/
theorem nrComplexPlaces_eq_zero_of_finrank_eq_one (h : finrank ℚ K = 1) :
    nrComplexPlaces K = 0 := by linarith [card_add_two_mul_card_eq_rank K]
/-
**NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.InfinitePlace`。
形式化陈述：nrRealPlaces_eq_one_of_finrank_eq_one (h : finrank Rat K = 1) : nrRealPlac
es K = 1
参数：h : finrank Rat K = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one`：nrC
omplexPlaces_eq_zero_of_finrank_eq_one (h : finrank Rat K = 1) : nrComplexPlaces
 K = 0
-/
theorem nrRealPlaces_eq_one_of_finrank_eq_one (h : finrank ℚ K = 1) :
    nrRealPlaces K = 1 := by
  have := card_add_two_mul_card_eq_rank K
  rwa [nrComplexPlaces_eq_zero_of_finrank_eq_one h, h, mul_zero, add_zero] at this
/-
**NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.InfinitePlace`。
形式化陈述：nrRealPlaces_pos_of_odd_finrank (h : Odd (finrank Rat K)) : 0 < nrRealPlac
es K
参数：h : Odd (finrank Rat K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`：card_add_two_mu
l_card_eq_rank : nrRealPlaces K + 2 * nrComplexPlaces K = finrank Rat K
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
theorem nrRealPlaces_pos_of_odd_finrank (h : Odd (finrank ℚ K)) :
    0 < nrRealPlaces K := by
  refine Nat.pos_of_ne_zero ?_
  by_contra hc
  refine (Nat.not_odd_iff_even.mpr ?_) h
  rw [← card_add_two_mul_card_eq_rank, hc, zero_add]
  exact even_two_mul (nrComplexPlaces K)

namespace IsPrimitiveRoot

variable {ζ : K} {k : ℕ}

/-
**NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.InfinitePlace.IsPrimitiveRoot`。
形式化陈述：nrRealPlaces_eq_zero_of_two_lt (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k) : N
umberField.InfinitePlace.nrRealPlaces K = 0
参数：hk : 2 < k；hζ : IsPrimitiveRoot ζ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq_zero_iff`：card_eq_zero_iff : card α = 0 ↔ IsEmpty α
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `NumberField.ComplexEmbedding.conjugate_coe_eq`：conjugate_coe_eq (φ : K -
>+* Complex) (x : K) : (conjugate φ) x = conj (φ x)
· 使用定理 `NumberField.InfinitePlace.isReal_iff`：isReal_iff {w : InfinitePlace K} :
 IsReal w ↔ ComplexEmbedding.IsReal (embedding w)
· 使用定理 `Complex.norm_eq_one_of_pow_eq_one`：∀ {ζ : ℂ} {n : ℕ}, ζ ^ n = 1 → n ≠ 0 
→ ‖ζ‖ = 1
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `abs_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] {a b : α}, |a| = |b| ↔ a = b ∨ a = -b
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `Complex.abs_re_eq_norm`：abs_re_eq_norm {z : Complex} : |z.re| = ‖z‖ ↔ z.
im = 0
· 使用定理 `IsPrimitiveRoot.ne_one`：ne_one (h : IsPrimitiveRoot ζ k) (hk : 1 < k) : 
ζ != 1
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `orderOf_neg_one`：orderOf_neg_one {R} [Ring R] [Nontrivial R] : orderOf (
-1 : R) = if ringChar R = 2 then 1 else 2
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ringChar.eq_zero`：eq_zero [CharZero R] : ringChar R = 0
-/
theorem nrRealPlaces_eq_zero_of_two_lt (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k) :
    NumberField.InfinitePlace.nrRealPlaces K = 0 := by
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ ↦ ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff] at hwreal
  let f := w.embedding
  have hζ' : IsPrimitiveRoot (f ζ) k := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← NumberField.ComplexEmbedding.conjugate_coe_eq]
    congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    rw [← Complex.abs_re_eq_norm] at him
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by lia)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
    exact hζ'.ne_one (by lia) <| Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero] at hζ'
    lia

end IsPrimitiveRoot

end NumberField.InfinitePlace

/-!

## The infinite place of the rationals.

-/

namespace Rat

open NumberField

/-- The infinite place of `ℚ`, coming from the canonical map `ℚ → ℂ`. -/
/-
**Rat.infinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `Rat`。
形式化陈述：NumberField.InfinitePlace ℚ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infinite place of `ℚ`, coming from the canonical map `ℚ → ℂ`.
-/
noncomputable def infinitePlace : InfinitePlace ℚ := .mk (Rat.castHom _)

@[simp]
/-
**Rat.infinitePlace_apply** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (v : NumberField.InfinitePlace ℚ) (x : ℚ), v x = ↑|x|
参数：v : NumberField.InfinitePlace ℚ；x : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.InfinitePlace.coe_apply`：coe_apply (v : InfinitePlace K) (x 
: K) : v x = v.1 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用引理 `Complex.norm_ratCast`：norm_ratCast (q : Rat) : ‖(q : Complex)‖ = |(q : R
eal)|
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma infinitePlace_apply (v : InfinitePlace ℚ) (x : ℚ) : v x = |x| := by
  rw [NumberField.InfinitePlace.coe_apply]
  obtain ⟨_, _, rfl⟩ := v
  simp
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (InfinitePlace ℚ) where
  allEq a b := by ext; simp
/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Unique (InfinitePlace ℚ) :=
  ⟨⟨infinitePlace⟩, fun _ ↦ Subsingleton.elim _ infinitePlace⟩
/-
**Rat.isReal_infinitePlace** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：Rat.infinitePlace.IsReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isReal_infinitePlace : InfinitePlace.IsReal (infinitePlace) :=
  ⟨Rat.castHom ℂ, by ext; simp, rfl⟩

end Rat

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] {v w : InfinitePlace K}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**NumberField.InfinitePlace.map_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (x : ℚ
), v ↑x = ‖x‖
参数：v : NumberField.InfinitePlace K；x : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
· 使用引理 `Complex.norm_ratCast`：norm_ratCast (q : Rat) : ‖(q : Complex)‖ = |(q : R
eal)|
-/
protected theorem map_ratCast (v : InfinitePlace K) (x : ℚ) : v x = ‖x‖ := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**NumberField.InfinitePlace.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (n : ℕ
), v ↑n = ↑n
参数：v : NumberField.InfinitePlace K；n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_natCast (v : InfinitePlace K) (n : ℕ) : v n = n := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**NumberField.InfinitePlace.map_intCast** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.I
nfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K) (z : ℤ
), v ↑z = ‖z‖
参数：v : NumberField.InfinitePlace K；z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用引理 `Complex.norm_intCast`：norm_intCast (n : Int) : ‖(n : Complex)‖ = |(n : R
eal)|
-/
protected theorem map_intCast (v : InfinitePlace K) (z : ℤ) : v z = ‖z‖ := by
  rcases v with ⟨_, _⟩
  aesop (add simp [coe_apply])

/-- If `v` and `w` are infinite places of `K` and `v = w ^ t` for some `t` then `t = 1`. -/
/-
**NumberField.InfinitePlace.eq_one_of_rpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {v w : NumberField.InfinitePlace K} {t :
 ℝ}, (fun x => w x) ^ t = ⇑v → t = 1
参数：fun x => w x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Real.rpow_right_inj`：rpow_right_inj (hx₀ : 0 < x) (hx₁ : x != 1) : x ^ y
 = x ^ z ↔ y = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.InfinitePlace.map_natCast`：∀ {K : Type u_1} [inst : Field K]
 (v : NumberField.InfinitePlace K) (n : ℕ), v ↑n = ↑n
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x

--- 原说明 ---
If `v` and `w` are infinite places of `K` and `v = w ^ t` for some `t` then `t =
 1`.
-/
theorem eq_one_of_rpow_eq {t : ℝ} (h : (w ·) ^ t = v) : t = 1 := by
  obtain ⟨n, hn⟩ := exists_gt (1 : ℕ)
  exact ((n : ℝ).rpow_right_inj (by grind [Nat.cast_pos]) (by aesop)).1 <|
    by simpa using funext_iff.1 h n

/-- Two infinite places `v` and `w` are equal if and only if their underlying absolute values
are equivalent. -/
/-
**NumberField.InfinitePlace.eq_iff_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.InfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {v w : NumberField.InfinitePlace K}, w =
 v ↔ (↑w).IsEquiv ↑v
参数：↑w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.IsEquiv.rfl`：∀ {R : Type u_1} [inst : Semiring R] {S : Typ
e u_2} [inst_1 : Semiring S] [inst_2 : PartialOrder S]   {v : AbsoluteValue R S}
, v.IsEquiv v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AbsoluteValue.isEquiv_iff_exists_rpow_eq`：isEquiv_iff_exists_rpow_eq {v 
w : AbsoluteValue F Real} : v.IsEquiv w ↔ exists c : Real, 0 < c ∧ (v · ^ c) = w
· 使用引理 `NumberField.InfinitePlace.ext`：ext (v₁ v₂ : InfinitePlace K) (h : forall
 k, v₁ k = v₂ k) : v₁ = v₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.InfinitePlace.eq_one_of_rpow_eq`：∀ {K : Type u_1} [inst : Fi
eld K] {v w : NumberField.InfinitePlace K} {t : ℝ}, (fun x => w x) ^ t = ⇑v → t 
= 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x

--- 原说明 ---
Two infinite places `v` and `w` are equal if and only if their underlying absolu
te values
are equivalent.
-/
theorem eq_iff_isEquiv : w = v ↔ w.1.IsEquiv v.1 := by
  refine ⟨fun h ↦ h ▸ .rfl, fun h ↦ ?_⟩
  obtain ⟨t, _, h⟩ := w.1.isEquiv_iff_exists_rpow_eq.1 h
  exact ext _ _ fun k ↦ by simpa [eq_one_of_rpow_eq h, ext, coe_apply] using funext_iff.1 h k

variable (v)

/-- Infinite places are represented by non-trivial absolute values. -/
/-
**NumberField.InfinitePlace.isNontrivial** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
InfinitePlace`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (v : NumberField.InfinitePlace K), (↑v).
IsNontrivial
参数：v : NumberField.InfinitePlace K；↑v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.pos_iff`：pos_iff {w : InfinitePlace K} {x : K}
 : 0 < w x ↔ x != 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.map_natCast`：∀ {K : Type u_1} [inst : Field K]
 (v : NumberField.InfinitePlace K) (n : ℕ), v ↑n = ↑n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Infinite places are represented by non-trivial absolute values.
-/
theorem isNontrivial : v.1.IsNontrivial := by
  obtain ⟨n, hn⟩ := exists_gt (1 : ℕ)
  exact ⟨n, v.pos_iff.1 <| zero_lt_one.trans (by simpa), by simp [← coe_apply]; grind⟩

variable {v} (K)

/--
*Weak approximation for infinite places*
The number field `K` is dense when embedded diagonally in the product
`(v : InfinitePlace K) → WithAbs v.1`, in which `WithAbs v.1` represents `K` equipped with the
topology coming from the infinite place `v`.
-/
/-
**NumberField.InfinitePlace.denseRange_algebraMap_pi** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.InfinitePlace`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [NumberField K],   DenseRange ⇑(algebraM
ap K ((v : NumberField.InfinitePlace K) → WithAbs ↑v))
参数：K : Type u_1；algebraMap K ((v : NumberField.InfinitePlace K) → WithAbs ↑v)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.denseRange_algebraMap_pi`：denseRange_algebraMap_pi {ι : Ty
pe*} [Finite ι] {v : ι -> AbsoluteValue F Real} (h : forall i, (v i).IsNontrivia
l) (hv : Pairwise fun i j =>…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.InfinitePlace.isNontrivial`：∀ {K : Type u_1} [inst : Field K
] (v : NumberField.InfinitePlace K), (↑v).IsNontrivial
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NumberField.InfinitePlace.eq_iff_isEquiv`：∀ {K : Type u_1} [inst : Field
 K] {v w : NumberField.InfinitePlace K}, w = v ↔ (↑w).IsEquiv ↑v

--- 原说明 ---
*Weak approximation for infinite places*
The number field `K` is dense when embedded diagonally in the product
`(v : InfinitePlace K) → WithAbs v.1`, in which `WithAbs v.1` represents `K` equ
ipped with the
topology coming from the infinite place `v`.
-/
theorem denseRange_algebraMap_pi [NumberField K] :
    DenseRange <| algebraMap K ((v : InfinitePlace K) → WithAbs v.1) :=
  AbsoluteValue.denseRange_algebraMap_pi (fun v ↦ v.isNontrivial)
    fun _ _ h ↦ (eq_iff_isEquiv (K := K)).not.mp h

end NumberField.InfinitePlace

