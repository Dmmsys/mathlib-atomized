/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `GradedRing 𝒜` where `𝒜 : ι → Submodule R A` and
operations on them.

## Main definitions

For any `I : Ideal A`:
* `Ideal.IsHomogeneous 𝒜 I`: The property that an ideal is closed under `GradedRing.proj`.
* `HomogeneousIdeal 𝒜`: The structure extending ideals which satisfy `Ideal.IsHomogeneous`.
* `Ideal.homogeneousCore I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `Ideal.homogeneousHull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `HomogeneousIdeal.completeLattice`: `Ideal.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Ideal.homogeneousCore.gi`: `Ideal.homogeneousCore` forms a Galois insertion with coercion.
* `Ideal.homogeneousHull.gi`: `Ideal.homogeneousHull` forms a Galois insertion with coercion.

## Implementation notes

We introduce `Ideal.homogeneousCore'` earlier than might be expected so that we can get access
to `Ideal.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

@[expose] public section

open SetLike DirectSum Set
open scoped Pointwise

variable {ι σ A : Type*}

section HomogeneousDef

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

/-- An `I : Ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`. -/
/-
**Ideal.IsHomogeneous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `I : Ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.
-/
abbrev Ideal.IsHomogeneous : Prop := Submodule.IsHomogeneous I 𝒜
/-
**Ideal.IsHomogeneous.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x} : x in 
I ↔ forall i, (decompose 𝒜 x i : A) in I
参数：hI : Ideal.IsHomogeneous 𝒜 I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff`：∀ {ι : Type u_1} {M :
 Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [ins
t_2 : SetLike σ M]   [inst_3 : AddSubmo…
-/
theorem Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x} :
    x ∈ I ↔ ∀ i, (decompose 𝒜 x i : A) ∈ I :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

/-- For any `Semiring A`, we collect the homogeneous ideals of `A` into a type. -/
/-
**HomogeneousIdeal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomogeneousIdeal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `Semiring A`, we collect the homogeneous ideals of `A` into a type.
-/
abbrev HomogeneousIdeal := HomogeneousSubmodule 𝒜 𝒜

variable {𝒜}

/-- Converting a homogeneous ideal to an ideal. -/
/-
**HomogeneousIdeal.toIdeal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A
参数：I : HomogeneousIdeal 𝒜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converting a homogeneous ideal to an ideal.
-/
abbrev HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule
/-
**coe_toIdeal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubmonoidClass σ A] {𝒜 : ι → σ} [inst_3 : Decidab
leEq ι] [inst_4 : AddMonoid ι] [inst_5 : GradedRing 𝒜]   (I : HomogeneousIdeal 𝒜
), ↑I.toIdeal = ↑I
参数：I : HomogeneousIdeal 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toIdeal (I : HomogeneousIdeal 𝒜) : (I.toIdeal : Set A) = I := rfl
/-
**HomogeneousIdeal.isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) : I.toIdeal.IsHomo
geneous 𝒜
参数：I : HomogeneousIdeal 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.is_homogeneous'`：∀ {ιA : Type u_1} {ιM : Type u_2} 
{σA : Type u_3} {σM : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A
]   [inst_1 : AddCommMonoi…
-/
theorem HomogeneousIdeal.isHomogeneous (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.IsHomogeneous 𝒜 := I.is_homogeneous'
/-
**HomogeneousIdeal.toIdeal_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.toIdeal_injective : Function.Injective (HomogeneousIdeal.
toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.toSubmodule_injective`：HomogeneousSubmodule.toSubmo
dule_injective : Function.Injective (HomogeneousSubmodule.toSubmodule : Homogene
ousSubmodule 𝒜 ℳ -> Submodule A …
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem HomogeneousIdeal.toIdeal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 → Ideal A) :=
  HomogeneousSubmodule.toSubmodule_injective 𝒜 𝒜
/-
**toIdeal_le_toIdeal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : SetLike σ A]   [inst_2 : AddSubmonoidClass σ A] {𝒜 : ι → σ} [inst_3 : Decidab
leEq ι] [inst_4 : AddMonoid ι] [inst_5 : GradedRing 𝒜]   {I J : HomogeneousIdeal
 𝒜}, I.toIdeal ≤ J.toIdeal ↔ I ≤ J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toIdeal_le_toIdeal_iff {I J : HomogeneousIdeal 𝒜} :
    I.toIdeal ≤ J.toIdeal ↔ I ≤ J := Iff.rfl
/-
**HomogeneousIdeal.setLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A :=
  HomogeneousSubmodule.setLike 𝒜 𝒜
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (HomogeneousIdeal 𝒜) := .ofSetLike (HomogeneousIdeal 𝒜) A

@[ext]
/-
**HomogeneousIdeal.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal
) : I = J
参数：h : I.toIdeal = J.toIdeal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
-/
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.toIdeal_injective h
/-
**HomogeneousIdeal.ext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.ext' {I J : HomogeneousIdeal 𝒜} (h : forall i, forall x i
n 𝒜 i, x in I ↔ x in J) : I = J
参数：h : forall i, forall x in 𝒜 i, x in I ↔ x in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.ext'`：HomogeneousSubmodule.ext' {I J : HomogeneousS
ubmodule 𝒜 ℳ} (h : forall i, forall x in ℳ i, x in I ↔ x in J) : I = J
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
theorem HomogeneousIdeal.ext' {I J : HomogeneousIdeal 𝒜} (h : ∀ i, ∀ x ∈ 𝒜 i, x ∈ I ↔ x ∈ J) :
    I = J := HomogeneousSubmodule.ext' 𝒜 𝒜 h

@[simp high]
/-
**HomogeneousIdeal.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x in I.toIdeal
 ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [Semiring A]
variable [SetLike σ A] (𝒜 : ι → σ)
variable (I : Ideal A)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
/-
**Ideal.homogeneousCore'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore' (I : Ideal A) : Ideal A
参数：I : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal.
-/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span ((↑) '' (((↑) : Subtype (SetLike.IsHomogeneousElem 𝒜) → A) ⁻¹' I))
/-
**Ideal.homogeneousCore'_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : SetLike σ A] (𝒜 : ι → σ),   Monotone (Ideal.homogeneousCore' 𝒜)
参数：𝒜 : ι → σ；Ideal.homogeneousCore' 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem Ideal.homogeneousCore'_mono : Monotone (Ideal.homogeneousCore' 𝒜) :=
  fun _ _ I_le_J => Ideal.span_mono <| Set.image_mono fun _ => @I_le_J _
/-
**Ideal.homogeneousCore'_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : SetLike σ A] (𝒜 : ι → σ) (I : Ideal A),   Ideal.homogeneousCore' 𝒜 I ≤ I
参数：𝒜 : ι → σ；I : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem Ideal.homogeneousCore'_le : I.homogeneousCore' 𝒜 ≤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiring A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : Ideal A)

/-
**Ideal.isHomogeneous_iff_forall_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isHomogeneous_iff_forall_subset : I.IsHomogeneous 𝒜 ↔ forall i, (I :
 Set A) subseteq GradedRing.proj 𝒜 i ⁻¹' I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ideal.isHomogeneous_iff_forall_subset :
    I.IsHomogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' I :=
  Iff.rfl
/-
**Ideal.isHomogeneous_iff_subset_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isHomogeneous_iff_subset_iInter : I.IsHomogeneous 𝒜 ↔ (I : Set A) su
bseteq ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.subset_iInter_iff`：subset_iInter_iff {s : Set α} {t : ι -> Set α} : 
(s subseteq ⋂ i, t i) ↔ forall i, s subseteq t i
-/
theorem Ideal.isHomogeneous_iff_subset_iInter :
    I.IsHomogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_iInter_iff.symm
/-
**Ideal.mul_homogeneous_element_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A) (hx₁ : Se
tLike.IsHomogeneousElem 𝒜 x) (hx₂ : x in I) (j : ι) : GradedRing.proj 𝒜 j (r * x
) in I
参数：r x : A；hx₁ : SetLike.IsHomogeneousElem 𝒜 x；hx₂ : x in I；j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `SetLike.GradedMul.mul_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : Mul R} {inst_2 : Add ι} {A : ι → S}   [self : S
etLike.GradedMu…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `GradedRing.proj_apply`：GradedRing.proj_apply (i : ι) (r : A) : GradedRin
g.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `DirectSum.coe_of_apply`：coe_of_apply {M S : Type*} [DecidableEq ι] [AddC
ommMonoid M] [SetLike S M] [AddSubmonoidClass S M] {A : ι -> S} (i j : ι) (x : A
 i) : (of (f…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem Ideal.mul_homogeneous_element_mem_of_mem
    {I : Ideal A} (r x : A) (hx₁ : SetLike.IsHomogeneousElem 𝒜 x)
    (hx₂ : x ∈ I) (j : ι) : GradedRing.proj 𝒜 j (r * x) ∈ I := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_mul, map_sum]
  apply Ideal.sum_mem
  intro k _
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) :=
    GradedMul.mul_mem (SetLike.coe_mem _) hi
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 mem₁, coe_of_apply]
  split_ifs
  · exact I.mul_mem_left _ hx₂
  · exact I.zero_mem

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.homogeneous_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneous_span (s : Set A) (h : forall x in s, SetLike.IsHomogeneo
usElem 𝒜 x) : (Ideal.span s).IsHomogeneous 𝒜
参数：s : Set A；h : forall x in s, SetLike.IsHomogeneousElem 𝒜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Finsupp.span_eq_range_linearCombination`：span_eq_range_linearCombination
 (s : Set M) : span R s = LinearMap.range (linearCombination R ((↑) : s -> M))
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `DirectSum.decompose_sum`：decompose_sum {ι'} (s : Finset ι') (f : ι' -> M
) : decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i)
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Ideal.mul_homogeneous_element_mem_of_mem`：Ideal.mul_homogeneous_element_
mem_of_mem {I : Ideal A} (r x : A) (hx₁ : SetLike.IsHomogeneousElem 𝒜 x) (hx₂ : 
x in I) (j : ι) : GradedRing.p…
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Ideal.homogeneous_span (s : Set A) (h : ∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) :
    (Ideal.span s).IsHomogeneous 𝒜 := by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_linearCombination] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.linearCombination_apply, Finsupp.sum, decompose_sum, DFinsupp.finsetSum_apply,
    AddSubmonoidClass.coe_finsetSum]
  refine Ideal.sum_mem _ ?_
  rintro z hz1
  rw [smul_eq_mul]
  refine Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z ?_ ?_ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
  · exact Ideal.subset_span z.2

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`. -/
/-
**Ideal.homogeneousCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore : HomogeneousIdeal 𝒜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousCore' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.
-/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.homogeneous_span _ _ fun _ h => by
      have := Subtype.image_preimage_coe (Set.ofPred (SetLike.IsHomogeneousElem 𝒜)) (I : Set A)
      exact (cast congr(_ ∈ $this) h).1⟩
/-
**Ideal.homogeneousCore_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.homogeneousCore'_mono`：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u
_3} [inst : Semiring A] [inst_1 : SetLike σ A] (𝒜 : ι → σ),   Monotone (Ideal.ho
mogeneousCore' 𝒜)
-/
theorem Ideal.homogeneousCore_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneousCore'_mono 𝒜
/-
**Ideal.toIdeal_homogeneousCore_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.homogeneousCore'_le`：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3
} [inst : Semiring A] [inst_1 : SetLike σ A] (𝒜 : ι → σ) (I : Ideal A),   Ideal.
homogeneousCore…
-/
theorem Ideal.toIdeal_homogeneousCore_le : (I.homogeneousCore 𝒜).toIdeal ≤ I :=
  Ideal.homogeneousCore'_le 𝒜 I

variable {𝒜 I}
/-
**Ideal.mem_homogeneousCore_of_homogeneous_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x : A} (h : SetLike.IsHom
ogeneousElem 𝒜 x) (hmem : x in I) : x in I.homogeneousCore 𝒜
参数：h : SetLike.IsHomogeneousElem 𝒜 x；hmem : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
theorem Ideal.mem_homogeneousCore_of_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneousElem 𝒜 x)
    (hmem : x ∈ I) : x ∈ I.homogeneousCore 𝒜 :=
  Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩
/-
**Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜
) : (I.homogeneousCore 𝒜).toIdeal = I
参数：h : I.IsHomogeneous 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.homogeneousCore'_le`：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3
} [inst : Semiring A] [inst_1 : SetLike σ A] (𝒜 : ι → σ) (I : Ideal A),   Ideal.
homogeneousCore…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `SetLike.isHomogeneousElem_coe`：SetLike.isHomogeneousElem_coe {A : ι -> S
} {i} (x : A i) : SetLike.IsHomogeneousElem A (x : R)
-/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I := by
  apply le_antisymm (I.homogeneousCore'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j _ => Ideal.subset_span ⟨⟨_, isHomogeneousElem_coe _⟩, h _ hx, rfl⟩

@[simp]
/-
**HomogeneousIdeal.toIdeal_homogeneousCore_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) 
: I.toIdeal.homogeneousCore 𝒜 = I
参数：I : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self`：Ideal.IsHomogeneous
.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) : (I.homogeneousCore 𝒜)
.toIdeal = I
· 使用定理 `HomogeneousIdeal.isHomogeneous`：HomogeneousIdeal.isHomogeneous (I : Homo
geneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜
-/
theorem HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousCore 𝒜 = I := by
  ext1
  convert! Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self I.isHomogeneous

variable (𝒜 I)
/-
**Ideal.IsHomogeneous.iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toI
deal = I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsHomogeneous.toIdeal_homogeneousCore_eq_self`：Ideal.IsHomogeneous
.toIdeal_homogeneousCore_eq_self (h : I.IsHomogeneous 𝒜) : (I.homogeneousCore 𝒜)
.toIdeal = I
· 使用定理 `HomogeneousSubmodule.is_homogeneous'`：∀ {ιA : Type u_1} {ιM : Type u_2} 
{σA : Type u_3} {σM : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A
]   [inst_1 : AddCommMonoi…
-/
theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  ⟨fun hI => hI.toIdeal_homogeneousCore_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩
/-
**Ideal.IsHomogeneous.iff_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.iff_exists : I.IsHomogeneous 𝒜 ↔ exists S : Set (homog
eneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsHomogeneous.iff_eq`：Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous
 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `GaloisConnection.exists_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u 
→ ∀ (a : α), (∃ b,…
· 使用定理 `GaloisConnection.compose`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {l1 : α → β}   {u1 : 
β → α} {l2 : β…
· 使用定理 `Set.image_preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, GaloisC
onnection (Set.image f) (Set.preimage f)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((Set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `Ideal.IsHomogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `HomogeneousIdeal`. -/


section Operations

section Semiring

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

namespace Ideal.IsHomogeneous

/-
**Ideal.IsHomogeneous.bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：bot : Ideal.IsHomogeneous 𝒜 ⊥
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_zero`：decompose_zero : decompose ℳ (0 : M) = 0
· 使用定理 `DirectSum.zero_apply`：zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr => by
  simp only [Ideal.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Ideal.zero_mem
/-
**Ideal.IsHomogeneous.top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：top : Ideal.IsHomogeneous 𝒜 ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r _ => by simp only [Submodule.mem_top]

variable {𝒜}
/-
**Ideal.IsHomogeneous.inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I
 ⊓ J).IsHomogeneous 𝒜
参数：HI : I.IsHomogeneous 𝒜；HJ : J.IsHomogeneous 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊓ J).IsHomogeneous 𝒜 :=
  fun _ _ hr => ⟨HI _ hr.1, HJ _ hr.2⟩
/-
**Ideal.IsHomogeneous.sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I
 ⊔ J).IsHomogeneous 𝒜
参数：HI : I.IsHomogeneous 𝒜；HJ : J.IsHomogeneous 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsHomogeneous.iff_exists`：Ideal.IsHomogeneous.iff_exists : I.IsHom
ogeneous 𝒜 ↔ exists S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S)
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
-/
theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I ⊔ J).IsHomogeneous 𝒜 := by
  rw [iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine ⟨s₁ ∪ s₂, ?_⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm
/-
**Ideal.IsHomogeneous.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : SetLike σ A] [inst_4 : AddS
ubmonoidClass σ A] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜] {κ : Sort u_4}   {f : κ →
 Ideal A}, (∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)) → Ideal.IsHomogeneous 𝒜 (⨆ i
, f i)
参数：∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `Ideal.span_iUnion`：span_iUnion {ι} (s : ι -> Set α) : span (⋃ i, s i) = 
⨆ i, span (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem iSup {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨆ i, f i).IsHomogeneous 𝒜 := by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine ⟨⋃ i, s i, ?_⟩
  simp_rw [Set.image_iUnion, Ideal.span_iUnion]
  congr
  exact funext hs
/-
**Ideal.IsHomogeneous.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : SetLike σ A] [inst_4 : AddS
ubmonoidClass σ A] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜] {κ : Sort u_4}   {f : κ →
 Ideal A}, (∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)) → Ideal.IsHomogeneous 𝒜 (⨅ i
, f i)
参数：∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)；⨅ i, f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem iInf {κ : Sort*} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) :
    (⨅ i, f i).IsHomogeneous 𝒜 := by
  intro i x hx
  simp only [Ideal.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)
/-
**Ideal.IsHomogeneous.iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : SetLike σ A] [inst_4 : AddS
ubmonoidClass σ A] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜] {κ : Sort u_4}   {f : κ →
 Ideal A}, (∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)) → Ideal.IsHomogeneous 𝒜 (⨆ i
, f i)
参数：∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `Ideal.span_iUnion`：span_iUnion {ι} (s : ι -> Set α) : span (⋃ i, s i) = 
⨆ i, span (s i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem iSup₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨆ (i) (j), f i j).IsHomogeneous 𝒜 :=
  IsHomogeneous.iSup fun i => IsHomogeneous.iSup <| h i
/-
**Ideal.IsHomogeneous.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : SetLike σ A] [inst_4 : AddS
ubmonoidClass σ A] {𝒜 : ι → σ} [inst_5 : GradedRing 𝒜] {κ : Sort u_4}   {f : κ →
 Ideal A}, (∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)) → Ideal.IsHomogeneous 𝒜 (⨅ i
, f i)
参数：∀ (i : κ), Ideal.IsHomogeneous 𝒜 (f i)；⨅ i, f i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInf₂ {κ : Sort*} {κ' : κ → Sort*} {f : ∀ i, κ' i → Ideal A}
    (h : ∀ i j, (f i j).IsHomogeneous 𝒜) : (⨅ (i) (j), f i j).IsHomogeneous 𝒜 :=
  IsHomogeneous.iInf fun i => IsHomogeneous.iInf <| h i
/-
**Ideal.IsHomogeneous.sSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：sSup {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I) : (s
Sup ℐ).IsHomogeneous 𝒜
参数：Ideal A；h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Ideal.IsHomogeneous.iSup₂`：iSup₂ {κ : Sort*} {κ' : κ -> Sort*} {f : fora
ll i, κ' i -> Ideal A} (h : forall i j, (f i j).IsHomogeneous 𝒜) : (⨆ (i) (j), f
 i j).IsHomogen…
-/
theorem sSup {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sSup ℐ).IsHomogeneous 𝒜 := by
  rw [sSup_eq_iSup]
  exact iSup₂ h
/-
**Ideal.IsHomogeneous.sInf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsHomogeneous`。
形式化陈述：sInf {ℐ : Set (Ideal A)} (h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I) : (s
Inf ℐ).IsHomogeneous 𝒜
参数：Ideal A；h : forall I in ℐ, Ideal.IsHomogeneous 𝒜 I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
· 使用定理 `Ideal.IsHomogeneous.iInf₂`：iInf₂ {κ : Sort*} {κ' : κ -> Sort*} {f : fora
ll i, κ' i -> Ideal A} (h : forall i j, (f i j).IsHomogeneous 𝒜) : (⨅ (i) (j), f
 i j).IsHomogen…
-/
theorem sInf {ℐ : Set (Ideal A)} (h : ∀ I ∈ ℐ, Ideal.IsHomogeneous 𝒜 I) :
    (sInf ℐ).IsHomogeneous 𝒜 := by
  rw [sInf_eq_iInf]
  exact iInf₂ h

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.sup J.isHomogeneous⟩⟩
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.isHomogeneous.inf J.isHomogeneous⟩⟩
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨆ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iSup₂ fun s _ => s.isHomogeneous⟩⟩
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨅ s ∈ S, toIdeal s, Ideal.IsHomogeneous.iInf₂ fun s _ => s.isHomogeneous⟩⟩

@[simp]
/-
**HomogeneousIdeal.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ :=
  rfl

@[simp]
/-
**HomogeneousIdeal.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 :=
  rfl

@[simp]
/-
**HomogeneousIdeal.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A)
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.coe_sup`：coe_sup : ↑(p ⊔ p') = (p + p' : Set M)
-/
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I ⊔ J) = (I + J : Set A) :=
  Submodule.coe_sup _ _

@[simp]
/-
**HomogeneousIdeal.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = ↑I inter ↑J
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I ⊓ J) : Set A) = ↑I ∩ ↑J :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_top** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_bot** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_sup** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.t
oIdeal
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_inf** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.t
oIdeal
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_sSup** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s in ℐ,
 toIdeal s
参数：ℐ : Set (HomogeneousIdeal 𝒜)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sSup ℐ).toIdeal = ⨆ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_sInf** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s in ℐ,
 toIdeal s
参数：ℐ : Set (HomogeneousIdeal 𝒜)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜)) : (sInf ℐ).toIdeal = ⨅ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_iSup** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_iSup {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) : (⨆ i, s i).toIdea
l = ⨆ i, (s i).toIdeal
参数：s : κ -> HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `HomogeneousIdeal.toIdeal_sSup`：toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem toIdeal_iSup {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal := by
  rw [iSup, toIdeal_sSup, iSup_range]

@[simp]
/-
**HomogeneousIdeal.toIdeal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_iInf {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) : (⨅ i, s i).toIdea
l = ⨅ i, (s i).toIdeal
参数：s : κ -> HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `HomogeneousIdeal.toIdeal_sInf`：toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem toIdeal_iInf {κ : Sort*} (s : κ → HomogeneousIdeal 𝒜) :
    (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal := by
  rw [iInf, toIdeal_sInf, iInf_range]
/-
**HomogeneousIdeal.toIdeal_iSup** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_iSup {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) : (⨆ i, s i).toIdea
l = ⨆ i, (s i).toIdeal
参数：s : κ -> HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `HomogeneousIdeal.toIdeal_sSup`：toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
theorem toIdeal_iSup₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iSup]
/-
**HomogeneousIdeal.toIdeal_iInf** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_iInf {κ : Sort*} (s : κ -> HomogeneousIdeal 𝒜) : (⨅ i, s i).toIdea
l = ⨅ i, (s i).toIdeal
参数：s : κ -> HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `HomogeneousIdeal.toIdeal_sInf`：toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
theorem toIdeal_iInf₂ {κ : Sort*} {κ' : κ → Sort*} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal := by
  simp_rw [toIdeal_iInf]

@[simp]
/-
**HomogeneousIdeal.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤
参数：I : HomogeneousIdeal 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
-/
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  toIdeal_injective.eq_iff.symm

@[simp]
/-
**HomogeneousIdeal.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥
参数：I : HomogeneousIdeal 𝒜。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
-/
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  toIdeal_injective.eq_iff.symm
/-
**HomogeneousIdeal.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
形式化陈述：completeLattice : CompleteLattice (HomogeneousIdeal 𝒜)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
· 使用定理 `HomogeneousIdeal.toIdeal_sup`：toIdeal_sup (I J : HomogeneousIdeal 𝒜) : (
I ⊔ J).toIdeal = I.toIdeal ⊔ J.toIdeal
· 使用定理 `HomogeneousIdeal.toIdeal_inf`：toIdeal_inf (I J : HomogeneousIdeal 𝒜) : (
I ⊓ J).toIdeal = I.toIdeal ⊓ J.toIdeal
· 使用定理 `HomogeneousIdeal.toIdeal_sSup`：toIdeal_sSup (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sSup ℐ).toIdeal = ⨆ s in ℐ, toIdeal s
· 使用定理 `HomogeneousIdeal.toIdeal_sInf`：toIdeal_sInf (ℐ : Set (HomogeneousIdeal 𝒜
)) : (sInf ℐ).toIdeal = ⨅ s in ℐ, toIdeal s
· 使用定理 `HomogeneousIdeal.toIdeal_top`：toIdeal_top : (⊤ : HomogeneousIdeal 𝒜).toI
deal = (⊤ : Ideal A)
· 使用定理 `HomogeneousIdeal.toIdeal_bot`：toIdeal_bot : (⊥ : HomogeneousIdeal 𝒜).toI
deal = (⊥ : Ideal A)
-/
instance completeLattice : CompleteLattice (HomogeneousIdeal 𝒜) :=
  toIdeal_injective.completeLattice _ .rfl .rfl toIdeal_sup toIdeal_inf toIdeal_sSup toIdeal_sInf
    toIdeal_top toIdeal_bot
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(· ⊔ ·)⟩

@[simp]
/-
**HomogeneousIdeal.toIdeal_add** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.t
oIdeal
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl
/-
**HomogeneousIdeal.** 是 Mathlib 中的一个实例，位于命名空间 `HomogeneousIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomogeneousIdeal 𝒜) where default := ⊥

end HomogeneousIdeal

end Semiring

section CommSemiring

variable [CommSemiring A]
variable [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]
variable (I : Ideal A)

/-
**Ideal.IsHomogeneous.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.I
sHomogeneous 𝒜) : (I * J).IsHomogeneous 𝒜
参数：HI : I.IsHomogeneous 𝒜；HJ : J.IsHomogeneous 𝒜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.IsHomogeneous.iff_exists`：Ideal.IsHomogeneous.iff_exists : I.IsHom
ogeneous 𝒜 ↔ exists S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span ((↑) '' S)
· 使用定理 `Ideal.span_mul_span'`：span_mul_span' (S T : Set R) [(span S).IsTwoSided]
 : span S * span T = span (S * T)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_mul`：image_mul : m '' (s * t) = m '' s * m '' t
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneousSubmonoid 𝒜).subtype).symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (HomogeneousIdeal 𝒜) where
  mul I J := ⟨I.toIdeal * J.toIdeal, I.isHomogeneous.mul J.isHomogeneous⟩

@[simp]
/-
**HomogeneousIdeal.toIdeal_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) : (I * J).toIdeal 
= I.toIdeal * J.toIdeal
参数：I J : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HomogeneousIdeal.toIdeal_mul (I J : HomogeneousIdeal 𝒜) :
    (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiring

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section homogeneousCore

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

/-
**Ideal.homogeneousCore.gc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore
 𝒜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.homogeneousCore_mono`：Ideal.homogeneousCore_mono : Monotone (Ideal
.homogeneousCore 𝒜)
· 使用定理 `HomogeneousIdeal.toIdeal_homogeneousCore_eq_self`：HomogeneousIdeal.toIde
al_homogeneousCore_eq_self (I : HomogeneousIdeal 𝒜) : I.toIdeal.homogeneousCore 
𝒜 = I
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.homogeneousCore'_le`：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3
} [inst : Semiring A] [inst_1 : SetLike σ A] (𝒜 : ι → σ) (I : Ideal A),   Ideal.
homogeneousCore…
-/
theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) := fun I _ =>
  ⟨fun H => I.toIdeal_homogeneousCore_eq_self ▸ Ideal.homogeneousCore_mono 𝒜 H,
    fun H => le_trans H (Ideal.homogeneousCore'_le _ _)⟩

/-- `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` and `Ideal.homogeneousCore 𝒜` forms a Galois
coinsertion. -/
/-
**Ideal.homogeneousCore.gi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCor
e 𝒜) where choice I HI
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.homogeneousCore.gc`：Ideal.homogeneousCore.gc : GaloisConnection to
Ideal (Ideal.homogeneousCore 𝒜)

--- 原说明 ---
`toIdeal : HomogeneousIdeal 𝒜 → Ideal A` and `Ideal.homogeneousCore 𝒜` forms a G
alois
coinsertion.
-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
  choice I HI :=
    ⟨I, le_antisymm (I.toIdeal_homogeneousCore_le 𝒜) HI ▸ HomogeneousIdeal.isHomogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le _ := Ideal.homogeneousCore'_le _ _
  choice_eq I H := le_antisymm H (I.toIdeal_homogeneousCore_le _)
/-
**Ideal.homogeneousCore_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousCore_eq_sSup : I.homogeneousCore 𝒜 = sSup { J : Homogeneo
usIdeal 𝒜 | J.toIdeal <= I }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `GaloisConnection.isGreatest_u`：∀ {α : Type u} {β : Type v} [inst : Preor
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀
 {a : α}, IsGreates…
· 使用定理 `Ideal.homogeneousCore.gc`：Ideal.homogeneousCore.gc : GaloisConnection to
Ideal (Ideal.homogeneousCore 𝒜)
-/
theorem Ideal.homogeneousCore_eq_sSup :
    I.homogeneousCore 𝒜 = sSup { J : HomogeneousIdeal 𝒜 | J.toIdeal ≤ I } :=
  Eq.symm <| IsLUB.sSup_eq <| (Ideal.homogeneousCore.gc 𝒜).isGreatest_u.isLUB
/-
**Ideal.homogeneousCore'_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {A : Type u_3} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : SetLike σ A] [inst_4 : AddS
ubmonoidClass σ A] (𝒜 : ι → σ) [inst_5 : GradedRing 𝒜] (I : Ideal A),   Ideal.ho
mogeneousCore' 𝒜 I = sSup {J | Ideal.IsHomogeneous 𝒜 J ∧ J ≤ I}
参数：𝒜 : ι → σ；I : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.sSup_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeSup α] {s : S
et α} {a : α}, IsLUB s a → sSup s = a
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HomogeneousIdeal.isHomogeneous`：HomogeneousIdeal.isHomogeneous (I : Homo
geneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜
· 使用定理 `Monotone.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α}, IsGrea
test s a → Is…
· 使用定理 `GaloisConnection.isGreatest_u`：∀ {α : Type u} {β : Type v} [inst : Preor
der α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → ∀
 {a : α}, IsGreates…
· 使用定理 `Ideal.homogeneousCore.gc`：Ideal.homogeneousCore.gc : GaloisConnection to
Ideal (Ideal.homogeneousCore 𝒜)
-/
theorem Ideal.homogeneousCore'_eq_sSup :
    I.homogeneousCore' 𝒜 = sSup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J ≤ I } := by
  refine (IsLUB.sSup_eq ?_).symm
  apply IsGreatest.isLUB
  have coe_mono : Monotone (toIdeal : HomogeneousIdeal 𝒜 → Ideal A) := fun x y => id
  convert! coe_mono.map_isGreatest (Ideal.homogeneousCore.gc 𝒜).isGreatest_u using 1
  ext x
  rw [mem_image, mem_ofPred_eq]
  refine ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, ?_⟩
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact ⟨x.isHomogeneous, hx⟩

end homogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
variable (I : Ideal A)

/-- For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousHull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
/-
**Ideal.homogeneousHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull : HomogeneousIdeal 𝒜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `I : Ideal A`, not necessarily homogeneous, `I.homogeneousHull 𝒜` is
the smallest homogeneous ideal containing `I`.
-/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | ∃ (i : ι) (x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.isHomogeneousElem_coe⟩
/-
**Ideal.le_toIdeal_homogeneousHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.le_toIdeal_homogeneousHull : I <= (Ideal.homogeneousHull 𝒜 I).toIdea
l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `Ideal.sum_mem`：sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι -
> α} : (forall c in t, f c in I) -> (∑ i in t, f i) in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
-/
theorem Ideal.le_toIdeal_homogeneousHull : I ≤ (Ideal.homogeneousHull 𝒜 I).toIdeal := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine Ideal.sum_mem _ ?_
  intro j _
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩
/-
**Ideal.homogeneousHull_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
-/
theorem Ideal.homogeneousHull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  exact ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {I 𝒜}
/-
**Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜
) : (Ideal.homogeneousHull 𝒜 I).toIdeal = I
参数：h : I.IsHomogeneous 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ideal.le_toIdeal_homogeneousHull`：Ideal.le_toIdeal_homogeneousHull : I <
= (Ideal.homogeneousHull 𝒜 I).toIdeal
-/
theorem Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜) :
    (Ideal.homogeneousHull 𝒜 I).toIdeal = I := by
  apply le_antisymm _ (Ideal.le_toIdeal_homogeneousHull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
/-
**HomogeneousIdeal.homogeneousHull_toIdeal_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) 
: I.toIdeal.homogeneousHull 𝒜 = I
参数：I : HomogeneousIdeal 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.toIdeal_injective`：HomogeneousIdeal.toIdeal_injective :
 Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 -> Ideal A)
· 使用定理 `Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self`：Ideal.IsHomogeneous
.toIdeal_homogeneousHull_eq_self (h : I.IsHomogeneous 𝒜) : (Ideal.homogeneousHul
l 𝒜 I).toIdeal = I
· 使用定理 `HomogeneousIdeal.isHomogeneous`：HomogeneousIdeal.isHomogeneous (I : Homo
geneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜
-/
theorem HomogeneousIdeal.homogeneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) :
    I.toIdeal.homogeneousHull 𝒜 = I :=
  HomogeneousIdeal.toIdeal_injective <| I.isHomogeneous.toIdeal_homogeneousHull_eq_self

variable (I 𝒜)
/-
**Ideal.toIdeal_homogeneousHull_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.toIdeal_homogeneousHull_eq_iSup : (I.homogeneousHull 𝒜).toIdeal = ⨆ 
i, Ideal.span (GradedRing.proj 𝒜 i '' I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_iUnion`：span_iUnion {ι} (s : ι -> Set α) : span (⋃ i, s i) = 
⨆ i, span (s i)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ideal.toIdeal_homogeneousHull_eq_iSup :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) := by
  rw [← Ideal.span_iUnion]
  apply congr_arg Ideal.span _
  ext1
  simp only [Set.mem_iUnion, Set.mem_image, mem_ofPred_eq, GradedRing.proj_apply, SetLike.exists,
    exists_prop, SetLike.mem_coe]
/-
**Ideal.homogeneousHull_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull_eq_iSup : I.homogeneousHull 𝒜 = ⨆ i, ⟨Ideal.span (Gr
adedRing.proj 𝒜 i '' I), Ideal.homogeneous_span 𝒜 _ (by rintro _ ⟨x, -, rfl⟩ app
ly SetLike.isHomogeneousElem_coe)⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousIdeal.ext`：HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h
 : I.toIdeal = J.toIdeal) : I = J
· 使用定理 `Ideal.homogeneous_span`：Ideal.homogeneous_span (s : Set A) (h : forall x
 in s, SetLike.IsHomogeneousElem 𝒜 x) : (Ideal.span s).IsHomogeneous 𝒜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.toIdeal_homogeneousHull_eq_iSup`：Ideal.toIdeal_homogeneousHull_eq_
iSup : (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I
)
· 使用定理 `HomogeneousIdeal.toIdeal_iSup`：toIdeal_iSup {κ : Sort*} (s : κ -> Homoge
neousIdeal 𝒜) : (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal
-/
theorem Ideal.homogeneousHull_eq_iSup :
    I.homogeneousHull 𝒜 =
      ⨆ i, ⟨Ideal.span (GradedRing.proj 𝒜 i '' I), Ideal.homogeneous_span 𝒜 _ (by
        rintro _ ⟨x, -, rfl⟩
        apply SetLike.isHomogeneousElem_coe)⟩ := by
  ext1
  rw [Ideal.toIdeal_homogeneousHull_eq_iSup, toIdeal_iSup]

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiring A] [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-
**Ideal.homogeneousHull.gc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toId
eal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.le_toIdeal_homogeneousHull`：Ideal.le_toIdeal_homogeneousHull : I <
= (Ideal.homogeneousHull 𝒜 I).toIdeal
· 使用定理 `Ideal.homogeneousHull_mono`：Ideal.homogeneousHull_mono : Monotone (Ideal
.homogeneousHull 𝒜)
· 使用定理 `HomogeneousIdeal.homogeneousHull_toIdeal_eq_self`：HomogeneousIdeal.homog
eneousHull_toIdeal_eq_self (I : HomogeneousIdeal 𝒜) : I.toIdeal.homogeneousHull 
𝒜 = I
-/
theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal := fun _ J =>
  ⟨le_trans (Ideal.le_toIdeal_homogeneousHull _ _),
    fun H => J.homogeneousHull_toIdeal_eq_self ▸ Ideal.homogeneousHull_mono 𝒜 H⟩

/-- `Ideal.homogeneousHull 𝒜` and `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` form a Galois
insertion. -/
/-
**Ideal.homogeneousHull.gi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIde
al where choice I H
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.homogeneousHull.gc`：Ideal.homogeneousHull.gc : GaloisConnection (I
deal.homogeneousHull 𝒜) toIdeal

--- 原说明 ---
`Ideal.homogeneousHull 𝒜` and `toIdeal : HomogeneousIdeal 𝒜 → Ideal A` form a Ga
lois
insertion.
-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
  choice I H := ⟨I, le_antisymm H (I.le_toIdeal_homogeneousHull 𝒜) ▸ isHomogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u _ := Ideal.le_toIdeal_homogeneousHull _ _
  choice_eq I H := le_antisymm (I.le_toIdeal_homogeneousHull 𝒜) H
/-
**Ideal.homogeneousHull_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.homogeneousHull_eq_sInf (I : Ideal A) : Ideal.homogeneousHull 𝒜 I = 
sInf { J : HomogeneousIdeal 𝒜 | I <= J.toIdeal }
参数：I : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.sInf_eq`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : S
et α} {a : α}, IsGLB s a → sInf s = a
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `GaloisConnection.isLeast_l`：isLeast_l {a : α} : IsLeast { b | a <= u b }
 (l a)
· 使用定理 `Ideal.homogeneousHull.gc`：Ideal.homogeneousHull.gc : GaloisConnection (I
deal.homogeneousHull 𝒜) toIdeal
-/
theorem Ideal.homogeneousHull_eq_sInf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = sInf { J : HomogeneousIdeal 𝒜 | I ≤ J.toIdeal } :=
  Eq.symm <| IsGLB.sInf_eq <| (Ideal.homogeneousHull.gc 𝒜).isLeast_l.isGLB

end GaloisConnection

section IrrelevantIdeal

namespace HomogeneousIdeal

variable [Semiring A]
variable [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

open GradedRing SetLike.GradedMonoid DirectSum

/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by
`[AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]`, the irrelevant ideal refers to
`⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj` construction where
`ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as 0-th coordinate.
-/
/-
**HomogeneousIdeal.irrelevant** 是 Mathlib 中的一个定义，位于命名空间 `HomogeneousIdeal`。
形式化陈述：irrelevant : HomogeneousIdeal 𝒜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a graded ring `⨁ᵢ 𝒜ᵢ` graded by
`[AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]`, the irrelevant i
deal refers to
`⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj` 
construction where
`ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as 0-th co
ordinate.
-/
def irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨RingHom.ker (GradedRing.projZeroRingHom 𝒜), fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]⟩

@[inherit_doc] scoped notation 𝒜 "₊" => irrelevant 𝒜

@[simp]
/-
**HomogeneousIdeal.mem_irrelevant_iff** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdea
l`。
形式化陈述：mem_irrelevant_iff (a : A) : a in 𝒜₊ ↔ proj 𝒜 0 a = 0
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_irrelevant_iff (a : A) :
    a ∈ 𝒜₊ ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl

@[simp]
/-
**HomogeneousIdeal.toIdeal_irrelevant** 是 Mathlib 中的一个定理，位于命名空间 `HomogeneousIdea
l`。
形式化陈述：toIdeal_irrelevant : 𝒜₊.toIdeal = RingHom.ker (GradedRing.projZeroRingHom 
𝒜)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toIdeal_irrelevant :
    𝒜₊.toIdeal = RingHom.ker (GradedRing.projZeroRingHom 𝒜) :=
  rfl
/-
**HomogeneousIdeal.mem_irrelevant_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousI
deal`。
形式化陈述：mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x in 𝒜 i) : x in 
𝒜₊
参数：hi : 0 < i；hx : x in 𝒜 i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousIdeal.mem_irrelevant_iff`：mem_irrelevant_iff (a : A) : a in 𝒜
₊ ↔ proj 𝒜 0 a = 0
· 使用定理 `GradedRing.proj_apply`：GradedRing.proj_apply (i : ι) (r : A) : GradedRin
g.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
-/
lemma mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x ∈ 𝒜 i) : x ∈ 𝒜₊ := by
  rw [mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx,
    DirectSum.of_eq_of_ne _ _ _ (by aesop), ZeroMemClass.coe_zero]

set_option backward.isDefEq.respectTransparency false in
/-- `irrelevant 𝒜 = ⨁_{i>0} 𝒜ᵢ` -/
/-
**HomogeneousIdeal.irrelevant_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdea
l`。
形式化陈述：irrelevant_eq_iSup : 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GradedRing.projZeroRingHom_apply`：∀ {ι : Type u_1} {A : Type u_3} {σ : T
ype u_4} [inst : Semiring A] [inst_1 : DecidableEq ι] [inst_2 : AddCommMonoid ι]
   [inst_3 : PartialOr…
· 使用定理 `AddSubmonoid.mem_iSup_of_mem`：∀ {M : Type u_1} [inst : AddZeroClass M] {
ι : Sort u_4} {S : ι → AddSubmonoid M} (i : ι) {x : M}, x ∈ S i → x ∈ iSup S
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用引理 `HomogeneousIdeal.mem_irrelevant_of_mem`：mem_irrelevant_of_mem {x : A} {i
 : ι} (hi : 0 < i) (hx : x in 𝒜 i) : x in 𝒜₊

--- 原说明 ---
`irrelevant 𝒜 = ⨁_{i>0} 𝒜ᵢ`
-/
lemma irrelevant_eq_iSup : 𝒜₊.toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i) := by
  refine le_antisymm (fun x hx ↦ ?_) <| iSup₂_le fun i hi x hx ↦ mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj ↦ ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
  · exact AddSubmonoid.mem_iSup_of_mem j <| AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀) <|
      Subtype.prop _

open AddSubmonoid Set in
/-
**HomogeneousIdeal.irrelevant_eq_closure** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousI
deal`。
形式化陈述：irrelevant_eq_closure : 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousIdeal.irrelevant_eq_iSup`：irrelevant_eq_iSup : 𝒜₊.toAddSubmon
oid = ⨆ i > 0, .ofClass (𝒜 i)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma irrelevant_eq_closure : 𝒜₊.toAddSubmonoid = .closure (⋃ i > 0, 𝒜 i) := by
  rw [irrelevant_eq_iSup]
  exact le_antisymm (iSup_le fun i ↦ iSup_le fun hi _ hx ↦ subset_closure <| mem_biUnion hi hx) <|
    closure_le.mpr <| iUnion_subset fun i ↦ iUnion_subset fun hi ↦ le_biSup (ofClass <| 𝒜 ·) hi

open AddSubmonoid Set in
/-
**HomogeneousIdeal.irrelevant_eq_span** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdea
l`。
形式化陈述：irrelevant_eq_span : 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `HomogeneousIdeal.irrelevant_eq_closure`：irrelevant_eq_closure : 𝒜₊.toAdd
Submonoid = .closure (⋃ i > 0, 𝒜 i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用引理 `HomogeneousIdeal.mem_irrelevant_of_mem`：mem_irrelevant_of_mem {x : A} {i
 : ι} (hi : 0 < i) (hx : x in 𝒜 i) : x in 𝒜₊
-/
lemma irrelevant_eq_span : 𝒜₊.toIdeal = .span (⋃ i > 0, 𝒜 i) :=
  le_antisymm ((irrelevant_eq_closure 𝒜).trans_le <| closure_le.mpr Ideal.subset_span) <|
    Ideal.span_le.mpr <| iUnion_subset fun _ ↦ iUnion_subset fun hi _ hx ↦
    mem_irrelevant_of_mem _ hi hx
/-
**HomogeneousIdeal.toAddSubmonoid_irrelevant_le** 是 Mathlib 中的一个引理，位于命名空间 `Homog
eneousIdeal`。
形式化陈述：toAddSubmonoid_irrelevant_le {P : AddSubmonoid A} : 𝒜₊.toAddSubmonoid <= P
 ↔ forall i > 0, .ofClass (𝒜 i) <= P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomogeneousIdeal.irrelevant_eq_iSup`：irrelevant_eq_iSup : 𝒜₊.toAddSubmon
oid = ⨆ i > 0, .ofClass (𝒜 i)
· 使用定理 `iSup₂_le_iff`：iSup₂_le_iff {f : forall i, κ i -> α} : ⨆ (i) (j), f i j <
= a ↔ forall i j, f i j <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toAddSubmonoid_irrelevant_le {P : AddSubmonoid A} :
    𝒜₊.toAddSubmonoid ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P := by
  rw [irrelevant_eq_iSup, iSup₂_le_iff]
/-
**HomogeneousIdeal.toIdeal_irrelevant_le** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousI
deal`。
形式化陈述：toIdeal_irrelevant_le {I : Ideal A} : 𝒜₊.toIdeal <= I ↔ forall i > 0, .ofC
lass (𝒜 i) <= I.toAddSubmonoid
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousIdeal.toAddSubmonoid_irrelevant_le`：toAddSubmonoid_irrelevant
_le {P : AddSubmonoid A} : 𝒜₊.toAddSubmonoid <= P ↔ forall i > 0, .ofClass (𝒜 i)
 <= P
-/
lemma toIdeal_irrelevant_le {I : Ideal A} :
    𝒜₊.toIdeal ≤ I ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ I.toAddSubmonoid :=
  toAddSubmonoid_irrelevant_le _
/-
**HomogeneousIdeal.irrelevant_le** 是 Mathlib 中的一个引理，位于命名空间 `HomogeneousIdeal`。
形式化陈述：irrelevant_le {P : HomogeneousIdeal 𝒜} : 𝒜₊ <= P ↔ forall i > 0, .ofClass 
(𝒜 i) <= P.toAddSubmonoid
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomogeneousIdeal.toIdeal_irrelevant_le`：toIdeal_irrelevant_le {I : Ideal
 A} : 𝒜₊.toIdeal <= I ↔ forall i > 0, .ofClass (𝒜 i) <= I.toAddSubmonoid
-/
lemma irrelevant_le {P : HomogeneousIdeal 𝒜} :
    𝒜₊ ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P.toAddSubmonoid :=
  toIdeal_irrelevant_le _

end HomogeneousIdeal

end IrrelevantIdeal

