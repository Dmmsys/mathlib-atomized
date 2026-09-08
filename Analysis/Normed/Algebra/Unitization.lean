/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Unitization norms

Given a not-necessarily-unital normed `𝕜`-algebra `A`, it is frequently of interest to equip its
`Unitization` with a norm which simultaneously makes it into a normed algebra and also satisfies
two properties:

- `‖1‖ = 1` (i.e., `NormOneClass`)
- The embedding of `A` in `Unitization 𝕜 A` is an isometry. (i.e., `Isometry Unitization.inr`)

One way to do this is to pull back the norm from `WithLp 1 (𝕜 × A)`, that is,
`‖(k, a)‖ = ‖k‖ + ‖a‖` using `Unitization.addEquiv` (i.e., the identity map).
This is implemented for the type synonym `WithLp 1 (Unitization 𝕜 A)` in
`WithLp.instUnitizationNormedAddCommGroup`, and it is shown there that this is a Banach algebra.
However, when the norm on `A` is *regular* (i.e., `ContinuousLinearMap.mul` is an isometry), there
is another natural choice: the pullback of the norm on `𝕜 × (A →L[𝕜] A)` under the map
`(k, a) ↦ (k, k • 1 + ContinuousLinearMap.mul 𝕜 A a)`. It turns out that among all norms on the
unitization satisfying the properties specified above, the norm inherited from
`WithLp 1 (𝕜 × A)` is maximal, and the norm inherited from this pullback is minimal.
Of course, this means that `WithLp.equiv : WithLp 1 (Unitization 𝕜 A) → Unitization 𝕜 A` can be
upgraded to a continuous linear equivalence (when `𝕜` and `A` are complete).

structure on `Unitization 𝕜 A` using the pullback described above. The reason for choosing this norm
is that for a C⋆-algebra `A` its norm is always regular, and the pullback norm on `Unitization 𝕜 A`
is then also a C⋆-norm.

## Main definitions

- `Unitization.splitMul : Unitization 𝕜 A →ₐ[𝕜] (𝕜 × (A →L[𝕜] A))`: The first coordinate of this
  map is just `Unitization.fst` and the second is the `Unitization.lift` of the left regular
  representation of `A` (i.e., `NonUnitalAlgHom.Lmul`). We use this map to pull back the
  `NormedRing` and `NormedAlgebra` structures.

## Main statements

- `Unitization.instNormedRing`, `Unitization.instNormedAlgebra`, `Unitization.instNormOneClass`,
  `Unitization.instCompleteSpace`: when `A` is a non-unital Banach `𝕜`-algebra with a regular norm,
  then `Unitization 𝕜 A` is a unital Banach `𝕜`-algebra with `‖1‖ = 1`.
- `Unitization.norm_inr`, `Unitization.isometry_inr`: the natural inclusion `A → Unitization 𝕜 A`
  is an isometry, or in mathematical parlance, the norm on `A` extends to a norm on
  `Unitization 𝕜 A`.

## Implementation details

We ensure that the uniform structure, and hence also the topological structure, is definitionally
equal to the pullback of `instUniformSpaceProd` along `Unitization.addEquiv` (this is essentially
viewing `Unitization 𝕜 A` as `𝕜 × A`) by means of forgetful inheritance. The same is true of the
bornology.

-/

@[expose] public section

suppress_compilation

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

open ContinuousLinearMap

namespace Unitization

/-- Given `(k, a) : Unitization 𝕜 A`, the second coordinate of `Unitization.splitMul (k, a)` is
the natural representation of `Unitization 𝕜 A` on `A` given by multiplication on the left in
`A →L[𝕜] A`; note that this is not just `NonUnitalAlgHom.Lmul` for a few reasons: (a) that would
either be `A` acting on `A`, or (b) `Unitization 𝕜 A` acting on `Unitization 𝕜 A`, and (c) that's a
`NonUnitalAlgHom` but here we need an `AlgHom`. In addition, the first coordinate of
`Unitization.splitMul (k, a)` should just be `k`. See `Unitization.splitMul_apply` also. -/
/-
**Unitization.splitMul** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：splitMul : Unitization 𝕜 A ->ₐ[𝕜] 𝕜 × (A ->L[𝕜] A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `(k, a) : Unitization 𝕜 A`, the second coordinate of `Unitization.splitMul
 (k, a)` is
the natural representation of `Unitization 𝕜 A` on `A` given by multiplication o
n the left in
`A →L[𝕜] A`; note that this is not just `NonUnitalAlgHom.Lmul` for a few reasons
: (a) that would
either be `A` acting on `A`, or (b) `Unitization 𝕜 A` acting on `Unitization 𝕜 A
`, and (c) that's a
`NonUnitalAlgHom` but here we need an `AlgHom`. In addition, the first coordinat
e of
`Unitization.splitMul (k, a)` should just be `k`. See `Unitization.splitMul_appl
y` also.
-/
def splitMul : Unitization 𝕜 A →ₐ[𝕜] 𝕜 × (A →L[𝕜] A) :=
  (lift 0).prod (lift <| NonUnitalAlgHom.Lmul 𝕜 A)

variable {𝕜 A}

@[simp]
/-
**Unitization.splitMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：splitMul_apply (x : Unitization 𝕜 A) : splitMul 𝕜 A x = (x.fst, algebraMap
 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd)
参数：x : Unitization 𝕜 A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem splitMul_apply (x : Unitization 𝕜 A) :
    splitMul 𝕜 A x = (x.fst, algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd) :=
  show (x.fst + 0, _) = (x.fst, _) by rw [add_zero]; rfl

/-- this lemma establishes that if `ContinuousLinearMap.mul 𝕜 A` is injective, then so is
`Unitization.splitMul 𝕜 A`. When `A` is a `RegularNormedAlgebra`, then
`ContinuousLinearMap.mul 𝕜 A` is an isometry, and is therefore automatically injective. -/
/-
**Unitization.splitMul_injective_of_clm_mul_injective** 是 Mathlib 中的一个定理，位于命名空间 
`Unitization`。
形式化陈述：splitMul_injective_of_clm_mul_injective (h : Function.Injective (mul 𝕜 A))
 : Function.Injective (splitMul 𝕜 A)
参数：h : Function.Injective (mul 𝕜 A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Unitization.ind`：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitiz
ation R A -> Prop} (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitiz
ation…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unitization.splitMul_apply`：splitMul_apply (x : Unitization 𝕜 A) : split
Mul 𝕜 A x = (x.fst, algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
this lemma establishes that if `ContinuousLinearMap.mul 𝕜 A` is injective, then 
so is
`Unitization.splitMul 𝕜 A`. When `A` is a `RegularNormedAlgebra`, then
`ContinuousLinearMap.mul 𝕜 A` is an isometry, and is therefore automatically inj
ective.
-/
theorem splitMul_injective_of_clm_mul_injective
    (h : Function.Injective (mul 𝕜 A)) :
    Function.Injective (splitMul 𝕜 A) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x
  rw [map_add] at hx
  simp only [splitMul_apply, fst_inl, snd_inl, map_zero, add_zero, fst_inr, snd_inr,
    zero_add, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
  obtain ⟨rfl, hx⟩ := hx
  simp only [map_zero, zero_add, inl_zero] at hx ⊢
  rw [← map_zero (mul 𝕜 A)] at hx
  rw [h hx, inr_zero]

variable [RegularNormedAlgebra 𝕜 A]
variable (𝕜 A)

/-- In a `RegularNormedAlgebra`, the map `Unitization.splitMul 𝕜 A` is injective.
We will use this to pull back the norm from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A`. -/
/-
**Unitization.splitMul_injective** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：splitMul_injective : Function.Injective (splitMul 𝕜 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.splitMul_injective_of_clm_mul_injective`：splitMul_injective_
of_clm_mul_injective (h : Function.Injective (mul 𝕜 A)) : Function.Injective (sp
litMul 𝕜 A)
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContinuousLinearMap.isometry_mul`：isometry_mul : Isometry (mul 𝕜 R)

--- 原说明 ---
In a `RegularNormedAlgebra`, the map `Unitization.splitMul 𝕜 A` is injective.
We will use this to pull back the norm from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 
A`.
-/
theorem splitMul_injective : Function.Injective (splitMul 𝕜 A) :=
  splitMul_injective_of_clm_mul_injective (isometry_mul 𝕜 A).injective

variable {𝕜 A}

section Aux

/-- Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This does not give us the desired topology,
uniformity or bornology on `Unitization 𝕜 A` (which we want to agree with `Prod`), so we only use
it as a local instance to build the real one. -/
/-
**Unitization.normedRingAux** 是 Mathlib 中的一个缩写定义，位于命名空间 `Unitization`。
形式化陈述：normedRingAux : NormedRing (Unitization 𝕜 A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.splitMul_injective`：splitMul_injective : Function.Injective 
(splitMul 𝕜 A)

--- 原说明 ---
Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` 
using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This does not give us the desir
ed topology,
uniformity or bornology on `Unitization 𝕜 A` (which we want to agree with `Prod`
), so we only use
it as a local instance to build the real one.
-/
noncomputable abbrev normedRingAux : NormedRing (Unitization 𝕜 A) :=
  NormedRing.induced (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A) (splitMul_injective 𝕜 A)

attribute [local instance] Unitization.normedRingAux

/-- Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This uses the wrong `NormedRing` instance (i.e.,
`Unitization.normedRingAux`), so we only use it as a local instance to build the real one. -/
/-
**Unitization.normedAlgebraAux** 是 Mathlib 中的一个缩写定义，位于命名空间 `Unitization`。
形式化陈述：normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 
A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. This uses the wrong `NormedRing
` instance (i.e.,
`Unitization.normedRingAux`), so we only use it as a local instance to build the
 real one.
-/
noncomputable abbrev normedAlgebraAux : NormedAlgebra 𝕜 (Unitization 𝕜 A) :=
  NormedAlgebra.induced 𝕜 (Unitization 𝕜 A) (𝕜 × (A →L[𝕜] A)) (splitMul 𝕜 A)

attribute [local instance] Unitization.normedAlgebraAux
/-
**Unitization.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜 A x‖
参数：x : Unitization 𝕜 A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜 A x‖ :=
  rfl
/-
**Unitization.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：nnnorm_def (x : Unitization 𝕜 A) : ‖x‖₊ = ‖splitMul 𝕜 A x‖₊
参数：x : Unitization 𝕜 A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_def (x : Unitization 𝕜 A) : ‖x‖₊ = ‖splitMul 𝕜 A x‖₊ :=
  rfl

/-- This is often the more useful lemma to rewrite the norm as opposed to `Unitization.norm_def`. -/
/-
**Unitization.norm_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜
] A) x.fst + mul 𝕜 A x.snd‖
参数：x : Unitization 𝕜 A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.norm_def`：norm_def (x : Unitization 𝕜 A) : ‖x‖ = ‖splitMul 𝕜
 A x‖
· 使用定理 `Unitization.splitMul_apply`：splitMul_apply (x : Unitization 𝕜 A) : split
Mul 𝕜 A x = (x.fst, algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd)
· 使用引理 `Prod.norm_def`：Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖

--- 原说明 ---
This is often the more useful lemma to rewrite the norm as opposed to `Unitizati
on.norm_def`.
-/
theorem norm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖ = ‖x.fst‖ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖ := by
  rw [norm_def, splitMul_apply, Prod.norm_def]

/-- This is often the more useful lemma to rewrite the norm as opposed to
`Unitization.nnnorm_def`. -/
/-
**Unitization.nnnorm_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：nnnorm_eq_sup (x : Unitization 𝕜 A) : ‖x‖₊ = ‖x.fst‖₊ ⊔ ‖algebraMap 𝕜 (A -
>L[𝕜] A) x.fst + mul 𝕜 A x.snd‖₊
参数：x : Unitization 𝕜 A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Unitization.norm_eq_sup`：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fs
t‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖

--- 原说明 ---
This is often the more useful lemma to rewrite the norm as opposed to
`Unitization.nnnorm_def`.
-/
theorem nnnorm_eq_sup (x : Unitization 𝕜 A) :
    ‖x‖₊ = ‖x.fst‖₊ ⊔ ‖algebraMap 𝕜 (A →L[𝕜] A) x.fst + mul 𝕜 A x.snd‖₊ :=
  NNReal.eq <| norm_eq_sup x
/-
**Unitization.lipschitzWith_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：lipschitzWith_addEquiv : LipschitzWith 2 (Unitization.addEquiv 𝕜 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.toNNReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).to
NNReal = OfNat.ofNat n
· 使用定理 `AddMonoidHomClass.lipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2} {F
 : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [in
st_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Unitization.norm_eq_sup`：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fs
t‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖
· 使用引理 `Prod.norm_def`：Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
（共 53 条，此处仅展示前 30 条）
-/
theorem lipschitzWith_addEquiv :
    LipschitzWith 2 (Unitization.addEquiv 𝕜 A) := by
  rw [← Real.toNNReal_ofNat]
  refine AddMonoidHomClass.lipschitz_of_bound (Unitization.addEquiv 𝕜 A) 2 fun x => ?_
  rw [norm_eq_sup, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    rw [two_mul]
    calc
      ‖x.snd‖ = ‖mul 𝕜 A x.snd‖ :=
        .symm <| (isometry_mul 𝕜 A).norm_map_of_map_zero (map_zero _) _
      _ ≤ ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ + ‖x.fst‖ := by
        simpa only [add_comm _ (mul 𝕜 A x.snd), norm_algebraMap'] using
          norm_le_add_norm_add (mul 𝕜 A x.snd) (algebraMap 𝕜 _ x.fst)
      _ ≤ _ := add_le_add le_sup_right le_sup_left
/-
**Unitization.antilipschitzWith_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`
。
形式化陈述：antilipschitzWith_addEquiv : AntilipschitzWith 2 (addEquiv 𝕜 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.antilipschitz_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2
} {F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]  
 [inst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.norm_eq_sup`：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fs
t‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖
· 使用引理 `Prod.norm_def`：Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖
· 使用定理 `NNReal.coe_two`：↑2 = 2
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
（共 50 条，此处仅展示前 30 条）
-/
theorem antilipschitzWith_addEquiv :
    AntilipschitzWith 2 (addEquiv 𝕜 A) := by
  refine AddMonoidHomClass.antilipschitz_of_bound (addEquiv 𝕜 A) fun x => ?_
  rw [norm_eq_sup, Prod.norm_def, NNReal.coe_two]
  refine max_le ?_ ?_
  · rw [mul_max_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2)]
    exact le_max_of_le_left ((le_add_of_nonneg_left (norm_nonneg _)).trans_eq (two_mul _).symm)
  · nontriviality A
    calc
      ‖algebraMap 𝕜 _ x.fst + mul 𝕜 A x.snd‖ ≤ ‖algebraMap 𝕜 _ x.fst‖ + ‖mul 𝕜 A x.snd‖ :=
        norm_add_le _ _
      _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [norm_algebraMap', (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 A)).mp (isometry_mul 𝕜 A)]
      _ ≤ _ := (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm

open Bornology Filter
open scoped Uniformity Topology
/-
**Unitization.uniformity_eq_aux** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：uniformity_eq_aux : 𝓤[instUniformSpaceProd.comap <| addEquiv 𝕜 A] = 𝓤 (Uni
tization 𝕜 A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Unitization.antilipschitzWith_addEquiv`：antilipschitzWith_addEquiv : Ant
ilipschitzWith 2 (addEquiv 𝕜 A)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Unitization.lipschitzWith_addEquiv`：lipschitzWith_addEquiv : LipschitzWi
th 2 (Unitization.addEquiv 𝕜 A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUniformInducing.comap_uniformity`：∀ {α : Type ua} {β : Type ub} [inst 
: UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformInducing f →
 Filter.comap (fun x => …
-/
theorem uniformity_eq_aux :
    𝓤[instUniformSpaceProd.comap <| addEquiv 𝕜 A] = 𝓤 (Unitization 𝕜 A) := by
  have key : IsUniformInducing (addEquiv 𝕜 A) :=
    antilipschitzWith_addEquiv.isUniformInducing lipschitzWith_addEquiv.uniformContinuous
  rw [← key.comap_uniformity]
  rfl
/-
**Unitization.cobounded_eq_aux** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：cobounded_eq_aux : @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobo
unded (Unitization 𝕜 A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LipschitzWith.comap_cobounded_le`：comap_cobounded_le (hf : LipschitzWith
 K f) : comap f (Bornology.cobounded β) <= Bornology.cobounded α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Unitization.lipschitzWith_addEquiv`：lipschitzWith_addEquiv : LipschitzWi
th 2 (Unitization.addEquiv 𝕜 A)
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `AntilipschitzWith.tendsto_cobounded`：tendsto_cobounded (hf : Antilipschi
tzWith K f) : Tendsto f (cobounded α) (cobounded β)
· 使用定理 `Unitization.antilipschitzWith_addEquiv`：antilipschitzWith_addEquiv : Ant
ilipschitzWith 2 (addEquiv 𝕜 A)
-/
theorem cobounded_eq_aux :
    @cobounded _ (Bornology.induced <| addEquiv 𝕜 A) = cobounded (Unitization 𝕜 A) :=
  le_antisymm lipschitzWith_addEquiv.comap_cobounded_le
    antilipschitzWith_addEquiv.tendsto_cobounded.le_comap

end Aux

/-- The uniformity on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
/-
**Unitization.instUniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instUniformSpace : UniformSpace (Unitization 𝕜 A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniformity on `Unitization 𝕜 A` is inherited from `𝕜 × A`.
-/
instance instUniformSpace : UniformSpace (Unitization 𝕜 A) :=
  instUniformSpaceProd.comap (addEquiv 𝕜 A)

/-- The natural equivalence between `Unitization 𝕜 A` and `𝕜 × A` as a uniform equivalence. -/
/-
**Unitization.uniformEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：uniformEquivProd : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between `Unitization 𝕜 A` and `𝕜 × A` as a uniform equiv
alence.
-/
def uniformEquivProd : (Unitization 𝕜 A) ≃ᵤ (𝕜 × A) :=
  Equiv.toUniformEquivOfIsUniformInducing (addEquiv 𝕜 A) ⟨rfl⟩

/-- The bornology on `Unitization 𝕜 A` is inherited from `𝕜 × A`. -/
/-
**Unitization.instBornology** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instBornology : Bornology (Unitization 𝕜 A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bornology on `Unitization 𝕜 A` is inherited from `𝕜 × A`.
-/
instance instBornology : Bornology (Unitization 𝕜 A) :=
  Bornology.induced <| addEquiv 𝕜 A
/-
**Unitization.isUniformEmbedding_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Unitization
`。
形式化陈述：isUniformEmbedding_addEquiv {𝕜} [NontriviallyNormedField 𝕜] : IsUniformEmb
edding (addEquiv 𝕜 A) where comap_uniformity
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
-/
theorem isUniformEmbedding_addEquiv {𝕜} [NontriviallyNormedField 𝕜] :
    IsUniformEmbedding (addEquiv 𝕜 A) where
  comap_uniformity := rfl
  injective := (addEquiv 𝕜 A).injective

/-- `Unitization 𝕜 A` is complete whenever `𝕜` and `A` are also. -/
/-
**Unitization.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] : CompleteSpace (Uni
tization 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformEquiv.completeSpace_iff`：completeSpace_iff (h : α ≃ᵤ β) : Complet
eSpace α ↔ CompleteSpace β

--- 原说明 ---
`Unitization 𝕜 A` is complete whenever `𝕜` and `A` are also.
-/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (Unitization 𝕜 A) :=
  uniformEquivProd.completeSpace_iff.2 .prod
/-
**Unitization.instT2Space** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instT2Space : T2Space (Unitization 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t2Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T2Space X] (h : X ≃ₜ Y),   T2Space Y
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
instance instT2Space : T2Space (Unitization 𝕜 A) :=
  Unitization.uniformEquivProd.symm.toHomeomorph.t2Space

/-- Pull back the metric structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`, but replace the bornology and the uniformity so
that they coincide with `𝕜 × A`. -/
/-
**Unitization.instMetricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instMetricSpace : MetricSpace (Unitization 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitization.uniformity_eq_aux`：uniformity_eq_aux : 𝓤[instUniformSpacePro
d.comap <| addEquiv 𝕜 A] = 𝓤 (Unitization 𝕜 A)

--- 原说明 ---
Pull back the metric structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using
 the
algebra homomorphism `Unitization.splitMul 𝕜 A`, but replace the bornology and t
he uniformity so
that they coincide with `𝕜 × A`.
-/
noncomputable instance instMetricSpace : MetricSpace (Unitization 𝕜 A) :=
  (normedRingAux.toMetricSpace.replaceUniformity uniformity_eq_aux).replaceBornology
    fun s => Filter.ext_iff.1 cobounded_eq_aux (sᶜ)

/-- Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. -/
/-
**Unitization.instNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNormedRing : NormedRing (Unitization 𝕜 A) where dist_eq
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back the normed ring structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` 
using the
algebra homomorphism `Unitization.splitMul 𝕜 A`.
-/
noncomputable instance instNormedRing : NormedRing (Unitization 𝕜 A) where
  dist_eq := normedRingAux.dist_eq
  norm_mul_le := normedRingAux.norm_mul_le
  norm := normedRingAux.norm

/-- Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`. -/
/-
**Unitization.instNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where norm_smul_le k
 x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back the normed algebra structure from `𝕜 × (A →L[𝕜] A)` to `Unitization 𝕜 
A` using the
algebra homomorphism `Unitization.splitMul 𝕜 A`.
-/
instance instNormedAlgebra : NormedAlgebra 𝕜 (Unitization 𝕜 A) where
  norm_smul_le k x := by rw [norm_def, map_smul, norm_smul, ← norm_def]
/-
**Unitization.instNormOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Unitization`。
形式化陈述：instNormOneClass : NormOneClass (Unitization 𝕜 A) where norm_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Unitization.norm_eq_sup`：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fs
t‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
instance instNormOneClass : NormOneClass (Unitization 𝕜 A) where
  norm_one := by simpa only [norm_eq_sup, fst_one, norm_one, snd_one, map_one, map_zero,
      add_zero, sup_eq_left] using opNorm_le_bound _ zero_le_one fun x => by simp
/-
**Unitization.norm_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Unitization.norm_eq_sup`：norm_eq_sup (x : Unitization 𝕜 A) : ‖x‖ = ‖x.fs
t‖ ⊔ ‖algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `ContinuousLinearMap.opNorm_mul_apply`：opNorm_mul_apply (x : R) : ‖mul 𝕜 
R x‖ = ‖x‖
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖ := by
  simp [norm_eq_sup]
/-
**Unitization.nnnorm_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
-/
lemma nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inr a
/-
**Unitization.isometry_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isometry_inr : Isometry ((↑) : A -> Unitization 𝕜 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
-/
lemma isometry_inr : Isometry ((↑) : A → Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm (inrNonUnitalAlgHom 𝕜 A) norm_inr

@[fun_prop]
/-
**Unitization.continuous_inr** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：continuous_inr : Continuous (inr : A -> Unitization 𝕜 A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用引理 `Unitization.isometry_inr`：isometry_inr : Isometry ((↑) : A -> Unitizatio
n 𝕜 A)
-/
theorem continuous_inr : Continuous (inr : A → Unitization 𝕜 A) :=
  isometry_inr.continuous
/-
**Unitization.dist_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：dist_inr (a b : A) : dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = di
st a b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用引理 `Unitization.isometry_inr`：isometry_inr : Isometry ((↑) : A -> Unitizatio
n 𝕜 A)
-/
lemma dist_inr (a b : A) : dist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = dist a b :=
  isometry_inr.dist_eq a b
/-
**Unitization.nndist_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：nndist_inr (a b : A) : nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) 
= nndist a b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用引理 `Unitization.isometry_inr`：isometry_inr : Isometry ((↑) : A -> Unitizatio
n 𝕜 A)
-/
lemma nndist_inr (a b : A) : nndist (a : Unitization 𝕜 A) (b : Unitization 𝕜 A) = nndist a b :=
  isometry_inr.nndist_eq a b

/-! These examples verify that the bornology and uniformity (hence also the topology) are the
correct ones. -/
/-
**Unitization.** 是 Mathlib 中的一个示例，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These examples verify that the bornology and uniformity (hence also the topology
) are the
correct ones.
-/
example : (instNormedRing (𝕜 := 𝕜) (A := A)).toMetricSpace = instMetricSpace := rfl
/-
**Unitization.** 是 Mathlib 中的一个示例，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toBornology = instBornology := rfl
/-
**Unitization.** 是 Mathlib 中的一个示例，位于命名空间 `Unitization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (instMetricSpace (𝕜 := 𝕜) (A := A)).toUniformSpace = instUniformSpace := rfl

section

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]

/-
**Unitization.uniformContinuous_fst** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {𝕜 : Type u_3} {A : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NonUnitalNormedRing A],   UniformContinuous fun x => x.toProd.1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_fst`：uniformContinuous_fst [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.1
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h
-/
protected theorem uniformContinuous_fst : UniformContinuous (fun x : Unitization 𝕜 A ↦ x.fst) :=
  uniformContinuous_fst.comp Unitization.uniformEquivProd.uniformContinuous
/-
**Unitization.uniformContinuous_snd** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {𝕜 : Type u_3} {A : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NonUnitalNormedRing A],   UniformContinuous fun x => x.toProd.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `uniformContinuous_snd`：uniformContinuous_snd [UniformSpace α] [UniformSp
ace β] : UniformContinuous fun p : α × β => p.2
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h
-/
protected theorem uniformContinuous_snd : UniformContinuous (fun x : Unitization 𝕜 A ↦ x.snd) :=
  uniformContinuous_snd.comp Unitization.uniformEquivProd.uniformContinuous

@[fun_prop]
/-
**Unitization.continuous_fst** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {𝕜 : Type u_3} {A : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NonUnitalNormedRing A],   Continuous fun x => x.toProd.1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Unitization.uniformContinuous_fst`：∀ {𝕜 : Type u_3} {A : Type u_4} [inst
 : NontriviallyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A],   UniformContinu
ous fun x => x.toProd.1
-/
protected theorem continuous_fst : Continuous (fun x : Unitization 𝕜 A ↦ x.fst) :=
  Unitization.uniformContinuous_fst.continuous

@[fun_prop]
/-
**Unitization.continuous_snd** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：∀ {𝕜 : Type u_3} {A : Type u_4} [inst : NontriviallyNormedField 𝕜] [inst_1
 : NonUnitalNormedRing A],   Continuous fun x => x.toProd.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Unitization.uniformContinuous_snd`：∀ {𝕜 : Type u_3} {A : Type u_4} [inst
 : NontriviallyNormedField 𝕜] [inst_1 : NonUnitalNormedRing A],   UniformContinu
ous fun x => x.toProd.2
-/
protected theorem continuous_snd : Continuous (fun x : Unitization 𝕜 A ↦ x.snd) :=
  Unitization.uniformContinuous_snd.continuous

end

end Unitization

