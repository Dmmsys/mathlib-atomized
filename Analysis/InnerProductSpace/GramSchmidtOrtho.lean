/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt`: the Gram-Schmidt process
- `gramSchmidt_orthogonal`: `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt`: `gramSchmidt` preserves span of vectors.
- `gramSchmidt_linearIndependent`: if the input vectors of `gramSchmidt` are linearly independent,
  then so are the output vectors.
- `gramSchmidt_ne_zero`: if the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidtBasis`: the basis produced by the Gram-Schmidt process when given a basis as input
- `gramSchmidtNormed`:
  the normalized `gramSchmidt` process, i.e each vector in `gramSchmidtNormed` has unit length
- `gramSchmidt_orthonormal`: `gramSchmidtNormed` produces an orthonormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/

@[expose] public section


open Finset Submodule Module

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace InnerProductSpace

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
/-
**InnerProductSpace.gramSchmidt** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpace`。
形式化陈述：gramSchmidt [WellFoundedLT ι] (f : ι -> E) (n : ι) : E
参数：f : ι -> E；n : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.
-/
noncomputable def gramSchmidt [WellFoundedLT ι] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

variable [WellFoundedLT ι]

/-- This lemma uses `∑ i in` instead of `∑ i :`. -/
/-
**InnerProductSpace.gramSchmidt_def** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace
`。
形式化陈述：gramSchmidt_def (f : ι -> E) (n : ι) : gramSchmidt 𝕜 f n = f n - ∑ i in Ii
o n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n)
参数：f : ι -> E；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
· 使用定理 `InnerProductSpace.gramSchmidt.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2} [ins
t : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]  
 {ι : Type u_3} [inst_3 …

--- 原说明 ---
This lemma uses `∑ i in` instead of `∑ i :`.
-/
theorem gramSchmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
/-
**InnerProductSpace.gramSchmidt_def'** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpac
e`。
形式化陈述：gramSchmidt_def' (f : ι -> E) (n : ι) : f n = gramSchmidt 𝕜 f n + ∑ i in I
io n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n)
参数：f : ι -> E；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def`：gramSchmidt_def (f : ι -> E) (n : ι) 
: gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection
 (f n)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem gramSchmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [gramSchmidt_def, sub_add_cancel]
/-
**InnerProductSpace.gramSchmidt_def''** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpa
ce`。
形式化陈述：gramSchmidt_def'' (f : ι -> E) (n : ι) : f n = gramSchmidt 𝕜 f n + ∑ i in 
Iio n, (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 
𝕜 f i
参数：f : ι -> E；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.gramSchmidt_def'`：gramSchmidt_def' (f : ι -> E) (n : ι
) : f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjecti
on (f n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gramSchmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n,
      (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]

@[simp]
/-
**InnerProductSpace.gramSchmidt_bot** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpace
`。
形式化陈述：gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderB
ot ι] [WellFoundedLT ι] (f : ι -> E) : gramSchmidt 𝕜 f ⊥ = f ⊥
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def`：gramSchmidt_def (f : ι -> E) (n : ι) 
: gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection
 (f n)
· 使用定理 `Finset.Iio_eq_Ico`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] [inst_2 : OrderBot α] (a : α),   Finset.Iio a = Finset.Ico ⊥ a
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gramSchmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]

@[simp]
/-
**InnerProductSpace.gramSchmidt_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpac
e`。
形式化陈述：gramSchmidt_zero (n : ι) : gramSchmidt 𝕜 (0 : ι -> E) n = 0
参数：n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def`：gramSchmidt_def (f : ι -> E) (n : ι) 
: gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection
 (f n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gramSchmidt_zero (n : ι) : gramSchmidt 𝕜 (0 : ι → E) n = 0 := by rw [gramSchmidt_def]; simp

/-- **Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors. -/
/-
**InnerProductSpace.gramSchmidt_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace`。
形式化陈述：gramSchmidt_orthogonal (f : ι -> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt
 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0
参数：f : ι -> E；h₀ : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction`：∀ {α : Sort u} {r : α → α → Prop},   WellFounded 
r → ∀ {C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) → C a
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `InnerProductSpace.gramSchmidt_def`：gramSchmidt_def (f : ι -> E) (n : ι) 
: gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection
 (f n)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Submodule.starProjection_singleton`：starProjection_singleton {v : E} (w 
: E) : (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `inner_eq_zero_symm`：inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ =
 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : K
) = (r : K) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
**Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors.
-/
theorem gramSchmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp only [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    starProjection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  · by_cases h : gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
    · rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, div_mul_cancel₀, sub_self]
      rwa [inner_self_ne_zero]
  intro i hi hia
  simp only [mul_eq_zero, div_eq_zero_iff]
  right
  rcases hia.lt_or_gt with hia₁ | hia₂
  · rw [inner_eq_zero_symm]
    exact ih a h₀ i hia₁
  · exact ih i (mem_Iio.1 hi) a hia₂

/-- This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead. -/
/-
**InnerProductSpace.gramSchmidt_pairwise_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `I
nnerProductSpace`。
形式化陈述：gramSchmidt_pairwise_orthogonal (f : ι -> E) : Pairwise fun a b => ⟪gramSc
hmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0

--- 原说明 ---
This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead.
-/
theorem gramSchmidt_pairwise_orthogonal (f : ι → E) :
    Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f
/-
**InnerProductSpace.gramSchmidt_inv_triangular** 是 Mathlib 中的一个定理，位于命名空间 `InnerP
roductSpace`。
形式化陈述：gramSchmidt_inv_triangular (v : ι -> E) {i j : ι} (hij : i < j) : ⟪gramSch
midt 𝕜 v j, v i⟫ = 0
参数：v : ι -> E；hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def''`：gramSchmidt_def'' (f : ι -> E) (n :
 ι) : f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gram
Schmidt 𝕜 f i‖ : 𝕜) ^ 2) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem gramSchmidt_inv_triangular (v : ι → E) {i j : ι} (hij : i < j) :
    ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gramSchmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι → E := gramSchmidt 𝕜 v
  convert! zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, b k⟫ = 0 := gramSchmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  simp [this]

open Submodule Set Order
/-
**InnerProductSpace.mem_span_gramSchmidt** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：mem_span_gramSchmidt (f : ι -> E) {i j : ι} (hij : i <= j) : f i in span 𝕜
 (gramSchmidt 𝕜 f '' Set.Iic j)
参数：f : ι -> E；hij : i <= j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def'`：gramSchmidt_def' (f : ι -> E) (n : ι
) : f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjecti
on (f n)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Submodule.starProjection_singleton`：starProjection_singleton {v : E} (w 
: E) : (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
-/
theorem mem_span_gramSchmidt (f : ι → E) {i j : ι} (hij : i ≤ j) :
    f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  simp_rw [starProjection_singleton]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
      subset_span <| mem_image_of_mem (gramSchmidt 𝕜 f) <| (Finset.mem_Iio.1 hk).le.trans hij)
/-
**InnerProductSpace.gramSchmidt_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：gramSchmidt_mem_span (f : ι -> E) : forall {j i}, i <= j -> gramSchmidt 𝕜 
f i in span 𝕜 (f '' Set.Iic j)
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidt_mem_span._unary`：∀ (𝕜 : Type u_1) {E : Typ
e u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductS
pace 𝕜 E]   {ι : Type u_3} [inst_3 …
-/
theorem gramSchmidt_mem_span (f : ι → E) :
    ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j) := by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  simp_rw [starProjection_singleton]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_mono <| Set.Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
termination_by j => j
/-
**InnerProductSpace.span_gramSchmidt_Iic** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：span_gramSchmidt_Iic (f : ι -> E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Set
.Iic c) = span 𝕜 (f '' Set.Iic c)
参数：f : ι -> E；c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `InnerProductSpace.gramSchmidt_mem_span`：gramSchmidt_mem_span (f : ι -> E
) : forall {j i}, i <= j -> gramSchmidt 𝕜 f i in span 𝕜 (f '' Set.Iic j)
· 使用定理 `InnerProductSpace.mem_span_gramSchmidt`：mem_span_gramSchmidt (f : ι -> E
) {i j : ι} (hij : i <= j) : f i in span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)
-/
theorem span_gramSchmidt_Iic (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic c) = span 𝕜 (f '' Set.Iic c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _) <|
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _
/-
**InnerProductSpace.span_gramSchmidt_Iio** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：span_gramSchmidt_Iio (f : ι -> E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Set
.Iio c) = span 𝕜 (f '' Set.Iio c)
参数：f : ι -> E；c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
· 使用定理 `InnerProductSpace.gramSchmidt_mem_span`：gramSchmidt_mem_span (f : ι -> E
) : forall {j i}, i <= j -> gramSchmidt 𝕜 f i in span 𝕜 (f '' Set.Iic j)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `InnerProductSpace.mem_span_gramSchmidt`：mem_span_gramSchmidt (f : ι -> E
) {i j : ι} (hij : i <= j) : f i in span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)
-/
theorem span_gramSchmidt_Iio (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ hi =>
    span_mono (image_mono <| Iic_subset_Iio.2 hi) <| gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
        span_mono (image_mono <| Iic_subset_Iio.2 hi) <| mem_span_gramSchmidt _ _ le_rfl

/-- `gramSchmidt` preserves span of vectors. -/
/-
**InnerProductSpace.span_gramSchmidt** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpac
e`。
形式化陈述：span_gramSchmidt (f : ι -> E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 
(range f)
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `InnerProductSpace.gramSchmidt_mem_span`：gramSchmidt_mem_span (f : ι -> E
) : forall {j i}, i <= j -> gramSchmidt 𝕜 f i in span 𝕜 (f '' Set.Iic j)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `InnerProductSpace.mem_span_gramSchmidt`：mem_span_gramSchmidt (f : ι -> E
) {i j : ι} (hij : i <= j) : f i in span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)

--- 原说明 ---
`gramSchmidt` preserves span of vectors.
-/
theorem span_gramSchmidt (f : ι → E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 fun _ =>
    span_mono (image_subset_range _ _) <| gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
        span_mono (image_subset_range _ _) <| mem_span_gramSchmidt _ _ le_rfl

/-- If given an orthogonal set of vectors, `gramSchmidt` fixes its input. -/
/-
**InnerProductSpace.gramSchmidt_of_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `InnerPr
oductSpace`。
形式化陈述：gramSchmidt_of_orthogonal {f : ι -> E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) : 
gramSchmidt 𝕜 f = f
参数：hf : Pairwise (⟪f ·, f ·⟫ = 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidt_def`：gramSchmidt_def (f : ι -> E) (n : ι) 
: gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection
 (f n)
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `Submodule.starProjection_apply`：starProjection_apply (U : Submodule 𝕜 E)
 [U.HasOrthogonalProjection] (v : E) : U.starProjection v = U.orthogonalProjecti
onOnto v
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `Submodule.isOrtho_span`：isOrtho_span {s t : Set E} : span 𝕜 s ⟂ span 𝕜 t
 ↔ forall ⦃u⦄, u in s -> forall ⦃v⦄, v in t -> ⟪u, v⟫ = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal`：orthogonalPr
ojectionOnto_apply_of_mem_orthogonal [K.HasOrthogonalProjection] {v : E} (hv : v
 in Kᗮ) : K.orthogonalProjectionOnto v = 0
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `InnerProductSpace.gramSchmidt_mem_span`：gramSchmidt_mem_span (f : ι -> E
) : forall {j i}, i <= j -> gramSchmidt 𝕜 f i in span 𝕜 (f '' Set.Iic j)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If given an orthogonal set of vectors, `gramSchmidt` fixes its input.
-/
theorem gramSchmidt_of_orthogonal {f : ι → E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) :
    gramSchmidt 𝕜 f = f := by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjectionOnto_apply_of_mem_orthogonal
      rw [mem_orthogonal_singleton_iff_inner_left, ← mem_orthogonal_singleton_iff_inner_right]
      exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
    rw [isOrtho_span]
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
    apply hf
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
  · simp

variable {𝕜}
/-
**InnerProductSpace.gramSchmidt_ne_zero_coe** 是 Mathlib 中的一个定理，位于命名空间 `InnerProd
uctSpace`。
形式化陈述：gramSchmidt_ne_zero_coe {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 (f 
∘ ((↑) : Set.Iic n -> ι))) : gramSchmidt 𝕜 f n != 0
参数：n : ι；h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.span_gramSchmidt_Iio`：span_gramSchmidt_Iio (f : ι -> E
) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `InnerProductSpace.gramSchmidt_def'`：gramSchmidt_def' (f : ι -> E) (n : ι
) : f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjecti
on (f n)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.starProjection_singleton`：starProjection_singleton {v : E} (w 
: E) : (𝕜 ∙ v).starProjection w = (⟪v, w⟫ / ((‖v‖ ^ 2 : Real) : 𝕜)) • v
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Finset.mem_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iio a ↔ x < a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.image_subtype_val_Iic_Iio`：image_subtype_val_Iic_Iio {a : α} (b : Ii
c a) : Subtype.val '' Iio b = Iio b.1
· 使用定理 `LinearIndependent.notMem_span_image`：LinearIndependent.notMem_span_image
 [Nontrivial R] (hv : LinearIndependent R v) {s : Set ι} {x : ι} (h : x ∉ s) : v
 x ∉ Submodule.span R (v …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem gramSchmidt_ne_zero_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n, gramSchmidt_def' 𝕜 f, h, zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [starProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    exact subset_span ⟨a, ha, by rfl⟩
  have h₂ : (f ∘ ((↑) : Set.Iic n → ι)) ⟨n, le_refl n⟩ ∈
      span 𝕜 (f ∘ ((↑) : Set.Iic n → ι) '' Set.Iio ⟨n, le_refl n⟩) := by
    rw [image_comp]
    simpa using h₁
  apply LinearIndependent.notMem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]

/-- If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero. -/
/-
**InnerProductSpace.gramSchmidt_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductS
pace`。
形式化陈述：gramSchmidt_ne_zero {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f) : gr
amSchmidt 𝕜 f n != 0
参数：n : ι；h₀ : LinearIndependent 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidt_ne_zero_coe`：gramSchmidt_ne_zero_coe {f : 
ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))) : gramSc
hmidt 𝕜 f n != 0
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero.
-/
theorem gramSchmidt_ne_zero {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n ≠ 0 :=
  gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- `gramSchmidt` produces a triangular matrix of vectors when given a basis. -/
/-
**InnerProductSpace.gramSchmidt_triangular** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace`。
形式化陈述：gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) : b.repr 
(gramSchmidt 𝕜 b i) j = 0
参数：hij : i < j；b : Basis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.span_gramSchmidt_Iio`：span_gramSchmidt_Iio (f : ι -> E
) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c)
· 使用定理 `Module.Basis.repr_support_subset_of_mem_span`：repr_support_subset_of_mem
_span (s : Set ι) {m : M} (hm : m in span R (b '' s)) : ↑(b.repr m).support subs
eteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `Set.self_notMem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∉ S
et.Iio a

--- 原说明 ---
`gramSchmidt` produces a triangular matrix of vectors when given a basis.
-/
theorem gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.Iio j :=
    Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.self_notMem_Iio

/-- `gramSchmidt` produces linearly independent vectors when given linearly independent vectors. -/
/-
**InnerProductSpace.gramSchmidt_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：gramSchmidt_linearIndependent {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) : 
LinearIndependent 𝕜 (gramSchmidt 𝕜 f)
参数：h₀ : LinearIndependent 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_of_ne_zero_of_inner_eq_zero`：linearIndependent_of_ne_z
ero_of_inner_eq_zero {ι : Type*} {v : ι -> E} (hz : forall i, v i != 0) (ho : Pa
irwise fun i j => ⟪v i, v j⟫ = 0) :…
· 使用定理 `InnerProductSpace.gramSchmidt_ne_zero`：gramSchmidt_ne_zero {f : ι -> E} 
(n : ι) (h₀ : LinearIndependent 𝕜 f) : gramSchmidt 𝕜 f n != 0
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0

--- 原说明 ---
`gramSchmidt` produces linearly independent vectors when given linearly independ
ent vectors.
-/
theorem gramSchmidt_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

/-- When given a basis, `gramSchmidt` produces a basis. -/
/-
**InnerProductSpace.gramSchmidtBasis** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpac
e`。
形式化陈述：gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E
参数：b : Basis ι 𝕜 E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When given a basis, `gramSchmidt` produces a basis.
-/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge
/-
**InnerProductSpace.coe_gramSchmidtBasis** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Space`。
形式化陈述：coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι -> E) = g
ramSchmidt 𝕜 b
参数：b : Basis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
theorem coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _

variable (𝕜) in
/-- the normalized `gramSchmidt` (i.e each vector in `gramSchmidtNormed` has unit length.) -/
/-
**InnerProductSpace.gramSchmidtNormed** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpa
ce`。
形式化陈述：gramSchmidtNormed (f : ι -> E) (n : ι) : E
参数：f : ι -> E；n : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the normalized `gramSchmidt` (i.e each vector in `gramSchmidtNormed` has unit le
ngth.)
-/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n
/-
**InnerProductSpace.gramSchmidtNormed_unit_length_coe** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductSpace`。
形式化陈述：gramSchmidtNormed_unit_length_coe {f : ι -> E} (n : ι) (h₀ : LinearIndepen
dent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))) : ‖gramSchmidtNormed 𝕜 f n‖ = 1
参数：n : ι；h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_smul_inv_norm`：norm_smul_inv_norm {x : E} (hx : x != 0) : ‖(‖x‖⁻¹ :
 𝕜) • x‖ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `InnerProductSpace.gramSchmidt_ne_zero_coe`：gramSchmidt_ne_zero_coe {f : 
ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n -> ι))) : gramSc
hmidt 𝕜 f n != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gramSchmidtNormed_unit_length_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne,
    not_false_iff]
/-
**InnerProductSpace.gramSchmidtNormed_unit_length** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：gramSchmidtNormed_unit_length {f : ι -> E} (n : ι) (h₀ : LinearIndependent
 𝕜 f) : ‖gramSchmidtNormed 𝕜 f n‖ = 1
参数：n : ι；h₀ : LinearIndependent 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidtNormed_unit_length_coe`：gramSchmidtNormed_u
nit_length_coe {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Ii
c n -> ι))) : ‖gramSchmidtNormed 𝕜 f n‖ =…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem gramSchmidtNormed_unit_length {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 :=
  gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)
/-
**InnerProductSpace.gramSchmidtNormed_unit_length'** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace`。
形式化陈述：gramSchmidtNormed_unit_length' {f : ι -> E} {n : ι} (hn : gramSchmidtNorme
d 𝕜 f n != 0) : ‖gramSchmidtNormed 𝕜 f n‖ = 1
参数：hn : gramSchmidtNormed 𝕜 f n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidtNormed.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {ι : Type u_3} [inst_3 …
· 使用定理 `norm_smul_inv_norm`：norm_smul_inv_norm {x : E} (hx : x != 0) : ‖(‖x‖⁻¹ :
 𝕜) • x‖ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem gramSchmidtNormed_unit_length' {f : ι → E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n ≠ 0) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` applied to a linearly independent set of vectors produces an orthonormal
system of vectors. -/
/-
**InnerProductSpace.gramSchmidtNormed_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `Inn
erProductSpace`。
形式化陈述：gramSchmidtNormed_orthonormal {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) : 
Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f)
参数：h₀ : LinearIndependent 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidtNormed_unit_length`：gramSchmidtNormed_unit_
length {f : ι -> E} (n : ι) (h₀ : LinearIndependent 𝕜 f) : ‖gramSchmidtNormed 𝕜 
f n‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `RCLike.conj_inv`：conj_inv (x : K) : conj x⁻¹ = (conj x)⁻¹
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0

--- 原说明 ---
**Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` applied to a linearly independent set of vectors produces an
 orthonormal
system of vectors.
-/
theorem gramSchmidtNormed_orthonormal {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gramSchmidtNormed_unit_length, h₀, imp_true_iff]
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, RCLike.conj_inv,
      RCLike.conj_ofReal, mul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero]
    repeat' right
    exact gramSchmidt_orthogonal 𝕜 f hij

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` produces an orthonormal system of vectors after removing the vectors which
become zero in the process. -/
/-
**InnerProductSpace.gramSchmidtNormed_orthonormal'** 是 Mathlib 中的一个定理，位于命名空间 `In
nerProductSpace`。
形式化陈述：gramSchmidtNormed_orthonormal' (f : ι -> E) : Orthonormal 𝕜 fun i : { i | 
gramSchmidtNormed 𝕜 f i != 0 } => gramSchmidtNormed 𝕜 f i
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidtNormed_unit_length'`：gramSchmidtNormed_unit
_length' {f : ι -> E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n != 0) : ‖gramSchmidt
Normed 𝕜 f n‖ = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` produces an orthonormal system of vectors after removing the
 vectors which
become zero in the process.
-/
theorem gramSchmidtNormed_orthonormal' (f : ι → E) :
    Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i ≠ 0 } => gramSchmidtNormed 𝕜 f i := by
  refine ⟨fun i => gramSchmidtNormed_unit_length' i.prop, ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

open Submodule Set Order
/-
**InnerProductSpace.span_gramSchmidtNormed** 是 Mathlib 中的一个定理，位于命名空间 `InnerProdu
ctSpace`。
形式化陈述：span_gramSchmidtNormed (f : ι -> E) (s : Set ι) : span 𝕜 (gramSchmidtNorme
d 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s)
参数：f : ι -> E；s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Finset.singleton_subset_set_iff`：singleton_subset_set_iff {s : Set α} {a
 : α} : ↑({a} : Finset α) subseteq s ↔ a in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
theorem span_gramSchmidtNormed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_mono <| singleton_subset_set_iff.2 hi) ?_)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h : gramSchmidt 𝕜 f i = 0
  · simp [h]
  · refine mem_span_singleton.2 ⟨‖gramSchmidt 𝕜 f i‖, smul_inv_smul₀ ?_ _⟩
    exact mod_cast norm_ne_zero_iff.2 h
/-
**InnerProductSpace.span_gramSchmidtNormed_range** 是 Mathlib 中的一个定理，位于命名空间 `Inne
rProductSpace`。
形式化陈述：span_gramSchmidtNormed_range (f : ι -> E) : span 𝕜 (range (gramSchmidtNorm
ed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f))
参数：f : ι -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `InnerProductSpace.span_gramSchmidtNormed`：span_gramSchmidtNormed (f : ι 
-> E) (s : Set ι) : span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 
f '' s)
-/
theorem span_gramSchmidtNormed_range (f : ι → E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ

/-- `gramSchmidtNormed` produces linearly independent vectors when given linearly independent
vectors. -/
/-
**InnerProductSpace.gramSchmidtNormed_linearIndependent** 是 Mathlib 中的一个定理，位于命名空
间 `InnerProductSpace`。
形式化陈述：gramSchmidtNormed_linearIndependent {f : ι -> E} (h₀ : LinearIndependent 𝕜
 f) : LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 f)
参数：h₀ : LinearIndependent 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `InnerProductSpace.gramSchmidt_ne_zero`：gramSchmidt_ne_zero {f : ι -> E} 
(n : ι) (h₀ : LinearIndependent 𝕜 f) : gramSchmidt 𝕜 f n != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)
· 使用定理 `InnerProductSpace.gramSchmidt_linearIndependent`：gramSchmidt_linearIndep
endent {f : ι -> E} (h₀ : LinearIndependent 𝕜 f) : LinearIndependent 𝕜 (gramSchm
idt 𝕜 f)

--- 原说明 ---
`gramSchmidtNormed` produces linearly independent vectors when given linearly in
dependent
vectors.
-/
theorem gramSchmidtNormed_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold gramSchmidtNormed
  have (i : ι) : IsUnit (‖gramSchmidt 𝕜 f i‖⁻¹ : 𝕜) :=
    isUnit_iff_ne_zero.mpr (by simp [gramSchmidt_ne_zero i h₀])
  let w : ι → 𝕜ˣ := fun i ↦ (this i).unit
  apply (gramSchmidt_linearIndependent h₀).units_smul (w := fun i ↦ (this i).unit)

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι → E)

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis** 是 Mathlib 中的一个定义，位于命名空间 `Inner
ProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an indexed family `f : ι → E` of vectors in an inner product space `E`, fo
r which the
size of the index set is the dimension of `E`, produce an orthonormal basis for 
`E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process
 on the elements of
`ι` for which this process gives a nonzero number.
-/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 
`InnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_apply {f : ι -> E} {i : ι} (hi : gramSchmidtNo
rmed 𝕜 f i != 0) : gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i
参数：hi : gramSchmidtNormed 𝕜 f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`：Orthonormal.ex
ists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fintype ι] (card_ι : fin
rank 𝕜 E = Fintype.card ι) {v : ι -> E} {s : S…
· 使用定理 `InnerProductSpace.gramSchmidtNormed_orthonormal'`：gramSchmidtNormed_orth
onormal' (f : ι -> E) : Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i != 0
 } => gramSchmidtNormed 𝕜 f i
-/
theorem gramSchmidtOrthonormalBasis_apply {f : ι → E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_apply_of_orthogonal** 是 Mathlib 
中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι -> E} (hf : Pairwis
e fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i != 0) : gramSchmidtOrthonormalBas
is h f i = (‖f i‖⁻¹ : 𝕜) • f i
参数：hf : Pairwise fun i j => ⟪f i, f j⟫ = 0；hi : f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.gramSchmidtNormed.eq_1`：∀ (𝕜 : Type u_1) {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {ι : Type u_3} [inst_3 …
· 使用定理 `InnerProductSpace.gramSchmidt_of_orthogonal`：gramSchmidt_of_orthogonal {
f : ι -> E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) : gramSchmidt 𝕜 f = f
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_apply`：gramSchmidtOrthonor
malBasis_apply {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0) : gramSc
hmidtOrthonormalBasis h f i = gramSchmidt…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = (‖f i‖⁻¹ : 𝕜) • f i := by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed, gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h, H]
  simpa [H] using hi
/-
**InnerProductSpace.inner_gramSchmidtOrthonormalBasis_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `InnerProductSpace`。
形式化陈述：inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι -> E} {i : ι} (hi : gramS
chmidtNormed 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0
参数：hi : gramSchmidtNormed 𝕜 f i = 0；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `Submodule.isOrtho_span`：isOrtho_span {s t : Set E} : span 𝕜 s ⟂ span 𝕜 t
 ↔ forall ⦃u⦄, u in s -> forall ⦃v⦄, v in t -> ⟪u, v⟫ = 0
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_apply`：gramSchmidtOrthonor
malBasis_apply {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0) : gramSc
hmidtOrthonormalBasis h f i = gramSchmidt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `InnerProductSpace.span_gramSchmidtNormed`：span_gramSchmidtNormed (f : ι 
-> E) (s : Set ι) : span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 
f '' s)
· 使用定理 `InnerProductSpace.mem_span_gramSchmidt`：mem_span_gramSchmidt (f : ι -> E
) {i j : ι} (hij : i <= j) : f i in span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι → E} {i : ι}
    (hi : gramSchmidtNormed 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
  by_cases hk : gramSchmidtNormed 𝕜 f k = 0
  · rw [hk, inner_zero_left]
  rw [← gramSchmidtOrthonormalBasis_apply h hk]
  have : k ≠ i := by
    rintro rfl
    exact hk hi
  exact (gramSchmidtOrthonormalBasis h f).orthonormal.2 this
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular** 是 Mathlib 中的一个定
理，位于命名空间 `InnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) : ⟪gram
SchmidtOrthonormalBasis h f j, f i⟫ = 0
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InnerProductSpace.inner_gramSchmidtOrthonormalBasis_eq_zero`：inner_gramS
chmidtOrthonormalBasis_eq_zero {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f 
i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_apply`：gramSchmidtOrthonor
malBasis_apply {f : ι -> E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i != 0) : gramSc
hmidtOrthonormalBasis h f i = gramSchmidt…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `InnerProductSpace.gramSchmidt_inv_triangular`：gramSchmidt_inv_triangular
 (v : ι -> E) {i j : ι} (hij : i < j) : ⟪gramSchmidt 𝕜 v j, v i⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'** 是 Mathlib 中的一个
定理，位于命名空间 `InnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) : (gra
mSchmidtOrthonormalBasis h f).repr (f i) j = 0
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular`：gramSchmid
tOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) : ⟪gramSchmidtOrthonorm
alBasis h f j, f i⟫ = 0
-/
theorem gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gramSchmidtOrthonormalBasis` constructed from `f` is upper-triangular. -/
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular** 是 Mathli
b 中的一个定理，位于命名空间 `InnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_inv_isUpperTriangular : ((gramSchmidtOrthonorm
alBasis h f).toBasis.toMatrix f).IsUpperTriangular
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular'`：gramSchmi
dtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) : (gramSchmidtOrthono
rmalBasis h f).repr (f i) j = 0

--- 原说明 ---
Given an indexed family `f : ι → E` of vectors in an inner product space `E`, fo
r which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f`
 with respect to the
orthonormal basis `gramSchmidtOrthonormalBasis` constructed from `f` is upper-tr
iangular.
-/
theorem gramSchmidtOrthonormalBasis_inv_isUpperTriangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).IsUpperTriangular := fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

@[deprecated (since := "2026-07-30")]
alias gramSchmidtOrthonormalBasis_inv_blockTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular
/-
**InnerProductSpace.gramSchmidtOrthonormalBasis_det** 是 Mathlib 中的一个定理，位于命名空间 `I
nnerProductSpace`。
形式化陈述：gramSchmidtOrthonormalBasis_det [DecidableEq ι] : (gramSchmidtOrthonormalB
asis h f).toBasis.det f = ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `Matrix.det_of_isUpperTriangular`：det_of_isUpperTriangular [LinearOrder m
] (h : M.IsUpperTriangular) : M.det = ∏ i : m, M i i
· 使用定理 `InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular`：gra
mSchmidtOrthonormalBasis_inv_isUpperTriangular : ((gramSchmidtOrthonormalBasis h
 f).toBasis.toMatrix f).IsUpperTriangular
-/
theorem gramSchmidtOrthonormalBasis_det [DecidableEq ι] :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f =
      ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert! Matrix.det_of_isUpperTriangular (gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

end OrthonormalBasis

end InnerProductSpace

