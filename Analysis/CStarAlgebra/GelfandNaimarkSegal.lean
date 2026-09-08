/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# The GNS (Gelfand-Naimark-Segal) construction

This file contains the constructions and definitions that produce a ⋆-homomorphism from an arbitrary
C⋆-algebra into the algebra of bounded linear operators on an appropriately constructed Hilbert
space.

## Main results

- `f.PreGNS` : a type synonym of `A` that bundles in a fixed positive linear functional `f` so that
  we can construct an inner product and inner product-induced norm.
- `f.GNS` : the Hilbert space completion of `f.preGNS`.
- `f.gnsNonUnitalStarAlgHom` : The non-unital ⋆-homomorphism from a non-unital `A` into the bounded
  linear operators on `f.GNS`.
- `f.gnsStarAlgHom` : The unital ⋆-homomorphism from a unital `A` into the bounded linear operators
  on `f.GNS`.

## TODO

- Explicitly construct a unit norm cyclic vector ζ such that
  a ↦ ⟨(f.gns(NonUnital)StarAlgHom a) \* ζ, ζ⟩ is a state on `A` for both unital and non-unital
  cases.

-/

@[expose] public section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

set_option linter.unusedVariables false in
/-- The Gelfand─Naimark─Segal (GNS) space constructed from a positive linear functional on a
non-unital C⋆-algebra. This is a type synonym of `A`.

This space is only a pre-inner product space. Its Hilbert space completion is
`PositiveLinearMap.GNS`. -/
@[nolint unusedArguments]
/-
**PositiveLinearMap.PreGNS** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：PreGNS (f : A ->ₚ[Complex] Complex)
参数：f : A ->ₚ[Complex] Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gelfand─Naimark─Segal (GNS) space constructed from a positive linear functio
nal on a
non-unital C⋆-algebra. This is a type synonym of `A`.

This space is only a pre-inner product space. Its Hilbert space completion is
`PositiveLinearMap.GNS`.
-/
def PreGNS (f : A →ₚ[ℂ] ℂ) := A
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup f.PreGNS := inferInstanceAs (AddCommGroup A)
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module ℂ f.PreGNS := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
/-
**PositiveLinearMap.toPreGNS** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：toPreGNS : A ≃ₗ[Complex] f.PreGNS
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the C⋆-algebra to the GNS space, as a linear equivalence.
-/
def toPreGNS : A ≃ₗ[ℂ] f.PreGNS := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
/-
**PositiveLinearMap.ofPreGNS** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：ofPreGNS : f.PreGNS ≃ₗ[Complex] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the GNS space to the C⋆-algebra, as a linear equivalence.
-/
def ofPreGNS : f.PreGNS ≃ₗ[ℂ] A := f.toPreGNS.symm

@[simp]
/-
**PositiveLinearMap.toPreGNS_ofPreGNS** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearM
ap`。
形式化陈述：toPreGNS_ofPreGNS (a : f.PreGNS) : f.toPreGNS (f.ofPreGNS a) = a
参数：a : f.PreGNS。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toPreGNS_ofPreGNS (a : f.PreGNS) : f.toPreGNS (f.ofPreGNS a) = a := rfl

@[simp]
/-
**PositiveLinearMap.ofPreGNS_toPreGNS** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearM
ap`。
形式化陈述：ofPreGNS_toPreGNS (a : A) : f.ofPreGNS (f.toPreGNS a) = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofPreGNS_toPreGNS (a : A) : f.ofPreGNS (f.toPreGNS a) = a := rfl

variable [StarOrderedRing A]

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm that is different from the norm on `A` and which is induced by `f`.
-/
/-
**PositiveLinearMap.preGNSpreInnerProdSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Positiv
eLinearMap`。
形式化陈述：preGNSpreInnerProdSpace : PreInnerProductSpace.Core Complex f.PreGNS where
 inner a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (semi-)inner product space whose elements are the elements of `A`, but which
 has an
inner product-induced norm that is different from the norm on `A` and which is i
nduced by `f`.
-/
noncomputable abbrev preGNSpreInnerProdSpace : PreInnerProductSpace.Core ℂ f.PreGNS where
  inner a b := f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SeminormedAddCommGroup f.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preGNSpreInnerProdSpace)
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : InnerProductSpace ℂ f.PreGNS :=
  InnerProductSpace.ofCore f.preGNSpreInnerProdSpace
/-
**PositiveLinearMap.preGNS_inner_def** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMa
p`。
形式化陈述：preGNS_inner_def (a b : f.PreGNS) : ⟪a, b⟫_Complex = f (star (f.ofPreGNS a
) * f.ofPreGNS b)
参数：a b : f.PreGNS。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preGNS_inner_def (a b : f.PreGNS) :
    ⟪a, b⟫_ℂ = f (star (f.ofPreGNS a) * f.ofPreGNS b) := rfl
/-
**PositiveLinearMap.preGNS_norm_def** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap
`。
形式化陈述：preGNS_norm_def (a : f.PreGNS) : ‖a‖ = √(f (star (f.ofPreGNS a) * f.ofPreG
NS a)).re
参数：a : f.PreGNS。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preGNS_norm_def (a : f.PreGNS) :
    ‖a‖ = √(f (star (f.ofPreGNS a) * f.ofPreGNS a)).re := rfl
/-
**PositiveLinearMap.preGNS_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap`
。
形式化陈述：preGNS_norm_sq (a : f.PreGNS) : ‖a‖ ^ 2 = f (star (f.ofPreGNS a) * f.ofPre
GNS a)
参数：a : f.PreGNS。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PositiveLinearMap.map_nonneg`：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Typ
e u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder 
E₁] [inst_3 : AddC…
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.conj_eq_iff_re`：conj_eq_iff_re {z : Complex} : conj z = z ↔ (z.r
e : Complex) = z
· 使用引理 `LE.le.star_eq`：LE.le.star_eq {x : R} (hx : 0 <= x) : star x = x
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preGNS_norm_sq (a : f.PreGNS) :
    ‖a‖ ^ 2 = f (star (f.ofPreGNS a) * f.ofPreGNS a) := by
  have : 0 ≤ f (star (f.ofPreGNS a) * f.ofPreGNS a) := f.map_nonneg (star_mul_self_nonneg _)
  simp [preGNS_norm_def, ← ofReal_pow, Real.sq_sqrt this.1, conj_eq_iff_re.mp this.star_eq]

/--
The Hilbert space constructed from a positive linear functional on a C⋆-algebra.
-/
/-
**PositiveLinearMap.GNS** 是 Mathlib 中的一个缩写定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：GNS
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hilbert space constructed from a positive linear functional on a C⋆-algebra.
-/
abbrev GNS := UniformSpace.Completion f.PreGNS

/--
The continuous linear map from a C⋆-algebra `A` to the `PositiveLinearMap.preGNS` space induced by
a positive linear functional `f : A →ₚ[ℂ] ℂ`. This map is given by left-multiplication by `a`:
`x ↦ f.toPreGNS (a * f.ofPreGNS x)`.

This is the map that is lifted to the completion of `f.PreGNS` (i.e. `f.GNS`) in order to define
`gnsNonUnitalStarAlgHom`.
-/
@[simps!]
/-
**PositiveLinearMap.leftMulMapPreGNS** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMa
p`。
形式化陈述：leftMulMapPreGNS (a : A) : f.PreGNS ->L[Complex] f.PreGNS
参数：a : A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A

--- 原说明 ---
The continuous linear map from a C⋆-algebra `A` to the `PositiveLinearMap.preGNS
` space induced by
a positive linear functional `f : A →ₚ[ℂ] ℂ`. This map is given by left-multipli
cation by `a`:
`x ↦ f.toPreGNS (a * f.ofPreGNS x)`.

This is the map that is lifted to the completion of `f.PreGNS` (i.e. `f.GNS`) in
 order to define
`gnsNonUnitalStarAlgHom`.
-/
noncomputable def leftMulMapPreGNS (a : A) : f.PreGNS →L[ℂ] f.PreGNS :=
  f.toPreGNS.toLinearMap ∘ₗ mul ℂ A a ∘ₗ f.ofPreGNS.toLinearMap |>.mkContinuous ‖a‖ fun x ↦ by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, ← RCLike.ofReal_le_ofReal (K := ℂ),
      RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, preGNS_norm_sq]
    have : star (f.ofPreGNS x) * star a * (a * f.ofPreGNS x) ≤
        ‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x := by
      rw [← mul_assoc, mul_assoc _ (star a), sq, ← CStarRing.norm_star_mul_self (x := a),
        smul_mul_assoc]
      exact CStarAlgebra.star_left_conjugate_le_norm_smul
    calc
      _ ≤ f (‖a‖ ^ 2 • star (f.ofPreGNS x) * f.ofPreGNS x) := by
        simpa using OrderHomClass.mono f this
      _ = _ := by simp [← Complex.coe_smul, preGNS_norm_sq, smul_mul_assoc]

@[simp]
/-
**PositiveLinearMap.leftMulMapPreGNS_mul_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Posi
tiveLinearMap`。
形式化陈述：leftMulMapPreGNS_mul_eq_comp (a b : A) : f.leftMulMapPreGNS (a * b) = f.le
ftMulMapPreGNS a ∘L f.leftMulMapPreGNS b
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PositiveLinearMap.leftMulMapPreGNS_apply`：∀ {A : Type u_1} [inst : NonUn
italCStarAlgebra A] [inst_1 : PartialOrder A] (f : A →ₚ[ℂ] ℂ) [inst_2 : StarOrde
redRing A]   (a : A) (x : f.Pr…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftMulMapPreGNS_mul_eq_comp (a b : A) :
    f.leftMulMapPreGNS (a * b) = f.leftMulMapPreGNS a ∘L f.leftMulMapPreGNS b := by
  ext c; simp [mul_assoc]

/--
This proves map_smul' of gnsNonUnitalStarAlgHom so that map_zero' can be proven as a direct
consequence.
-/
@[simp]
/-
**PositiveLinearMap.completion_leftMulMapPreGNS_map_smul** 是 Mathlib 中的一个引理，位于命名
空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This proves map_smul' of gnsNonUnitalStarAlgHom so that map_zero' can be proven 
as a direct
consequence.
-/
private lemma completion_leftMulMapPreGNS_map_smul (m : ℂ) (x : A) :
    (f.leftMulMapPreGNS (m • x)).completion = m • (f.leftMulMapPreGNS x).completion := by
  ext a
  induction a using induction_on with
  | hp =>
    exact isClosed_eq (f.leftMulMapPreGNS (m • x)).completion.continuous
      (m • (f.leftMulMapPreGNS x).completion).continuous
  | ih a => simp [smul_mul_assoc]

/--
The non-unital ⋆-homomorphism/⋆-representation of `A` into the algebra of bounded operators on
a Hilbert space that is constructed from a positive linear functional `f` on a possibly non-unital
C⋆-algebra.
-/
/-
**PositiveLinearMap.gnsNonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLi
nearMap`。
形式化陈述：gnsNonUnitalStarAlgHom : A ->⋆ₙₐ[Complex] (f.GNS ->L[Complex] f.GNS) where
 toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The non-unital ⋆-homomorphism/⋆-representation of `A` into the algebra of bounde
d operators on
a Hilbert space that is constructed from a positive linear functional `f` on a p
ossibly non-unital
C⋆-algebra.
-/
noncomputable def gnsNonUnitalStarAlgHom : A →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  toFun a := (f.leftMulMapPreGNS a).completion
  map_smul' := by simp
  map_zero' := by simpa using f.completion_leftMulMapPreGNS_map_smul 0 0
  map_add' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp [add_mul, Completion.coe_add]
  map_mul' _ _ := by
    ext c
    induction c using induction_on with
      | hp => apply isClosed_eq <;> fun_prop
      | ih c => simp
  map_star' a := by
    refine (eq_adjoint_iff (f.leftMulMapPreGNS (star a)).completion
      (f.leftMulMapPreGNS a).completion).mpr ?_
    intro x y
    induction x, y using induction_on₂ with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x y => simp [mul_assoc, preGNS_inner_def]
/-
**PositiveLinearMap.gnsNonUnitalStarAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Posi
tiveLinearMap`。
形式化陈述：gnsNonUnitalStarAlgHom_apply {a : A} : f.gnsNonUnitalStarAlgHom a = (f.lef
tMulMapPreGNS a).completion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `UniformSpace.Completion.instUniformContinuousConstSMul`：∀ (M : Type v) (
X : Type x) [inst : UniformSpace X] [inst_1 : SMul M X],   UniformContinuousCons
tSMul M (UniformSpace.Completion X)
· 使用定理 `UniformSpace.Completion.instSMulCommClassOfUniformContinuousConstSMul`：∀
 (M : Type v) (N : Type w) (X : Type x) [inst : UniformSpace X] [inst_1 : SMul M
 X] [inst_2 : SMul N X]   [SMulCommClass M N X] [UniformCon…
-/
lemma gnsNonUnitalStarAlgHom_apply {a : A} :
    f.gnsNonUnitalStarAlgHom a = (f.leftMulMapPreGNS a).completion := rfl

@[simp]
/-
**PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `
PositiveLinearMap`。
形式化陈述：gnsNonUnitalStarAlgHom_apply_coe {a : A} {b : f.PreGNS} : f.gnsNonUnitalSt
arAlgHom a b = f.leftMulMapPreGNS a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `UniformSpace.Completion.instUniformContinuousConstSMul`：∀ (M : Type v) (
X : Type x) [inst : UniformSpace X] [inst_1 : SMul M X],   UniformContinuousCons
tSMul M (UniformSpace.Completion X)
· 使用定理 `UniformSpace.Completion.instSMulCommClassOfUniformContinuousConstSMul`：∀
 (M : Type v) (N : Type w) (X : Type x) [inst : UniformSpace X] [inst_1 : SMul M
 X] [inst_2 : SMul N X]   [SMulCommClass M N X] [UniformCon…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.completion_apply_coe`：completion_apply_coe (f : α ->
SL[σ] β) (a : α) : f.completion a = f a
· 使用定理 `PositiveLinearMap.leftMulMapPreGNS_apply`：∀ {A : Type u_1} [inst : NonUn
italCStarAlgebra A] [inst_1 : PartialOrder A] (f : A →ₚ[ℂ] ℂ) [inst_2 : StarOrde
redRing A]   (a : A) (x : f.Pr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma gnsNonUnitalStarAlgHom_apply_coe {a : A} {b : f.PreGNS} :
    f.gnsNonUnitalStarAlgHom a b = f.leftMulMapPreGNS a b := by
  simp [gnsNonUnitalStarAlgHom_apply]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PositiveLinearMap.gnsNonUnitalStarAlgHom_map_one** 是 Mathlib 中的一个引理，位于命名空间 `Po
sitiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma gnsNonUnitalStarAlgHom_map_one : f.gnsNonUnitalStarAlgHom 1 = 1 := by
  ext b
  induction b using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih b => simp [gnsNonUnitalStarAlgHom]

/--
The unital ⋆-homomorphism/⋆-representation of `A` into the algebra of bounded operators on a Hilbert
space that is constructed from a positive linear functional `f` on a unital C⋆-algebra.

This is the unital version of `gnsNonUnitalStarAlgHom`.
-/
@[simps]
/-
**PositiveLinearMap.gnsStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：gnsStarAlgHom : A ->⋆ₐ[Complex] (f.GNS ->L[Complex] f.GNS) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unital ⋆-homomorphism/⋆-representation of `A` into the algebra of bounded op
erators on a Hilbert
space that is constructed from a positive linear functional `f` on a unital C⋆-a
lgebra.

This is the unital version of `gnsNonUnitalStarAlgHom`.
-/
noncomputable def gnsStarAlgHom : A →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) where
  __ := f.gnsNonUnitalStarAlgHom
  map_one' := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

end PositiveLinearMap

