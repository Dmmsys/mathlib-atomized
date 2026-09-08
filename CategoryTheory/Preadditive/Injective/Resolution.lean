/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a quasi-isomorphism `I.ι` from the cochain complex consisting just of `Z`
in degree zero to `I.cocomplex`.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/

@[expose] public section


noncomputable section

universe v u

namespace CategoryTheory

open Limits HomologicalComplex CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
/--
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism from the complex consisting of just `Z` supported in degree `0`.
-/
/-
**CategoryTheory.InjectiveResolution** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：InjectiveResolution (Z : C) where /-- the cochain complex involved in the 
resolution -/ cocomplex : CochainComplex C Nat /-- the cochain complex must be d
egreewise injective -/ injective : forall n, Injective (cocomplex.X n)
参数：Z : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of 
injective objects,
along with a quasi-isomorphism from the complex consisting of just `Z` supported
 in degree `0`.
-/
structure InjectiveResolution (Z : C) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C ℕ
  /-- the cochain complex must be degreewise injective -/
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  /-- the cochain complex must have homology -/
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  /-- the morphism from the single cochain complex with `Z` in degree `0` -/
  ι : (single₀ C).obj Z ⟶ cocomplex
  /-- the morphism from the single cochain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance

open InjectiveResolution in
attribute [instance] injective hasHomology InjectiveResolution.quasiIso

/-- An object admits an injective resolution. -/
/-
**CategoryTheory.HasInjectiveResolution** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroObject C] → [CategoryTheory.Limits.HasZeroMorphisms C] → C 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object admits an injective resolution.
-/
class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)

attribute [inherit_doc HasInjectiveResolution] HasInjectiveResolution.out

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughInjectives C]` and `[Abelian C]`. -/
/-
**CategoryTheory.HasInjectiveResolutions** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroObject C] → [CategoryTheory.Limits.HasZeroMorphisms C] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
You will rarely use this typeclass directly: it is implied by the combination
`[EnoughInjectives C]` and `[Abelian C]`.
-/
class HasInjectiveResolutions : Prop where
  out : ∀ Z : C, HasInjectiveResolution Z

attribute [instance 100] HasInjectiveResolutions.out

end

namespace InjectiveResolution

variable {Z : C} (I : InjectiveResolution Z)

/-
**CategoryTheory.InjectiveResolution.cocomplex_exactAt_succ** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：cocomplex_exactAt_succ (n : Nat) : I.cocomplex.ExactAt (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.InjectiveResolution.hasHomology`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C
]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIsoAt_iff_exactAt`：quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.Ha
sHomology i] [L.HasHomology i] (hK : K.ExactAt i) : QuasiIsoAt f i ↔ L.ExactAt i
· 使用引理 `CochainComplex.exactAt_succ_single_obj`：CochainComplex.exactAt_succ_sing
le_obj (A : C) (n : Nat) : ExactAt ((single₀ C).obj A) (n + 1)
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `CategoryTheory.InjectiveResolution.quasiIso`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]  
 [inst_2 : CategoryTheory.Limits.…
-/
lemma cocomplex_exactAt_succ (n : ℕ) :
    I.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance
/-
**CategoryTheory.InjectiveResolution.exact_succ** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.InjectiveResolution`。
形式化陈述：exact_succ (n : Nat) : (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1
) (n + 2))).Exact
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.prev_nat_succ`：prev_nat_succ (i : Nat) : (ComplexShape.up
 Nat).prev (i + 1) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用引理 `CategoryTheory.InjectiveResolution.cocomplex_exactAt_succ`：cocomplex_exa
ctAt_succ (n : Nat) : I.cocomplex.ExactAt (n + 1)
-/
lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

@[simp]
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_f_succ (n : ℕ) : I.ι.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_f_zero_comp_complex_d :
    I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
  simp
/-
**CategoryTheory.InjectiveResolution.complex_d_comp** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.InjectiveResolution`。
形式化陈述：complex_d_comp (n : Nat) : I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1)
 (n + 2) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem complex_d_comp (n : ℕ) :
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) kernel fork given by the composition
`Z ⟶ I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
@[simp]
/-
**CategoryTheory.InjectiveResolution.kernelFork** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.InjectiveResolution`。
形式化陈述：kernelFork : KernelFork (I.cocomplex.d 0 1)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.InjectiveResolution.ι_f_zero_comp_complex_d`：ι_f_zero_com
p_complex_d : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0

--- 原说明 ---
The (limit) kernel fork given by the composition
`Z ⟶ I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`.
-/
def kernelFork : KernelFork (I.cocomplex.d 0 1) :=
  KernelFork.ofι _ I.ι_f_zero_comp_complex_d

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Z` is the kernel of `I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
/-
**CategoryTheory.InjectiveResolution.isLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.InjectiveResolution`。
形式化陈述：isLimitKernelFork : IsLimit (I.kernelFork)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Z` is the kernel of `I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveReso
lution Z`.
-/
def isLimitKernelFork : IsLimit (I.kernelFork) := by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up ℕ) _ _).hom,
    ← cancel_epi (isoHomologyπ₀ _).hom,
    ← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up ℕ) _ _).inv]
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Mono (I.ι.f n) := by
  cases n
  · exact mono_of_isLimit_fork I.isLimitKernelFork
  · rw [ι_f_succ]; infer_instance

variable (Z)

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
@[simps]
/-
**CategoryTheory.InjectiveResolution.self** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.InjectiveResolution`。
形式化陈述：self [Injective Z] : InjectiveResolution Z where cocomplex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective object admits a trivial injective resolution: itself in degree 0.
-/
def self [Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp

variable {Z} {Z' : C} (I' : InjectiveResolution Z')

/-- Given injective resolutions `I` and `I'` of two objects `Z` and `Z'`,
and a morphism `f : Z ⟶ Z'`, this structure contains the data of a morphism
`I.cocomplex ⟶ I'.cocomplex` which is compatible with `f` -/
/-
**CategoryTheory.InjectiveResolution.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.InjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] →       [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] →         {Z : C} →           CategoryTheory.InjectiveResolu
tion Z → {Z' : C} → CategoryTheory.InjectiveResolution Z' → (Z ⟶ Z') → Type v
参数：Z ⟶ Z'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given injective resolutions `I` and `I'` of two objects `Z` and `Z'`,
and a morphism `f : Z ⟶ Z'`, this structure contains the data of a morphism
`I.cocomplex ⟶ I'.cocomplex` which is compatible with `f`
-/
structure Hom (f : Z ⟶ Z') where
  /-- A morphism between the cocomplexes -/
  hom : I.cocomplex ⟶ I'.cocomplex
  ι_f_zero_comp_hom_f_zero : I.ι.f 0 ≫ hom.f 0 = ((single₀ C).map f).f 0 ≫ I'.ι.f 0

namespace Hom

attribute [reassoc (attr := simp)] ι_f_zero_comp_hom_f_zero

set_option backward.isDefEq.respectTransparency false in
variable {I I'} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.InjectiveResolution.Hom.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.InjectiveResolution.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_hom {f : Z ⟶ Z'} (φ : Hom I I' f) :
    I.ι ≫ φ.hom = (single₀ C).map f ≫ I'.ι := by cat_disch

end Hom

end InjectiveResolution

end CategoryTheory

