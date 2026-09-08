/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

@[expose] public section


universe v u v' u'

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex

variable {C : Type u} [Category.{v} C]

open Projective

variable [HasZeroObject C] [HasZeroMorphisms C]

/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
/-
**CategoryTheory.ProjectiveResolution** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`
。
形式化陈述：ProjectiveResolution (Z : C) where /-- the chain complex involved in the r
esolution -/ complex : ChainComplex C Nat /-- the chain complex must be degreewi
se projective -/ projective : forall n, Projective (complex.X n)
参数：Z : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of pr
ojective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported i
n degree `0`.
-/
structure ProjectiveResolution (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C ℕ
  /-- the chain complex must be degreewise projective -/
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  /-- the chain complex must have homology -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance

open ProjectiveResolution in
attribute [instance] projective hasHomology ProjectiveResolution.quasiIso

/-- An object admits a projective resolution.
-/
/-
**CategoryTheory.HasProjectiveResolution** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroObject C] → [CategoryTheory.Limits.HasZeroMorphisms C] → C 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object admits a projective resolution.
-/
class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[EnoughProjectives C]` and `[Abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
/-
**CategoryTheory.HasProjectiveResolutions** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroObject C] → [CategoryTheory.Limits.HasZeroMorphisms C] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
You will rarely use this typeclass directly: it is implied by the combination
`[EnoughProjectives C]` and `[Abelian C]`.
By itself it's enough to set up the basic theory of derived functors.
-/
class HasProjectiveResolutions : Prop where
  out : ∀ Z : C, HasProjectiveResolution Z

attribute [instance 100] HasProjectiveResolutions.out

namespace ProjectiveResolution

variable {C}
variable {Z : C} (P : ProjectiveResolution Z)

/-
**CategoryTheory.ProjectiveResolution.complex_exactAt_succ** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：complex_exactAt_succ (n : Nat) : P.complex.ExactAt (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.ProjectiveResolution.hasHomology`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject 
C]   [inst_2 : CategoryTheory.Limits.…
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasiIsoAt_iff_exactAt'`：quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.
HasHomology i] [L.HasHomology i] (hL : L.ExactAt i) : QuasiIsoAt f i ↔ K.ExactAt
 i
· 使用引理 `ChainComplex.exactAt_succ_single_obj`：ChainComplex.exactAt_succ_single_o
bj (A : C) (n : Nat) : ExactAt ((single₀ C).obj A) (n + 1)
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `CategoryTheory.ProjectiveResolution.quasiIso`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
  [inst_2 : CategoryTheory.Limits.…
-/
lemma complex_exactAt_succ (n : ℕ) :
    P.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance
/-
**CategoryTheory.ProjectiveResolution.exact_succ** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ProjectiveResolution`。
形式化陈述：exact_succ (n : Nat) : (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n
 + 1) n)).Exact
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.prev`：prev (α : Type*) [AddRightCancelSemigroup α] [One α] 
(i : α) : (ComplexShape.down α).prev i = i + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ChainComplex.next_nat_succ`：next_nat_succ (i : Nat) : (ComplexShape.down
 Nat).next (i + 1) = i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ProjectiveResolution.complex_exactAt_succ`：complex_exactA
t_succ (n : Nat) : P.complex.ExactAt (n + 1)
-/
lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_f_succ (n : ℕ) : P.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.complex_d_comp_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem complex_d_comp_π_f_zero :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← P.π.comm 1 0, single_obj_d, comp_zero]
/-
**CategoryTheory.ProjectiveResolution.complex_d_succ_comp** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：complex_d_succ_comp (n : Nat) : P.complex.d n (n + 1) ≫ P.complex.d (n + 1
) (n + 2) = 0
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
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `ComplexShape.down_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRight
CancelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.down α).Rel i j = (j + 
1 = i)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem complex_d_succ_comp (n : ℕ) :
    P.complex.d n (n + 1) ≫ P.complex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) cokernel cofork given by the composition
`P.complex.X 1 ⟶ P.complex.X 0 ⟶ Z` when `P : ProjectiveResolution Z`. -/
@[simp]
/-
**CategoryTheory.ProjectiveResolution.cokernelCofork** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ProjectiveResolution`。
形式化陈述：cokernelCofork : CokernelCofork (P.complex.d 1 0)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ProjectiveResolution.complex_d_comp_π_f_zero`：complex_d_c
omp_π_f_zero : P.complex.d 1 0 ≫ P.π.f 0 = 0

--- 原说明 ---
The (limit) cokernel cofork given by the composition
`P.complex.X 1 ⟶ P.complex.X 0 ⟶ Z` when `P : ProjectiveResolution Z`.
-/
noncomputable def cokernelCofork : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Z` is the cokernel of `P.complex.X 1 ⟶ P.complex.X 0` when `P : ProjectiveResolution Z`. -/
/-
**CategoryTheory.ProjectiveResolution.isColimitCokernelCofork** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：isColimitCokernelCofork : IsColimit (P.cokernelCofork)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Z` is the cokernel of `P.complex.X 1 ⟶ P.complex.X 0` when `P : ProjectiveResol
ution Z`.
-/
noncomputable def isColimitCokernelCofork : IsColimit (P.cokernelCofork) := by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Epi (P.π.f n) := by
  cases n
  · exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  · rw [π_f_succ]; infer_instance

variable (Z)

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
@[simps]
/-
**CategoryTheory.ProjectiveResolution.self** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ProjectiveResolution`。
形式化陈述：self [Projective Z] : ProjectiveResolution Z where complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A projective object admits a trivial projective resolution: itself in degree 0.
-/
noncomputable def self [Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp

variable {Z} {Z' : C} (P' : ProjectiveResolution Z')

/-- Given projective resolutions `P` and `P'` of two objects `Z` and `Z'`,
and a morphism `f : Z ⟶ Z'`, this structure contains the data of a morphism
`P.complex ⟶ P'.complex` which is compatible with `f` -/
/-
**CategoryTheory.ProjectiveResolution.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.ProjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] →       [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] →         {Z : C} →           CategoryTheory.ProjectiveResol
ution Z → {Z' : C} → CategoryTheory.ProjectiveResolution Z' → (Z ⟶ Z') → Type v
参数：Z ⟶ Z'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given projective resolutions `P` and `P'` of two objects `Z` and `Z'`,
and a morphism `f : Z ⟶ Z'`, this structure contains the data of a morphism
`P.complex ⟶ P'.complex` which is compatible with `f`
-/
structure Hom (f : Z ⟶ Z') where
  /-- A morphism between the cocomplexes -/
  hom : P.complex ⟶ P'.complex
  hom_f_zero_comp_π_f_zero : hom.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ ((single₀ C).map f).f 0

namespace Hom

attribute [reassoc (attr := simp)] hom_f_zero_comp_π_f_zero

set_option backward.isDefEq.respectTransparency false in
variable {I I'} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ProjectiveResolution.Hom.hom_comp_** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ProjectiveResolution.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp_π {f : Z ⟶ Z'} (φ : Hom P P' f) :
    φ.hom ≫ P'.π = P.π ≫ (single₀ C).map f := by cat_disch

end Hom

end ProjectiveResolution

namespace Functor

open Limits

variable {C : Type u} [Category* C] [HasZeroObject C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [CategoryWithHomology D]

/-- An additive functor `F` which preserves homology and sends projective objects to projective
objects sends a projective resolution of `Z` to a projective resolution of `F.obj Z`. -/
@[simps complex π]
/-
**CategoryTheory.Functor.mapProjectiveResolution** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：mapProjectiveResolution (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObj
ects] [F.PreservesHomology] {Z : C} (P : ProjectiveResolution Z) : ProjectiveRes
olution (F.obj Z) where complex
参数：F : C ⥤ D；P : ProjectiveResolution Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
An additive functor `F` which preserves homology and sends projective objects to
 projective
objects sends a projective resolution of `Z` to a projective resolution of `F.ob
j Z`.
-/
noncomputable def mapProjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology] {Z : C} (P : ProjectiveResolution Z) :
    ProjectiveResolution (F.obj Z) where
  complex := (F.mapHomologicalComplex _).obj P.complex
  projective n := PreservesProjectiveObjects.projective_obj (P.projective n)
  π := (F.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end CategoryTheory.Functor

