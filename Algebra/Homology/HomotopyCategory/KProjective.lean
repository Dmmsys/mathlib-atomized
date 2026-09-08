/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.CochainComplexOpposite

/-!
# K-projective cochain complexes

We define the notion of K-projective cochain complex in an abelian category,
and show that bounded above complexes of projective objects are K-projective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using a projective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

open CategoryTheory Limits Preadditive Opposite

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `L`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `L`.)
/-- A cochain complex `K` is K-projective if any morphism `K ⟶ L`
with `L` acyclic is homotopic to zero. -/
/-
**CochainComplex.IsKProjective** 是 Mathlib 中的一个类，位于命名空间 `CochainComplex`。
形式化陈述：IsKProjective (K : CochainComplex C Int) : Prop where nonempty_homotopy_ze
ro {L : CochainComplex C Int} (f : K ⟶ L) : L.Acyclic -> Nonempty (Homotopy f 0)
  /-- A choice of homotopy to zero for a morphism from a K-projective cochain co
mplex to an acyclic cochain complex. -/ noncomputable irreducible_def IsKProject
ive.homotopyZero {K L : CochainComplex C Int} (f : K ⟶ L) (hL : L.Acyclic) [K.Is
KProjective] : Homotopy f 0
参数：K : CochainComplex C Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cochain complex `K` is K-projective if any morphism `K ⟶ L`
with `L` acyclic is homotopic to zero.
-/
class IsKProjective (K : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {L : CochainComplex C ℤ} (f : K ⟶ L) :
    L.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from a
K-projective cochain complex to an acyclic cochain complex. -/
noncomputable irreducible_def IsKProjective.homotopyZero
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hL : L.Acyclic) [K.IsKProjective] :
    Homotopy f 0 :=
  (IsKProjective.nonempty_homotopy_zero f hL).some

/-
**CochainComplex._root_.HomotopyEquiv.isKProjective** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HomotopyEquiv.isKProjective {K₁ K₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv K₁ K₂)
    [K₁.IsKProjective] : K₂.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compRight f).trans (.ofEq (by simp))))
        (((IsKProjective.homotopyZero (e.hom ≫ f) hL).compLeft e.inv).trans (.ofEq (by simp)))⟩
/-
**CochainComplex.isKProjective_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`
。
形式化陈述：isKProjective_of_iso {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂) [K₁.IsKP
rojective] : K₂.IsKProjective
参数：e : K₁ ≅ K₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomotopyEquiv.isKProjective`：∀ {C : Type u_1} [inst : CategoryTheory.Cat
egory.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   {K₁ K₂ : CochainComple
x C ℤ} (e : Homot…
-/
lemma isKProjective_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂)
    [K₁.IsKProjective] :
    K₂.IsKProjective :=
  (HomotopyEquiv.ofIso e).isKProjective
/-
**CochainComplex.isKProjective_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex`。
形式化陈述：isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C Int} (e : K₁ ≅ K₂) : K₁
.IsKProjective ↔ K₂.IsKProjective
参数：e : K₁ ≅ K₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isKProjective_of_iso`：isKProjective_of_iso {K₁ K₂ : Cocha
inComplex C Int} (e : K₁ ≅ K₂) [K₁.IsKProjective] : K₂.IsKProjective
-/
lemma isKProjective_iff_of_iso {K₁ K₂ : CochainComplex C ℤ} (e : K₁ ≅ K₂) :
    K₁.IsKProjective ↔ K₂.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso e, fun _ ↦ isKProjective_of_iso e.symm⟩
/-
**CochainComplex.isKProjective_iff_leftOrthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex`。
形式化陈述：isKProjective_iff_leftOrthogonal (K : CochainComplex C Int) : K.IsKProject
ive ↔ (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal ((HomotopyCategory.
quotient _ _).obj K)
参数：K : CochainComplex C Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `HomotopyCategory.quotient_obj_surjective`：quotient_obj_surjective (X : H
omotopyCategory V c) : exists (K : HomologicalComplex V c), (quotient _ _).obj K
 = X
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopyCategory.eq_of_homotopy`：eq_of_homotopy {C D : HomologicalComple
x V c} (f g : C ⟶ D) (h : Homotopy f g) : (quotient V c).map f = (quotient V c).
map g
· 使用引理 `HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic`：quotie
nt_obj_mem_subcategoryAcyclic_iff_acyclic (K : CochainComplex C Int) : subcatego
ryAcyclic C ((quotient _ _).obj K) ↔ K.Acyclic
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomotopyCategory.instAdditiveHomologicalComplexQuotient`：∀ {ι : Type u_2
} (V : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheor
y.Preadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isKProjective_iff_leftOrthogonal (K : CochainComplex C ℤ) :
    K.IsKProjective ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL ↦ ?_,
      fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]
/-
**CochainComplex.IsKProjective.leftOrthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.IsKProjective`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   (K : CochainComplex C ℤ) [K.IsKProjective],   (Homoto
pyCategory.subcategoryAcyclic C).leftOrthogonal ((HomotopyCategory.quotient C (C
omplexShape.up ℤ)).obj K)
参数：K : CochainComplex C ℤ；HomotopyCategory.subcategoryAcyclic C；(HomotopyCategor
y.quotient C (ComplexShape.up ℤ)).obj K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.isKProjective_iff_leftOrthogonal`：isKProjective_iff_leftO
rthogonal (K : CochainComplex C Int) : K.IsKProjective ↔ (HomotopyCategory.subca
tegoryAcyclic C).leftOrthogonal ((Hom…
-/
lemma IsKProjective.leftOrthogonal (K : CochainComplex C ℤ) [K.IsKProjective] :
    (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  rwa [← isKProjective_iff_leftOrthogonal]
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : CochainComplex C ℤ) [hK : K.IsKProjective] (n : ℤ) :
    (K⟦n⟧).IsKProjective := by
  rw [isKProjective_iff_leftOrthogonal] at hK ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app K)
    ((HomotopyCategory.subcategoryAcyclic C).leftOrthogonal.le_shift n _ hK)
/-
**CochainComplex.isKProjective_shift_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex`。
形式化陈述：isKProjective_shift_iff (K : CochainComplex C Int) (n : Int) : (K⟦n⟧).IsKP
rojective ↔ K.IsKProjective
参数：K : CochainComplex C Int；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isKProjective_of_iso`：isKProjective_of_iso {K₁ K₂ : Cocha
inComplex C Int} (e : K₁ ≅ K₂) [K₁.IsKProjective] : K₂.IsKProjective
· 使用定理 `CochainComplex.instIsKProjectiveObjIntShiftFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]  
 (K : CochainComplex C ℤ) [hK : K.IsKPro…
-/
lemma isKProjective_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (K⟦n⟧).IsKProjective ↔ K.IsKProjective :=
  ⟨fun _ ↦ isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ ↦ inferInstance⟩
/-
**CochainComplex.isKProjective_of_op** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isKProjective_of_op {K : CochainComplex C Int} (hK : IsKInjective ((opEqui
valence C).functor.obj (op K))) : K.IsKProjective where nonempty_homotopy_zero {
L} f hL
参数：hK : IsKInjective ((opEquivalence C).functor.obj (op K))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.acyclic_op`：acyclic_op {K : CochainComplex C Int} (hK : K
.Acyclic) : ((opEquivalence C).functor.obj (op K)).Acyclic
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `HomologicalComplex.instHasZeroObject`：∀ {ι : Type u_1} {V : Type u} [ins
t : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `HomologicalComplex.instHasLimit`：∀ {C : Type u_1} {ι : Type u_2} {J : Ty
pe u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory
.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isKProjective_of_op {K : CochainComplex C ℤ}
    (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) :
    K.IsKProjective where
  nonempty_homotopy_zero {L} f hL :=
    ⟨homotopyUnop ((IsKInjective.homotopyZero
      ((opEquivalence C).functor.map f.op) (acyclic_op hL)).trans
        (.ofEq (by simp)))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence in
open Cochain.InductionUp in
/-
**CochainComplex.isKProjective_of_projective** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex`。
形式化陈述：isKProjective_of_projective (K : CochainComplex C Int) (d : Int) [K.IsStri
ctlyLE d] [forall (n : Int), Projective (K.X n)] : K.IsKProjective
参数：K : CochainComplex C Int；d : Int；n : Int；K.X n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Injective.instOppositeOpOfProjective`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {P : C} [CategoryTheory.Projective P], 
  CategoryTheory.Injective (Opposite.op P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用定理 `CategoryTheory.Limits.IsZero.op`：op (h : IsZero X) : IsZero (Opposite.op
 X)
· 使用引理 `CochainComplex.isZero_of_isStrictlyLE`：isZero_of_isStrictlyLE (n i : Int
) (hi : n < i
· 使用引理 `CochainComplex.isKProjective_of_op`：isKProjective_of_op {K : CochainComp
lex C Int} (hK : IsKInjective ((opEquivalence C).functor.obj (op K))) : K.IsKPro
jective where nonempty_h…
· 使用引理 `CochainComplex.isKInjective_of_injective`：isKInjective_of_injective (L :
 CochainComplex C Int) (d : Int) [L.IsStrictlyGE d] [forall (n : Int), Injective
 (L.X n)] : L.IsKInjective whe…
-/
lemma isKProjective_of_projective (K : CochainComplex C ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ (n : ℤ), Projective (K.X n)] :
    K.IsKProjective := by
  let L := ((opEquivalence C).functor.obj (op K))
  have (n : ℤ) : Injective (L.X n) := by
    dsimp [L]
    infer_instance
  have : L.IsStrictlyGE (-d) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE d _ (by dsimp; lia)).op
  exact isKProjective_of_op (isKInjective_of_injective L (-d))
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)] :
    CochainComplex.IsKProjective (K.extend ComplexShape.embeddingDownNat) :=
  CochainComplex.isKProjective_of_projective _ 0

end CochainComplex

