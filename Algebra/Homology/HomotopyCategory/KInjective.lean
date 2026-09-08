/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# K-injective cochain complexes

We define the notion of K-injective cochain complex in an abelian category,
and show that bounded below complexes of injective objects are K-injective.

## TODO (@joelriou)
* Provide an API for computing `Ext`-groups using an injective resolution

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive

variable {C : Type*} [Category* C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `K`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `K`.)
/-- A cochain complex `L` is K-injective if any morphism `K ⟶ L`
with `K` acyclic is homotopic to zero. -/
/-
**CochainComplex.IsKInjective** 是 Mathlib 中的一个类，位于命名空间 `CochainComplex`。
形式化陈述：IsKInjective (L : CochainComplex C Int) : Prop where nonempty_homotopy_zer
o {K : CochainComplex C Int} (f : K ⟶ L) : K.Acyclic -> Nonempty (Homotopy f 0) 
 /-- A choice of homotopy to zero for a morphism from an acyclic cochain complex
 to a K-injective cochain complex. -/ noncomputable irreducible_def IsKInjective
.homotopyZero {K L : CochainComplex C Int} (f : K ⟶ L) (hK : K.Acyclic) [L.IsKIn
jective] : Homotopy f 0
参数：L : CochainComplex C Int。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cochain complex `L` is K-injective if any morphism `K ⟶ L`
with `K` acyclic is homotopic to zero.
-/
class IsKInjective (L : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {K : CochainComplex C ℤ} (f : K ⟶ L) :
    K.Acyclic → Nonempty (Homotopy f 0)

/-- A choice of homotopy to zero for a morphism from an acyclic
cochain complex to a K-injective cochain complex. -/
noncomputable irreducible_def IsKInjective.homotopyZero {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : K.Acyclic) [L.IsKInjective] :
    Homotopy f 0 :=
  (IsKInjective.nonempty_homotopy_zero f hK).some

/-
**CochainComplex._root_.HomotopyEquiv.isKInjective** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HomotopyEquiv.isKInjective {L₁ L₂ : CochainComplex C ℤ}
    (e : HomotopyEquiv L₁ L₂)
    [L₁.IsKInjective] : L₂.IsKInjective where
  nonempty_homotopy_zero {K} f hK :=
    ⟨Homotopy.trans (Homotopy.trans (.ofEq (by simp))
      ((e.homotopyInvHomId.symm.compLeft f).trans (.ofEq (by simp))))
        (((IsKInjective.homotopyZero (f ≫ e.inv) hK).compRight e.hom).trans (.ofEq (by simp)))⟩
/-
**CochainComplex.isKInjective_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：isKInjective_of_iso {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂) [L₁.IsKIn
jective] : L₂.IsKInjective
参数：e : L₁ ≅ L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomotopyEquiv.isKInjective`：∀ {C : Type u_1} [inst : CategoryTheory.Cate
gory.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   {L₁ L₂ : CochainComplex
 C ℤ} (e : Homot…
-/
lemma isKInjective_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂)
    [L₁.IsKInjective] :
    L₂.IsKInjective :=
  (HomotopyEquiv.ofIso e).isKInjective
/-
**CochainComplex.isKInjective_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex`。
形式化陈述：isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C Int} (e : L₁ ≅ L₂) : L₁.
IsKInjective ↔ L₂.IsKInjective
参数：e : L₁ ≅ L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isKInjective_of_iso`：isKInjective_of_iso {L₁ L₂ : Cochain
Complex C Int} (e : L₁ ≅ L₂) [L₁.IsKInjective] : L₂.IsKInjective
-/
lemma isKInjective_iff_of_iso {L₁ L₂ : CochainComplex C ℤ} (e : L₁ ≅ L₂) :
    L₁.IsKInjective ↔ L₂.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso e, fun _ ↦ isKInjective_of_iso e.symm⟩
/-
**CochainComplex.isKInjective_iff_rightOrthogonal** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex`。
形式化陈述：isKInjective_iff_rightOrthogonal (L : CochainComplex C Int) : L.IsKInjecti
ve ↔ (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal ((HomotopyCategory.
quotient _ _).obj L)
参数：L : CochainComplex C Int。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopyCategory.eq_of_homotopy`：eq_of_homotopy {C D : HomologicalComple
x V c} (f g : C ⟶ D) (h : Homotopy f g) : (quotient V c).map f = (quotient V c).
map g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
lemma isKInjective_iff_rightOrthogonal (L : CochainComplex C ℤ) :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  refine ⟨fun _ K f hK ↦ ?_,
      fun hL ↦ ⟨fun {K} f hK ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]
/-
**CochainComplex.IsKInjective.rightOrthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Cochain
Complex.IsKInjective`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Abelian C]   (L : CochainComplex C ℤ) [L.IsKInjective],   (Homotop
yCategory.subcategoryAcyclic C).rightOrthogonal ((HomotopyCategory.quotient C (C
omplexShape.up ℤ)).obj L)
参数：L : CochainComplex C ℤ；HomotopyCategory.subcategoryAcyclic C；(HomotopyCategor
y.quotient C (ComplexShape.up ℤ)).obj L。
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
· 使用引理 `CochainComplex.isKInjective_iff_rightOrthogonal`：isKInjective_iff_rightO
rthogonal (L : CochainComplex C Int) : L.IsKInjective ↔ (HomotopyCategory.subcat
egoryAcyclic C).rightOrthogonal ((Hom…
-/
lemma IsKInjective.rightOrthogonal (L : CochainComplex C ℤ) [L.IsKInjective] :
    (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  rwa [← isKInjective_iff_rightOrthogonal]
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : CochainComplex C ℤ) [hL : L.IsKInjective] (n : ℤ) :
    (L⟦n⟧).IsKInjective := by
  rw [isKInjective_iff_rightOrthogonal] at hL ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app L)
    ((HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.le_shift n _ hL)
/-
**CochainComplex.isKInjective_shift_iff** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x`。
形式化陈述：isKInjective_shift_iff (L : CochainComplex C Int) (n : Int) : (L⟦n⟧).IsKIn
jective ↔ L.IsKInjective
参数：L : CochainComplex C Int；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.isKInjective_of_iso`：isKInjective_of_iso {L₁ L₂ : Cochain
Complex C Int} (e : L₁ ≅ L₂) [L₁.IsKInjective] : L₂.IsKInjective
· 使用定理 `CochainComplex.instIsKInjectiveObjIntShiftFunctor`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]   
(L : CochainComplex C ℤ) [hL : L.IsKInj…
-/
lemma isKInjective_shift_iff (L : CochainComplex C ℤ) (n : ℤ) :
    (L⟦n⟧).IsKInjective ↔ L.IsKInjective :=
  ⟨fun _ ↦ isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ ↦ inferInstance⟩
/-
**CochainComplex.isKInjective_of_injective_aux** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex`。
形式化陈述：isKInjective_of_injective_aux {K L : CochainComplex C Int} (f : K ⟶ L) (α 
: Cochain K L (-1)) (n m : Int) (hnm : n + 1 = m) (hK : K.ExactAt m) [Injective 
(L.X m)] (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) : exists (h : K.X (n + 2
) ⟶ L.X (n + 1)), (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f
) m
参数：f : K ⟶ L；α : Cochain K L (-1)；n m : Int；hnm : n + 1 = m；hK : K.ExactAt m；L.X
 m；hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.Hom.comm`：∀ {ι : Type u_1} {V : Type u} [inst : Categ
oryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
V] {c : ComplexSh…
· 使用引理 `CochainComplex.HomComplex.δ_v`：δ_v (hnm : n + 1 = m) (z : Cochain F G n)
 (p q : Int) (hpq : p + m = q) (q₁ q₂ : Int) (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q
₂) : (δ n m z).v p …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `HomologicalComplex.d_comp_d_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.exactAt_iff'`：exactAt_iff' (hi : c.prev j = i) (hk : 
c.next j = k) : K.ExactAt j ↔ (K.sc' i j k).Exact
· 使用定理 `CochainComplex.prev`：prev (α : Type*) [AddGroup α] [One α] (i : α) : (Co
mplexShape.up α).prev i = i - 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `CategoryTheory.ShortComplex.Exact.comp_descToInjective`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian 
C]   {S : CategoryTheory.ShortComplex C} (hS…
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
（共 39 条，此处仅展示前 30 条）
-/
lemma isKInjective_of_injective_aux {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

open Cochain.InductionUp in
/-
**CochainComplex.isKInjective_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `CochainCom
plex`。
形式化陈述：isKInjective_of_injective (L : CochainComplex C Int) (d : Int) [L.IsStrict
lyGE d] [forall (n : Int), Injective (L.X n)] : L.IsKInjective where nonempty_ho
motopy_zero {K} f hK
参数：L : CochainComplex C Int；d : Int；n : Int；L.X n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用引理 `CochainComplex.isKInjective_of_injective_aux`：isKInjective_of_injective_
aux {K L : CochainComplex C Int} (f : K ⟶ L) (α : Cochain K L (-1)) (n m : Int) 
(hnm : n + 1 = m) (hK : K.ExactAt …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v_eq_zero`：single_v_eq_zero {p 
q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q') (hp' :
 p' != p) : (single f n).v p' q' hpq' = …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_zero`：ofHom_zero : ofHom (0 : F 
⟶ G) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.ext₀`：ext₀ (z₁ z₂ : Cochain F G 0) (h 
: forall (p : Int), z₁.v p p (add_zero p) = z₂.v p p (add_zero p)) : z₁ = z₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `CochainComplex.HomComplex.δ_v`：δ_v (hnm : n + 1 = m) (z : Cochain F G n)
 (p q : Int) (hpq : p + m = q) (q₁ q₂ : Int) (hq₁ : q₁ = q - 1) (hq₂ : p + 1 = q
₂) : (δ n m z).v p …
· 使用引理 `CochainComplex.HomComplex.Cochain.InductionUp.limitSequence_eqUpTo`：limi
tSequence_eqUpTo (n : Nat) : (limitSequence φ hφ x₀).EqUpTo (sequence φ x₀ n).1 
(p₀ + n)
-/
lemma isKInjective_of_injective (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : ℕ) : Set (Cochain K L (-1)) :=
      Set.ofPred (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by lia)) _ _⟩
    let φ (n : ℕ) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
        (by lia) (hK _) α.2).choose_spec⟩
    have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by lia) (n - 1) (n + 1) rfl (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by lia) (by lia),
      limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by lia) (by lia)]
/-
**CochainComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : CochainComplex C ℕ) [∀ n, Injective (K.X n)] :
    IsKInjective (K.extend ComplexShape.embeddingUpNat) :=
  isKInjective_of_injective _ 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.IsKInjective.eq_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsKInjective.eq_δ_of_cocycle {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [L.IsKInjective] (hK : K.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKInjective.nonempty_homotopy_zero φ hK
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ, hf, δ_units_smul, Cochain.rightShift_units_smul,
    Cochain.δ_rightUnshift _ _ _ _ 0 (by simp)]
  simp [smul_smul]
/-
**CochainComplex.IsKInjective.eq_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsKInjective.eq_δ_of_cocycle' {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [L.IsKInjective] (hL : L.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨β, hβ⟩ :=
    IsKInjective.eq_δ_of_cocycle (Cocycle.ofHom (𝟙 L)) hL (-1) (by simp)
  exact ⟨z.1.comp β (by lia), by simp [δ_comp z.1 β _ _ 0 _ hm rfl (by simp), hβ]⟩

end CochainComplex

