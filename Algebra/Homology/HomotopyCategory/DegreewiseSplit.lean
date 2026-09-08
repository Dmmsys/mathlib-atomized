/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Degreewise split exact sequences of cochain complexes

The main result of this file is the lemma
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` which asserts
that a triangle in `HomotopyCategory C (ComplexShape.up ℤ)`
is distinguished iff it is isomorphic to the triangle attached to a
degreewise split short exact sequence of cochain complexes.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated Preadditive

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex HomComplex

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `1`-cocycle attached to a degreewise split short exact sequence of cochain complexes. -/
/-
**CochainComplex.cocycleOfDegreewiseSplit** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex`。
形式化陈述：cocycleOfDegreewiseSplit : Cocycle S.X₃ S.X₁ 1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `1`-cocycle attached to a degreewise split short exact sequence of cochain c
omplexes.
-/
def cocycleOfDegreewiseSplit : Cocycle S.X₃ S.X₁ 1 :=
  Cocycle.mk
    (Cochain.mk (fun p q _ => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by lia) (by
      ext p _ rfl
      have := mono_of_mono_fac (σ (p + 2)).f_r
      have r_f := fun n => (σ n).r_f
      have s_g := fun n => (σ n).s_g
      dsimp at this r_f s_g ⊢
      rw [δ_v 1 2 (by lia) _ p (p + 2) (by lia) (p + 1) (p + 1)
        (by lia) (by lia), Cochain.mk_v, Cochain.mk_v,
        show Int.negOnePow 2 = 1 by rfl, one_smul, assoc, assoc,
        ← cancel_mono (S.f.f (p + 2)), add_comp, assoc, assoc, assoc,
        assoc, assoc, assoc, zero_comp, ← S.f.comm, reassoc_of% (r_f (p + 1)),
        sub_comp, comp_sub, comp_sub, assoc, id_comp, d_comp_d, comp_zero, zero_sub,
        ← S.g.comm_assoc, reassoc_of% (s_g p), r_f (p + 2), comp_sub, comp_sub, comp_id,
        comp_sub, ← S.g.comm_assoc, reassoc_of% (s_g (p + 1)), d_comp_d_assoc, zero_comp,
        sub_zero, neg_add_cancel])

/-- The canonical morphism `S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧` attached to a degreewise split
short exact sequence of cochain complexes. -/
/-
**CochainComplex.homOfDegreewiseSplit** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex`
。
形式化陈述：homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(1 : Int)⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧` attached to a degreewise split
short exact sequence of cochain complexes.
-/
def homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CochainComplex.homOfDegreewiseSplit_f** 是 Mathlib 中的一个引理，位于命名空间 `CochainComple
x`。
形式化陈述：homOfDegreewiseSplit_f (n : Int) : (homOfDegreewiseSplit S σ).f n = (cocyc
leOfDegreewiseSplit S σ).1.v n (n + 1) rfl
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homOfDegreewiseSplit_f (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n =
      (cocycleOfDegreewiseSplit S σ).1.v n (n + 1) rfl := by
  simp [homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

/-- The triangle in `CochainComplex C ℤ` attached to a degreewise split short exact sequence
of cochain complexes. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
/-
**CochainComplex.triangleOfDegreewiseSplit** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex`。
形式化陈述：triangleOfDegreewiseSplit : Triangle (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle in `CochainComplex C ℤ` attached to a degreewise split short exact 
sequence
of cochain complexes.
-/
def triangleOfDegreewiseSplit : Triangle (CochainComplex C ℤ) :=
  Triangle.mk S.f S.g (homOfDegreewiseSplit S σ)

/-- The (distinguished) triangle in `HomotopyCategory C (ComplexShape.up ℤ)` attached to a
degreewise split short exact sequence of cochain complexes. -/
/-
**CochainComplex.trianglehOfDegreewiseSplit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cochain
Complex`。
形式化陈述：trianglehOfDegreewiseSplit : Triangle (HomotopyCategory C (ComplexShape.up
 Int))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (distinguished) triangle in `HomotopyCategory C (ComplexShape.up ℤ)` attache
d to a
degreewise split short exact sequence of cochain complexes.
-/
noncomputable abbrev trianglehOfDegreewiseSplit :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)

variable [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `(mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q`
when `p + 1 = q`. -/
/-
**CochainComplex.mappingConeHomOfDegreewiseSplitXIso** 是 Mathlib 中的一个定义，位于命名空间 `
CochainComplex`。
形式化陈述：mappingConeHomOfDegreewiseSplitXIso (p q : Int) (hpq : p + 1 = q) : (mappi
ngCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q where hom
参数：p q : Int；hpq : p + 1 = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X
 q`
when `p + 1 = q`.
-/
noncomputable def mappingConeHomOfDegreewiseSplitXIso (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q where
  hom := (mappingCone.fst (homOfDegreewiseSplit S σ)).1.v p q hpq ≫ (σ q).s -
    (mappingCone.snd (homOfDegreewiseSplit S σ)).v p p (add_zero p) ≫
      by exact (Cochain.ofHom S.f).v (p + 1) q (by lia)
  inv := S.g.f q ≫ (mappingCone.inl (homOfDegreewiseSplit S σ)).v q p (by lia) -
    by exact (σ q).r ≫ (S.X₁.XIsoOfEq hpq.symm).hom ≫
      (mappingCone.inr (homOfDegreewiseSplit S σ)).f p
  hom_inv_id := by
    subst hpq
    have s_g := (σ (p + 1)).s_g
    have f_r := (σ (p + 1)).f_r
    dsimp at s_g f_r ⊢
    -- the following list of lemmas was obtained by doing
    -- simp? [mappingCone.ext_from_iff _ (p + 1) _ rfl, reassoc_of% f_r, reassoc_of% s_g]
    -- which may require increasing maximum heart beats
    simp only [Cochain.ofHom_v, Int.reduceNeg, id_comp, comp_sub, sub_comp, assoc,
        reassoc_of% s_g, ShortComplex.Splitting.s_r_assoc, ShortComplex.map_X₃, eval_obj,
        ShortComplex.map_X₁, zero_comp, comp_zero, reassoc_of% f_r, zero_sub, sub_neg_eq_add,
        mappingCone.ext_from_iff _ (p + 1) _ rfl, comp_add, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, shiftFunctor_obj_X', sub_zero, add_zero, comp_id,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, add_eq_right, neg_eq_zero,
        true_and]
    rw [← comp_f_assoc, S.zero, zero_f, zero_comp]
  inv_hom_id := by
    subst hpq
    have h := (σ (p + 1)).id
    dsimp at h ⊢
    simp only [id_comp, Cochain.ofHom_v, comp_sub, sub_comp, assoc, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inr_f_fst_v_assoc, shiftFunctor_obj_X', zero_comp, comp_zero, sub_zero,
      mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_snd_v_assoc, zero_sub, sub_neg_eq_add, ← h]
    abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)⟧`. -/
@[simps!]
/-
**CochainComplex.mappingConeHomOfDegreewiseSplitIso** 是 Mathlib 中的一个定义，位于命名空间 `C
ochainComplex`。
形式化陈述：mappingConeHomOfDegreewiseSplitIso : mappingCone (homOfDegreewiseSplit S σ
) ≅ S.X₂⟦(1 : Int)⟧
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)
⟧`.
-/
noncomputable def mappingConeHomOfDegreewiseSplitIso :
    mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)⟧ :=
  Hom.isoOfComponents (fun p => mappingConeHomOfDegreewiseSplitXIso S σ p _ rfl) (by
    rintro p _ rfl
    have r_f := (σ (p + 1 + 1)).r_f
    have s_g := (σ (p + 1)).s_g
    dsimp at r_f s_g ⊢
    simp only [mappingConeHomOfDegreewiseSplitXIso, mappingCone.ext_from_iff _ _ _ rfl,
      mappingCone.inl_v_d_assoc _ (p + 1) _ (p + 1 + 1) (by linarith) (by lia),
      cocycleOfDegreewiseSplit, r_f, Int.reduceNeg, Cochain.ofHom_v, sub_comp, assoc,
      Hom.comm, comp_sub, mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
      shiftFunctor_obj_X', zero_comp, sub_zero, homOfDegreewiseSplit_f,
      mappingCone.inr_f_fst_v_assoc, comp_zero, zero_sub, mappingCone.inr_f_snd_v_assoc,
      neg_neg, mappingCone.inr_f_d_assoc, shiftFunctor_obj_d',
      Int.negOnePow_one, neg_comp, sub_neg_eq_add, zero_add, and_true,
      Units.neg_smul, one_smul, comp_neg, ShortComplex.map_X₂, eval_obj, Cocycle.mk_coe,
      Cochain.mk_v]
    simp only [← S.g.comm_assoc, reassoc_of% s_g, comp_id]
    abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv** 是 Mathlib
 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv : S.f⟦(1 : Int)⟧' ≫ (m
appingConeHomOfDegreewiseSplitIso S σ).inv = -mappingCone.inr _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.ShortComplex.Splitting.f_r`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S :
 CategoryTheory.ShortComplex C}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomologicalComplex.comp_f_assoc`：∀ {ι : Type u_1} {V : Type u} [inst : C
ategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.ShortComplex.zero`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   (
self : CategoryTheory.…
· 使用定理 `HomologicalComplex.zero_f`：zero_f (C D : HomologicalComplex V c) (i : ι)
 : (0 : C ⟶ D).f i = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
-/
lemma shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv :
    S.f⟦(1 : ℤ)⟧' ≫ (mappingConeHomOfDegreewiseSplitIso S σ).inv = -mappingCone.inr _ := by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp, comp_sub, ← comp_f_assoc, S.zero, zero_f, zero_comp, zero_sub, reassoc_of% h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor** 是 Ma
thlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃ :
    (mappingConeHomOfDegreewiseSplitIso S σ).inv ≫
      (mappingCone.triangle (homOfDegreewiseSplit S σ)).mor₃ = -S.g⟦(1 : ℤ)⟧' := by
  ext n
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  simp only [Int.reduceNeg, id_comp, sub_comp, assoc, mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id,
    mappingCone.inr_f_triangle_mor₃_f, comp_zero, sub_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of triangles
`(triangleOfDegreewiseSplit S σ).rotate.rotate ≅ mappingCone.triangle (homOfDegreewiseSplit S σ)`
when `S` is a degreewise split short exact sequence of cochain complexes. -/
/-
**CochainComplex.triangleOfDegreewiseSplitRotateRotateIso** 是 Mathlib 中的一个定义，位于命
名空间 `CochainComplex`。
形式化陈述：triangleOfDegreewiseSplitRotateRotateIso : (triangleOfDegreewiseSplit S σ)
.rotate.rotate ≅ mappingCone.triangle (homOfDegreewiseSplit S σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism of triangles
`(triangleOfDegreewiseSplit S σ).rotate.rotate ≅ mappingCone.triangle (homOfDegr
eewiseSplit S σ)`
when `S` is a degreewise split short exact sequence of cochain complexes.
-/
noncomputable def triangleOfDegreewiseSplitRotateRotateIso :
    (triangleOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangle (homOfDegreewiseSplit S σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mappingConeHomOfDegreewiseSplitIso S σ).symm
    (by dsimp; simp only [comp_id, id_comp])
    (by dsimp; simp only [neg_comp, shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv,
      neg_neg, id_comp])
    (by dsimp; simp only [CategoryTheory.Functor.map_id, comp_id,
      mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃])

/-- The canonical isomorphism between `(trianglehOfDegreewiseSplit S σ).rotate.rotate` and
`mappingCone.triangleh (homOfDegreewiseSplit S σ)` when `S` is a degreewise split
short exact sequence of cochain complexes. -/
/-
**CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso** 是 Mathlib 中的一个定义，位于
命名空间 `CochainComplex`。
形式化陈述：trianglehOfDegreewiseSplitRotateRotateIso : (trianglehOfDegreewiseSplit S 
σ).rotate.rotate ≅ mappingCone.triangleh (homOfDegreewiseSplit S σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism between `(trianglehOfDegreewiseSplit S σ).rotate.rotat
e` and
`mappingCone.triangleh (homOfDegreewiseSplit S σ)` when `S` is a degreewise spli
t
short exact sequence of cochain complexes.
-/
noncomputable def trianglehOfDegreewiseSplitRotateRotateIso :
    (trianglehOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangleh (homOfDegreewiseSplit S σ) :=
  (rotate _).mapIso ((HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _) ≪≫
    (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ)

namespace mappingCone

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
/-- Given a morphism of cochain complexes `φ`, this is the short complex
given by `(triangle φ).rotate`. -/
@[simps]
/-
**CochainComplex.mappingCone.triangleRotateShortComplex** 是 Mathlib 中的一个定义，位于命名空
间 `CochainComplex.mappingCone`。
形式化陈述：triangleRotateShortComplex : ShortComplex (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of cochain complexes `φ`, this is the short complex
given by `(triangle φ).rotate`.
-/
noncomputable def triangleRotateShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (triangle φ).rotate.mor₁ (triangle φ).rotate.mor₂ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `triangleRotateShortComplex φ` is a degreewise split short exact sequence of
cochain complexes. -/
@[simps]
/-
**CochainComplex.mappingCone.triangleRotateShortComplexSplitting** 是 Mathlib 中的一
个定义，位于命名空间 `CochainComplex.mappingCone`。
形式化陈述：triangleRotateShortComplexSplitting (n : Int) : ((triangleRotateShortCompl
ex φ).map (eval _ _ n)).Splitting where s
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`triangleRotateShortComplex φ` is a degreewise split short exact sequence of
cochain complexes.
-/
noncomputable def triangleRotateShortComplexSplitting (n : ℤ) :
    ((triangleRotateShortComplex φ).map (eval _ _ n)).Splitting where
  s := -(inl φ).v (n + 1) n (by lia)
  r := (snd φ).v n n (add_zero n)
  id := by simp [ext_from_iff φ _ _ rfl]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CochainComplex.mappingCone.cocycleOfDegreewiseSplit_triangleRotateShortComplex
Splitting_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mappingCone`。
形式化陈述：cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v (p : Int) :
 (cocycleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)).1.v p _ rf
l = -φ.f _
参数：p : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CochainComplex.HomComplex.Cocycle.mk.congr_simp`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G
 : CochainComplex C ℤ} {n : ℤ} (z z_1…
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.mappingCone.d_snd_v`：d_snd_v (i j : Int) (hij : i + 1 = j
) : (mappingCone φ).d i j ≫ (snd φ).v j j (add_zero _) = (fst φ).1.v i j hij ≫ φ
.f j + (snd φ).v i i (ad…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.mappingCone.inl_v_fst_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CochainComplex.mappingCone.inl_v_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v (p : ℤ) :
    (cocycleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)).1.v p _ rfl =
      -φ.f _ := by
  simp [cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]

set_option backward.isDefEq.respectTransparency false in
/-- The triangle `(triangle φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes. -/
/-
**CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit** 是 Math
lib 中的一个定义，位于命名空间 `CochainComplex.mappingCone`。
形式化陈述：triangleRotateIsoTriangleOfDegreewiseSplit : (triangle φ).rotate ≅ triangl
eOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle `(triangle φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes.
-/
noncomputable def triangleRotateIsoTriangleOfDegreewiseSplit :
    (triangle φ).rotate ≅
      triangleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by ext; simp)

/-- The triangle `(triangleh φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes. -/
/-
**CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit** 是 Ma
thlib 中的一个定义，位于命名空间 `CochainComplex.mappingCone`。
形式化陈述：trianglehRotateIsoTrianglehOfDegreewiseSplit : (triangleh φ).rotate ≅ tria
nglehOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle `(triangleh φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes.
-/
noncomputable def trianglehRotateIsoTrianglehOfDegreewiseSplit :
    (triangleh φ).rotate ≅
      trianglehOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleRotateIsoTriangleOfDegreewiseSplit φ)

end mappingCone

end CochainComplex

namespace HomotopyCategory

variable [HasZeroObject C] [HasBinaryBiproducts C]

/-
**HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit** 是 Mathlib 
中的一个引理，位于命名空间 `HomotopyCategory`。
形式化陈述：distinguished_iff_iso_trianglehOfDegreewiseSplit (T : Triangle (HomotopyCa
tegory C (ComplexShape.up Int))) : (T in distTriang _) ↔ exists (S : ShortComple
x (CochainComplex C Int)) (σ : forall n, (S.map (HomologicalComplex.eval C _ n))
.Splitting), Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ)
参数：T : Triangle (HomotopyCategory C (ComplexShape.up Int))。
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
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `CategoryTheory.Pretriangulated.inv_rot_of_distTriang`：inv_rot_of_distTri
ang (T : Triangle C) (H : T in distTriang C) : T.invRotate in distTriang C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pretriangulated.rotate_distinguished_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
-/
lemma distinguished_iff_iso_trianglehOfDegreewiseSplit
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    (T ∈ distTriang _) ↔ ∃ (S : ShortComplex (CochainComplex C ℤ))
      (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting),
      Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle, rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

end HomotopyCategory

