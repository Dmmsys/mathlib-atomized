/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Refinements

/-!
# The mapping cone of a monomorphism, up to a quasi-isomorphism

If `S` is a short exact short complex of cochain complexes in an abelian category,
we construct a quasi-isomorphism `descShortComplex S : mappingCone S.f ⟶ S.X₃`.

We obtain this by comparing the homology sequence of `S` and the homology
sequence of the homology functor on the homotopy category, applied to the
distinguished triangle attached to the mapping cone of `S.f`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape HomotopyCategory Limits
  HomologicalComplex.HomologySequence Pretriangulated Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in -- Needed in homologySequenceδ_triangleh
@[reassoc]
/-
**CochainComplex.homologySequence** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequenceδ_quotient_mapTriangle_obj
    (T : Triangle (CochainComplex C ℤ)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ
        ((quotient C (up ℤ)).mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        (HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftMap T.mor₃ n₀ n₁ (by lia) ≫
        (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  apply homologyFunctor_shiftMap

namespace mappingCone

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

/-- The canonical morphism `mappingCone S.f ⟶ S.X₃` when `S` is a short complex
of cochain complexes. -/
/-
**CochainComplex.mappingCone.descShortComplex** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.mappingCone`。
形式化陈述：descShortComplex : mappingCone S.f ⟶ S.X₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `mappingCone S.f ⟶ S.X₃` when `S` is a short complex
of cochain complexes.
-/
noncomputable def descShortComplex : mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_descShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.mappingCone`。
形式化陈述：inr_descShortComplex : inr S.f ≫ descShortComplex S = S.g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.inr_desc`：inr_desc : inr φ ≫ desc φ α β eq = 
β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_descShortComplex : inr S.f ≫ descShortComplex S = S.g := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_descShortComplex_f** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.mappingCone`。
形式化陈述：inr_f_descShortComplex_f (n : Int) : (inr S.f).f n ≫ (descShortComplex S).
f n = S.g.f n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_f_descShortComplex_f (n : ℤ) : (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n := by
  simp [descShortComplex]

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_descShortComplex_f** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.mappingCone`。
形式化陈述：inl_v_descShortComplex_f (i j : Int) (h : i + (-1) = j) : (inl S.f).v i j 
h ≫ (descShortComplex S).f j = 0
参数：i j : Int；h : i + (-1) = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.inl_v_desc_f`：inl_v_desc_f (p q : Int) (h : p
 + (-1) = q) : (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_v_descShortComplex_f (i j : ℤ) (h : i + (-1) = j) :
    (inl S.f).v i j h ≫ (descShortComplex S).f j = 0 := by
  simp [descShortComplex]

section

variable (S₁ S₂ : ShortComplex (CochainComplex C ℤ)) (f : S₁ ⟶ S₂)

/-
**CochainComplex.mappingCone.map_descShortComplex** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.mappingCone`。
形式化陈述：map_descShortComplex : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortCo
mplex S₂ = descShortComplex S₁ ≫ f.τ₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.mappingCone.inl_v_desc_f_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F
 G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CochainComplex.mappingCone.inl_v_descShortComplex_f`：inl_v_descShortComp
lex_f (i j : Int) (h : i + (-1) = j) : (inl S.f).v i j h ≫ (descShortComplex S).
f j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   (S : CategoryTheory.ShortComplex (Cocha…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CochainComplex.mappingCone.inr_f_desc_f_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F
 G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.inr_f_descShortComplex_f`：inr_f_descShortComp
lex_f (n : Int) : (inr S.f).f n ≫ (descShortComplex S).f n = S.g.f n
· 使用定理 `CochainComplex.mappingCone.inr_f_descShortComplex_f_assoc`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   (S : CategoryTheory.ShortComplex (Cocha…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
-/
lemma map_descShortComplex : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ =
    descShortComplex S₁ ≫ f.τ₃ := by
  ext i
  simpa [mappingCone.ext_from_iff _ _ _ rfl, map] using
    congr_fun (congr_arg HomologicalComplex.Hom.f f.comm₂₃) i

end

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCone.homologySequence** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequenceδ_triangleh (n₀ : ℤ) (n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ (triangleh S.f) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        HomologicalComplex.homologyMap (descShortComplex S) n₀ ≫ hS.δ n₀ n₁ h ≫
          (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  /- We proceed by diagram chase. We test the identity on
     cocycles `x' : A' ⟶ (mappingCone S.f).X n₀` -/
  dsimp
  rw [← cancel_mono ((homologyFunctorFactors C (up ℤ) n₁).hom.app _),
    assoc, assoc, assoc, Iso.inv_hom_id_app,
    ← cancel_epi ((homologyFunctorFactors C (up ℤ) n₀).inv.app _), Iso.inv_hom_id_app_assoc]
  apply yoneda.map_injective
  ext ⟨A⟩ (x : A ⟶ _)
  obtain ⟨A', π, _, x', w, hx'⟩ :=
    (mappingCone S.f).eq_liftCycles_homologyπ_up_to_refinements x n₁ (by simpa using h)
  erw [homologySequenceδ_quotient_mapTriangle_obj_assoc _ _ _ h]
  dsimp
  -- simp? says
  simp only [Iso.inv_hom_id_app, HomologicalComplex.homologyFunctor_obj, Iso.inv_hom_id_app_assoc,
    comp_id]
  erw [comp_id]
  rw [← cancel_epi π, reassoc_of% hx', reassoc_of% hx',
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  /- We decompose the cocycle `x'` into two morphisms `a : A' ⟶ S.X₁.X n₁`
     and `b : A' ⟶ S.X₂.X n₀` satisfying certain relations. -/
  obtain ⟨a, b, hab⟩ := decomp_to _ x' n₁ h
  rw [hab, ext_to_iff _ n₁ (n₁ + 1) rfl, add_comp, assoc, assoc, inr_f_d, add_comp, assoc,
    assoc, assoc, assoc, inr_f_fst_v, comp_zero, comp_zero, add_zero, zero_comp,
    d_fst_v _ _ _ _ h, comp_neg, inl_v_fst_v_assoc, comp_neg, neg_eq_zero,
    add_comp, assoc, assoc, assoc, assoc, inr_f_snd_v, comp_id, zero_comp,
    d_snd_v _ _ _ h, comp_add, inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, add_zero] at w
  /- We simplify the RHS. -/
  conv_rhs => simp only [hab, add_comp, assoc, inr_f_descShortComplex_f,
    inl_v_descShortComplex_f, comp_zero, zero_add]
  rw [hS.δ_eq n₀ n₁ (by simpa using h) (b ≫ S.g.f n₀) _ b rfl (-a)
    (by simp only [neg_comp, neg_eq_iff_add_eq_zero, w.2]) (n₁ + 1) (by simp)]
  /- We simplify the LHS. -/
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    S.X₁.liftCycles_shift_homologyπ_assoc _ _ _ _ n₁ (by lia) (n₁ + 1) (by simp),
    Iso.inv_hom_id_app]
  dsimp [homologyFunctor_shift]
  simp only [hab, add_comp, assoc, inl_v_triangle_mor₃_f_assoc,
    shiftFunctorObjXIso, neg_comp, Iso.inv_hom_id, comp_neg, comp_id,
    inr_f_triangle_mor₃_f_assoc, zero_comp, comp_zero, add_zero]

open ComposableArrows

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hS in
/-
**CochainComplex.mappingCone.quasiIso_descShortComplex** 是 Mathlib 中的一个引理，位于命名空间
 `CochainComplex.mappingCone`。
形式化陈述：quasiIso_descShortComplex : QuasiIso (descShortComplex S) where quasiIsoAt
 n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff_isIso_homologyMap`：quasiIsoAt_iff_isIso_homologyMap (f : 
K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt f i ↔ IsIso (hom
ologyMap f i)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.homologyMap_comp`：homologyMap_comp : homologyMap (φ ≫
 ψ) i = homologyMap φ i ≫ homologyMap ψ i
· 使用引理 `CochainComplex.mappingCone.inr_descShortComplex`：inr_descShortComplex : 
inr S.f ≫ descShortComplex S = S.g
· 使用引理 `CochainComplex.mappingCone.homologySequenceδ_triangleh`：homologySequence
δ_triangleh (n₀ : Int) (n₁ : Int) (h : n₀ + 1 = n₁) : (homologyFunctor C (up Int
) 0).homologySequenceδ (triangleh S.f) n₀ n₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`：isIso_of_
epi_of_isIso_of_isIso_of_mono (h₀ : Epi (app' φ 0)) (h₁ : IsIso (app' φ 1)) (h₃ 
: IsIso (app' φ 3)) (h₄ : Mono (app' φ 4)) : IsIso …
· 使用定理 `CategoryTheory.ComposableArrows.Exact.δlast`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   {n : ℕ} {S : CategoryTh…
· 使用引理 `CategoryTheory.Functor.homologySequenceComposableArrows₅_exact`：homology
SequenceComposableArrows₅_exact : (F.homologySequenceComposableArrows₅ T n₀ n₁ h
).Exact
· 使用定理 `HomotopyCategory.instHasZeroObject`：∀ {ι : Type u_2} (V : Type u) [inst 
: CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Preadditive V]   (c
 : ComplexShape ι) [Cate…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
（共 44 条，此处仅展示前 30 条）
-/
lemma quasiIso_descShortComplex : QuasiIso (descShortComplex S) where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let φ : ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅
        (triangleh S.f) n _ rfl).δlast ⟶ (composableArrows₅ hS n _ rfl).δlast :=
      homMk₄ ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _ ≫
          HomologicalComplex.homologyMap (descShortComplex S) n)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.app _)
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
        (by
          erw [(homologyFunctorFactors C (up ℤ) n).hom.naturality_assoc]
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          rw [← HomologicalComplex.homologyMap_comp, inr_descShortComplex])
        (by
          -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
          dsimp [-Fin.reduceFinMk]
          erw [homologySequenceδ_triangleh hS]
          simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj, assoc,
            Iso.inv_hom_id_app, comp_id])
        ((homologyFunctorFactors C (up ℤ) _).hom.naturality S.f)
    have : IsIso ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f) ≫
        HomologicalComplex.homologyMap (descShortComplex S) n) := by
      apply Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
        ((homologyFunctor C (up ℤ) 0).homologySequenceComposableArrows₅_exact _
          (mappingCone_triangleh_distinguished S.f) n _ rfl).δlast
        (composableArrows₅_exact hS n _ rfl).δlast φ
      all_goals dsimp [φ]; infer_instance
    apply IsIso.of_isIso_comp_left ((homologyFunctorFactors C (up ℤ) n).hom.app (mappingCone S.f))

@[reassoc]
/-
**CochainComplex.mappingCone.descShortComplex_naturality** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.mappingCone`。
形式化陈述：descShortComplex_naturality {S₁ S₂ : ShortComplex (CochainComplex C Int)} 
(f : S₁ ⟶ S₂) : map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ = de
scShortComplex S₁ ≫ f.τ₃
参数：CochainComplex C Int；f : S₁ ⟶ S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₁₂`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用引理 `CochainComplex.mappingCone.ext_from`：ext_from (i j : Int) (hij : j + 1 =
 i) {A : C} {f g : (mappingCone φ).X j ⟶ A} (h₁ : (inl φ).v i j (by lia) ≫ f = (
inl φ).v i j (by lia) ≫ g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.mappingCone.inl_v_desc_f_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F
 G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CochainComplex.mappingCone.inl_v_descShortComplex_f`：inl_v_descShortComp
lex_f (i j : Int) (h : i + (-1) = j) : (inl S.f).v i j h ≫ (descShortComplex S).
f j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CochainComplex.mappingCone.inl_v_descShortComplex_f_assoc`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abeli
an C]   (S : CategoryTheory.ShortComplex (Cocha…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.mappingCone.inr_desc_assoc`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G :
 CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.inr_descShortComplex`：inr_descShortComplex : 
inr S.f ≫ descShortComplex S = S.g
· 使用定理 `CategoryTheory.ShortComplex.Hom.comm₂₃`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CochainComplex.mappingCone.inr_descShortComplex_assoc`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C
]   (S : CategoryTheory.ShortComplex (Cocha…
-/
lemma descShortComplex_naturality {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (f : S₁ ⟶ S₂) :
    map S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm ≫ descShortComplex S₂ = descShortComplex S₁ ≫ f.τ₃ := by
  ext n
  apply ext_from _ (n + 1) n rfl
  · simp [map]
  · simp [map, ← HomologicalComplex.comp_f, f.comm₂₃]

variable {D : Type*} [Category* D] [Abelian D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex** 是 M
athlib 中的一个引理，位于命名空间 `CochainComplex.mappingCone`。
形式化陈述：mapHomologicalComplexIso_hom_descShortComplex (F : C ⥤ D) [F.Additive] (S 
: ShortComplex (CochainComplex C Int)) : (mapHomologicalComplexIso _ _).hom ≫ de
scShortComplex (S.map (F.mapHomologicalComplex (.up Int))) = (F.mapHomologicalCo
mplex (.up Int)).map (descShortComplex S)
参数：F : C ⥤ D；S : ShortComplex (CochainComplex C Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.instPreservesZeroMorphismsHomologicalComplexMapHomologica
lComplex`：∀ {ι : Type u_1} {W₁ : Type u_3} {W₂ : Type u_4} [inst : CategoryTheor
y.Category.{v_2, u_3} W₁]   [inst_1 : CategoryTheory.Category.{v_3, u_…
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.mappingCone.desc_f`：desc_f (p q : Int) (hpq : p + 1 = q) 
: (desc φ α β eq).f p = (fst φ).1.v p q hpq ≫ α.v q p (by lia) + (snd φ).v p p (
add_zero p) ≫ β.f p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CochainComplex.mappingCone.inl_v_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CochainComplex.mappingCone.inr_f_snd_v_assoc`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F 
G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapHomologicalComplexIso_hom_descShortComplex (F : C ⥤ D) [F.Additive]
    (S : ShortComplex (CochainComplex C ℤ)) :
    (mapHomologicalComplexIso _ _).hom ≫
      descShortComplex (S.map (F.mapHomologicalComplex (.up ℤ))) =
    (F.mapHomologicalComplex (.up ℤ)).map (descShortComplex S) := by
  symm
  ext n
  simp [mapHomologicalComplexIso, descShortComplex, mapHomologicalComplexXIso,
    mapHomologicalComplexXIso'_hom, Functor.mapHomologicalComplex_map_f,
    desc_f _ _ _ _ n (n + 1) rfl]

end mappingCone

end CochainComplex

