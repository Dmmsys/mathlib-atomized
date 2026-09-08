/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # The pretriangulated structure on the homotopy category of complexes

In this file, we define the pretriangulated structure on the homotopy
category `HomotopyCategory C (ComplexShape.up ℤ)` of an additive category `C`.
The distinguished triangles are the triangles that are isomorphic to the
image in the homotopy category of the standard triangle
`K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` for some morphism of
cochain complexes `φ : K ⟶ L`.

This result first appeared in the Liquid Tensor Experiment. In the LTE, the
formalization followed the Stacks Project: in particular, the distinguished
triangles were defined using degreewise-split short exact sequences of cochain
complexes. Here, we follow the original definitions in [Verdier's thesis, I.3][verdier1996]
(with the better sign conventions from the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000]).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Brian Conrad, Grothendieck duality and base change][conrad2000]
* https://stacks.math.columbia.edu/tag/014P

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits CochainComplex.HomComplex Pretriangulated

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

namespace CochainComplex

namespace mappingCone

/-- The standard triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` in `CochainComplex C ℤ`
attached to a morphism `φ : K ⟶ L`. It involves `φ`, `inr φ : L ⟶ mappingCone φ` and
the morphism induced by the `1`-cocycle `-mappingCone.fst φ`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
/-
**CochainComplex.mappingCone.triangle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：triangle : Triangle (CochainComplex C Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` in `CochainComplex C 
ℤ`
attached to a morphism `φ : K ⟶ L`. It involves `φ`, `inr φ : L ⟶ mappingCone φ`
 and
the morphism induced by the `1`-cocycle `-mappingCone.fst φ`.
-/
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk φ (inr φ) (Cocycle.homOf ((-fst φ).rightShift 1 0 (zero_add 1)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inl_v_triangle_mor** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inl_v_triangle_mor₃_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (triangle φ).mor₃.f q =
      -(K.shiftFunctorObjXIso 1 q p (by rw [← hpq, neg_add_cancel_right])).inv := by
  dsimp [triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by lia)]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by lia), shiftFunctor_obj_X,
    shiftFunctorObjXIso, Preadditive.comp_neg, inl_v_fst_v_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_f_triangle_mor** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_f_triangle_mor₃_f (p : ℤ) : (inr φ).f p ≫ (triangle φ).mor₃.f p = 0 := by
  dsimp [triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p+1) rfl]
  simp only [Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p + 1) rfl, shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id,
    Preadditive.comp_neg, inr_f_fst_v, neg_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.inr_triangle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_triangleδ : inr φ ≫ (triangle φ).mor₃ = 0 := by ext; simp

/-- The (distinguished) triangle in the homotopy category that is associated to
a morphism `φ : K ⟶ L` in the category `CochainComplex C ℤ`. -/
/-
**CochainComplex.mappingCone.triangleh** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：triangleh : Triangle (HomotopyCategory C (ComplexShape.up Int))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (distinguished) triangle in the homotopy category that is associated to
a morphism `φ : K ⟶ L` in the category `CochainComplex C ℤ`.
-/
noncomputable abbrev triangleh : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (triangle φ)

variable (K) in
/-- The mapping cone of the identity is contractible. -/
/-
**CochainComplex.mappingCone.homotopyToZeroOfId** 是 Mathlib 中的一个定义，位于命名空间 `Cocha
inComplex.mappingCone`。
形式化陈述：homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The mapping cone of the identity is contractible.
-/
noncomputable def homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  descHomotopy (𝟙 K) _ _ 0 (inl _) (by simp) (by simp)

section mapOfHomotopy

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a square that
is commutative up to homotopy. -/
/-
**CochainComplex.mappingCone.mapOfHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `CochainCom
plex.mappingCone`。
形式化陈述：mapOfHomotopy : mappingCone φ₁ ⟶ mappingCone φ₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a square that
is commutative up to homotopy.
-/
noncomputable def mapOfHomotopy :
    mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _) +
    ((Cochain.equivHomotopy _ _) H).1.comp (Cochain.ofHom (inr φ₂)) (add_zero _))
    (b ≫ inr φ₂) (by simp)

@[reassoc]
/-
**CochainComplex.mappingCone.triangleMapOfHomotopy_comm** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleMapOfHomotopy_comm₂ :
    inr φ₁ ≫ mapOfHomotopy H = b ≫ inr φ₂ := by
  simp [mapOfHomotopy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CochainComplex.mappingCone.triangleMapOfHomotopy_comm** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleMapOfHomotopy_comm₃ :
    mapOfHomotopy H ≫ (triangle φ₂).mor₃ = (triangle φ₁).mor₃ ≫ a⟦1⟧' := by
  ext p
  dsimp [mapOfHomotopy, triangle]
  -- the following list of lemmas as been obtained by doing
  -- simp? [ext_from_iff _ _ _ rfl, Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Preadditive.comp_neg,
    Preadditive.neg_comp, ext_from_iff _ _ _ rfl, inl_v_desc_f_assoc, Cochain.add_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v, Preadditive.add_comp,
    assoc, inl_v_fst_v, inr_f_fst_v, comp_zero, add_zero, inl_v_fst_v_assoc, inr_f_desc_f_assoc,
    HomologicalComplex.comp_f, neg_zero, inr_f_fst_v_assoc, zero_comp, and_self]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `triangleh φ₁ ⟶ triangleh φ₂` that is induced by a square that
is commutative up to homotopy. -/
@[simps]
/-
**CochainComplex.mappingCone.trianglehMapOfHomotopy** 是 Mathlib 中的一个定义，位于命名空间 `C
ochainComplex.mappingCone`。
形式化陈述：trianglehMapOfHomotopy : triangleh φ₁ ⟶ triangleh φ₂ where hom₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `triangleh φ₁ ⟶ triangleh φ₂` that is induced by a square that
is commutative up to homotopy.
-/
noncomputable def trianglehMapOfHomotopy :
    triangleh φ₁ ⟶ triangleh φ₂ where
  hom₁ := (HomotopyCategory.quotient _ _).map a
  hom₂ := (HomotopyCategory.quotient _ _).map b
  hom₃ := (HomotopyCategory.quotient _ _).map (mapOfHomotopy H)
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMapOfHomotopy_comm₃, Functor.map_comp, assoc, assoc]
    simp

end mapOfHomotopy

section map

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a commutative square. -/
/-
**CochainComplex.mappingCone.map** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.mappi
ngCone`。
形式化陈述：map (comm : φ₁ ≫ b = a ≫ φ₂) : mappingCone φ₁ ⟶ mappingCone φ₂
参数：comm : φ₁ ≫ b = a ≫ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a commutative 
square.
-/
noncomputable def map (comm : φ₁ ≫ b = a ≫ φ₂) : mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _)) (b ≫ inr φ₂)
    (by simp [reassoc_of% comm])

variable (comm : φ₁ ≫ b = a ≫ φ₂)
/-
**CochainComplex.mappingCone.map_eq_mapOfHomotopy** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.mappingCone`。
形式化陈述：map_eq_mapOfHomotopy : map φ₁ φ₂ a b comm = mapOfHomotopy (Homotopy.ofEq c
omm)
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CochainComplex.HomComplex.Cochain.equivHomotopy_apply_coe`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   {F G : CochainComplex C ℤ} (φ₁ φ₂ : F ⟶ G…
· 使用定理 `CochainComplex.HomComplex.Cochain.zero_comp`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K :
 CochainComplex C ℤ} {n₁ n₂ n₁₂ :…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CochainComplex.mappingCone.desc.congr_simp`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_eq_mapOfHomotopy : map φ₁ φ₂ a b comm = mapOfHomotopy (Homotopy.ofEq comm) := by
  simp [map, mapOfHomotopy]
/-
**CochainComplex.mappingCone.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.ma
ppingCone`。
形式化陈述：map_id : map φ φ (𝟙 _) (𝟙 _) (by rw [id_comp, comp_id]) = 𝟙 _
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CochainComplex.HomComplex.Cochain.id_comp`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : Coc
hainComplex C ℤ} {n : ℤ} (z₂ : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.mappingCone.desc.congr_simp`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.mappingCone.inl_v_desc_f`：inl_v_desc_f (p q : Int) (h : p
 + (-1) = q) : (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma map_id : map φ φ (𝟙 _) (𝟙 _) (by rw [id_comp, comp_id]) = 𝟙 _ := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]

variable (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃)

@[reassoc]
/-
**CochainComplex.mappingCone.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：map_comp (comm' : φ₂ ≫ b' = a' ≫ φ₃) : map φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw 
[reassoc_of% comm, comm', assoc]) = map φ₁ φ₂ a b comm ≫ map φ₂ φ₃ a' b' comm'
参数：comm' : φ₂ ≫ b' = a' ≫ φ₃。
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_comp`：ofHom_comp (f : F ⟶ G) (g 
: G ⟶ K) : ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0)
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain`：c
omp_assoc_of_first_is_zero_cochain {n₂ n₃ n₂₃ : Int} (z₁ : Cochain F G 0) (z₂ : 
Cochain G K n₂) (z₃ : Cochain K L n₃) (h₂₃ : n₂ + n₃ = n₂₃)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.mappingCone.desc.congr_simp`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} (φ : F ⟶ G…
· 使用引理 `CochainComplex.mappingCone.ext_from_iff`：ext_from_iff (i j : Int) (hij :
 j + 1 = i) {A : C} (f g : (mappingCone φ).X j ⟶ A) : f = g ↔ (inl φ).v i j (by 
lia) ≫ f = (inl φ).v i j (by …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.mappingCone.inl_v_desc_f`：inl_v_desc_f (p q : Int) (h : p
 + (-1) = q) : (inl φ).v p q h ≫ (desc φ α β eq).f q = α.v p q h
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CochainComplex.mappingCone.inl_v_desc_f_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F
 G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.mappingCone.inr_f_desc_f`：inr_f_desc_f (p : Int) : (inr φ
).f p ≫ (desc φ α β eq).f p = β.f p
· 使用定理 `CochainComplex.mappingCone.inr_f_desc_f_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {F
 G : CochainComplex C ℤ} (φ : F ⟶ G…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma map_comp (comm' : φ₂ ≫ b' = a' ≫ φ₃) :
    map φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw [reassoc_of% comm, comm', assoc]) =
      map φ₁ φ₂ a b comm ≫ map φ₂ φ₃ a' b' comm' := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `triangle φ₁ ⟶ triangle φ₂` that is induced by a commutative square. -/
@[simps]
/-
**CochainComplex.mappingCone.triangleMap** 是 Mathlib 中的一个定义，位于命名空间 `CochainCompl
ex.mappingCone`。
形式化陈述：triangleMap : triangle φ₁ ⟶ triangle φ₂ where hom₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `triangle φ₁ ⟶ triangle φ₂` that is induced by a commutative square
.
-/
noncomputable def triangleMap :
    triangle φ₁ ⟶ triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map φ₁ φ₂ a b comm
  comm₁ := comm
  comm₂ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₃]

end map

section Rotate

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `φ : K ⟶ L`, `K⟦(1 : ℤ)⟧` is homotopy equivalent to
the mapping cone of `inr φ : L ⟶ mappingCone φ`. -/
/-
**CochainComplex.mappingCone.rotateHomotopyEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.mappingCone`。
形式化陈述：rotateHomotopyEquiv : HomotopyEquiv (K⟦(1 : Int)⟧) (mappingCone (inr φ)) w
here hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `φ : K ⟶ L`, `K⟦(1 : ℤ)⟧` is homotopy equivalent to
the mapping cone of `inr φ : L ⟶ mappingCone φ`.
-/
noncomputable def rotateHomotopyEquiv :
    HomotopyEquiv (K⟦(1 : ℤ)⟧) (mappingCone (inr φ)) where
  hom := lift (inr φ) (-(Cocycle.ofHom φ).leftShift 1 1 (zero_add 1))
    (-(inl φ).leftShift 1 0 (neg_add_cancel 1)) (by
      -- the following list of lemmas has been obtained by doing
      -- simp? [Cochain.δ_leftShift _ 1 0 1 (neg_add_cancel 1) 0 (zero_add 1)]
      simp only [Int.reduceNeg, δ_neg,
        Cochain.δ_leftShift _ 1 0 1 (neg_add_cancel 1) 0 (zero_add 1),
        Int.negOnePow_one, δ_inl, Cochain.ofHom_comp, Cochain.leftShift_comp_zero_cochain,
        Units.neg_smul, one_smul, neg_neg, Cocycle.coe_neg, Cocycle.leftShift_coe,
        Cocycle.ofHom_coe, Cochain.neg_comp, add_neg_cancel])
  inv := desc (inr φ) 0 (triangle φ).mor₃
    (by simp only [δ_zero, inr_triangleδ, Cochain.ofHom_zero])
  homotopyHomInvId := Homotopy.ofEq (by
    ext n
    -- the following list of lemmas has been obtained by doing
    -- simp? [lift_desc_f _ _ _ _ _ _ _ _ _ rfl,
    --   (inl φ).leftShift_v 1 0 _ _ n _ (n + 1) (by simp only [add_neg_cancel_right])]
    simp only [shiftFunctor_obj_X', Int.reduceNeg, HomologicalComplex.comp_f,
      lift_desc_f _ _ _ _ _ _ _ _ _ rfl, Cocycle.coe_neg, Cocycle.leftShift_coe,
      Cocycle.ofHom_coe, Cochain.neg_v, Cochain.zero_v,
      comp_zero, (inl φ).leftShift_v 1 0 _ _ n _ (n + 1) (by simp only [add_neg_cancel_right]),
      shiftFunctor_obj_X, mul_zero, sub_self, Int.zero_ediv, add_zero, Int.negOnePow_zero,
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp, one_smul,
      Preadditive.neg_comp, inl_v_triangle_mor₃_f, Iso.refl_inv, neg_neg, zero_add,
      HomologicalComplex.id_f])
  homotopyInvHomId := (Cochain.equivHomotopy _ _).symm
    ⟨-(snd (inr φ)).comp ((snd φ).comp (inl (inr φ)) (zero_add (-1))) (zero_add (-1)), by
      ext n
      -- the following list of lemmas has been obtained by doing
      -- simp? [ext_to_iff _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl,
      --   δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
      --   (inl φ).leftShift_v 1 0 (neg_add_cancel 1) n n (add_zero n) (n + 1) (by lia),
      --   (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by lia),
      --   Cochain.comp_v _ _ (add_neg_cancel 1) n (n + 1) n rfl (by lia)]
      simp only [Int.reduceNeg, Cochain.ofHom_comp, ofHom_desc, ofHom_lift, Cocycle.coe_neg,
        Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.comp_zero_cochain_v,
        shiftFunctor_obj_X', δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1), δ_inl,
        Int.negOnePow_neg, Int.negOnePow_one, δ_snd, Cochain.neg_comp,
        Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul,
        neg_neg, Cochain.comp_add, inr_snd_assoc, neg_add_rev, Cochain.add_v, Cochain.neg_v,
        Cochain.comp_v _ _ (add_neg_cancel 1) n (n + 1) n rfl (by lia),
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.id_f,
        ext_to_iff _ _ (n + 1) rfl, assoc, liftCochain_v_fst_v,
        (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by lia),
        shiftFunctor_obj_X, mul_one, sub_self, mul_zero, Int.zero_ediv, add_zero,
        shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp,
        Preadditive.add_comp, Preadditive.neg_comp, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero,
        neg_zero, neg_add_cancel_comm, ext_from_iff _ (n + 1) _ rfl, inl_v_descCochain_v_assoc,
        Cochain.zero_v, zero_comp, Preadditive.comp_neg, inl_v_snd_v_assoc,
        inr_f_descCochain_v_assoc, inr_f_snd_v_assoc, inl_v_triangle_mor₃_f_assoc, triangle_obj₁,
        Iso.refl_inv, inl_v_fst_v_assoc, inr_f_triangle_mor₃_f_assoc, inr_f_fst_v_assoc, and_self,
        liftCochain_v_snd_v,
        (inl φ).leftShift_v 1 0 (neg_add_cancel 1) n n (add_zero n) (n + 1) (by lia),
        Int.negOnePow_zero, inl_v_snd_v, inr_f_snd_v, zero_add, inl_v_descCochain_v,
        inr_f_descCochain_v, inl_v_triangle_mor₃_f, inr_f_triangle_mor₃_f, neg_add_cancel]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `rotateTrianglehIso`. -/
/-
**CochainComplex.mappingCone.rotateHomotopyEquivComm** 是 Mathlib 中的一个定义，位于命名空间 `
CochainComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `rotateTrianglehIso`.
-/
noncomputable def rotateHomotopyEquivComm₂Homotopy :
    Homotopy ((triangle φ).mor₃ ≫ (rotateHomotopyEquiv φ).hom)
      (inr (CochainComplex.mappingCone.inr φ)) := (Cochain.equivHomotopy _ _).symm
      ⟨-(snd φ).comp (inl (inr φ)) (zero_add (-1)), by
        ext p
        dsimp [rotateHomotopyEquiv]
        -- the following list of lemmas has been obtained by doing
        -- simp? [ext_from_iff _ _ _ rfl, ext_to_iff _ _ _ rfl,
        --  (inl φ).leftShift_v 1 0 (neg_add_cancel 1) p p (add_zero p) (p + 1) (by lia),
        --  δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
        --  Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p rfl (by lia),
        --  (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia)]⟩
        simp only [Int.reduceNeg, Cochain.ofHom_comp, ofHom_lift, Cocycle.coe_neg,
          Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.comp_zero_cochain_v,
          shiftFunctor_obj_X', Cochain.ofHom_v, δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
          δ_inl, Int.negOnePow_neg, Int.negOnePow_one, δ_snd, Cochain.neg_comp,
          Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul, neg_neg,
          neg_add_rev, Cochain.add_v, Cochain.neg_v,
          Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p rfl (by lia),
          Cochain.zero_cochain_comp_v, ext_from_iff _ _ _ rfl, inl_v_triangle_mor₃_f_assoc,
          triangle_obj₁, shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
          Iso.refl_inv, Preadditive.neg_comp, id_comp, Preadditive.comp_add, Preadditive.comp_neg,
          inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, neg_zero, add_zero, ext_to_iff _ _ _ rfl,
          liftCochain_v_fst_v,
          (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia), mul_one,
          sub_self, mul_zero, Int.zero_ediv, Iso.refl_hom, Preadditive.add_comp, assoc, inl_v_fst_v,
          comp_id, inr_f_fst_v, comp_zero, liftCochain_v_snd_v,
          (inl φ).leftShift_v 1 0 (neg_add_cancel 1) p p (add_zero p) (p + 1) (by lia),
          Int.negOnePow_zero, inl_v_snd_v, inr_f_snd_v, zero_add, and_self,
          inr_f_triangle_mor₃_f_assoc, inr_f_fst_v_assoc, inr_f_snd_v_assoc, neg_add_cancel]⟩

@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.rotateHomotopyEquiv_comm** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rotateHomotopyEquiv_comm₂ :
    (HomotopyCategory.quotient _ _).map (triangle φ).mor₃ ≫
      (HomotopyCategory.quotient _ _).map (rotateHomotopyEquiv φ).hom =
      (HomotopyCategory.quotient _ _).map (inr (inr φ)) := by
  simpa only [Functor.map_comp]
    using! HomotopyCategory.eq_of_homotopy _ _ (rotateHomotopyEquivComm₂Homotopy φ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CochainComplex.mappingCone.rotateHomotopyEquiv_comm** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.mappingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rotateHomotopyEquiv_comm₃ :
    (rotateHomotopyEquiv φ).hom ≫ (triangle (inr φ)).mor₃ = -φ⟦1⟧' := by
  ext p
  dsimp [rotateHomotopyEquiv]
  -- the following list of lemmas has been obtained by doing
  -- simp? [lift_f _ _ _ _ _ (p + 1) rfl,
  --   (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia)]
  simp only [Int.reduceNeg, lift_f _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X', Cocycle.coe_neg,
    Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v,
    (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia), mul_one,
      sub_self, mul_zero, Int.zero_ediv, add_zero, Int.negOnePow_one,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Cochain.ofHom_v, id_comp,
    Units.neg_smul, one_smul, neg_neg, Preadditive.neg_comp, Preadditive.add_comp, assoc,
    inl_v_triangle_mor₃_f, Iso.refl_inv, Preadditive.comp_neg, comp_id, inr_f_triangle_mor₃_f,
    comp_zero, neg_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of triangles `(triangleh φ).rotate ≅ (triangleh (inr φ))`. -/
/-
**CochainComplex.mappingCone.rotateTrianglehIso** 是 Mathlib 中的一个定义，位于命名空间 `Cocha
inComplex.mappingCone`。
形式化陈述：rotateTrianglehIso : (triangleh φ).rotate ≅ (triangleh (inr φ))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism of triangles `(triangleh φ).rotate ≅ (triangleh (inr φ
))`.
-/
noncomputable def rotateTrianglehIso :
    (triangleh φ).rotate ≅ (triangleh (inr φ)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app K ≪≫
      HomotopyCategory.isoOfHomotopyEquiv (rotateHomotopyEquiv φ))
        (by simp) (by simp) (by
        dsimp
        rw [CategoryTheory.Functor.map_id, comp_id, assoc, ← Functor.map_comp_assoc,
          rotateHomotopyEquiv_comm₃, Functor.map_neg, Preadditive.neg_comp,
          Functor.commShiftIso_hom_naturality, Preadditive.comp_neg,
          Iso.inv_hom_id_app_assoc])

end Rotate

section Shift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `(mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧')`. -/
/-
**CochainComplex.mappingCone.shiftIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.
mappingCone`。
形式化陈述：shiftIso (n : Int) : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧') where hom
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧')`.
-/
noncomputable def shiftIso (n : ℤ) : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧') where
  hom := lift _ (n.negOnePow • (fst φ).shift n) ((snd φ).shift n) (by
    ext p q hpq
    dsimp
    simp only [Cochain.δ_shift, δ_snd, Cochain.shift_neg, smul_neg, Cochain.neg_v,
      shiftFunctor_obj_X', Cochain.units_smul_v, Cochain.shift_v', Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, Cochain.units_smul_comp, shiftFunctor_map_f', neg_add_cancel])
  inv := desc _ (n.negOnePow • (inl φ).shift n) ((inr φ)⟦n⟧') (by
    ext p
    dsimp
    simp only [Int.reduceNeg, δ_units_smul, Cochain.δ_shift, δ_inl, Cochain.ofHom_comp, smul_smul,
      Int.units_mul_self, one_smul, Cochain.shift_v', Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, shiftFunctor_obj_X', shiftFunctor_map_f'])
  hom_inv_id := by
    ext p
    dsimp
    simp only [Int.reduceNeg, lift_desc_f _ _ _ _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X',
      Cocycle.coe_units_smul, Cocycle.shift_coe, Cochain.units_smul_v, Cochain.shift_v',
      Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
      shiftFunctor_map_f', id_X]
  inv_hom_id := by
    ext p
    dsimp
    simp only [Int.reduceNeg, ext_from_iff _ (p + 1) _ rfl, shiftFunctor_obj_X',
      inl_v_desc_f_assoc, Cochain.units_smul_v, Cochain.shift_v', Linear.units_smul_comp, comp_id,
      ext_to_iff _ _ (p + 1) rfl, assoc, lift_f_fst_v,
      Cocycle.coe_units_smul, Cocycle.shift_coe, Linear.comp_units_smul, inl_v_fst_v, smul_smul,
      Int.units_mul_self, one_smul, lift_f_snd_v, inl_v_snd_v, smul_zero, and_self,
      inr_f_desc_f_assoc, shiftFunctor_map_f', inr_f_fst_v, inr_f_snd_v]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism `(triangle φ)⟦n⟧ ≅ triangle (φ⟦n⟧')`. -/
/-
**CochainComplex.mappingCone.shiftTriangleIso** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.mappingCone`。
形式化陈述：shiftTriangleIso (n : Int) : (Triangle.shiftFunctor _ n).obj (triangle φ) 
≅ triangle (φ⟦n⟧')
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(triangle φ)⟦n⟧ ≅ triangle (φ⟦n⟧')`.
-/
noncomputable def shiftTriangleIso (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj (triangle φ) ≅ triangle (φ⟦n⟧') := by
  refine Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftIso φ n) ?_ ?_ ?_
  · dsimp
    simp only [Linear.comp_units_smul, comp_id, id_comp, smul_smul,
      Int.units_mul_self, one_smul]
  · ext p
    dsimp
    simp only [Units.smul_def, shiftIso, Int.reduceNeg, Linear.smul_comp, id_comp,
      ext_to_iff _ _ (p + 1) rfl, shiftFunctor_obj_X', assoc, lift_f_fst_v, Cocycle.coe_smul,
      Cocycle.shift_coe, Cochain.smul_v, Cochain.shift_v', Linear.comp_smul, inr_f_fst_v,
      smul_zero, lift_f_snd_v, inr_f_snd_v, and_true]
  · ext p
    dsimp
    simp only [triangle, Triangle.mk_mor₃, Cocycle.homOf_f, Cocycle.rightShift_coe,
      Cocycle.coe_neg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
      (fst φ).1.rightShift_v 1 0 (zero_add 1) (p + n) (p + n) (add_zero (p + n)) (p + 1 + n)
        (by lia),
      shiftFunctor_obj_X, shiftFunctorObjXIso, shiftFunctorComm_hom_app_f, Preadditive.neg_comp,
      assoc, Iso.inv_hom_id, comp_id, smul_neg, Units.smul_def, shiftIso, Int.reduceNeg,
      (fst (φ⟦n⟧')).1.rightShift_v 1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.comp_neg, lift_f_fst_v,
      Cocycle.coe_smul, Cocycle.shift_coe, Cochain.smul_v, Cochain.shift_v']

/-- The canonical isomorphism `(triangleh φ)⟦n⟧ ≅ triangleh (φ⟦n⟧')`. -/
/-
**CochainComplex.mappingCone.shiftTrianglehIso** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.mappingCone`。
形式化陈述：shiftTrianglehIso (n : Int) : (Triangle.shiftFunctor _ n).obj (triangleh φ
) ≅ triangleh (φ⟦n⟧')
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CochainComplex.instAdditiveHomologicalComplexIntUpShiftFunctor`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C] (n : ℤ),   (CategoryTheory.shiftFunctor (Ho…
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…

--- 原说明 ---
The canonical isomorphism `(triangleh φ)⟦n⟧ ≅ triangleh (φ⟦n⟧')`.
-/
noncomputable def shiftTrianglehIso (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj (triangleh φ) ≅ triangleh (φ⟦n⟧') :=
  ((HomotopyCategory.quotient _ _).mapTriangle.commShiftIso n).symm.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso (shiftTriangleIso φ n)

end Shift

section

open Preadditive

variable (G : C ⥤ D) [G.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.mappingCone.map_** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.mapp
ingCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_δ :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (triangle φ).mor₃ ≫
      NatTrans.app ((Functor.mapHomologicalComplex G (ComplexShape.up ℤ)).commShiftIso 1).hom K =
    (mapHomologicalComplexIso φ G).hom ≫
      (triangle ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).mor₃ := by
  ext n
  dsimp [mapHomologicalComplexIso]
  rw [mapHomologicalComplexXIso_eq φ G n (n + 1) rfl, mapHomologicalComplexXIso'_hom]
  simp only [Functor.mapHomologicalComplex_obj_X, add_comp, assoc, inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    comp_neg, comp_id, inr_f_triangle_mor₃_f, comp_zero, add_zero]
  dsimp [triangle]
  rw [Cochain.rightShift_v _ 1 0 (by lia) n n (by lia) (n + 1) (by lia)]
  simp only [shiftFunctor_obj_X, Cochain.neg_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Functor.map_neg]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangle φ` identifies to
the triangle associated to the image of `φ` by `G`. -/
/-
**CochainComplex.mappingCone.mapTriangleIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainCo
mplex.mappingCone`。
形式化陈述：mapTriangleIso : (G.mapHomologicalComplex (ComplexShape.up Int)).mapTriang
le.obj (triangle φ) ≅ triangle ((G.mapHomologicalComplex (ComplexShape.up Int)).
map φ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…

--- 原说明 ---
If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangle φ` identifies 
to
the triangle associated to the image of `φ` by `G`.
-/
noncomputable def mapTriangleIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj (triangle φ) ≅
      triangle ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mapHomologicalComplexIso φ G) ?_ ?_ ?_
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp
    rw [map_inr, id_comp]
  · dsimp
    simp only [CategoryTheory.Functor.map_id, comp_id, map_δ]

/-- If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangleh φ` identifies to
the triangle associated to the image of `φ` by `G`. -/
/-
**CochainComplex.mappingCone.mapTrianglehIso** 是 Mathlib 中的一个定义，位于命名空间 `CochainC
omplex.mappingCone`。
形式化陈述：mapTrianglehIso : (G.mapHomotopyCategory (ComplexShape.up Int)).mapTriangl
e.obj (triangleh φ) ≅ triangleh ((G.mapHomologicalComplex (ComplexShape.up Int))
.map φ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomotopyCategory.instCommShiftHomologicalComplexIntUpHomFunctorMapHomoto
pyCategoryFactors`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [ins
t_1 : CategoryTheory.Preadditive C] {D : Type u'}   [inst_2 : CategoryTheory.Ca…

--- 原说明 ---
If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangleh φ` identifies
 to
the triangle associated to the image of `φ` by `G`.
-/
noncomputable def mapTrianglehIso :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.obj (triangleh φ) ≅
      triangleh ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.mapIso
      (CochainComplex.mappingCone.mapTriangleIso φ G)

end

end mappingCone

end CochainComplex

namespace HomotopyCategory

variable (C)

namespace Pretriangulated

/-- A triangle in `HomotopyCategory C (ComplexShape.up ℤ)` is distinguished if it is isomorphic to
the triangle `CochainComplex.mappingCone.triangleh φ` for some morphism of cochain
complexes `φ`. -/
/-
**HomotopyCategory.Pretriangulated.distinguishedTriangles** 是 Mathlib 中的一个定义，位于命
名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：distinguishedTriangles : Set (Triangle (HomotopyCategory C (ComplexShape.u
p Int)))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A triangle in `HomotopyCategory C (ComplexShape.up ℤ)` is distinguished if it is
 isomorphic to
the triangle `CochainComplex.mappingCone.triangleh φ` for some morphism of cocha
in
complexes `φ`.
-/
def distinguishedTriangles : Set (Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :=
  {T | ∃ (X Y : CochainComplex C ℤ) (φ : X ⟶ Y),
    Nonempty (T ≅ CochainComplex.mappingCone.triangleh φ)}

variable {C}
/-
**HomotopyCategory.Pretriangulated.isomorphic_distinguished** 是 Mathlib 中的一个引理，位
于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：isomorphic_distinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.
up Int))) (hT₁ : T₁ in distinguishedTriangles C) (T₂ : Triangle (HomotopyCategor
y C (ComplexShape.up Int))) (e : T₂ ≅ T₁) : T₂ in distinguishedTriangles C
参数：T₁ : Triangle (HomotopyCategory C (ComplexShape.up Int))；hT₁ : T₁ in distingu
ishedTriangles C；T₂ : Triangle (HomotopyCategory C (ComplexShape.up Int))；e : T₂
 ≅ T₁。
该定理/引理描述了相关对象所满足的性质。
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
-/
lemma isomorphic_distinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, ⟨e ≪≫ e'⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable [HasZeroObject C] in
/-
**HomotopyCategory.Pretriangulated.contractible_distinguished** 是 Mathlib 中的一个引理
，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：contractible_distinguished (X : HomotopyCategory C (ComplexShape.up Int)) 
: Pretriangulated.contractibleTriangle X in distinguishedTriangles C
参数：X : HomotopyCategory C (ComplexShape.up Int)。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `HomotopyCategory.isZero_quotient_obj_iff`：isZero_quotient_obj_iff (C : H
omologicalComplex V c) : IsZero ((quotient _ _).obj C) ↔ Nonempty (Homotopy (𝟙 C
) 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
lemma contractible_distinguished (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    Pretriangulated.contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  refine ⟨_, _, 𝟙 X, ⟨?_⟩⟩
  have h := (isZero_quotient_obj_iff _).2 ⟨CochainComplex.mappingCone.homotopyToZeroOfId X⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp) (h.eq_of_tgt _ _) (by dsimp; ext)
/-
**HomotopyCategory.Pretriangulated.distinguished_cocone_triangle** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：distinguished_cocone_triangle {X Y : HomotopyCategory C (ComplexShape.up I
nt)} (f : X ⟶ Y) : exists (Z : HomotopyCategory C (ComplexShape.up Int)) (g : Y 
⟶ Z) (h : Z ⟶ X⟦1⟧), Triangle.mk f g h in distinguishedTriangles C
参数：ComplexShape.up Int；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
-/
lemma distinguished_cocone_triangle {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory C (ComplexShape.up ℤ)) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩
/-
**HomotopyCategory.Pretriangulated.rotate_distinguished_triangle'** 是 Mathlib 中的
一个引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：rotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexS
hape.up Int))) (hT : T in distinguishedTriangles C) : T.rotate in distinguishedT
riangles C
参数：T : Triangle (HomotopyCategory C (ComplexShape.up Int))；hT : T in distinguish
edTriangles C。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma rotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate _).mapIso e ≪≫ CochainComplex.mappingCone.rotateTrianglehIso φ⟩⟩
/-
**HomotopyCategory.Pretriangulated.shift_distinguished_triangle** 是 Mathlib 中的一个
引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：shift_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexSha
pe.up Int))) (hT : T in distinguishedTriangles C) (n : Int) : (Triangle.shiftFun
ctor _ n).obj T in distinguishedTriangles C
参数：T : Triangle (HomotopyCategory C (ComplexShape.up Int))；hT : T in distinguish
edTriangles C；n : Int。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma shift_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) (n : ℤ) :
      (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨Functor.mapIso _ e ≪≫ CochainComplex.mappingCone.shiftTrianglehIso φ n⟩⟩
/-
**HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle'** 是 Mathlib
 中的一个引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (Compl
exShape.up Int))) (hT : T in distinguishedTriangles C) : T.invRotate in distingu
ishedTriangles C
参数：T : Triangle (HomotopyCategory C (ComplexShape.up Int))；hT : T in distinguish
edTriangles C。
该定理/引理描述了相关对象所满足的性质。
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
· 使用引理 `HomotopyCategory.Pretriangulated.isomorphic_distinguished`：isomorphic_di
stinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up Int))) (hT₁ : T₁
 in distinguishedTriangles C) (T₂ : Triangle (H…
· 使用引理 `HomotopyCategory.Pretriangulated.shift_distinguished_triangle`：shift_dis
tinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up Int))) (h
T : T in distinguishedTriangles C) (n : Int) : (Tri…
· 使用引理 `HomotopyCategory.Pretriangulated.rotate_distinguished_triangle'`：rotate_
distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up Int))
) (hT : T in distinguishedTriangles C) : T.rotate in …
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
-/
lemma invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.invRotate ∈ distinguishedTriangles C :=
  isomorphic_distinguished _
    (shift_distinguished_triangle _ (rotate_distinguished_triangle' _
      (rotate_distinguished_triangle' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)
/-
**HomotopyCategory.Pretriangulated.rotate_distinguished_triangle** 是 Mathlib 中的一
个引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexSh
ape.up Int))) : T in distinguishedTriangles C ↔ T.rotate in distinguishedTriangl
es C
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
· 使用引理 `HomotopyCategory.Pretriangulated.rotate_distinguished_triangle'`：rotate_
distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up Int))
) (hT : T in distinguishedTriangles C) : T.rotate in …
· 使用引理 `HomotopyCategory.Pretriangulated.isomorphic_distinguished`：isomorphic_di
stinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up Int))) (hT₁ : T₁
 in distinguishedTriangles C) (T₂ : Triangle (H…
· 使用引理 `HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle'`：invR
otate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up
 Int))) (hT : T in distinguishedTriangles C) : T.invRota…
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…
-/
lemma rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  constructor
  · exact rotate_distinguished_triangle' T
  · intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open CochainComplex.mappingCone in
/-
**HomotopyCategory.Pretriangulated.complete_distinguished_triangle_morphism** 是 
Mathlib 中的一个引理，位于命名空间 `HomotopyCategory.Pretriangulated`。
形式化陈述：complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (HomotopyCatego
ry C (ComplexShape.up Int))) (hT₁ : T₁ in distinguishedTriangles C) (hT₂ : T₂ in
 distinguishedTriangles C) (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac 
: T₁.mor₁ ≫ b = a ≫ T₂.mor₁) : exists (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫
 T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : Int)⟧' = c ≫ T₂.mor₃
参数：T₁ T₂ : Triangle (HomotopyCategory C (ComplexShape.up Int))；hT₁ : T₁ in disti
nguishedTriangles C；hT₂ : T₂ in distinguishedTriangles C；a : T₁.obj₁ ⟶ T₂.obj₁；b
 : T₁.obj₂ ⟶ T₂.obj₂；fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁。
该定理/引理给出了一组等式。
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
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Functor.map_surjective`：map_surjective (F : C ⥤ D) [Full 
F] : Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `HomotopyCategory.instFullHomologicalComplexQuotient`：∀ {ι : Type u_2} (V
 : Type u) [inst : CategoryTheory.Category.{v, u} V] [inst_1 : CategoryTheory.Pr
eadditive V]   (c : ComplexShape ι), (Hom…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₁`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₂`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₂_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift 
C ℤ]   {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₂`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A B : Ca
tegoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₂_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A 
B : CategoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₁`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A B : Ca
tegoryTheory.Pretriangulated.Tria…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_triangle_hom₁_assoc`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]   {A 
B : CategoryTheory.Pretriangulated.Tria…
-/
lemma complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := hT₂
  obtain ⟨a', ha'⟩ : ∃ (a' : (quotient _ _).obj K₁ ⟶ (quotient _ _).obj K₂),
    a' = e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ (b' : (quotient _ _).obj L₁ ⟶ (quotient _ _).obj L₂),
    b' = e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ := ⟨_, rfl⟩
  obtain ⟨a'', rfl⟩ := (quotient _ _).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient _ _).map_surjective b'
  have H : Homotopy (φ₁ ≫ b'') (a'' ≫ φ₂) := homotopyOfEq _ _ (by
    have comm₁₁ := e₁.inv.comm₁
    have comm₁₂ := e₂.hom.comm₁
    dsimp at comm₁₁ comm₁₂
    simp only [Functor.map_comp, ha', hb', reassoc_of% comm₁₁,
      reassoc_of% fac, comm₁₂, assoc])
  let γ := e₁.hom ≫ trianglehMapOfHomotopy H ≫ e₂.inv
  have comm₂ := γ.comm₂
  have comm₃ := γ.comm₃
  dsimp [γ] at comm₂ comm₃
  simp only [ha', hb'] at comm₂ comm₃
  refine ⟨γ.hom₃, ?_, ?_⟩
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₂
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, TriangleMorphism.comm₂_assoc, Triangle.mk_obj₂,
      Triangle.mk_mor₂, assoc, Iso.hom_inv_id_triangle_hom₂, comp_id,
      Iso.hom_inv_id_triangle_hom₂_assoc, γ] using comm₂
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₃
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, assoc, Triangle.mk_obj₁, Iso.hom_inv_id_triangle_hom₁, comp_id,
      Iso.hom_inv_id_triangle_hom₁_assoc, γ] using comm₃

end Pretriangulated

variable [HasZeroObject C]

/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pretriangulated (HomotopyCategory C (ComplexShape.up ℤ)) where
  distinguishedTriangles := Pretriangulated.distinguishedTriangles C
  isomorphic_distinguished := Pretriangulated.isomorphic_distinguished
  contractible_distinguished := Pretriangulated.contractible_distinguished
  distinguished_cocone_triangle := Pretriangulated.distinguished_cocone_triangle
  rotate_distinguished_triangle := Pretriangulated.rotate_distinguished_triangle
  complete_distinguished_triangle_morphism :=
    Pretriangulated.complete_distinguished_triangle_morphism

variable {C}
/-
**HomotopyCategory.mappingCone_triangleh_distinguished** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopyCategory`。
形式化陈述：mappingCone_triangleh_distinguished {X Y : CochainComplex C Int} (f : X ⟶ 
Y) : CochainComplex.mappingCone.triangleh f in distTriang (HomotopyCategory _ _)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma mappingCone_triangleh_distinguished {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    CochainComplex.mappingCone.triangleh f ∈ distTriang (HomotopyCategory _ _) :=
  ⟨_, _, f, ⟨Iso.refl _⟩⟩

variable [HasZeroObject D]
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : C ⥤ D) [G.Additive] :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated where
  map_distinguished := by
    rintro T ⟨K, L, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(G.mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.mapIso e ≪≫
      CochainComplex.mappingCone.mapTrianglehIso f G⟩⟩

end HomotopyCategory

