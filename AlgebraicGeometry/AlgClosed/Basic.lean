/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Schemes over algebraically closed fields

We show that if `X` is locally of finite type over an algebraically closed field `k`,
then the closed points of `X` are in bijection with the `k`-points of `X`.
See `AlgebraicGeometry.pointEquivClosedPoint`.

-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x})

/-- If `X` is a locally of finite type `k`-scheme and `k` is algebraically closed, then
the residue field of any closed point of `x` is isomorphic to `k`. -/
/-
**AlgebraicGeometry.residueFieldIsoBase** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：residueFieldIsoBase : X.residueField x ≅ .of K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a locally of finite type `k`-scheme and `k` is algebraically closed, t
hen
the residue field of any closed point of `x` is isomorphic to `k`.
-/
def residueFieldIsoBase : X.residueField x ≅ .of K :=
  letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  (asIso (Spec.preimage (X.fromSpecResidueField x ≫ f))).symm

@[simp, reassoc]
/-
**AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：SpecMap_residueFieldIsoBase_inv : Spec.map (residueFieldIsoBase f x hx).in
v = X.fromSpecResidueField x ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.map_preimage`：∀ {R S : CommRingCat} (f : Algebrai
cGeometry.Spec S ⟶ AlgebraicGeometry.Spec R),   AlgebraicGeometry.Spec.map (Alge
braicGeometry.Spec.preima…
-/
lemma SpecMap_residueFieldIsoBase_inv :
    Spec.map (residueFieldIsoBase f x hx).inv = X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- If `k` is algebraically closed, this is the `k`-point of `X` associated to a closed point. -/
noncomputable
/-
**AlgebraicGeometry.pointOfClosedPoint** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：pointOfClosedPoint : Spec (.of K) ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pointOfClosedPoint : Spec (.of K) ⟶ X :=
  Spec.map (residueFieldIsoBase f x hx).hom ≫ X.fromSpecResidueField x

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pointOfClosedPoint_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：pointOfClosedPoint_comp : pointOfClosedPoint f x hx ≫ f = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointOfClosedPoint_comp : pointOfClosedPoint f x hx ≫ f = 𝟙 _ := by
  simp [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv, ← Spec.map_comp]

@[simp]
/-
**AlgebraicGeometry.pointOfClosedPoint_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：pointOfClosedPoint_apply (a : _) : pointOfClosedPoint f x hx a = x
参数：a : _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pointOfClosedPoint_apply (a : _) : pointOfClosedPoint f x hx a = x := by
  simp [pointOfClosedPoint]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `k` is algebraically closed,
then the closed points of `X` are in bijection with the `k`-points of `X`. -/
@[simps]
/-
**AlgebraicGeometry.pointEquivClosedPoint** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：pointEquivClosedPoint : {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoin
ts X where toFun p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `k` is algebraically closed,
then the closed points of `X` are in bijection with the `k`-points of `X`.
-/
def pointEquivClosedPoint :
    {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoints X where
  toFun p := ⟨p.1 (IsLocalRing.closedPoint K), by
    have := isClosedImmersion_of_comp_eq_id _ _ p.2
    have := p.1.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at this
    exact fun x ↦ congr(p.1 $(Subsingleton.elim _ _))⟩
  invFun x := ⟨pointOfClosedPoint f x.1 x.2, pointOfClosedPoint_comp f x.1 x.2⟩
  left_inv p := by
    ext
    refine ((Scheme.SpecToEquivOfField _ _).symm_apply_eq (x := ⟨_, _⟩)).mpr ?_
    rw [Scheme.SpecToEquivOfField_eq_iff]
    dsimp [Scheme.SpecToEquivOfField]
    simp only [Category.id_comp, exists_const]
    generalize_proofs _ h
    refine (Category.comp_id _).symm.trans (((residueFieldIsoBase f _ h).eq_inv_comp).mp ?_)
    rw [← Spec.map_injective.eq_iff]
    simp only [Spec.map_id, Spec.map_comp, SpecMap_residueFieldIsoBase_inv]
    rw [reassoc_of% Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, p.2]
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ext_of_apply_closedPoint_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：ext_of_apply_closedPoint_eq {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K)
) [LocallyOfFiniteType h] (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _) (H : f (IsLocalR
ing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g
参数：.of K；h : X ⟶ Spec (.of K)；hf : f ≫ h = 𝟙 _；hg : g ≫ h = 𝟙 _；H : f (IsLocalRi
ng.closedPoint K) = g (IsLocalRing.closedPoint K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma ext_of_apply_closedPoint_eq
    {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K))
    [LocallyOfFiniteType h]
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g :=
  congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `X` and `Y` be locally of finite type `K`-schemes with `K` algebraically closed and `Y`
separated over `K`. Suppose `X` is reduced, then two `K`-morphisms `f g : X ⟶ Y` are equal if
they are equal on the closed points of a dense locally closed subset of `X`. -/
/-
**AlgebraicGeometry.ext_of_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
`。
形式化陈述：ext_of_apply_eq {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [IsSeparated i] [Loca
llyOfFiniteType i] [IsReduced X] [LocallyOfFiniteType (f ≫ i)] (S : Set X) (hS :
 IsLocallyClosed S) (hS' : Dense S) (H : forall x in S, IsClosed {x} -> f x = g 
x) (H' : f ≫ i = g ≫ i) : f = g
参数：i : Y ⟶ Spec (.of K)；f ≫ i；S : Set X；hS : IsLocallyClosed S；hS' : Dense S；H :
 forall x in S, IsClosed {x} -> f x = g x；H' : f ≫ i = g ≫ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] [JacobsonS
pace ↥Y],   JacobsonSpace ↥X
· 使用定理 `AlgebraicGeometry.instJacobsonSpaceCarrierCarrierCommRingCatSpecOfOfIsJa
cobsonRing`：∀ {R : Type u_1} [inst : CommRing R] [IsJacobsonRing R], JacobsonSpa
ce ↥(AlgebraicGeometry.Spec (CommRingCat.of R))
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用引理 `AlgebraicGeometry.ext_of_fromSpecResidueField_eq`：ext_of_fromSpecResidue
Field_eq (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X] (S : Set X) (hS
' : Dense S) (H : forall x in S, X.fro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `JacobsonSpace.closure_inter_closedPoints_eq_closure`：JacobsonSpace.closu
re_inter_closedPoints_eq_closure [JacobsonSpace X] {S : Set X} (hS : IsLocallyCl
osed S) : closure (S inter closedPoints X…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `AlgebraicGeometry.ext_of_apply_closedPoint_eq`：ext_of_apply_closedPoint_
eq {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K)) [LocallyOfFiniteType h] (hf :
 f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _) (H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv`：SpecMap_residueFieldI
soBase_inv : Spec.map (residueFieldIsoBase f x hx).inv = X.fromSpecResidueField 
x ≫ f
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x

--- 原说明 ---
Let `X` and `Y` be locally of finite type `K`-schemes with `K` algebraically clo
sed and `Y`
separated over `K`. Suppose `X` is reduced, then two `K`-morphisms `f g : X ⟶ Y`
 are equal if
they are equal on the closed points of a dense locally closed subset of `X`.
-/
lemma ext_of_apply_eq {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [IsSeparated i] [LocallyOfFiniteType i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : ∀ x ∈ S, IsClosed {x} → f x = g x)
    (H' : f ≫ i = g ≫ i) : f = g := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S ∩ closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ i) x hx).hom)]
    refine ext_of_apply_closedPoint_eq i ?_ ?_ (by simpa using H x hxS hx) <;>
      simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, ← H']

end AlgebraicGeometry

