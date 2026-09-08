/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

import Mathlib.RingTheory.FreeCommRing
import Mathlib.Algebra.Ring.Subring.Units
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* tensor product over `ℤ` is the binary coproduct
* `ℤ` is the initial object
* `0` is the strict terminal object
* Cartesian product is the product
* arbitrary direct product of a family of rings is the product object (Pi object)
* `RingHom.eqLocus` is the equalizer

-/

@[expose] public section

universe u u'

open CategoryTheory Limits TensorProduct

namespace CommRingCat

section Pushout

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
/-
**CommRingCat.pushoutCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：pushoutCocone : Limits.PushoutCocone (CommRingCat.ofHom (algebraMap R A)) 
(CommRingCat.ofHom (algebraMap R B))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit cocone with tensor products as the fibered product in `CommRingCat`
.
-/
def pushoutCocone : Limits.PushoutCocone
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) := by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A ⊗[R] B)
  · exact ofHom <| Algebra.TensorProduct.includeLeftRingHom (A := A)
  · exact ofHom <| Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm

@[simp]
/-
**CommRingCat.pushoutCocone_inl** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：pushoutCocone_inl : (pushoutCocone R A B).inl = ofHom (Algebra.TensorProdu
ct.includeLeftRingHom (A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCocone_inl :
    (pushoutCocone R A B).inl = ofHom (Algebra.TensorProduct.includeLeftRingHom (A := A)) :=
  rfl

@[simp]
/-
**CommRingCat.pushoutCocone_inr** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：pushoutCocone_inr : (pushoutCocone R A B).inr = ofHom (Algebra.TensorProdu
ct.includeRight.toRingHom (A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCocone_inr :
    (pushoutCocone R A B).inr = ofHom (Algebra.TensorProduct.includeRight.toRingHom (A := B)) :=
  rfl

@[simp]
/-
**CommRingCat.pushoutCocone_pt** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：pushoutCocone_pt : (pushoutCocone R A B).pt = CommRingCat.of (A otimes[R] 
B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pushoutCocone_pt :
    (pushoutCocone R A B).pt = CommRingCat.of (A ⊗[R] B) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Verify that the `pushout_cocone` is indeed the colimit. -/
/-
**CommRingCat.pushoutCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone R A B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Verify that the `pushout_cocone` is indeed the colimit.
-/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone R A B) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra (s.inl.hom.comp (algebraMap R A))
    let f' : A →ₐ[R] s.pt :=
      { s.inl.hom with
        commutes' := fun r => rfl }
    let g' : B →ₐ[R] s.pt :=
      { s.inr.hom with
        commutes' := DFunLike.congr_fun <| congrArg Hom.hom
          ((s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
            (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm) }
    letI : Algebra R (pushoutCocone R A B).pt := show Algebra R (A ⊗[R] B) by infer_instance
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use ofHom (AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g'))
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_left_apply (A := A) _ _ x
    constructor
    · ext x
      exact Algebra.TensorProduct.productMap_right_apply (B := B) _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.pt :=
      { h.hom with
        commutes' := fun r => by
          change h (algebraMap R A r ⊗ₜ[R] 1) = s.inl (algebraMap R A r)
          rw [← eq1]
          simp only [pushoutCocone_pt, coe_of]
          rfl }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [f', g', ← eq1, pushoutCocone_pt, ← eq2, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_mk]
    change _ = h (a ⊗ₜ 1) * h (1 ⊗ₜ b)
    rw [← h.hom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
/-
**CommRingCat.isPushout_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRi
ng B] [Algebra R A] [Algebra R B] : IsPushout (ofHom <| algebraMap R A) (ofHom <
| algebraMap R B) (ofHom (S
参数：R A B : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨pushoutCoconeIsColimit R A B⟩
/-
**CommRingCat.isPushout_of_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：isPushout_of_isPushout (R S A B : Type u) [CommRing R] [CommRing S] [CommR
ing A] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Alg
ebra R B] [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B
] : IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R A)) (ofHom (algebraM
ap S B)) (ofHom (algebraMap A B))
参数：R S A B : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.toCommRingCatIso_hom`：∀ {R S : Type u} [inst : CommRing R] [in
st_1 : CommRing S] (e : R ≃+* S), e.toCommRingCatIso.hom = CommRingCat.ofHom ↑e
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Algebra.TensorProduct.includeLeftRingHom_apply`：∀ {R : Type uR} {A : Typ
e uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Alge
bra R A]   [inst_3 : Semiring B] [in…
· 使用引理 `Algebra.IsPushout.equiv_tmul`：Algebra.IsPushout.equiv_tmul [h : Algebra.
IsPushout R S R' S'] (a : S) (b : R') : equiv R S R' S' (a otimesₜ b) = algebraM
ap _ _ a * algebra…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma isPushout_of_isPushout (R S A B : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R A))
      (ofHom (algebraMap S B)) (ofHom (algebraMap A B)) :=
  (isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**CommRingCat.isPushout_iff_isPushout** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra 
R S] {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] 
[Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] : 
IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S) (ofHom <| algebra
Map R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom`：inl_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inl ≫ h.isoPushout.hom = pushout.inl _ _
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_inv`：inl_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inl _ _ ≫ h.isoPushout.inv = inl
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `CategoryTheory.Iso.commRingCatIsoToRingEquiv.eq_1`：∀ {R S : CommRingCat}
 (e : R ≅ S),   e.commRingCatIsoToRingEquiv = RingEquiv.ofRingHom (CommRingCat.H
om.hom e.hom) (CommRingCat.Hom.hom e.in…
· 使用定理 `RingEquiv.ofRingHom_apply`：∀ {R : Type u_4} {S : Type u_5} [inst : NonAs
socSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) (g : S →+* R)   (h₁ :
 f.comp g = Rin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Algebra.IsPushout.of_equiv`：Algebra.IsPushout.of_equiv [h : IsPushout R 
R' S S'] {T : Type*} [CommSemiring T] [Algebra R' T] [Algebra S T] [Algebra R T]
 [IsScalarTower …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_inv`：inr_isoPushout_inv (h : IsP
ushout f g inl inr) [HasPushout f g] : pushout.inr _ _ ≫ h.isoPushout.inv = inr
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用引理 `CommRingCat.isPushout_of_isPushout`：isPushout_of_isPushout (R S A B : Ty
pe u) [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S] [Algebra
 S B] [Algebra R A] [Alg…
-/
lemma isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨fun h ↦ ?_, fun h ↦ isPushout_of_isPushout ..⟩
  let e : R' ⊗[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ⊗ₜ 1) = (pushout.inl (ofHom _) (ofHom _)) r :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inl_isoPushout_hom).hom r)
  have h3 (x : R') := congr($(h.inl_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h3
  let e' : R' ⊗[R] S ≃ₐ[R'] S' := {
    __ := e
    commutes' r := by simp [Iso.commRingCatIsoToRingEquiv, h2, e, h3] }
  refine Algebra.IsPushout.of_equiv e' ?_
  ext s
  have h1 : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (algebraMap S (R' ⊗[R] S) s) = (pushout.inr (ofHom _) (ofHom _)) s :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inr_isoPushout_hom).hom s)
  have h4 (x : S) := congr($(h.inr_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h4
  simp [Iso.commRingCatIsoToRingEquiv, h1, e', e, h4]
/-
**CommRingCat.isPushout_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat
`。
形式化陈述：isPushout_of_isLocalization {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing Rₘ
] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ] (f : R ->+* S) (fₘ : 
Rₘ ->+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f) (M : Submon
oid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] : IsPushout (CommRing
Cat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ)) (CommRingCat.ofHom (algebraMa
p S Sₘ)) (CommRingCat.ofHom fₘ)
参数：f : R ->+* S；fₘ : Rₘ ->+* Sₘ；H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).
comp f；M : Submonoid R；M.map f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CommRingCat.isPushout_iff_isPushout`：isPushout_iff_isPushout {R S : Type
 u} [CommRing R] [CommRing S] [Algebra R S] {R' S' : Type u} [CommRing R'] [Comm
Ring S'] [Algebra R R'] […
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
-/
lemma isPushout_of_isLocalization {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ]
    (f : R →+* S) (fₘ : Rₘ →+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f)
    (M : Submonoid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ))
      (CommRingCat.ofHom (algebraMap S Sₘ)) (CommRingCat.ofHom fₘ) := by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)
/-
**CommRingCat.closure_range_union_range_eq_top_of_isPushout** 是 Mathlib 中的一个引理，位
于命名空间 `CommRingCat`。
形式化陈述：closure_range_union_range_eq_top_of_isPushout {R A B X : CommRingCat.{u}} 
{f : R ⟶ A} {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X} (H : IsPushout f g a b) : Subrin
g.closure (Set.range a union Set.range b) = ⊤
参数：H : IsPushout f g a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective {
f : R ->+* S} (hf : Function.Injective f) (s : Subring R) : (s.map f).comap f = 
s
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `RingHom.map_closure`：map_closure (f : R ->+* S) (s : Set R) : (closure s
).map f = closure (f '' s)
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subring.map_le_iff_le_comap`：map_le_iff_le_comap {f : R ->+* S} {s : Sub
ring R} {t : Subring S} : s.map f <= t ↔ s <= t.comap f
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `CategoryTheory.IsPushout.inl_isoIsPushout_inv`：inl_isoIsPushout_inv (h :
 IsPushout f g inl inr) (h' : IsPushout f g inl' inr') : inl' ≫ (h.isoIsPushout 
_ _ h').inv = inl
· 使用定理 `CategoryTheory.IsPushout.inr_isoIsPushout_inv`：inr_isoIsPushout_inv (h :
 IsPushout f g inl inr) (h' : IsPushout f g inl' inr') : inr' ≫ (h.isoIsPushout 
_ _ h').inv = inr
· 使用引理 `CommRingCat.hom_ofHom`：hom_ofHom {R S : Type u} [CommRing R] [CommRing S
] (f : R ->+* S) : (ofHom f).hom = f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `Algebra.TensorProduct.closure_range_union_range_eq_top`：closure_range_un
ion_range_eq_top [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] : Su
bring.closure (Set.range (Algebra.TensorProd…
-/
lemma closure_range_union_range_eq_top_of_isPushout
    {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X}
    (H : IsPushout f g a b) :
    Subring.closure (Set.range a ∪ Set.range b) = ⊤ := by
  algebraize [f.hom, g.hom]
  let e := ((isPushout_tensorProduct R A B).isoIsPushout A B H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _), RingHom.map_closure,
    ← top_le_iff, ← Subring.map_le_iff_le_comap, Set.image_union]
  simp only [AlgHom.toRingHom_eq_coe, ← Set.range_comp, ← RingHom.coe_comp]
  rw [← hom_comp, ← hom_comp, IsPushout.inl_isoIsPushout_inv, IsPushout.inr_isoIsPushout_inv,
    hom_ofHom, hom_ofHom]
  exact le_top.trans (Algebra.TensorProduct.closure_range_union_range_eq_top R A B).ge

end Pushout

section BinaryCoproduct

variable (A B : CommRingCat.{u})

/-- The tensor product `A ⊗[ℤ] B` forms a cocone for `A` and `B`. -/
@[simps! pt ι]
/-
**CommRingCat.coproductCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coproductCocone : BinaryCofan A B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product `A ⊗[ℤ] B` forms a cocone for `A` and `B`.
-/
def coproductCocone : BinaryCofan A B :=
  BinaryCofan.mk
    (ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom : A ⟶ of (A ⊗[ℤ] B))
    (ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom : B ⟶ of (A ⊗[ℤ] B))

@[simp]
/-
**CommRingCat.coproductCocone_inl** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：coproductCocone_inl : (coproductCocone A B).inl = ofHom (Algebra.TensorPro
duct.includeLeft (S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coproductCocone_inl :
    (coproductCocone A B).inl = ofHom (Algebra.TensorProduct.includeLeft (S := ℤ)).toRingHom := rfl

@[simp]
/-
**CommRingCat.coproductCocone_inr** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：coproductCocone_inr : (coproductCocone A B).inr = ofHom (Algebra.TensorPro
duct.includeRight (R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coproductCocone_inr :
    (coproductCocone A B).inr = ofHom (Algebra.TensorProduct.includeRight (R := ℤ)).toRingHom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product `A ⊗[ℤ] B` is a coproduct for `A` and `B`. -/
@[simps]
/-
**CommRingCat.coproductCoconeIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coproductCoconeIsColimit : IsColimit (coproductCocone A B) where desc (s :
 BinaryCofan A B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product `A ⊗[ℤ] B` is a coproduct for `A` and `B`.
-/
def coproductCoconeIsColimit : IsColimit (coproductCocone A B) where
  desc (s : BinaryCofan A B) :=
    ofHom (Algebra.TensorProduct.lift s.inl.hom.toIntAlgHom s.inr.hom.toIntAlgHom
      (fun _ _ => by apply Commute.all)).toRingHom
  fac (s : BinaryCofan A B) := fun ⟨j⟩ => by cases j <;> ext a <;> simp
  uniq (s : BinaryCofan A B) := by
    rintro ⟨m : A ⊗[ℤ] B →+* s.pt⟩ hm
    apply CommRingCat.hom_ext
    apply RingHom.toIntAlgHom_injective
    apply Algebra.TensorProduct.liftEquiv.symm.injective
    apply Subtype.ext
    rw [Algebra.TensorProduct.liftEquiv_symm_apply_coe, Prod.mk.injEq]
    constructor
    · ext a
      simp [map_one, mul_one, ← hm (Discrete.mk WalkingPair.left)]
    · ext b
      simp [map_one, ← hm (Discrete.mk WalkingPair.right)]

/-- The limit cone of the tensor product `A ⊗[ℤ] B` in `CommRingCat`. -/
/-
**CommRingCat.coproductColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：coproductColimitCocone : Limits.ColimitCocone (pair A B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone of the tensor product `A ⊗[ℤ] B` in `CommRingCat`.
-/
def coproductColimitCocone : Limits.ColimitCocone (pair A B) :=
  ⟨_, coproductCoconeIsColimit A B⟩

end BinaryCoproduct


section Terminal

/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CommRingCat.{u}) : Unique (X ⟶ CommRingCat.of.{u} PUnit) :=
  ⟨⟨ofHom <| ⟨1, rfl, by simp⟩⟩, fun f ↦ by ext⟩

/-- The trivial ring is the (strict) terminal object of `CommRingCat`. -/
/-
**CommRingCat.punitIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial ring is the (strict) terminal object of `CommRingCat`.
-/
def punitIsTerminal : IsTerminal (CommRingCat.of.{u} PUnit) :=
  IsTerminal.ofUnique _
/-
**CommRingCat.commRingCat_hasStrictTerminalObjects** 是 Mathlib 中的一个实例，位于命名空间 `Co
mmRingCat`。
形式化陈述：commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCa
t.{u}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasStrictTerminalObjects_of_terminal_is_strict`：ha
sStrictTerminalObjects_of_terminal_is_strict (I : C) (h : forall (A) (f : I ⟶ A)
, IsIso f) : HasStrictTerminalObjects C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `PUnit.ext`：∀ (a b : PUnit.{u_1}), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
instance commRingCat_hasStrictTerminalObjects : HasStrictTerminalObjects CommRingCat.{u} := by
  apply hasStrictTerminalObjects_of_terminal_is_strict (CommRingCat.of PUnit)
  intro X f
  refine ⟨ofHom ⟨1, rfl, by simp⟩, ?_, ?_⟩
  · ext
  · ext x
    have e : (0 : X) = 1 := by
      rw [← f.hom.map_one, ← f.hom.map_zero]
    replace e : 0 * x = 1 * x := congr_arg (· * x) e
    rw [one_mul, zero_mul, ← f.hom.map_zero] at e
    exact e
/-
**CommRingCat.subsingleton_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`
。
形式化陈述：subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsing
leton X
参数：hX : IsTerminal X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X :=
  (hX.uniqueUpToIso punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

/-- `ℤ` is the initial object of `CommRingCat`. -/
/-
**CommRingCat.zIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：zIsInitial : IsInitial (CommRingCat.of Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℤ` is the initial object of `CommRingCat`.
-/
def zIsInitial : IsInitial (CommRingCat.of ℤ) :=
  IsInitial.ofUnique (h := fun R => ⟨⟨ofHom <| Int.castRingHom R⟩,
    fun a => hom_ext <| a.hom.ext_int _⟩)

/-- `ULift.{u} ℤ` is initial in `CommRingCat`. -/
/-
**CommRingCat.isInitial** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：isInitial : IsInitial (CommRingCat.of (ULift.{u} Int))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ULift.{u} ℤ` is initial in `CommRingCat`.
-/
def isInitial : IsInitial (CommRingCat.of (ULift.{u} ℤ)) :=
  IsInitial.ofUnique (h := fun R ↦ ⟨⟨ofHom <| (Int.castRingHom R).comp ULift.ringEquiv.toRingHom⟩,
    fun _ ↦ by
      ext : 1
      rw [← RingHom.cancel_right (f := (ULift.ringEquiv.{0, u} (R := ℤ)).symm.toRingHom)
        (hf := ULift.ringEquiv.symm.surjective)]
      apply RingHom.ext_int⟩)

end Terminal

section Product

variable (A B : CommRingCat.{u})

/-- The product in `CommRingCat` is the Cartesian product. This is the binary fan. -/
@[simps! pt]
/-
**CommRingCat.prodFan** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：prodFan : BinaryFan A B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product in `CommRingCat` is the Cartesian product. This is the binary fan.
-/
def prodFan : BinaryFan A B :=
  BinaryFan.mk (CommRingCat.ofHom <| RingHom.fst A B) (CommRingCat.ofHom <| RingHom.snd A B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The product in `CommRingCat` is the Cartesian product. -/
/-
**CommRingCat.prodFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：prodFanIsLimit : IsLimit (prodFan A B) where lift c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product in `CommRingCat` is the Cartesian product.
-/
def prodFanIsLimit : IsLimit (prodFan A B) where
  lift c := ofHom <| RingHom.prod (c.π.app ⟨WalkingPair.left⟩).hom (c.π.app ⟨WalkingPair.right⟩).hom
  fac c j := by
    ext
    rcases j with ⟨⟨⟩⟩ <;>
    simp only [pair_obj_left, prodFan_pt, BinaryFan.π_app_left, BinaryFan.π_app_right] <;> rfl
  uniq s m h := by
    ext x
    change m x = (BinaryFan.fst s x, BinaryFan.snd s x)
    have eq1 : (m ≫ (A.prodFan B).fst) x = (BinaryFan.fst s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.left⟩) x
    have eq2 : (m ≫ (A.prodFan B).snd) x = (BinaryFan.snd s) x :=
      ConcreteCategory.congr_hom (h ⟨WalkingPair.right⟩) x
    rw [← eq1, ← eq2]
    simp [prodFan]

end Product

section Pi

variable {ι : Type u} (R : ι → CommRingCat.{u})

/--
The categorical product of rings is the Cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
/-
**CommRingCat.piFan** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：piFan : Fan R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical product of rings is the Cartesian product of rings. This is its 
`Fan`.
-/
def piFan : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (fun i ↦ ofHom <| Pi.evalRingHom _ i)

/--
The categorical product of rings is the Cartesian product of rings.
-/
/-
**CommRingCat.piFanIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：piFanIsLimit : IsLimit (piFan R) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical product of rings is the Cartesian product of rings.
-/
def piFanIsLimit : IsLimit (piFan R) where
  lift s := ofHom <| RingHom.pi fun i ↦ (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
  uniq _ _ h := hom_ext <| DFunLike.ext _ _ fun x ↦ funext fun i ↦
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

/--
The categorical product and the usual product agree
-/
/-
**CommRingCat.piIsoPi** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) -> R i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical product and the usual product agree
-/
noncomputable def piIsoPi : ∏ᶜ R ≅ CommRingCat.of ((i : ι) → R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩

/--
The categorical product and the usual product agree
-/
/-
**CommRingCat._root_.RingEquiv.piEquivPi** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical product and the usual product agree
-/
noncomputable def _root_.RingEquiv.piEquivPi (R : ι → Type u) [∀ i, CommRing (R i)] :
    (∏ᶜ (fun i : ι ↦ CommRingCat.of (R i)) : CommRingCat.{u}) ≃+* ((i : ι) → R i) :=
  (piIsoPi (CommRingCat.of <| R ·)).commRingCatIsoToRingEquiv

end Pi

namespace Limits

variable {J : Type u'} [SmallCategory J] (F : J ⥤ CommRingCat.{u}) {c : Cone F}

set_option backward.isDefEq.respectTransparency false in
/-
**CommRingCat.Limits.isUnit_iff_forall_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `CommRin
gCat.Limits`。
形式化陈述：isUnit_iff_forall_isUnit (hc : IsLimit c) (r : c.pt) : IsUnit r ↔ forall (
j : J), IsUnit (c.π.app j r)
参数：hc : IsLimit c；r : c.pt。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `FreeCommRing.hom_ext`：hom_ext ⦃f g : FreeCommRing α ->+* R⦄ (h : forall 
x, f (of x) = g (of x)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FreeCommRing.lift_of`：lift_of (x : α) : lift f (of x) = f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.Concrete.isLimit_ext`：isLimit_ext {D : Cone F} (hD
 : IsLimit D) (x y : ToType D.pt) : (forall j, D.π.app j x = D.π.app j y) -> x =
 y
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CommRingCat.instIsRightAdjointForgetRingHomCarrier`：(CategoryTheory.forg
et CommRingCat).IsRightAdjoint
（共 36 条，此处仅展示前 30 条）
-/
theorem isUnit_iff_forall_isUnit (hc : IsLimit c) (r : c.pt) : IsUnit r ↔
    ∀ (j : J), IsUnit (c.π.app j r) := by
  refine ⟨fun h _ ↦ h.map _, fun h ↦ ?_⟩
  simp only [isUnit_iff_exists_inv] at h ⊢
  choose inv h_inv using h
  have map_inv {j k : J} (f : j ⟶ k) : F.map f (inv j) = inv k := by
    have h := congr(F.map f $(h_inv j))
    have : F.map f (c.π.app j r) = c.π.app k r :=
      DFunLike.congr_fun (congr(Hom.hom $(c.w f))) r
    rw [map_mul, map_one, this] at h
    rw [← mul_one (F.map f (inv j)), ← h_inv k, ← mul_assoc]
    nth_rw 2 [mul_comm]; rw [h, one_mul]
  let inv_r : Cone F := .mk (CommRingCat.of (FreeCommRing PUnit)) {
    app j := ConcreteCategory.ofHom (FreeCommRing.lift (fun _ ↦ inv j))
    naturality j k f := by
      ext1; change FreeCommRing.lift (fun _ => inv k) = _
      ext; simp [map_inv f] }
  use hc.lift inv_r (FreeCommRing.of PUnit.unit)
  refine Concrete.isLimit_ext _ hc _ _ fun j ↦ ?_
  rw [RingHom.map_mul, RingHom.map_one]; convert h_inv j
  change (hc.lift inv_r ≫ c.π.app j) (FreeCommRing.of PUnit.unit) = inv j
  rw [IsLimit.fac]; exact FreeCommRing.lift_of ..

-- The assumption `hj` can be generalized to a zigzag-like assumption of finite steps.
/-
**CommRingCat.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_isLocalHom (hc : IsLimit c) (j : J) (hj : ∀ (x : c.pt), IsUnit (c.π.app j x) →
    ∀ (i : J), ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), IsLocalHom (F.map f).hom ∧
      F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalHom (c.π.app j).hom := by
  refine ⟨fun (x : c.pt) hx ↦ (?_ : IsUnit x)⟩
  rw [isUnit_iff_forall_isUnit F hc]; intro i
  obtain ⟨k, f, g, lh, eq⟩ := hj x hx i
  exact lh.map_nonunit _ (eq ▸ hx.map _)
/-
**CommRingCat.Limits.isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat.Limits`。
形式化陈述：isLocalRing (hc : IsLimit c) (j : J) [IsLocalRing (F.obj j)] (hj : forall 
(x : c.pt), IsUnit (c.π.app j x) -> forall (i : J), exists (k : J) (f : i ⟶ k) (
g : j ⟶ k), IsLocalHom (F.map f).hom ∧ F.map f (c.π.app i x) = F.map g (c.π.app 
j x)) : IsLocalRing c.pt
参数：hc : IsLimit c；j : J；F.obj j；hj : forall (x : c.pt), IsUnit (c.π.app j x) -> 
forall (i : J), exists (k : J) (f : i ⟶ k) (g : j ⟶ k), IsLocalHom (F.map f).hom
 ∧ F.map f (c.π.app i x) = F.map g (c.π.app j x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CommRingCat.Limits.π_isLocalHom`：π_isLocalHom (hc : IsLimit c) (j : J) (
hj : forall (x : c.pt), IsUnit (c.π.app j x) -> forall (i : J), exists (k : J) (
f : i ⟶ k) (g : j ⟶ k…
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial
-/
theorem isLocalRing (hc : IsLimit c) (j : J) [IsLocalRing (F.obj j)]
    (hj : ∀ (x : c.pt), IsUnit (c.π.app j x) → ∀ (i : J), ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k),
      IsLocalHom (F.map f).hom ∧ F.map f (c.π.app i x) = F.map g (c.π.app j x)) :
    IsLocalRing c.pt := by
  have := π_isLocalHom F hc j hj
  apply RingHom.domain_isLocalRing (c.π.app j).hom

end Limits

section Equalizer

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

/-- The equalizer in `CommRingCat` is the equalizer as sets. This is the equalizer fork. -/
/-
**CommRingCat.equalizerFork** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：equalizerFork : Fork f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer in `CommRingCat` is the equalizer as sets. This is the equalizer f
ork.
-/
def equalizerFork : Fork f g :=
  Fork.ofι (CommRingCat.ofHom (RingHom.eqLocus f.hom g.hom).subtype) <| by
      ext ⟨x, e⟩
      simpa using e

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
/-
**CommRingCat.equalizerForkIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：equalizerForkIsLimit : IsLimit (equalizerFork f g)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equalizer in `CommRingCat` is the equalizer as sets.
-/
def equalizerForkIsLimit : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  use ofHom <| s.ι.hom.codRestrict _ fun x => (ConcreteCategory.congr_hom s.condition x :)
  constructor
  · ext
    rfl
  · intro m hm
    ext x
    exact Subtype.ext <| RingHom.congr_fun (congrArg Hom.hom hm) x

set_option backward.isDefEq.respectTransparency.types false in
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (equalizerFork f g).ι.hom :=
  inferInstanceAs <| IsLocalHom (f.hom.eqLocus g.hom).subtype

open WalkingParallelPair WalkingParallelPairHom Opposite

set_option backward.isDefEq.respectTransparency.types false in
/-
**CommRingCat.equalizer_** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) zero fun x hx i ↦ ?_
  rcases i with _ | _
  · exact ⟨zero, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, 𝟙 _, left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π, RingHom.id_apply]
    exact (limit.w_apply F left x).symm
/-
**CommRingCat.equalizer_limit_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat
`。
形式化陈述：equalizer_limit_isLocalRing (F : WalkingParallelPair ⥤ CommRingCat.{u}) [I
sLocalRing (F.obj zero)] : IsLocalRing ↑(limit F)
参数：F : WalkingParallelPair ⥤ CommRingCat.{u}；F.obj zero。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem equalizer_limit_isLocalRing (F : WalkingParallelPair ⥤ CommRingCat.{u})
    [IsLocalRing (F.obj zero)] : IsLocalRing ↑(limit F) :=
  RingHom.domain_isLocalRing (limit.π F WalkingParallelPair.zero).hom
/-
**CommRingCat.equalizer_** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equalizer_ι_isLocalHom' (F : WalkingParallelPairᵒᵖ ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F (op one)).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) (op one) fun x hx i ↦ ?_
  rcases i with _ | _
  · refine ⟨op zero, 𝟙 _, op left, inferInstance, ?_⟩
    simp only [CategoryTheory.Functor.map_id, hom_id, limit.cone_x, limit.cone_π,
      RingHom.id_apply]
    exact (limit.w_apply F (op left) x).symm
  · exact ⟨op one, 𝟙 _, 𝟙 _, inferInstance, by simp⟩

end Equalizer

section Pullback

variable {A B C : CommRingCat.{u}}

/-- In the category of `CommRingCat`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is the `eqLocus`
of the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
/-
**CommRingCat.pullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：pullbackCone (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g
参数：f : A ⟶ C；g : B ⟶ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the category of `CommRingCat`, the pullback of `f : A ⟶ C` and `g : B ⟶ C` is
 the `eqLocus`
of the two maps `A × B ⟶ C`. This is the constructed pullback cone.
-/
def pullbackCone (f : A ⟶ C) (g : B ⟶ C) : PullbackCone f g :=
  PullbackCone.mk
    (CommRingCat.ofHom <|
      (RingHom.fst A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (CommRingCat.ofHom <|
      (RingHom.snd A B).comp
        (RingHom.eqLocus (f.hom.comp (RingHom.fst A B)) (g.hom.comp (RingHom.snd A B))).subtype)
    (by
      ext ⟨x, e⟩
      simpa [CommRingCat.ofHom] using e)

/-- The constructed pullback cone is indeed the limit. -/
/-
**CommRingCat.pullbackConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：pullbackConeIsLimit (f : A ⟶ C) (g : B ⟶ C) : IsLimit (pullbackCone f g)
参数：f : A ⟶ C；g : B ⟶ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed pullback cone is indeed the limit.
-/
def pullbackConeIsLimit (f : A ⟶ C) (g : B ⟶ C) :
    IsLimit (pullbackCone f g) := by
  fapply PullbackCone.IsLimit.mk
  · intro s
    refine ofHom ((s.fst.hom.prod s.snd.hom).codRestrict _ ?_)
    intro x
    exact congr_arg (fun f : s.pt →+* C => f x) (congrArg Hom.hom s.condition)
  · intro s
    ext x
    rfl
  · intro s
    ext x
    rfl
  · intro s m e₁ e₂
    refine hom_ext <| RingHom.ext fun (x : s.pt) => Subtype.ext ?_
    change (m x).1 = (_, _)
    have eq1 := (congr_arg (fun f : s.pt →+* A => f x) (congrArg Hom.hom e₁) :)
    have eq2 := (congr_arg (fun f : s.pt →+* B => f x) (congrArg Hom.hom e₂) :)
    rw [← eq1, ← eq2]
    rfl

open WalkingCospan
/-
**CommRingCat.pullbackFst_isLocalHom** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
形式化陈述：pullbackFst_isLocalHom (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] : IsLoca
lHom (pullback.fst f g).hom
参数：f : A ⟶ C；g : B ⟶ C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CommRingCat.Limits.π_isLocalHom`：π_isLocalHom (hc : IsLimit c) (j : J) (
hj : forall (x : c.pt), IsUnit (c.π.app j x) -> forall (i : J), exists (k : J) (
f : i ⟶ k) (g : j ⟶ k…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `isLocalHom_of_isIso`：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S)
 [IsIso f] : IsLocalHom f.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_one`：condition_one (t : Pul
lbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance pullbackFst_isLocalHom (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] :
    IsLocalHom (pullback.fst f g).hom := by
  refine Limits.π_isLocalHom _ (limit.isLimit _) left fun x hx i ↦ ?_
  rcases i with _ | _ | _
  · exact ⟨one, 𝟙 _, Hom.inl, inferInstance, by simp; rfl⟩
  · exact ⟨left, 𝟙 _, 𝟙 _, inferInstance, by simp⟩
  · refine ⟨one, Hom.inr, Hom.inl, ‹_›, ?_⟩
    exact DFunLike.congr_fun (congr(Hom.hom $(pullback.condition (f := f) (g := g)))) x |>.symm
/-
**CommRingCat.pullback_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `CommRingCat`。
形式化陈述：pullback_isLocalRing (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] [IsLocalRi
ng A] : IsLocalRing ↑(pullback f g)
参数：f : A ⟶ C；g : B ⟶ C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_isLocalRing`：RingHom.domain_isLocalRing [IsLocalRing S] (
f : R ->+* S) [IsLocalHom f] : IsLocalRing R where toNontrivial
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem pullback_isLocalRing (f : A ⟶ C) (g : B ⟶ C) [IsLocalHom g.hom] [IsLocalRing A] :
    IsLocalRing ↑(pullback f g) :=
  RingHom.domain_isLocalRing (pullback.fst f g).hom

end Pullback

end CommRingCat

