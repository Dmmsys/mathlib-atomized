/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Properties of ring homomorphisms

We provide the basic framework for talking about properties of ring homomorphisms.
The following meta-properties of predicates on ring homomorphisms are defined

* `RingHom.RespectsIso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and
  `P f → P (f ≫ e)`, where `e` is an isomorphism.
* `RingHom.StableUnderComposition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `RingHom.IsStableUnderBaseChange`: `P` is stable under base change if `P (S ⟶ Y)`
  implies `P (X ⟶ X ⊗[S] Y)`.

-/

@[expose] public section


universe u

open CategoryTheory Opposite CategoryTheory.Limits TensorProduct

namespace RingHom

variable {P Q : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop}

section RespectsIso

variable (P) in
/-- A property `RespectsIso` if it still holds when composed with an isomorphism -/
/-
**RingHom.RespectsIso** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：RespectsIso : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property `RespectsIso` if it still holds when composed with an isomorphism
-/
def RespectsIso : Prop :=
  (∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (e : S ≃+* T) (_ : P f), P (e.toRingHom.comp f)) ∧
    ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : S →+* T) (e : R ≃+* S) (_ : P f), P (f.comp e.toRingHom)
/-
**RingHom.RespectsIso.cancel_left_isIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Respe
ctsIso`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.RespectsIso P →     ∀ {R S T : CommRingCat} (f : R ⟶ S)
 (g : S ⟶ T) [CategoryTheory.IsIso f],       P ((CommRingCat.Hom.hom g).comp (Co
mmRingCat.Hom.hom f)) ↔ P (CommRingCat.Hom.hom g)
参数：R →+* S；f : R ⟶ S；g : S ⟶ T；(CommRingCat.Hom.hom g).comp (CommRingCat.Hom.hom
 f)；CommRingCat.Hom.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem RespectsIso.cancel_left_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso f] : P (g.hom.comp f.hom) ↔ P g.hom :=
  ⟨fun H => by
    convert! hP.2 (f ≫ g).hom (asIso f).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp], hP.2 g.hom (asIso f).commRingCatIsoToRingEquiv⟩
/-
**RingHom.RespectsIso.cancel_right_isIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Resp
ectsIso`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.RespectsIso P →     ∀ {R S T : CommRingCat} (f : R ⟶ S)
 (g : S ⟶ T) [CategoryTheory.IsIso g],       P ((CommRingCat.Hom.hom g).comp (Co
mmRingCat.Hom.hom f)) ↔ P (CommRingCat.Hom.hom f)
参数：R →+* S；f : R ⟶ S；g : S ⟶ T；(CommRingCat.Hom.hom g).comp (CommRingCat.Hom.hom
 f)；CommRingCat.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem RespectsIso.cancel_right_isIso (hP : RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S)
    (g : S ⟶ T) [IsIso g] : P (g.hom.comp f.hom) ↔ P f.hom :=
  ⟨fun H => by
    convert! hP.1 (f ≫ g).hom (asIso g).symm.commRingCatIsoToRingEquiv H
    simp [← CommRingCat.hom_comp],
   hP.1 f.hom (asIso g).commRingCatIsoToRingEquiv⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**RingHom.RespectsIso.isLocalization_away_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
.RespectsIso`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.RespectsIso P →     ∀ {R S : Type u} (R' S' : Type u) [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing R']       [inst_3 : 
CommRing S'] [inst_4 : Algebra R R'] [inst_5 : Algebra S S'] (f : R →+* S) (r : 
R)       [inst_6 : IsLocalization.Away r R'] [inst_7 : IsLocalization.Away (f r)
 S'],       P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r)
参数：R →+* S；R' S' : Type u；f : R →+* S；r : R；f r；Localization.awayMap f r；IsLocal
ization.Away.map R' S' f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RingHom.RespectsIso.cancel_left_isIso`：∀ {P : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P 
→     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem RespectsIso.isLocalization_away_iff (hP : RingHom.RespectsIso @P) {R S : Type u}
    (R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R R']
    [Algebra S S'] (f : R →+* S) (r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] :
    P (Localization.awayMap f r) ↔ P (IsLocalization.Away.map R' S' f r) := by
  let e₁ : R' ≃+* Localization.Away r :=
    (IsLocalization.algEquiv (Submonoid.powers r) _ _).toRingEquiv
  let e₂ : Localization.Away (f r) ≃+* S' :=
    (IsLocalization.algEquiv (Submonoid.powers (f r)) _ _).toRingEquiv
  refine (hP.cancel_left_isIso e₁.toCommRingCatIso.hom (CommRingCat.ofHom _)).symm.trans ?_
  refine (hP.cancel_right_isIso (CommRingCat.ofHom _) e₂.toCommRingCatIso.hom).symm.trans ?_
  rw [← eq_iff_iff]
  congr 1
  -- Porting note: Here, the proof used to have a huge `simp` involving `[anonymous]`, which didn't
  -- work out anymore. The issue seemed to be that it couldn't handle a term in which Ring
  -- homomorphisms were repeatedly casted to the bundled category and back. Here we resolve the
  -- problem by converting the goal to a more straightforward form.
  let e := (e₂ : Localization.Away (f r) →+* S').comp
      (((IsLocalization.map (Localization.Away (f r)) f
            (by rintro x ⟨n, rfl⟩; use n; simp : Submonoid.powers r ≤ Submonoid.comap f
                (Submonoid.powers (f r)))) : Localization.Away r →+* Localization.Away (f r)).comp
                (e₁ : R' →+* Localization.Away r))
  suffices e = IsLocalization.Away.map R' S' f r by
    convert! this
  apply IsLocalization.ringHom_ext (Submonoid.powers r) _
  ext1 x
  dsimp [e, e₁, e₂, IsLocalization.Away.map]
  simp only [IsLocalization.map_eq, id_apply, RingHomCompTriple.comp_apply]
/-
**RingHom.RespectsIso.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.RespectsIso`。
形式化陈述：∀ {P Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop},   (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P
) →     (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => Q) →       R
ingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] f => P f ∧ Q f
参数：R →+* S；RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P；RingHom.
RespectsIso fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma RespectsIso.and (hP : RespectsIso P) (hQ : RespectsIso Q) :
    RespectsIso (fun f ↦ P f ∧ Q f) := by
  refine ⟨?_, ?_⟩
  · introv hf
    exact ⟨hP.1 f e hf.1, hQ.1 f e hf.2⟩
  · introv hf
    exact ⟨hP.2 f e hf.1, hQ.2 f e hf.2⟩

end RespectsIso

section StableUnderComposition

variable (P) in
/-- A property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class. -/
/-
**RingHom.StableUnderComposition** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：StableUnderComposition : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property is `StableUnderComposition` if the composition of two such morphisms
still falls in the class.
-/
def StableUnderComposition : Prop :=
  ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
    ∀ (f : R →+* S) (g : S →+* T) (_ : P f) (_ : P g), P (g.comp f)
/-
**RingHom.StableUnderComposition.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.
StableUnderComposition`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.StableUnderComposition P →     (∀ {R S : Type u} [inst 
: CommRing R] [inst_1 : CommRing S] (e : R ≃+* S), P e.toRingHom) → RingHom.Resp
ectsIso P
参数：R →+* S；∀ {R S : Type u} [inst : CommRing R] [inst_1 : CommRing S] (e : R ≃+*
 S), P e.toRingHom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StableUnderComposition.respectsIso (hP : RingHom.StableUnderComposition @P)
    (hP' : ∀ {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S), P e.toRingHom) :
    RingHom.RespectsIso @P := by
  constructor
  · introv H
    apply hP
    exacts [H, hP' e]
  · introv H
    apply hP
    exacts [hP' e, H]
/-
**RingHom.StableUnderComposition.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.StableUn
derComposition`。
形式化陈述：∀ {P Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop},   (RingHom.StableUnderComposition fun {R S} [CommRing R] [CommR
ing S] => P) →     (RingHom.StableUnderComposition fun {R S} [CommRing R] [CommR
ing S] => Q) →       RingHom.StableUnderComposition fun {R S} [CommRing R] [Comm
Ring S] f => P f ∧ Q f
参数：R →+* S；RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] =>
 P；RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma StableUnderComposition.and (hP : StableUnderComposition P) (hQ : StableUnderComposition Q) :
    StableUnderComposition (fun f ↦ P f ∧ Q f) := by
  introv R hf hg
  exact ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

end StableUnderComposition

section IsStableUnderBaseChange

variable (P) in
/-- A morphism property `P` is `IsStableUnderBaseChange` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`. -/
/-
**RingHom.IsStableUnderBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：IsStableUnderBaseChange : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property `P` is `IsStableUnderBaseChange` if `P(S →+* A)` implies
`P(B →+* A ⊗[S] B)`.
-/
def IsStableUnderBaseChange : Prop :=
  ∀ (R S R' S') [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
    ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
      ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
        ∀ [Algebra.IsPushout R S R' S'], P (algebraMap R S) → P (algebraMap R' S')
/-
**RingHom.IsStableUnderBaseChange.mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStable
UnderBaseChange`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.RespectsIso P →     (∀ ⦃R S T : Type u⦄ [inst : CommRin
g R] [inst_1 : CommRing S] [inst_2 : CommRing T] [inst_3 : Algebra R S]         
[inst_4 : Algebra R T], P (algebraMap R T) → P (algebraMap S (TensorProduct R S 
T))) →       RingHom.IsStableUnderBaseChange P
参数：R →+* S；∀ ⦃R S T : Type u⦄ [inst : CommRing R] [inst_1 : CommRing S] [inst_2 
: CommRing T] [inst_3 : Algebra R S]         [inst_4 : Algebra R T], P (algebraM
ap R T) → P (algebraMap S (TensorProduct R S T))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsStableUnderBaseChange.mk (h₁ : RespectsIso @P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T],
      P (algebraMap R T) → P (algebraMap S (S ⊗[R] T))) :
    IsStableUnderBaseChange @P := by
  introv R h H
  let e := h.symm.1.equiv
  let f' := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R R' S')
    (IsScalarTower.toAlgHom R S S')
  have hef (x : _) : e x = f' x := by
    suffices e.toLinearMap.restrictScalars R = f'.toLinearMap from congr($this x)
    exact ext' fun x y ↦ by simp [e, f', IsBaseChange.equiv_tmul, Algebra.smul_def]
  have hemul (x y : _) : e (x * y) = e x * e y := by simp_rw [hef, map_mul]
  convert! h₁.1 _ { e with map_mul' := hemul } (h₂ H)
  ext x
  simp [e, h.symm.1.equiv_tmul, Algebra.smul_def]

attribute [local instance] Algebra.TensorProduct.rightAlgebra
/-
**RingHom.IsStableUnderBaseChange.tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.IsStableUnderBaseChange`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   (RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRi
ng S] => P) →     ∀ {R S : Type u} (T : Type u) [inst : CommRing R] [inst_1 : Co
mmRing S] [inst_2 : CommRing T] [inst_3 : Algebra R S]       [inst_4 : Algebra R
 T], P (algebraMap R S) → P (algebraMap T (TensorProduct R T S))
参数：R →+* S；RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] =
> P；T : Type u；algebraMap R S；algebraMap T (TensorProduct R T S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma IsStableUnderBaseChange.tensorProduct (hP : RingHom.IsStableUnderBaseChange P)
    {R S : Type u} (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (h : P (algebraMap R S)) :
    P (algebraMap T (T ⊗[R] S)) :=
  -- This only works because the `Algebra.TensorProduct.rightAlgebra` instance is present here.
  hP _ _ _ _ h

set_option backward.isDefEq.respectTransparency false in
/-
**RingHom.IsStableUnderBaseChange.pushout_inl** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
.IsStableUnderBaseChange`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   RingHom.IsStableUnderBaseChange P →     RingHom.RespectsIso P →
       ∀ {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T),         P (CommRingCat.H
om.hom g) → P (CommRingCat.Hom.hom (CategoryTheory.Limits.pushout.inl f g))
参数：R →+* S；f : R ⟶ S；g : R ⟶ T；CommRingCat.Hom.hom g；CommRingCat.Hom.hom (Catego
ryTheory.Limits.pushout.inl f g)。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem IsStableUnderBaseChange.pushout_inl (hP : RingHom.IsStableUnderBaseChange @P)
    (hP' : RingHom.RespectsIso @P) {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T) (H : P g.hom) :
    P (pushout.inl _ _ : S ⟶ pushout f g).hom := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  rw [← show _ = pushout.inl f g from
      colimit.isoColimitCocone_ι_inv ⟨_, CommRingCat.pushoutCoconeIsColimit R S T⟩ WalkingSpan.left,
    CommRingCat.hom_comp, hP'.cancel_right_isIso]
  dsimp only [CommRingCat.pushoutCocone_inl, PushoutCocone.ι_app_left]
  apply hP R T S (S ⊗[R] T)
  exact H
/-
**RingHom.IsStableUnderBaseChange.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsStabl
eUnderBaseChange`。
形式化陈述：∀ {P Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop},   (RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [Comm
Ring S] => P) →     (RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [Com
mRing S] => Q) →       RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [C
ommRing S] f => P f ∧ Q f
参数：R →+* S；RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] =
> P；RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsStableUnderBaseChange.and (hP : IsStableUnderBaseChange P)
    (hQ : IsStableUnderBaseChange Q) :
    IsStableUnderBaseChange (fun f ↦ P f ∧ Q f) := by
  introv R _ h
  exact ⟨hP R S R' S' h.1, hQ R S R' S' h.2⟩

end IsStableUnderBaseChange

section ToMorphismProperty

variable (P) in
/-- The categorical `MorphismProperty` associated to a property of ring homs expressed
non-categorical terms. -/
/-
**RingHom.toMorphismProperty** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：toMorphismProperty : MorphismProperty CommRingCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical `MorphismProperty` associated to a property of ring homs express
ed
non-categorical terms.
-/
def toMorphismProperty : MorphismProperty CommRingCat := fun _ _ f ↦ P f.hom
/-
**RingHom.toMorphismProperty_respectsIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`
。
形式化陈述：toMorphismProperty_respectsIso_iff : RespectsIso P ↔ (toMorphismProperty P
).RespectsIso
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.precomp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P
.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) […
-/
lemma toMorphismProperty_respectsIso_iff :
    RespectsIso P ↔ (toMorphismProperty P).RespectsIso := by
  refine ⟨fun h ↦ MorphismProperty.RespectsIso.mk _ ?_ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · intro X Y Z e f hf
    exact h.right f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z e f hf
    exact h.left f.hom e.commRingCatIsoToRingEquiv hf
  · intro X Y Z _ _ _ f e hf
    exact MorphismProperty.RespectsIso.postcomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f) hf
  · intro X Y Z _ _ _ f e
    exact MorphismProperty.RespectsIso.precomp (toMorphismProperty P)
      e.toCommRingCatIso.hom (CommRingCat.ofHom f)
/-
**RingHom.isStableUnderCobaseChange_toMorphismProperty_iff** 是 Mathlib 中的一个引理，位于
命名空间 `RingHom`。
形式化陈述：isStableUnderCobaseChange_toMorphismProperty_iff : (toMorphismProperty P).
IsStableUnderCobaseChange ↔ IsStableUnderBaseChange P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.of_isPushout`：
∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Mor
phismProperty C}   [self : P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.isPushout_iff_isPushout`：isPushout_iff_isPushout {R S : Type
 u} [CommRing R] [CommRing S] [Algebra R S] {R' S' : Type u} [CommRing R'] [Comm
Ring S'] [Algebra R R'] […
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPushout.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {in
r : Y ⟶ P}, CategoryThe…
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma isStableUnderCobaseChange_toMorphismProperty_iff :
    (toMorphismProperty P).IsStableUnderCobaseChange ↔ IsStableUnderBaseChange P := by
  refine ⟨fun h R S R' S' _ _ _ _ _ _ _ _ _ _ _ hsq hRS ↦ ?_,
      fun h ↦ ⟨fun {R} S R' S' f g f' g' hsq hf ↦ ?_⟩⟩
  · rw [← CommRingCat.isPushout_iff_isPushout] at hsq
    exact h.1 (f := CommRingCat.ofHom (algebraMap R S)) hsq.flip hRS
  · algebraize [f.hom, g.hom, f'.hom, g'.hom, f'.hom.comp g.hom]
    have : IsScalarTower R S S' := .of_algebraMap_eq fun x ↦ congr($(hsq.1.1).hom x)
    have : Algebra.IsPushout R S R' S' := (CommRingCat.isPushout_iff_isPushout.mp hsq).symm
    exact h (R := R) (S := S) _ _ hf

/-- Variant of `MorphismProperty.arrow_mk_iso_iff` specialized to morphism properties in
`CommRingCat` given by ring hom properties. -/
/-
**RingHom.RespectsIso.arrow_mk_iso_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Respec
tsIso`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop},   (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P) 
→     ∀ {A B A' B' : CommRingCat} {f : A ⟶ B} {g : A' ⟶ B'} (e : CategoryTheory.
Arrow.mk f ≅ CategoryTheory.Arrow.mk g),       P (CommRingCat.Hom.hom f) ↔ P (Co
mmRingCat.Hom.hom g)
参数：R →+* S；RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P；e : Cate
goryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk g；CommRingCat.Hom.hom f；CommRing
Cat.Hom.hom g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.toMorphismProperty_respectsIso_iff`：toMorphismProperty_respectsI
so_iff : RespectsIso P ↔ (toMorphismProperty P).RespectsIso
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Variant of `MorphismProperty.arrow_mk_iso_iff` specialized to morphism propertie
s in
`CommRingCat` given by ring hom properties.
-/
lemma RespectsIso.arrow_mk_iso_iff (hQ : RingHom.RespectsIso P) {A B A' B' : CommRingCat}
    {f : A ⟶ B} {g : A' ⟶ B'} (e : Arrow.mk f ≅ Arrow.mk g) :
    P f.hom ↔ P g.hom := by
  have : (toMorphismProperty P).RespectsIso := by
    rwa [← toMorphismProperty_respectsIso_iff]
  change toMorphismProperty P _ ↔ toMorphismProperty P _
  rw [MorphismProperty.arrow_mk_iso_iff (toMorphismProperty P) e]

end ToMorphismProperty

section Descent

variable (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable (R S T : Type u) [CommRing R] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

variable (P) in
/-- A property of ring homomorphisms `Q` codescends along `Q'` if whenever
`R' →+* R' ⊗[R] S` satisfies `Q` and `R →+* R'` satisfies `Q'`, then `R →+* S` satisfies `Q`. -/
/-
**RingHom.CodescendsAlong** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：CodescendsAlong : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of ring homomorphisms `Q` codescends along `Q'` if whenever
`R' →+* R' ⊗[R] S` satisfies `Q` and `R →+* R'` satisfies `Q'`, then `R →+* S` s
atisfies `Q`.
-/
def CodescendsAlong : Prop :=
  ∀ ⦃R S R' S' : Type u⦄ [CommRing R] [CommRing S] [CommRing R'] [CommRing S'],
  ∀ [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S'],
    ∀ [IsScalarTower R S S'] [IsScalarTower R R' S'],
      ∀ [Algebra.IsPushout R S R' S'],
        Q (algebraMap R R') → P (algebraMap R' S') → P (algebraMap R S)
/-
**RingHom.CodescendsAlong.mk** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.CodescendsAlong`
。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   (Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S
] → (R →+* S) → Prop),   (RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S
] => P) →     (∀ ⦃R S T : Type u⦄ [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : CommRing T] [inst_3 : Algebra R S]         [inst_4 : Algebra R T], Q (alge
braMap R S) → P (algebraMap S (TensorProduct R S T)) → P (algebraMap R T)) →    
   RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => P) fun {R S} 
[CommRing R] [CommRing S] => Q
参数：R →+* S；Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop；RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => P；∀ ⦃R
 S T : Type u⦄ [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T] [
inst_3 : Algebra R S]         [inst_4 : Algebra R T], Q (algebraMap R S) → P (al
gebraMap S (TensorProduct R S T)) → P (algebraMap R T)；fun {R S} [CommRing R] [C
ommRing S] => P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma CodescendsAlong.mk (h₁ : RespectsIso P)
    (h₂ : ∀ ⦃R S T⦄ [CommRing R] [CommRing S] [CommRing T],
      ∀ [Algebra R S] [Algebra R T],
        Q (algebraMap R S) → P (algebraMap S (S ⊗[R] T)) → P (algebraMap R T)) :
    CodescendsAlong P Q := by
  introv R h hQ H
  let e := h.symm.equiv
  have : (e.symm : _ →+* _).comp (algebraMap R' S') = algebraMap R' (R' ⊗[R] S) := by
    ext r
    simp [e]
  apply h₂ hQ
  rw [← this]
  exact h₁.1 _ _ H
/-
**RingHom.CodescendsAlong.algebraMap_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `Ri
ngHom.CodescendsAlong`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   (Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S
] → (R →+* S) → Prop) (R S T : Type u)   [inst : CommRing R] [inst_1 : CommRing 
S] [inst_2 : Algebra R S] [inst_3 : CommRing T] [inst_4 : Algebra R T],   (RingH
om.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => P) fun {R S} [CommRin
g R] [CommRing S] => Q) →     Q (algebraMap R S) → P (algebraMap S (TensorProduc
t R S T)) → P (algebraMap R T)
参数：R →+* S；Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop；R S T : Type u；RingHom.CodescendsAlong (fun {R S} [CommRing R] [C
ommRing S] => P) fun {R S} [CommRing R] [CommRing S] => Q；algebraMap R S；algebra
Map S (TensorProduct R S T)；algebraMap R T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma CodescendsAlong.algebraMap_tensorProduct (hPQ : CodescendsAlong P Q)
    (h : Q (algebraMap R S)) (H : P (algebraMap S (S ⊗[R] T))) :
    P (algebraMap R T) :=
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  hPQ h H
/-
**RingHom.CodescendsAlong.includeRight** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Codesc
endsAlong`。
形式化陈述：∀ {P : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R →
+* S) → Prop}   (Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S
] → (R →+* S) → Prop) (R S T : Type u)   [inst : CommRing R] [inst_1 : CommRing 
S] [inst_2 : Algebra R S] [inst_3 : CommRing T] [inst_4 : Algebra R T],   (RingH
om.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => P) fun {R S} [CommRin
g R] [CommRing S] => Q) →     Q (algebraMap R T) → P Algebra.TensorProduct.inclu
deRight.toRingHom → P (algebraMap R S)
参数：R →+* S；Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop；R S T : Type u；RingHom.CodescendsAlong (fun {R S} [CommRing R] [C
ommRing S] => P) fun {R S} [CommRing R] [CommRing S] => Q；algebraMap R T；algebra
Map R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma CodescendsAlong.includeRight (hPQ : CodescendsAlong P Q) (h : Q (algebraMap R T))
    (H : P ((Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T))) :
    P (algebraMap R S) := by
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  apply hPQ h H

variable {Q} {P' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
/-
**RingHom.CodescendsAlong.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.CodescendsAlong
`。
形式化陈述：∀ {P Q P' : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] →
 (R →+* S) → Prop},   (RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing
 S] => P) fun {R S} [CommRing R] [CommRing S] => Q) →     (RingHom.CodescendsAlo
ng (fun {R S} [CommRing R] [CommRing S] => P') fun {R S} [CommRing R] [CommRing 
S] => Q) →       RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] f 
=> P f ∧ P' f)         fun {R S} [CommRing R] [CommRing S] => Q
参数：R →+* S；RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => P) fu
n {R S} [CommRing R] [CommRing S] => Q；RingHom.CodescendsAlong (fun {R S} [CommR
ing R] [CommRing S] => P') fun {R S} [CommRing R] [CommRing S] => Q；fun {R S} [C
ommRing R] [CommRing S] f => P f ∧ P' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma CodescendsAlong.and (hP : CodescendsAlong P Q) (hP' : CodescendsAlong P' Q) :
    CodescendsAlong (fun f ↦ P f ∧ P' f) Q :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ ↦ ⟨hP h₁ h₂.1, hP' h₁ h₂.2⟩

end Descent

/-- A property of ring homomorphisms `P` is said to have equalizers, if the equalizer of algebra
maps between algebras satisfying `P` also satisfies `P`. -/
/-
**RingHom.HasEqualizers** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：HasEqualizers (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+
* S) -> Prop) : Prop
参数：P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of ring homomorphisms `P` is said to have equalizers, if the equalize
r of algebra
maps between algebras satisfying `P` also satisfies `P`.
-/
def HasEqualizers (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), P (algebraMap R S) → P (algebraMap R T) →
      P (algebraMap R (AlgHom.equalizer f g))
/-
**RingHom.HasEqualizers.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.HasEqualizers`。
形式化陈述：∀ {P Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop},   (RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] =>
 P) →     (RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] => Q) →    
   RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] f => P f ∧ Q f
参数：R →+* S；RingHom.HasEqualizers fun {R S} [CommRing R] [CommRing S] => P；RingHo
m.HasEqualizers fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma HasEqualizers.and (hP : HasEqualizers P) (hQ : HasEqualizers Q) :
    HasEqualizers (fun f ↦ P f ∧ Q f) :=
  fun f g hf hg ↦ ⟨hP f g hf.1 hg.1, hQ f g hf.2 hg.2⟩

/-- A property of ring homomorphisms `P` is said to have finite products, if a finite product of
algebras satisfying `Q` also satisfies `P`. -/
/-
**RingHom.HasFiniteProducts** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：HasFiniteProducts (P : forall {R S : Type u} [CommRing R] [CommRing S], (R
 ->+* S) -> Prop) : Prop
参数：P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of ring homomorphisms `P` is said to have finite products, if a finit
e product of
algebras satisfying `Q` also satisfies `P`.
-/
def HasFiniteProducts (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)],
    (∀ i, P (algebraMap R (S i))) → P (algebraMap R (Π i, S i))
/-
**RingHom.HasFiniteProducts.and** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.HasFiniteProd
ucts`。
形式化陈述：∀ {P Q : {R S : Type u} → [inst : CommRing R] → [inst_1 : CommRing S] → (R
 →+* S) → Prop},   (RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S
] => P) →     (RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => 
Q) →       RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] f => P 
f ∧ Q f
参数：R →+* S；RingHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => P；Ri
ngHom.HasFiniteProducts fun {R S} [CommRing R] [CommRing S] => Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma HasFiniteProducts.and (hP : HasFiniteProducts P) (hQ : HasFiniteProducts Q) :
    HasFiniteProducts (fun f ↦ P f ∧ Q f) :=
  fun _ _ _ hS ↦ ⟨hP _ fun i ↦ (hS i).1, hQ _ fun i ↦ (hS i).2⟩

end RingHom

