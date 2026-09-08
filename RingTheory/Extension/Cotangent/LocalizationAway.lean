/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Cotangent and localization away

Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P : R[X] → S` with kernel `I` and
`Q : S[Y] → T` is the canonical `S`-presentation of `T` with kernel `K`.
Denote by `J` the kernel of the composition `R[X,Y] → T`.

This file proves `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`. For this we establish the exact sequence:
```
0 → T ⊗[S] (I/I²) → J/J² → K/K² → 0
```
and use that `K/K²` is free, so the sequence splits. The first part of the file
shows the exactness on the left and the rest of the file deduces the exact sequence
and the splitting from the Jacobi Zariski sequence.

## Main results

- `Algebra.Generators.liftBaseChange_injective`:
  `T ⊗[S] (I/I²) → J/J²` is injective if `T` is the localization of `S` away from an element.
- `Algebra.Generators.cotangentCompLocalizationAwayEquiv`: `J/J² ≃ₗ[T] T ⊗[S] (I/I²) × K/K²`.
-/

@[expose] public section

open TensorProduct MvPolynomial

namespace Algebra.Generators

variable {R S T ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (g : S) [IsLocalization.Away g T] (P : Generators R S ι)

/-
**Algebra.Generators.comp_localizationAway_ker** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Generators`。
形式化陈述：comp_localizationAway_ker (P : Generators R S ι) (f : P.Ring) (h : algebra
Map P.Ring S f = g) : ((Generators.localizationAway T g).comp P).ker = Ideal.map
 ((Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔ Ideal.span {renam
e Sum.inr f * X (Sum.inl ()) - 1}
参数：P : Generators R S ι；f : P.Ring；h : algebraMap P.Ring S f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
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
· 使用定理 `Algebra.Generators.ker_localizationAway`：∀ {R : Type u} {S : Type v} [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   [inst_3 
: IsLocalization.Away r S],  …
· 使用定理 `Algebra.Generators.Hom.toAlgHom_X`：∀ {R : Type u} {S : Type v} {ι : Type
 w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Alge
bra.Generators R S ι} {…
· 使用引理 `Algebra.Generators.toAlgHom_ofComp_rename`：toAlgHom_ofComp_rename (Q : G
enerators S T ι') (P : Generators R S ι) (p : P.Ring) : (Q.ofComp P).toAlgHom ((
rename Sum.inr) p) = C (algebra…
· 使用定理 `Algebra.Generators.ofComp_val`：∀ {R : Type u} {S : Type v} {ι : Type w} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {ι' : Type u_
3} {T : Type u_7} […
· 使用定理 `Sum.elim_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α → γ)
 (g : β → γ) (x : α), Sum.elim f g (Sum.inl x) = f x
· 使用引理 `Algebra.Generators.ker_comp_eq_sup`：ker_comp_eq_sup (Q : Generators S T 
ι') (P : Generators R S ι) : (Q.comp P).ker = Ideal.map (Q.toComp P).toAlgHom P.
ker ⊔ Ideal.comap (Q.ofC…
· 使用引理 `Algebra.Generators.map_toComp_ker`：map_toComp_ker (Q : Generators S T ι'
) (P : Generators R S ι) : P.ker.map (Q.toComp P).toAlgHom = RingHom.ker (Q.ofCo
mp P).toAlgHom
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用引理 `Algebra.Generators.toAlgHom_ofComp_surjective`：toAlgHom_ofComp_surjectiv
e (Q : Generators S T ι') (P : Generators R S ι) : Function.Surjective (Q.ofComp
 P).toAlgHom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
（共 31 条，此处仅展示前 30 条）
-/
lemma comp_localizationAway_ker (P : Generators R S ι) (f : P.Ring)
    (h : algebraMap P.Ring S f = g) :
    ((Generators.localizationAway T g).comp P).ker =
      Ideal.map ((Generators.localizationAway T g).toComp P).toAlgHom P.ker ⊔
        Ideal.span {rename Sum.inr f * X (Sum.inl ()) - 1} := by
  have : (localizationAway T g).ker = Ideal.map ((localizationAway T g).ofComp P).toAlgHom
      (Ideal.span {MvPolynomial.rename Sum.inr f * MvPolynomial.X (Sum.inl ()) - 1}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, map_one, ker_localizationAway,
      Hom.toAlgHom_X, toAlgHom_ofComp_rename, h, ofComp_val, Sum.elim_inl]
  rw [ker_comp_eq_sup, Algebra.Generators.map_toComp_ker, this,
    Ideal.comap_map_of_surjective _ (toAlgHom_ofComp_surjective _ P), ← RingHom.ker_eq_comap_bot,
    ← sup_assoc]
  simp

variable (T) in
/-- If `R[X] → S` generates `S`, `T` is the localization of `S` away from `g` and
`f` is a pre-image of `g` in `R[X]`, this is the `R`-algebra map `R[X,Y] →ₐ[R] (R[X]/I²)[1/f]`
defined via mapping `Y` to `1/f`. -/
noncomputable
/-
**Algebra.Generators.compLocalizationAwayAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.Generators`。
形式化陈述：compLocalizationAwayAlgHom : ((Generators.localizationAway T g).comp P).Ri
ng ->ₐ[R] Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def compLocalizationAwayAlgHom : ((Generators.localizationAway T g).comp P).Ring →ₐ[R]
      Localization.Away (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)) :=
  aeval (R := R) (S₁ := Localization.Away _)
    (Sum.elim
      (fun _ ↦ IsLocalization.Away.invSelf <| (Ideal.Quotient.mk (P.ker ^ 2) (P.σ g)))
      (fun i : ι ↦ algebraMap P.Ring _ (X i)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.Generators.compLocalizationAwayAlgHom_toAlgHom_toComp** 是 Mathlib 中的一个
引理，位于命名空间 `Algebra.Generators`。
形式化陈述：compLocalizationAwayAlgHom_toAlgHom_toComp (x : P.Ring) : compLocalization
AwayAlgHom T g P (((localizationAway T g).toComp P).toAlgHom x) = algebraMap P.R
ing _ x
参数：x : P.Ring。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.Generators.toComp_toAlgHom`：toComp_toAlgHom (Q : Generators S T 
ι') (P : Generators R S ι) : (Q.toComp P).toAlgHom = rename Sum.inr
· 使用定理 `MvPolynomial.aeval_rename`：aeval_rename [Algebra R S] : aeval g (rename 
k p) = aeval (g ∘ k) p
· 使用定理 `MvPolynomial.aeval_X_left_apply`：aeval_X_left_apply (p : MvPolynomial σ 
R) : aeval X p = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compLocalizationAwayAlgHom_toAlgHom_toComp (x : P.Ring) :
    compLocalizationAwayAlgHom T g P (((localizationAway T g).toComp P).toAlgHom x) =
      algebraMap P.Ring _ x := by
  simp only [toComp_toAlgHom, compLocalizationAwayAlgHom, comp,
    localizationAway, AlgHom.toRingHom_eq_coe, aeval_rename,
    Sum.elim_comp_inr, ← IsScalarTower.toAlgHom_apply (R := R), ← comp_aeval_apply,
    aeval_X_left_apply]

@[simp]
/-
**Algebra.Generators.compLocalizationAwayAlgHom_X_inl** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.Generators`。
形式化陈述：compLocalizationAwayAlgHom_X_inl : compLocalizationAwayAlgHom T g P (X (Su
m.inl ())) = IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g
))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compLocalizationAwayAlgHom_X_inl : compLocalizationAwayAlgHom T g P (X (Sum.inl ())) =
      IsLocalization.Away.invSelf ((Ideal.Quotient.mk (P.ker ^ 2)) (P.σ g)) := by
  simp [compLocalizationAwayAlgHom]
/-
**Algebra.Generators.compLocalizationAwayAlgHom_relation_eq_zero** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：compLocalizationAwayAlgHom_relation_eq_zero : compLocalizationAwayAlgHom T
 g P (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Generators.toComp_toAlgHom`：toComp_toAlgHom (Q : Generators S T 
ι') (P : Generators R S ι) : (Q.toComp P).toAlgHom = rename Sum.inr
· 使用引理 `Algebra.Generators.compLocalizationAwayAlgHom_toAlgHom_toComp`：compLocal
izationAwayAlgHom_toAlgHom_toComp (x : P.Ring) : compLocalizationAwayAlgHom T g 
P (((localizationAway T g).toComp P).toAlgHom x) = …
· 使用引理 `Algebra.Generators.compLocalizationAwayAlgHom_X_inl`：compLocalizationAwa
yAlgHom_X_inl : compLocalizationAwayAlgHom T g P (X (Sum.inl ())) = IsLocalizati
on.Away.invSelf ((Ideal.Quotient.mk (P.ke…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.Away.mul_invSelf`：mul_invSelf : algebraMap R S x * invSel
f x = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma compLocalizationAwayAlgHom_relation_eq_zero :
    compLocalizationAwayAlgHom T g P (rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1) = 0 := by
  rw [map_sub, map_one, map_mul, ← toComp_toAlgHom (Generators.localizationAway T g) P]
  change (compLocalizationAwayAlgHom T g P)
    (((localizationAway T g).toComp P).toAlgHom _) * _ - _ = _
  rw [compLocalizationAwayAlgHom_toAlgHom_toComp, compLocalizationAwayAlgHom_X_inl,
    IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _)]
  simp
/-
**Algebra.Generators.sq_ker_comp_le_ker_compLocalizationAwayAlgHom** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：sq_ker_comp_le_ker_compLocalizationAwayAlgHom : ((localizationAway T g).co
mp P).ker ^ 2 <= RingHom.ker (compLocalizationAwayAlgHom T g P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `Algebra.Generators.compLocalizationAwayAlgHom_relation_eq_zero`：compLoca
lizationAwayAlgHom_relation_eq_zero : compLocalizationAwayAlgHom T g P (rename S
um.inr (P.σ g) * X (Sum.inl ()) - 1) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.Generators.comp_localizationAway_ker`：comp_localizationAway_ker 
(P : Generators R S ι) (f : P.Ring) (h : algebraMap P.Ring S f = g) : ((Generato
rs.localizationAway T g).comp P).k…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用引理 `Algebra.Generators.aeval_val_σ`：aeval_val_σ (s) : aeval P.val (P.σ s) = 
s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ideal.sup_mul`：sup_mul : (I ⊔ J) * K = I * K ⊔ J * K
· 使用定理 `Ideal.mul_sup`：mul_sup : I * (J ⊔ K) = I * J ⊔ I * K
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_mul`：∀ {S : Type v} {F : Type u_1} [inst : CommSemiring S] {R 
: Type u_2} [inst_1 : Semiring R] [inst_2 : FunLike F R S]   [RingHomClass F R S
] (…
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `Algebra.Generators.compLocalizationAwayAlgHom_toAlgHom_toComp`：compLocal
izationAwayAlgHom_toAlgHom_toComp (x : P.Ring) : compLocalizationAwayAlgHom T g 
P (((localizationAway T g).toComp P).toAlgHom x) = …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 36 条，此处仅展示前 30 条）
-/
lemma sq_ker_comp_le_ker_compLocalizationAwayAlgHom :
    ((localizationAway T g).comp P).ker ^ 2 ≤
      RingHom.ker (compLocalizationAwayAlgHom T g P) := by
  have hsple {x} (hx : x ∈ Ideal.span {(rename Sum.inr) (P.σ g) * X (Sum.inl ()) - 1}) :
        (compLocalizationAwayAlgHom T g P) x = 0 := by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, compLocalizationAwayAlgHom_relation_eq_zero, zero_mul]
  rw [comp_localizationAway_ker _ _ (P.σ g) (by simp), sq, Ideal.sup_mul, Ideal.mul_sup,
    Ideal.mul_sup]
  apply sup_le
  · apply sup_le
    · rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap, ← sq]
      intro x hx
      simp only [Ideal.mem_comap, RingHom.mem_ker,
        compLocalizationAwayAlgHom_toAlgHom_toComp (T := T) g P x]
      rw [IsScalarTower.algebraMap_apply P.Ring (P.Ring ⧸ P.ker ^ 2) (Localization.Away _),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hy]
  · apply sup_le <;>
    · rw [Ideal.mul_le]
      intro x hx y hy
      simp [hsple hx]

set_option backward.isDefEq.respectTransparency false in
/--
Let `R → S → T` be algebras such that `T` is the localization of `S` away from one
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`. Denote by `J` the kernel of the composition
`R[X,Y] → T`. Then `T ⊗[S] (I/I²) → J/J²` is injective.
-/
@[stacks 08JZ "part of (1)"]
/-
**Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway** 是 Mathlib 
中的一个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：liftBaseChange_injective_of_isLocalizationAway : Function.Injective (Linea
rMap.liftBaseChange T (Extension.Cotangent.map ((Generators.localizationAway T g
).toComp P).toExtensionHom))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `IsLocalizedModule.injective_of_map_zero`：injective_of_map_zero {M M' N :
 Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] (f : M ->ₗ
[R] M') [IsLocalizedModule S …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Generators.compLocalizationAwayAlgHom_toAlgHom_toComp`：compLocal
izationAwayAlgHom_toAlgHom_toComp (x : P.Ring) : compLocalizationAwayAlgHom T g 
P (((localizationAway T g).toComp P).toAlgHom x) = …
· 使用引理 `Algebra.Generators.sq_ker_comp_le_ker_compLocalizationAwayAlgHom`：sq_ker
_comp_le_ker_compLocalizationAwayAlgHom : ((localizationAway T g).comp P).ker ^ 
2 <= RingHom.ker (compLocalizationAwayAlgHom T g P)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.restrictScalars.congr_simp`：∀ (R : Type u_1) {S : Type u_5} {M
 : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_
2 : AddCommMonoid M] [inst…
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsLocalization.map_eq_zero_iff`：map_eq_zero_iff (r : R) : algebraMap R S
 r = 0 ↔ exists m : M, ↑m * r = 0
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsLocalizedModule.eq_zero_iff`：eq_zero_iff {m : M} : f m = 0 ↔ exists s'
 : S, s' • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用引理 `Algebra.Generators.aeval_val_σ`：aeval_val_σ (s) : aeval P.val (P.σ s) = 
s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R → S → T` be algebras such that `T` is the localization of `S` away from o
ne
element, where `S` is generated over `R` by `P` with kernel `I` and `Q` is the
canonical `S`-presentation of `T`. Denote by `J` the kernel of the composition
`R[X,Y] → T`. Then `T ⊗[S] (I/I²) → J/J²` is injective.
-/
lemma liftBaseChange_injective_of_isLocalizationAway :
    Function.Injective (LinearMap.liftBaseChange T
      (Extension.Cotangent.map
        ((Generators.localizationAway T g).toComp P).toExtensionHom)) := by
  set Q := Generators.localizationAway T g
  algebraize [((Generators.localizationAway T g).toComp P).toAlgHom.toRingHom]
  let f : P.Ring ⧸ P.ker ^ 2 := P.σ g
  let π := compLocalizationAwayAlgHom T g P
  refine IsLocalizedModule.injective_of_map_zero (Submonoid.powers g)
    (TensorProduct.mk S T P.toExtension.Cotangent 1) (fun x hx ↦ ?_)
  obtain ⟨x, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
  suffices h : algebraMap P.Ring (Localization.Away f) x.val = 0 by
    rw [IsScalarTower.algebraMap_apply _ (P.Ring ⧸ P.ker ^ 2) _,
      IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f)] at h
    obtain ⟨⟨m, ⟨n, rfl⟩⟩, hm⟩ := h
    rw [IsLocalizedModule.eq_zero_iff (Submonoid.powers g)]
    use ⟨g ^ n, n, rfl⟩
    dsimp [f] at hm
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
    simp only [Submonoid.smul_def]
    rw [show g = algebraMap P.Ring S (P.σ g) by simp, ← map_pow, algebraMap_smul, ← map_smul,
      Extension.Cotangent.mk_eq_zero_iff]
    simpa using! hm
  rw [← compLocalizationAwayAlgHom_toAlgHom_toComp (T := T)]
  apply sq_ker_comp_le_ker_compLocalizationAwayAlgHom
  simpa only [LinearEquiv.coe_coe, LinearMap.ringLmapEquivSelf_symm_apply,
    mk_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.coe_smulRight,
    Module.End.one_apply, LinearMap.smul_apply, one_smul, Algebra.Extension.Cotangent.map_mk,
    Extension.Cotangent.mk_eq_zero_iff] using! hx

/--
In the notation of the module docstring: Since `T` is standard smooth
of relative dimension one over `S`, `K/K²` is free of rank one generated
by the image of `g * X - 1`.
This is the section `K/K² → J/J²` defined by sending the image of `g * X - 1` to `x : J/J²`.
-/
/-
**Algebra.Generators.cotangentCompAwaySec** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Gen
erators`。
形式化陈述：cotangentCompAwaySec (x : ((localizationAway T g).comp P).toExtension.Cota
ngent) : (localizationAway T g).toExtension.Cotangent ->ₗ[T] ((localizationAway 
T g).comp P).toExtension.Cotangent
参数：x : ((localizationAway T g).comp P).toExtension.Cotangent。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the notation of the module docstring: Since `T` is standard smooth
of relative dimension one over `S`, `K/K²` is free of rank one generated
by the image of `g * X - 1`.
This is the section `K/K² → J/J²` defined by sending the image of `g * X - 1` to
 `x : J/J²`.
-/
noncomputable def cotangentCompAwaySec (x : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (localizationAway T g).toExtension.Cotangent →ₗ[T]
      ((localizationAway T g).comp P).toExtension.Cotangent :=
  (basisCotangentAway T g).constr T fun _ ↦ x

variable (x : ((localizationAway T g).comp P).toExtension.Cotangent)

/-- By construction, the section `cotangentCompAwaySec` sends `g * X - 1` to `x`. -/
/-
**Algebra.Generators.cotangentCompAwaySec_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
ra.Generators`。
形式化陈述：cotangentCompAwaySec_apply : cotangentCompAwaySec g P x (cMulXSubOneCotang
ent T g) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Generators.basisCotangentAway_apply`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   
[inst_3 : IsLocalization.Away r S…
· 使用定理 `Algebra.Generators.cotangentCompAwaySec.eq_1`：∀ {R : Type u_1} {S : Type
 u_2} {T : Type u_3} {ι : Type u_4} [inst : CommRing R] [inst_1 : CommRing S]   
[inst_2 : Algebra R S] [inst_3 : C…
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'

--- 原说明 ---
By construction, the section `cotangentCompAwaySec` sends `g * X - 1` to `x`.
-/
lemma cotangentCompAwaySec_apply :
    cotangentCompAwaySec g P x (cMulXSubOneCotangent T g) = x := by
  rw [← basisCotangentAway_apply _ (), cotangentCompAwaySec, Module.Basis.constr_basis]

variable {x}
  (hx : Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom x =
    cMulXSubOneCotangent T g)

include hx in
/-- The section `cotangentCompAwaySec` is indeed a section of the canonical map `J/J² → K/K²`. -/
/-
**Algebra.Generators.map_comp_cotangentCompAwaySec** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Generators`。
形式化陈述：map_comp_cotangentCompAwaySec : (Extension.Cotangent.map ((localizationAwa
y T g).ofComp P).toExtensionHom) ∘ₗ cotangentCompAwaySec g P x = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.Generators.basisCotangentAway_apply`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   
[inst_3 : IsLocalization.Away r S…
· 使用引理 `Algebra.Generators.cotangentCompAwaySec_apply`：cotangentCompAwaySec_appl
y : cotangentCompAwaySec g P x (cMulXSubOneCotangent T g) = x

--- 原说明 ---
The section `cotangentCompAwaySec` is indeed a section of the canonical map `J/J
² → K/K²`.
-/
lemma map_comp_cotangentCompAwaySec :
    (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom) ∘ₗ
      cotangentCompAwaySec g P x = .id := by
  refine (basisCotangentAway T g).ext fun r ↦ ?_
  simpa only [LinearMap.coe_comp, Function.comp_apply, basisCotangentAway_apply,
    cotangentCompAwaySec_apply]

/--
Let `S` be generated over `R` by `P : R[X] → S` with kernel `I` and let `T`
be the localization of `S` away from `g` generated over `S` by `S[Y] → T` with
kernel `K`.
Denote by `J` the kernel of the induced `R[X, Y] → T`. Then
`J/J² ≃ₗ[T] T ⊗[S] (I/I²) × (K/K²)`.

This is the splitting characterised by `x ↦ (0, g * X - 1)`.
-/
@[stacks 08JZ "(1)"]
noncomputable
/-
**Algebra.Generators.cotangentCompLocalizationAwayEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `Algebra.Generators`。
形式化陈述：cotangentCompLocalizationAwayEquiv : ((localizationAway T g).comp P).toExt
ension.Cotangent ≃ₗ[T] T otimes[S] P.toExtension.Cotangent × (Generators.localiz
ationAway T g).toExtension.Cotangent
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`：liftB
aseChange_injective_of_isLocalizationAway : Function.Injective (LinearMap.liftBa
seChange T (Extension.Cotangent.map ((Generators.locali…
· 使用引理 `Algebra.Generators.map_comp_cotangentCompAwaySec`：map_comp_cotangentComp
AwaySec : (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtension
Hom) ∘ₗ cotangentCompAwaySec g P x = .…
-/
def cotangentCompLocalizationAwayEquiv :
    ((localizationAway T g).comp P).toExtension.Cotangent ≃ₗ[T]
      T ⊗[S] P.toExtension.Cotangent × (Generators.localizationAway T g).toExtension.Cotangent :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).1

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_inr** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：cotangentCompLocalizationAwayEquiv_symm_inr : (cotangentCompLocalizationAw
ayEquiv g P hx).symm (0, cMulXSubOneCotangent T g) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Algebra.Generators.cotangentCompAwaySec_apply`：cotangentCompAwaySec_appl
y : cotangentCompAwaySec g P x (cMulXSubOneCotangent T g) = x
-/
lemma cotangentCompLocalizationAwayEquiv_symm_inr :
    (cotangentCompLocalizationAwayEquiv g P hx).symm
      (0, cMulXSubOneCotangent T g) = x := by
  simpa [cotangentCompLocalizationAwayEquiv, Function.Exact.splitSurjectiveEquiv] using
    cotangentCompAwaySec_apply g P x
/-
**Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_comp_inl** 是 Mathli
b 中的一个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：cotangentCompLocalizationAwayEquiv_symm_comp_inl : (cotangentCompLocalizat
ionAwayEquiv g P hx).symm.toLinearMap ∘ₗ .inl T (T otimes[S] P.toExtension.Cotan
gent) (localizationAway T g).toExtension.Cotangent = .liftBaseChange T (Extensio
n.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Generators.Cotangent.exact`：∀ {R : Type u₁} {S : Type u₂} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Type u₃}   [inst
_3 : CommRing T] [inst_4…
· 使用引理 `Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`：liftB
aseChange_injective_of_isLocalizationAway : Function.Injective (LinearMap.liftBa
seChange T (Extension.Cotangent.map ((Generators.locali…
· 使用引理 `Algebra.Generators.map_comp_cotangentCompAwaySec`：map_comp_cotangentComp
AwaySec : (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtension
Hom) ∘ₗ cotangentCompAwaySec g P x = .…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma cotangentCompLocalizationAwayEquiv_symm_comp_inl :
    (cotangentCompLocalizationAwayEquiv g P hx).symm.toLinearMap ∘ₗ
      .inl T (T ⊗[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent =
      .liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) :=
  ((Cotangent.exact (localizationAway g (S := T)) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x,
      map_comp_cotangentCompAwaySec g P hx⟩).2.left.symm

@[simp]
/-
**Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_inl** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：cotangentCompLocalizationAwayEquiv_symm_inl (a : T otimes[S] P.toExtension
.Cotangent) : (cotangentCompLocalizationAwayEquiv g P hx).symm (a, 0) = LinearMa
p.liftBaseChange T (Extension.Cotangent.map ((localizationAway T g).toComp P).to
ExtensionHom) a
参数：a : T otimes[S] P.toExtension.Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Generators.cotangentCompLocalizationAwayEquiv_symm_comp_inl`：cot
angentCompLocalizationAwayEquiv_symm_comp_inl : (cotangentCompLocalizationAwayEq
uiv g P hx).symm.toLinearMap ∘ₗ .inl T (T otimes[S] P.toE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentCompLocalizationAwayEquiv_symm_inl (a : T ⊗[S] P.toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx).symm (a, 0) = LinearMap.liftBaseChange T
        (Extension.Cotangent.map ((localizationAway T g).toComp P).toExtensionHom) a := by
  simp [← cotangentCompLocalizationAwayEquiv_symm_comp_inl g P hx]
/-
**Algebra.Generators.snd_comp_cotangentCompLocalizationAwayEquiv** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators`。
形式化陈述：snd_comp_cotangentCompLocalizationAwayEquiv : LinearMap.snd T (T otimes[S]
 P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent ∘ₗ (cotan
gentCompLocalizationAwayEquiv g P hx).toLinearMap = Extension.Cotangent.map ((lo
calizationAway T g).ofComp P).toExtensionHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Generators.Cotangent.exact`：∀ {R : Type u₁} {S : Type u₂} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {T : Type u₃}   [inst
_3 : CommRing T] [inst_4…
· 使用引理 `Algebra.Generators.liftBaseChange_injective_of_isLocalizationAway`：liftB
aseChange_injective_of_isLocalizationAway : Function.Injective (LinearMap.liftBa
seChange T (Extension.Cotangent.map ((Generators.locali…
· 使用引理 `Algebra.Generators.map_comp_cotangentCompAwaySec`：map_comp_cotangentComp
AwaySec : (Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtension
Hom) ∘ₗ cotangentCompAwaySec g P x = .…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma snd_comp_cotangentCompLocalizationAwayEquiv :
    LinearMap.snd T (T ⊗[S] P.toExtension.Cotangent) (localizationAway T g).toExtension.Cotangent ∘ₗ
      (cotangentCompLocalizationAwayEquiv g P hx).toLinearMap =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom :=
  ((Cotangent.exact (localizationAway T g) P).splitSurjectiveEquiv
    (liftBaseChange_injective_of_isLocalizationAway _ P)
    ⟨cotangentCompAwaySec g P x, map_comp_cotangentCompAwaySec g P hx⟩).2.right.symm

@[simp]
/-
**Algebra.Generators.snd_cotangentCompLocalizationAwayEquiv** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.Generators`。
形式化陈述：snd_cotangentCompLocalizationAwayEquiv (a : ((localizationAway T g).comp P
).toExtension.Cotangent) : (cotangentCompLocalizationAwayEquiv g P hx a).2 = Ext
ension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom a
参数：a : ((localizationAway T g).comp P).toExtension.Cotangent。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Generators.snd_comp_cotangentCompLocalizationAwayEquiv`：snd_comp
_cotangentCompLocalizationAwayEquiv : LinearMap.snd T (T otimes[S] P.toExtension
.Cotangent) (localizationAway T g).toExtension.Cotan…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_cotangentCompLocalizationAwayEquiv
    (a : ((localizationAway T g).comp P).toExtension.Cotangent) :
    (cotangentCompLocalizationAwayEquiv g P hx a).2 =
      Extension.Cotangent.map ((localizationAway T g).ofComp P).toExtensionHom a := by
  simp [← snd_comp_cotangentCompLocalizationAwayEquiv g P hx]

end Algebra.Generators

