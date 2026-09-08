/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Epimorphisms in `CommRingCat`

## Main results
- `RingHom.surjective_iff_epi_and_finite`: surjective <=> epi + finite
-/

public section

open CategoryTheory TensorProduct

universe u

/-
**CommRingCat.epi_iff_epi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.epi_iff_epi {R S : Type u} [CommRing R] [CommRing S] [Algebra 
R S] : Epi (CommRingCat.ofHom (algebraMap R S)) ↔ Algebra.IsEpi R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Epi.left_cancellation`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Epi f] {Z : 
C}   (g h : Y ⟶ Z), Catego…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma CommRingCat.epi_iff_epi {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Epi (CommRingCat.ofHom (algebraMap R S)) ↔ Algebra.IsEpi R S := by
  simp_rw [Algebra.isEpi_iff_forall_one_tmul_eq, eq_comm]
  constructor
  · intro H
    have := H.1 (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom <| (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom)
      (by ext r; change algebraMap R S r ⊗ₜ 1 = 1 ⊗ₜ algebraMap R S r;
          simp only [Algebra.algebraMap_eq_smul_one, smul_tmul])
    exact RingHom.congr_fun (congrArg Hom.hom this)
  · refine fun H ↦ ⟨fun {T} f g e ↦ ?_⟩
    let : Algebra R T := (ofHom (algebraMap R S) ≫ g).hom.toAlgebra
    let f' : S →ₐ[R] T := ⟨f.hom, RingHom.congr_fun (congrArg Hom.hom e)⟩
    let g' : S →ₐ[R] T := ⟨g.hom, fun _ ↦ rfl⟩
    ext s
    simpa using! congr(Algebra.TensorProduct.lift f' g' (fun _ _ ↦ .all _ _) $(H s))

@[deprecated (since := "2026-01-13")]
alias CommRingCat.epi_iff_tmul_eq_tmul := CommRingCat.epi_iff_epi
/-
**RingHom.surjective_of_epi_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [Epi f
] (h₂ : RingHom.Finite f.hom) : Function.Surjective f
参数：f : R ⟶ S；h₂ : RingHom.Finite f.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CommRingCat.epi_iff_epi`：CommRingCat.epi_iff_epi {R S : Type u} [CommRin
g R] [CommRing S] [Algebra R S] : Epi (CommRingCat.ofHom (algebraMap R S)) ↔ Alg
ebra.IsEpi R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isEpi_iff_surjective_algebraMap_of_finite`：isEpi_iff_surjective_
algebraMap_of_finite [Module.Finite R A] : Algebra.IsEpi R A ↔ Surjective (algeb
raMap R A)
-/
lemma RingHom.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [Epi f]
    (h₂ : RingHom.Finite f.hom) : Function.Surjective f := by
  algebraize [f.hom]
  have : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp <| inferInstanceAs (Epi f)
  rwa [Algebra.isEpi_iff_surjective_algebraMap_of_finite] at this
/-
**RingHom.surjective_iff_epi_and_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.surjective_iff_epi_and_finite {R S : CommRingCat} {f : R ⟶ S} : Fu
nction.Surjective f ↔ Epi f ∧ RingHom.Finite f.hom where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
· 使用定理 `RingHom.Finite.of_surjective`：of_surjective (f : A ->+* B) (hf : Surject
ive f) : f.Finite
· 使用引理 `RingHom.surjective_of_epi_of_finite`：RingHom.surjective_of_epi_of_finite
 {R S : CommRingCat} (f : R ⟶ S) [Epi f] (h₂ : RingHom.Finite f.hom) : Function.
Surjective f
-/
lemma RingHom.surjective_iff_epi_and_finite {R S : CommRingCat} {f : R ⟶ S} :
    Function.Surjective f ↔ Epi f ∧ RingHom.Finite f.hom where
  mp h := ⟨ConcreteCategory.epi_of_surjective f h, .of_surjective f.hom h⟩
  mpr := fun ⟨_, h⟩ ↦ surjective_of_epi_of_finite f h
