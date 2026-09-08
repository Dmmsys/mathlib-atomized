/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Unramified.Basic

/-!

# Smooth morphisms

An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
An `R`-algebra `A` is smooth if it is formally smooth and of finite presentation.

We show that the property of being formally smooth extends onto nilpotent ideals,
and that it is stable under `R`-algebra homomorphisms and compositions.

We show that smooth is stable under algebra isomorphisms, composition and
localization at an element.

## Main results
- `Algebra.FormallySmooth`: The class of formally smooth algebras.
- `Algebra.formallySmooth_iff` :
  Formally smooth iff `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
- `Algebra.FormallySmooth.lift`: If `A` is formally smooth and `I` is nilpotent,
  any map `A →ₐ[R] B ⧸ I` lifts to `A →ₐ[R] B`.
- `Algebra.FormallySmooth.iff_comp_surjective`: `A` is formally smooth iff
  any map `A →ₐ[R] B ⧸ I` lifts to `A →ₐ[R] B` for any square zero `I`.

Suppose `P` is a formally smooth `R` algebra that surjects onto `A` with kernel `I`, then
- `Algebra.FormallySmooth.iff_split_surjection`: `A` is formally smooth iff
  the algebra map `P ⧸ I² →ₐ[R] A` has an `R`-algebra section.
- `Algebra.Extension.equivH1CotangentOfFormallySmooth`:
  `H¹(L_{A/R})` is isomorphic to `ker(I/I² → A ⊗[P] Ω[P⁄R])`.
- `Algebra.FormallySmooth.iff_split_injection`: `A` is formally smooth iff
  the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split injective.

-/

@[expose] public section

open scoped TensorProduct
open Algebra.Extension KaehlerDifferential MvPolynomial

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {B P C : Type*} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing P] [Algebra R P]
namespace Algebra

section

variable (R A) in
/--
An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
For the infinitesimal lifting definition,
see `FormallySmooth.lift` and `FormallySmooth.iff_comp_surjective`.
-/
@[stacks 00TI "Also see 031J (6) for the equivalence with the definition given here.", mk_iff]
/-
**Algebra.FormallySmooth** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (A : Type v) → [inst : CommRing R] → [inst_1 : CommRing A] 
→ [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A
/R}) = 0`.
For the infinitesimal lifting definition,
see `FormallySmooth.lift` and `FormallySmooth.iff_comp_surjective`.
-/
class FormallySmooth : Prop where
  projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance] FormallySmooth.projective_kaehlerDifferential
  FormallySmooth.subsingleton_h1Cotangent

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-
**Algebra.FormallySmooth.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Form
allySmooth`。
形式化陈述：∀ (R : Type u) (A : Type v) [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] {B : Type u_1}   [inst_3 : CommRing B] [inst_4 : Algebra R B]
 [Algebra.FormallySmooth R A] (I : Ideal B),   I ^ 2 = ⊥ → Function.Surjective (
Ideal.Quotient.mkₐ R I).comp
参数：R : Type u；A : Type v；I : Ideal B；Ideal.Quotient.mkₐ R I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `Algebra.FormallySmooth.subsingleton_h1Cotangent`：∀ {R : Type u} {A : Typ
e v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : 
Algebra.FormallySmooth R A], Subsingl…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Function.Exact.split_tfae'`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_
4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommGroup M]   [inst_2 : AddC
ommGroup N] [ins…
· 使用引理 `Algebra.Extension.exact_cotangentComplex_toKaehler`：exact_cotangentCompl
ex_toKaehler : Function.Exact P.cotangentComplex P.toKaehler
· 使用引理 `Algebra.Extension.subsingleton_h1Cotangent`：subsingleton_h1Cotangent (P 
: Extension R S) : Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentCo
mplex
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Algebra.FormallySmooth.projective_kaehlerDifferential`：∀ {R : Type u} {A
 : Type v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [s
elf : Algebra.FormallySmooth R A], Module.P…
· 使用引理 `Algebra.Extension.toKaehler_surjective`：toKaehler_surjective : Function.
Surjective P.toKaehler
· 使用定理 `Algebra.Generators.instIsScalarTowerRing`：∀ {R : Type u} {S : Type v} {ι
 : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : Algebra.Generators R S ι) {…
· 使用引理 `Algebra.Generators.algebraMap_surjective`：algebraMap_surjective : Functi
on.Surjective (algebraMap P.Ring S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Algebra.Extension.Cotangent.val_smul'`：∀ {R : Type u} {S : Type v} [inst
 : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensi
on R S}   (r : P.Ring) (x :…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
（共 56 条，此处仅展示前 30 条）
-/
lemma FormallySmooth.comp_surjective [FormallySmooth R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  intro f
  let P : Algebra.Generators R A A := Generators.self R A
  have hP : Function.Injective P.toExtension.cotangentComplex := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    exact FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨l, hl⟩ := ((P.toExtension.exact_cotangentComplex_toKaehler.split_tfae'.out 0 1 rfl rfl).mp
    ⟨P.toExtension.subsingleton_h1Cotangent.mp FormallySmooth.subsingleton_h1Cotangent,
      Module.projective_lifting_property _ _ P.toExtension.toKaehler_surjective⟩).2
  obtain ⟨g, hg⟩ := retractionKerCotangentToTensorEquivSection (R := R) P.algebraMap_surjective
    ⟨⟨⟨Cotangent.val, by simp⟩, by simpa using! Cotangent.val_smul' (P := P.toExtension)⟩ ∘ₗ
      l.restrictScalars P.toExtension.Ring, LinearMap.ext fun x ↦ congr($hl x)⟩
  let σ := Function.surjInv (f := algebraMap B (B ⧸ I)) Ideal.Quotient.mk_surjective
  have H (x : P.Ring) : ↑(aeval (σ ∘ f) x) = f (algebraMap _ A x) := by
    rw [← Ideal.Quotient.algebraMap_eq, ← aeval_algebraMap_apply, P.algebraMap_eq,
      AlgHom.coe_toRingHom, comp_aeval_apply, ← Function.comp_assoc, Function.comp_surjInv,]
    simp [P]
  let l : P.Ring ⧸ (RingHom.ker (algebraMap P.Ring A)) ^ 2 →ₐ[R] B :=
    Ideal.Quotient.liftₐ _ (aeval (σ ∘ f)) <|
      have : RingHom.ker (algebraMap P.Ring A) ≤ I.comap (aeval (σ ∘ f)).toRingHom := fun x hx ↦ by
        simp_all [← Ideal.Quotient.eq_zero_iff_mem (I := I), -map_aeval]
      show RingHom.ker _ ^ 2 ≤ RingHom.ker _ from
        (Ideal.pow_right_mono this 2).trans ((Ideal.le_comap_pow _ _).trans_eq (hI ▸ rfl))
  have : f.comp (IsScalarTower.toAlgHom R P.Ring A).kerSquareLift =
      (Ideal.Quotient.mkₐ R _).comp l := by
    refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
    change f (algebraMap P.Ring A (.X i)) = algebraMap _ _ (MvPolynomial.aeval (σ ∘ f) (.X i))
    simpa using! (Function.surjInv_eq _ _).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
/-
**Algebra.instFormallySmoothMvPolynomial** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：instFormallySmoothMvPolynomial (σ : Type*) : FormallySmooth R (MvPolynomia
l σ R)
参数：σ : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用引理 `Algebra.Generators.ker_mvPolynomial`：ker_mvPolynomial : (mvPolynomial R 
ι).ker = ⊥
· 使用定理 `Function.Surjective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} [Subsingleton α], Function.Surjective f → Subsingleton β
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Algebra.Extension.h1Cotangentι_injective`：h1Cotangentι_injective : Funct
ion.Injective P.h1Cotangentι
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `instFreeMvPolynomialKaehlerDifferential`：∀ (R : Type u) [inst : CommRing
 R] (σ : Type u_1), Module.Free (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R]
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
-/
instance instFormallySmoothMvPolynomial (σ : Type*) : FormallySmooth R (MvPolynomial σ R) := by
  let P := Generators.mvPolynomial R σ
  have : Subsingleton ↥P.toExtension.ker :=
    Submodule.subsingleton_iff_eq_bot.mpr Generators.ker_mvPolynomial
  have : Subsingleton P.toExtension.Cotangent := Cotangent.mk_surjective.subsingleton
  have := P.toExtension.h1Cotangentι_injective.subsingleton
  exact ⟨inferInstance, P.equivH1Cotangent.symm.subsingleton⟩

@[deprecated (since := "2026-05-22")] alias mvPolynomial := instFormallySmoothMvPolynomial

end

namespace FormallySmooth

/-
**Algebra.FormallySmooth.exists_lift** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Formally
Smooth`。
形式化陈述：exists_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A
 ->ₐ[R] B ⧸ I) : exists f : A ->ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g
参数：I : Ideal B；hI : IsNilpotent I；g : A ->ₐ[R] B ⧸ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsNilpotent.induction_on`：Ideal.IsNilpotent.induction_on (hI : IsN
ilpotent I) {P : forall ⦃S : Type _⦄ [CommRing S], Ideal S -> Prop} (h₁ : forall
 ⦃S : Type _⦄ [CommR…
· 使用定理 `Algebra.FormallySmooth.comp_surjective`：∀ (R : Type u) (A : Type v) [ins
t : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_1}   [i
nst_3 : CommRing B] [inst_4 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
· 使用定理 `AlgHom.id_comp`：id_comp : (AlgHom.id R B).comp φ = φ
-/
theorem exists_lift
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective R A I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.toAlgHom.comp g)
    obtain ⟨g', rfl⟩ := h₁ g'
    replace e := congr_arg this.toAlgHom.comp e
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.id_comp]
    exact ⟨g', e⟩

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` square-zero,
this is an arbitrary lift `A →ₐ[R] B`. -/
/-
**Algebra.FormallySmooth.lift** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.FormallySmooth`
。
形式化陈述：lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A ->ₐ[R]
 B ⧸ I) : A ->ₐ[R] B
参数：I : Ideal B；hI : IsNilpotent I；g : A ->ₐ[R] B ⧸ I。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.exists_lift`：exists_lift [FormallySmooth R A] (I 
: Ideal B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) : exists f : A ->ₐ[R] B, (I
deal.Quotient.mkₐ R I).c…

--- 原说明 ---
For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` squ
are-zero,
this is an arbitrary lift `A →ₐ[R] B`.
-/
noncomputable def lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : A →ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).choose

@[simp]
/-
**Algebra.FormallySmooth.comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySm
ooth`。
形式化陈述：comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A -
>ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g
参数：I : Ideal B；hI : IsNilpotent I；g : A ->ₐ[R] B ⧸ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.exists_lift`：exists_lift [FormallySmooth R A] (I 
: Ideal B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) : exists f : A ->ₐ[R] B, (I
deal.Quotient.mkₐ R I).c…
-/
theorem comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).choose_spec

@[simp]
/-
**Algebra.FormallySmooth.mk_lift** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmoo
th`。
形式化陈述：mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A ->ₐ
[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x
参数：I : Ideal B；hI : IsNilpotent I；g : A ->ₐ[R] B ⧸ I；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.comp_lift`：comp_lift [FormallySmooth R A] (I : Id
eal B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp
 (FormallySmooth.lift …
-/
theorem mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A →ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g :) x

variable {C : Type*} [CommRing C] [Algebra R C]

/-- For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nilpotent,
this is an arbitrary lift `A →ₐ[R] B`. -/
/-
**Algebra.FormallySmooth.liftOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.For
mallySmooth`。
形式化陈述：liftOfSurjective [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (h
g : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B ->+* C)) : A
 ->ₐ[R] B
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；hg : Function.Surjective g；hg' : IsNilpotent <|
 RingHom.ker (g : B ->+* C)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a formally smooth `R`-algebra `A` and a map `f : A →ₐ[R] B ⧸ I` with `I` nil
potent,
this is an arbitrary lift `A →ₐ[R] B`.
-/
noncomputable def liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C)
    (g : B →ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    A →ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.FormallySmooth.liftOfSurjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.FormallySmooth`。
形式化陈述：liftOfSurjective_apply [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R]
 C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker g) (x : A) : 
g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；hg : Function.Surjective g；hg' : IsNilpotent <|
 RingHom.ker g；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Algebra.FormallySmooth.mk_lift`：mk_lift [FormallySmooth R A] (I : Ideal 
B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (Form
allySmooth.lift I hI…
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Ideal.quotientKerAlgEquivOfSurjective_apply`：∀ {R₁ : Type u_1} {A : Type
 u_3} {B : Type u_4} [inst : CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebr
a R₁ A]   [inst_3 : Semiring B] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHom.kerLift_mk`：kerLift_mk (r : R) : kerLift f (Ideal.Quotient.mk (k
er f) r) = f r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftOfSurjective_apply [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker g) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  conv_rhs => rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    ← FormallySmooth.mk_lift (A := A) _ hg']
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  rw [AlgEquiv.apply_symm_apply, Ideal.quotientKerAlgEquivOfSurjective_apply]
  simp only [liftOfSurjective, ← RingHom.ker_coe_toRingHom g, RingHom.kerLift_mk, RingHom.coe_coe]

@[simp]
/-
**Algebra.FormallySmooth.comp_liftOfSurjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.FormallySmooth`。
形式化陈述：comp_liftOfSurjective [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] 
C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B ->+* C)
) : g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f
参数：f : A ->ₐ[R] C；g : B ->ₐ[R] C；hg : Function.Surjective g；hg' : IsNilpotent <|
 RingHom.ker (g : B ->+* C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Algebra.FormallySmooth.liftOfSurjective_apply`：liftOfSurjective_apply [F
ormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C) (hg : Function.Surjective g
) (hg' : IsNilpotent <| RingHom.ker…
-/
theorem comp_liftOfSurjective [FormallySmooth R A] (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B →+* C)) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')
/-
**Algebra.FormallySmooth.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssFiniteType R A] [FormallySmooth R A] : Module.FinitePresentation A Ω[A⁄R] :=
  Module.finitePresentation_of_projective A Ω[A⁄R]

end FormallySmooth

namespace Extension

set_option backward.isDefEq.respectTransparency false in
/--
Given extensions `0 → I₁ → P₁ → A → 0` and `0 → I₂ → P₂ → A → 0` with `P₁` formally smooth,
this is an arbitrarily chosen map `P₁/I₁² → P₂/I₂²` of extensions.
-/
noncomputable
/-
**Algebra.Extension.homInfinitesimal** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extensio
n`。
形式化陈述：homInfinitesimal (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring] : P₁.i
nfinitesimal.Hom P₂.infinitesimal
参数：P₁ P₂ : Extension R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def homInfinitesimal (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring] :
    P₁.infinitesimal.Hom P₂.infinitesimal :=
  letI lift : P₁.Ring →ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring A)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; exact Ideal.cotangentIdeal_square _⟩
  { toRingHom := (Ideal.Quotient.liftₐ (P₁.ker ^ 2) lift (by
        change P₁.ker ^ 2 ≤ RingHom.ker lift
        rw [pow_two, Ideal.mul_le]
        have : ∀ r ∈ P₁.ker, lift r ∈ P₂.infinitesimal.ker :=
          fun r hr ↦ (FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ r).trans hr
        intro r hr s hs
        rw [RingHom.mem_ker, map_mul, ← Ideal.mem_bot, ← P₂.ker.cotangentIdeal_square,
          ← ker_infinitesimal, pow_two]
        exact Ideal.mul_mem_mul (this r hr) (this s hs))).toRingHom
    toRingHom_algebraMap := by simp
    algebraMap_toRingHom x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ x }

/-- Formally smooth extensions have isomorphic `H¹(L_P)`. -/
noncomputable
/-
**Algebra.Extension.H1Cotangent.equivOfFormallySmooth** 是 Mathlib 中的一个定义，位于命名空间 
`Algebra.Extension.H1Cotangent`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing A] →         [inst_2 : Algebra R A] →           (P₁ : Algebra.Extension
 R A) →             (P₂ : Algebra.Extension R A) →               [Algebra.Formal
lySmooth R P₁.Ring] →                 [Algebra.FormallySmooth R P₂.Ring] → P₁.H1
Cotangent ≃ₗ[A] P₂.H1Cotangent
参数：P₁ : Algebra.Extension R A；P₂ : Algebra.Extension R A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.H1Cotangent.map_toInfinitesimal_bijective`：∀ {R : Type
 u_1} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra
 R S]   (P : Algebra.Extension R S), Function.Bij…
-/
def H1Cotangent.equivOfFormallySmooth (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    P₁.H1Cotangent ≃ₗ[A] P₂.H1Cotangent :=
  .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))
/-
**Algebra.Extension.H1Cotangent.equivOfFormallySmooth_toLinearMap** 是 Mathlib 中的
一个定理，位于命名空间 `Algebra.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A]   {P₁ : Algebra.Extension R A} {P₂ : Algebra.Extension R A} (
f : P₁.Hom P₂) [inst_3 : Algebra.FormallySmooth R P₁.Ring]   [inst_4 : Algebra.F
ormallySmooth R P₂.Ring],   ↑(Algebra.Extension.H1Cotangent.equivOfFormallySmoot
h P₁ P₂) = Algebra.Extension.H1Cotangent.map f
参数：f : P₁.Hom P₂；Algebra.Extension.H1Cotangent.equivOfFormallySmooth P₁ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.Extension.H1Cotangent.map_toInfinitesimal_bijective`：∀ {R : Type
 u_1} {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra
 R S]   (P : Algebra.Extension R S), Function.Bij…
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Extension.H1Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.Extension.H1Cotangent.map_eq`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u'} {S…
-/
lemma H1Cotangent.equivOfFormallySmooth_toLinearMap {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (H1Cotangent.equivOfFormallySmooth P₁ P₂).toLinearMap = map f := by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars A ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars A ∘ₗ map f) x
  rw [← map_comp, ← map_comp, map_eq]
/-
**Algebra.Extension.H1Cotangent.equivOfFormallySmooth_apply** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A]   {P₁ : Algebra.Extension R A} {P₂ : Algebra.Extension R A} (
f : P₁.Hom P₂) [inst_3 : Algebra.FormallySmooth R P₁.Ring]   [inst_4 : Algebra.F
ormallySmooth R P₂.Ring] (x : P₁.H1Cotangent),   (Algebra.Extension.H1Cotangent.
equivOfFormallySmooth P₁ P₂) x = (Algebra.Extension.H1Cotangent.map f) x
参数：f : P₁.Hom P₂；x : P₁.H1Cotangent；Algebra.Extension.H1Cotangent.equivOfFormall
ySmooth P₁ P₂；Algebra.Extension.H1Cotangent.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Extension.H1Cotangent.equivOfFormallySmooth_toLinearMap`：∀ {R : 
Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra
 R A]   {P₁ : Algebra.Extension R A} {P₂ : Algebra.Ex…
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
-/
lemma H1Cotangent.equivOfFormallySmooth_apply {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] (x) :
    H1Cotangent.equivOfFormallySmooth P₁ P₂ x = map f x := by
  rw [← equivOfFormallySmooth_toLinearMap, LinearEquiv.coe_coe]
/-
**Algebra.Extension.H1Cotangent.equivOfFormallySmooth_symm** 是 Mathlib 中的一个定理，位于
命名空间 `Algebra.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A]   (P₁ : Algebra.Extension R A) (P₂ : Algebra.Extension R A) [
inst_3 : Algebra.FormallySmooth R P₁.Ring]   [inst_4 : Algebra.FormallySmooth R 
P₂.Ring],   (Algebra.Extension.H1Cotangent.equivOfFormallySmooth P₁ P₂).symm =  
   Algebra.Extension.H1Cotangent.equivOfFormallySmooth P₂ P₁
参数：P₁ : Algebra.Extension R A；P₂ : Algebra.Extension R A；Algebra.Extension.H1Cot
angent.equivOfFormallySmooth P₁ P₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma H1Cotangent.equivOfFormallySmooth_symm (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (equivOfFormallySmooth P₁ P₂).symm = equivOfFormallySmooth P₂ P₁ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any formally smooth extension can be used to calculate `H¹(L_{A/R})`. -/
noncomputable
/-
**Algebra.Extension.equivH1CotangentOfFormallySmooth** 是 Mathlib 中的一个定义，位于命名空间 `
Algebra.Extension`。
形式化陈述：equivH1CotangentOfFormallySmooth (P : Extension R A) [FormallySmooth R P.R
ing] : P.H1Cotangent ≃ₗ[A] H1Cotangent R A
参数：P : Extension R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivH1CotangentOfFormallySmooth (P : Extension R A) [FormallySmooth R P.Ring] :
    P.H1Cotangent ≃ₗ[A] H1Cotangent R A :=
  haveI : FormallySmooth R (Generators.self R A).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _
/-
**Algebra.Extension.cotangentComplex_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Extension`。
形式化陈述：cotangentComplex_injective_iff (P : Extension R A) [FormallySmooth R P.Rin
g] : Function.Injective P.cotangentComplex ↔ Subsingleton (Algebra.H1Cotangent R
 A)
参数：P : Extension R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Extension.subsingleton_h1Cotangent`：subsingleton_h1Cotangent (P 
: Extension R S) : Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentCo
mplex
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma cotangentComplex_injective_iff
    (P : Extension R A) [FormallySmooth R P.Ring] :
    Function.Injective P.cotangentComplex ↔ Subsingleton (Algebra.H1Cotangent R A) := by
  rw [← Algebra.Extension.subsingleton_h1Cotangent,
    P.equivH1CotangentOfFormallySmooth.subsingleton_congr]

end Algebra.Extension

namespace Algebra.FormallySmooth

section iff_split

variable [Algebra.FormallySmooth R P]

/-
**Algebra.FormallySmooth.kerCotangentToTensor_injective_iff** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.FormallySmooth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] {P : Type u_2}   [inst_3 : CommRing P] [inst_4 : Algebra R P]
 [Algebra.FormallySmooth R P] [inst_6 : Algebra P A]   [IsScalarTower R P A],   
Function.Surjective ⇑(algebraMap P A) →     (Function.Injective ⇑(KaehlerDiffere
ntial.kerCotangentToTensor R P A) ↔ Subsingleton (Algebra.H1Cotangent R A))
参数：algebraMap P A；Function.Injective ⇑(KaehlerDifferential.kerCotangentToTensor 
R P A) ↔ Subsingleton (Algebra.H1Cotangent R A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用引理 `Algebra.Extension.cotangentComplex_injective_iff`：cotangentComplex_injec
tive_iff (P : Extension R A) [FormallySmooth R P.Ring] : Function.Injective P.co
tangentComplex ↔ Subsingleton (Algebra…
-/
lemma kerCotangentToTensor_injective_iff
    [Algebra P A] [IsScalarTower R P A] (hf : Function.Surjective (algebraMap P A)) :
    Function.Injective (kerCotangentToTensor R P A) ↔ Subsingleton (Algebra.H1Cotangent R A) :=
  let P' : Algebra.Extension R A := ⟨P, _, Function.surjInv_eq hf⟩
  have : Algebra.FormallySmooth R P'.Ring := ‹_›
  P'.cotangentComplex_injective_iff

/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] A`
with kernel `I` (typically a presentation `R[X] → A`),
`A` is formally smooth iff the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split injective.
Also see `Algebra.Extension.formallySmooth_iff_split_injection`
for the version in terms of `Extension`.
-/
@[stacks 031I]
/-
**Algebra.FormallySmooth.iff_split_injection** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
FormallySmooth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] {P : Type u_2}   [inst_3 : CommRing P] [inst_4 : Algebra R P]
 [Algebra.FormallySmooth R P] [inst_6 : Algebra P A]   [IsScalarTower R P A],   
Function.Surjective ⇑(algebraMap P A) →     (Algebra.FormallySmooth R A ↔ ∃ l, l
 ∘ₗ KaehlerDifferential.kerCotangentToTensor R P A = LinearMap.id)
参数：algebraMap P A；Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ KaehlerDifferential.ker
CotangentToTensor R P A = LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.formallySmooth_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing
 R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallySmooth R A ↔
 Module.Projecti…
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Module.Projective.iff_split_of_projective`：∀ {R : Type u_1} [inst : Semi
ring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]  
 {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.tensorProduct`：∀ {R : Type u} [inst : Semiring R] {R₀ 
: Type u_2} {M : Type u_1} {N : Type u_3} [inst_1 : CommSemiring R₀]   [inst_2 :
 Algebra R₀ R] [inst_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Algebra.FormallySmooth.projective_kaehlerDifferential`：∀ {R : Type u} {A
 : Type v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [s
elf : Algebra.FormallySmooth R A], Module.P…
· 使用引理 `KaehlerDifferential.mapBaseChange_surjective`：KaehlerDifferential.mapBas
eChange_surjective (h : Function.Surjective (algebraMap A B)) : Function.Surject
ive (KaehlerDifferential.mapBaseCh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.FormallySmooth.kerCotangentToTensor_injective_iff`：∀ {R : Type u
} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] 
{P : Type u_2}   [inst_3 : CommRing P] [inst_4 …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Equiv.exists_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∃ a, q (e a)) ↔ ∃ b, q b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Function.Exact.split_tfae'`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_
4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommGroup M]   [inst_2 : AddC
ommGroup N] [ins…
· 使用定理 `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`：KaehlerDif
ferential.exact_kerCotangentToTensor_mapBaseChange (h : Function.Surjective (alg
ebraMap A B)) : Function.Exact (kerCotangentToTens…

--- 原说明 ---
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f
 : P →ₐ[R] A`
with kernel `I` (typically a presentation `R[X] → A`),
`A` is formally smooth iff the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split in
jective.
Also see `Algebra.Extension.formallySmooth_iff_split_injection`
for the version in terms of `Extension`.
-/
theorem iff_split_injection
    [Algebra P A] [IsScalarTower R P A] (hf : Function.Surjective (algebraMap P A)) :
    Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ (kerCotangentToTensor R P A) = LinearMap.id := by
  rw [formallySmooth_iff, and_comm,
    Module.Projective.iff_split_of_projective (KaehlerDifferential.mapBaseChange R P A)
      (mapBaseChange_surjective R P A hf), ← kerCotangentToTensor_injective_iff hf]
  convert!
    (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfae' (g :=
          (KaehlerDifferential.mapBaseChange R P A).restrictScalars P)).out
      0 1) using 2
  · rw [← (LinearMap.extendScalarsOfSurjectiveEquiv hf).exists_congr_right]
    simp [LinearMap.ext_iff]
  · rw [and_iff_right (by exact mapBaseChange_surjective R P A hf)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
-/
@[stacks 031I]
/-
**Algebra.FormallySmooth._root_.Algebra.Extension.formallySmooth_iff_split_injec
tion** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f
 : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split in
jective.
-/
theorem _root_.Algebra.Extension.formallySmooth_iff_split_injection
    (P : Algebra.Extension.{w} R A) [FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id := by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMap_surjective,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩
  · intro ⟨l, hl⟩
    exact ⟨e.symm.toLinearMap ∘ₗ l.restrictScalars P.Ring,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩

/-- Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-algebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside `Spec P` admits
a retraction. -/
/-
**Algebra.FormallySmooth.iff_split_surjection** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.FormallySmooth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] {P : Type u_2}   [inst_3 : CommRing P] [inst_4 : Algebra R P]
 [Algebra.FormallySmooth R P] (f : P →ₐ[R] A),   Function.Surjective ⇑f → (Algeb
ra.FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A)
参数：f : P →ₐ[R] A；Algebra.FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgH
om.id R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallySmooth.iff_split_injection`：∀ {R : Type u} {A : Type v} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2} 
  [inst_3 : CommRing P] [inst_4 …
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let `P →ₐ[R] A` be a surjection with kernel `J`, and `P` a formally smooth `R`-a
lgebra,
then `A` is formally smooth over `R` iff the surjection `P ⧸ J ^ 2 →ₐ[R] A` has 
a section.

Geometric intuition: we require that a first-order thickening of `Spec A` inside
 `Spec P` admits
a retraction.
-/
theorem iff_split_surjection (f : P →ₐ[R] A) (hf : Function.Surjective f) :
    FormallySmooth R A ↔ ∃ g, f.kerSquareLift.comp g = AlgHom.id R A := by
  let := f.toAlgebra
  rw [iff_split_injection hf, ← nonempty_subtype, ← nonempty_subtype,
    (retractionKerCotangentToTensorEquivSection hf).nonempty_congr]
  rfl
/-
**Algebra.FormallySmooth.of_split** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmo
oth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A] {P : Type u_2}   [inst_3 : CommRing P] [inst_4 : Algebra R P]
 [Algebra.FormallySmooth R P] (f : P →ₐ[R] A)   (g : A →ₐ[R] P ⧸ RingHom.ker f.t
oRingHom ^ 2), f.kerSquareLift.comp g = AlgHom.id R A → Algebra.FormallySmooth R
 A
参数：f : P →ₐ[R] A；g : A →ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallySmooth.iff_split_surjection`：∀ {R : Type u} {A : Type v}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2}
   [inst_3 : CommRing P] [inst_4 …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem of_split (f : P →ₐ[R] A) (g : A →ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2)
    (h : f.kerSquareLift.comp g = AlgHom.id R A) :
    FormallySmooth R A := by
  refine (iff_split_surjection f fun x ↦ ?_).mpr ⟨g, h⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
  exact ⟨y, congr(f.kerSquareLift $hy).trans congr($h x)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.FormallySmooth.of_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.F
ormallySmooth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A],   (∀ ⦃B : Type (max u v)⦄ [inst_3 : CommRing B] [inst_4 : Al
gebra R B] (I : Ideal B),       I ^ 2 = ⊥ → Function.Surjective (Ideal.Quotient.
mkₐ R I).comp) →     Algebra.FormallySmooth R A
参数：∀ ⦃B : Type (max u v)⦄ [inst_3 : CommRing B] [inst_4 : Algebra R B] (I : Idea
l B),       I ^ 2 = ⊥ → Function.Surjective (Ideal.Quotient.mkₐ R I).comp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.Generators.instIsScalarTowerRing`：∀ {R : Type u} {S : Type v} {ι
 : Type w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P
 : Algebra.Generators R S ι) {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallySmooth.iff_split_surjection`：∀ {R : Type u} {A : Type v}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2}
   [inst_3 : CommRing P] [inst_4 …
· 使用引理 `Algebra.Generators.algebraMap_surjective`：algebraMap_surjective : Functi
on.Surjective (algebraMap P.Ring S)
· 使用定理 `Ideal.Quotient.lift_surjective_of_surjective`：lift_surjective_of_surject
ive {f : R ->+* S} (H : forall a : R, a in I -> f a = 0) (hf : Function.Surjecti
ve f) : Function.Surjective (Ideal…
· 使用定理 `AlgHom.ker_kerSquareLift`：∀ {R : Type u} [inst : CommRing R] {A : Type u
_1} {B : Type u_2} [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algeb
ra R A] [inst_…
· 使用定理 `Ideal.cotangentIdeal_square`：cotangentIdeal_square (I : Ideal R) : I.cot
angentIdeal ^ 2 = ⊥
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.quotientKerAlgEquivOfSurjective_apply`：∀ {R₁ : Type u_1} {A : Type
 u_3} {B : Type u_4} [inst : CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebr
a R₁ A]   [inst_3 : Semiring B] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_comp_surjective
    (H : ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I)) :
    FormallySmooth R A := by
  let P := Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [iff_split_surjection f P.algebraMap_surjective]
  have surj : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  dsimp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at sqz
  obtain ⟨g, hg⟩ := H _ sqz (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
  refine ⟨g, AlgHom.ext fun x ↦ congr(f.kerSquareLift.kerLift ($hg x)).trans ?_⟩
  obtain ⟨x, rfl⟩ := (Ideal.quotientKerAlgEquivOfSurjective surj).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    AlgHom.coe_id, id_eq]
  simp only [Ideal.quotientKerAlgEquivOfSurjective_apply]

/--
An `R`-algebra `A` is formally smooth iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
-/
/-
**Algebra.FormallySmooth.iff_comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
FormallySmooth`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A],   Algebra.FormallySmooth R A ↔     ∀ ⦃B : Type (max u v)⦄ [i
nst_3 : CommRing B] [inst_4 : Algebra R B] (I : Ideal B),       I ^ 2 = ⊥ → Func
tion.Surjective (Ideal.Quotient.mkₐ R I).comp
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.comp_surjective`：∀ (R : Type u) (A : Type v) [ins
t : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_1}   [i
nst_3 : CommRing B] [inst_4 …
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…

--- 原说明 ---
An `R`-algebra `A` is formally smooth iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
-/
theorem iff_comp_surjective :
   FormallySmooth R A ↔ ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
      Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨fun _ _ ↦ comp_surjective R A, of_comp_surjective⟩

end iff_split

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-
**Algebra.FormallySmooth.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmo
oth`。
形式化陈述：∀ {R : Type u_4} [inst : CommRing R] {A : Type u_5} {B : Type u_6} [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [Algebra.FormallySmooth R A] (e : A ≃ₐ[R] B), Algebra.FormallySmooth R B
参数：e : A ≃ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallySmooth.iff_split_surjection`：∀ {R : Type u} {A : Type v}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2}
   [inst_3 : CommRing P] [inst_4 …
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
theorem of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B :=
  (iff_split_surjection e.toAlgHom e.surjective).mpr
    ⟨(Ideal.Quotient.mkₐ _ _).comp e.symm, AlgHom.ext e.apply_symm_apply⟩
/-
**Algebra.FormallySmooth.iff_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Formall
ySmooth`。
形式化陈述：∀ {R : Type u_4} [inst : CommRing R] {A : Type u_5} {B : Type u_6} [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] (e : A ≃ₐ[R] B), Algebra.FormallySmooth R A ↔ Algebra.FormallySmooth R B
参数：e : A ≃ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
-/
theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A ↔ FormallySmooth R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Polynomial

open scoped Polynomial in
/-
**Algebra.FormallySmooth.polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyS
mooth`。
形式化陈述：∀ (R : Type u_4) [inst : CommRing R], Algebra.FormallySmooth R (Polynomial
 R)
参数：R : Type u_4；Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
-/
instance polynomial (R : Type*) [CommRing R] :
  FormallySmooth R R[X] := .of_equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit)
/-
**Algebra.FormallySmooth.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FormallySmooth R R := .of_equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

end Polynomial

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-
**Algebra.FormallySmooth.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmooth`
。
形式化陈述：∀ (R : Type u_4) [inst : CommRing R] (A : Type u_5) [inst_1 : CommRing A] 
[inst_2 : Algebra R A] (B : Type u_6)   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [inst_5 : Algebra A B] [IsScalarTower R A B] [Algebra.FormallySmooth R A]  
 [Algebra.FormallySmooth A B], Algebra.FormallySmooth R B
参数：R : Type u_4；A : Type u_5；B : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.comp_surjective`：∀ (R : Type u) (A : Type v) [ins
t : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_1}   [i
nst_3 : CommRing B] [inst_4 …
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  refine .of_comp_surjective fun C _ _ I hI f ↦ ?_
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective _ _ I hI (f.comp (IsScalarTower.toAlgHom R A B))
  let := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ := comp_surjective _ _ I hI { f with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩
/-
**Algebra.FormallySmooth.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.F
ormallySmooth`。
形式化陈述：∀ (R : Type u_4) [inst : CommRing R] (A : Type u_5) [inst_1 : CommRing A] 
[inst_2 : Algebra R A] (B : Type u_6)   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [inst_5 : Algebra A B] [IsScalarTower R A B]   [Algebra.FormallyUnramified 
R A] [Algebra.FormallySmooth R B], Algebra.FormallySmooth A B
参数：R : Type u_4；A : Type u_5；B : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallySmooth.iff_comp_surjective`：∀ {R : Type u} {A : Type v} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.Form
allySmooth R A ↔     ∀ ⦃B : Type…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Algebra.FormallySmooth.comp_surjective`：∀ (R : Type u) (A : Type v) [ins
t : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_1}   [i
nst_3 : CommRing B] [inst_4 …
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
lemma of_restrictScalars [FormallyUnramified R A] [FormallySmooth R B] :
    FormallySmooth A B := by
  refine iff_comp_surjective.mpr fun C _ _ I hI f ↦ ?_
  algebraize [(algebraMap A C).comp (algebraMap R A)]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective _ _ I hI (f.restrictScalars R)
  suffices g.comp (IsScalarTower.toAlgHom R A B) = IsScalarTower.toAlgHom R A C from
    ⟨{ __ := g, commutes' x := congr($this x) }, AlgHom.ext fun x ↦ congr($hg x)⟩
  apply Algebra.FormallyUnramified.comp_injective _ hI
  rw [← AlgHom.comp_assoc, hg]
  exact AlgHom.ext f.commutes

end Comp

section surjective

variable {R : Type*} [CommRing R]
variable {P A : Type*} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
variable (f : P →ₐ[R] A)

/-
**Algebra.FormallySmooth.iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallySmooth`。
形式化陈述：∀ {R : Type u_4} [inst : CommRing R] {A : Type u_6} [inst_1 : CommRing A] 
[inst_2 : Algebra R A],   Function.Surjective ⇑(algebraMap R A) → (Algebra.Forma
llySmooth R A ↔ IsIdempotentElem (RingHom.ker (algebraMap R A)))
参数：algebraMap R A；Algebra.FormallySmooth R A ↔ IsIdempotentElem (RingHom.ker (al
gebraMap R A))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallySmooth.iff_split_surjection`：∀ {R : Type u} {A : Type v}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2}
   [inst_3 : CommRing P] [inst_4 …
· 使用定理 `Algebra.FormallySmooth.inst`：∀ {R : Type u} [inst : CommRing R], Algebra
.FormallySmooth R R
· 使用定理 `Ideal.Quotient.algHom_ext`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : Comm
Semiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] {I : Ideal A}   [inst_3 :
 I.IsTwoSided] …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用引理 `RingHom.ker_comp_of_injective`：ker_comp_of_injective [Semiring T] (g : T
 ->+* R) {f : R ->+* S} (hf : Function.Injective f) : ker (f.comp g) = RingHom.k
er g
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iff_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Algebra.FormallySmooth R A ↔ IsIdempotentElem (RingHom.ker (algebraMap R A)) := by
  rw [Algebra.FormallySmooth.iff_split_surjection (Algebra.ofId R A) h]
  constructor
  · intro ⟨g, hg⟩
    let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) ^ 2 :=
      .ofAlgHom _ _ (Ideal.Quotient.algHom_ext _ (by ext)) hg
    rw [IsIdempotentElem, ← pow_two, ← Ideal.mk_ker (I := _ ^ 2), ← Ideal.Quotient.algebraMap_eq,
      ← e.toAlgHom.comp_algebraMap, RingHom.ker_comp_of_injective _ (by exact e.injective)]
  · intro H
    let e := (Ideal.quotientEquivAlgOfEq _ ((pow_two _).trans H)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) h)
    exact ⟨e.symm.toAlgHom, AlgHom.ext <| h.forall.mpr fun x ↦ by simp⟩

end surjective

section BaseChange


variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.FormallySmooth.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallySmooth R A] : FormallySmooth B (B ⊗[R] A) := by
  refine .of_comp_surjective fun C _ _ I hI f ↦ ?_
  let := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) ?_, ?_⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.restrictScalars R).comp TensorProduct.includeRight)
  · apply AlgHom.restrictScalars_injective R
    apply TensorProduct.ext'
    intro b a
    suffices algebraMap B _ b * f (1 ⊗ₜ[R] a) = f (b ⊗ₜ[R] a) by simpa [Algebra.ofId_apply]
    rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end BaseChange

section Localization

variable {R A Rₘ Sₘ : Type*} [CommRing R] [CommRing A] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R A] [Algebra R Sₘ] [Algebra A Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R A Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R A)) Sₘ]
include M

/-
**Algebra.FormallySmooth.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallySmooth`。
形式化陈述：∀ {R : Type u_4} {Rₘ : Type u_6} [inst : CommRing R] [inst_1 : CommRing Rₘ
] (M : Submonoid R) [inst_2 : Algebra R Rₘ]   [IsLocalization M Rₘ], Algebra.For
mallySmooth R Rₘ
参数：M : Submonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsNilpotent.isUnit_quotient_mk_iff`：IsNilpotent.isUnit_quotient_mk_iff {
R : Type*} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) {x : R} : IsUnit (Ide
al.Quotient.mk I x) ↔ Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
-/
theorem of_isLocalization : FormallySmooth R Rₘ := by
  refine .of_comp_surjective fun Q _ _ I e f ↦ ?_
  have : ∀ x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert! (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let : Rₘ →ₐ[R] Q :=
    { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp
/-
**Algebra.FormallySmooth.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallySmooth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallySmooth R A] (M : Submonoid A) : FormallySmooth R (Localization M) :=
  have : FormallySmooth A (Localization M) := of_isLocalization M
  .comp _ A _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.FormallySmooth.localization_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallySmooth`。
形式化陈述：∀ {R : Type u_4} {Rₘ : Type u_6} {Sₘ : Type u_7} [inst : CommRing R] [inst
_1 : CommRing Rₘ] [inst_2 : CommRing Sₘ]   (M : Submonoid R) [inst_3 : Algebra R
 Sₘ] [inst_4 : Algebra R Rₘ] [inst_5 : Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]   
[IsLocalization M Rₘ] [Algebra.FormallySmooth R Sₘ], Algebra.FormallySmooth Rₘ S
ₘ
参数：M : Submonoid R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.FormallySmooth.mk_lift`：mk_lift [FormallySmooth R A] (I : Ideal 
B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (Form
allySmooth.lift I hI…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  refine .of_comp_surjective fun Q _ _ I e f ↦ ?_
  let := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  let : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ →ₐ[Rₘ] Q := by
    refine { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := ?_ }
    intro r
    change
      (RingHom.comp (FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) : Sₘ →+* Q)
            (algebraMap _ _))
          r =
        algebraMap _ _ r
    congr 1
    refine IsLocalization.ringHom_ext M ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      AlgHom.comp_algebraMap]
  use f
  ext
  simp [f]
/-
**Algebra.FormallySmooth.localization_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.For
mallySmooth`。
形式化陈述：∀ {R : Type u_4} {A : Type u_5} {Rₘ : Type u_6} {Sₘ : Type u_7} [inst : Co
mmRing R] [inst_1 : CommRing A]   [inst_2 : CommRing Rₘ] [inst_3 : CommRing Sₘ] 
(M : Submonoid R) [inst_4 : Algebra R A] [inst_5 : Algebra R Sₘ]   [inst_6 : Alg
ebra A Sₘ] [inst_7 : Algebra R Rₘ] [inst_8 : Algebra Rₘ Sₘ] [IsScalarTower R Rₘ 
Sₘ]   [IsScalarTower R A Sₘ] [IsLocalization M Rₘ] [IsLocalization (Submonoid.ma
p (algebraMap R A) M) Sₘ]   [Algebra.FormallySmooth R A], Algebra.FormallySmooth
 Rₘ Sₘ
参数：M : Submonoid R；Submonoid.map (algebraMap R A) M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `Algebra.FormallySmooth.localization_base`：∀ {R : Type u_4} {Rₘ : Type u_
6} {Sₘ : Type u_7} [inst : CommRing R] [inst_1 : CommRing Rₘ] [inst_2 : CommRing
 Sₘ]   (M : Submonoid R) [inst…
-/
theorem localization_map [FormallySmooth R A] : FormallySmooth Rₘ Sₘ := by
  have : FormallySmooth A Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R A))
  have : FormallySmooth R Sₘ := FormallySmooth.comp R A Sₘ
  exact FormallySmooth.localization_base M

end Localization

end FormallySmooth

section

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
@[stacks 00T2 "In the stacks project, the definition of smooth is completely different, and tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.",
mk_iff]
/-
**Algebra.Smooth** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_4) → [inst : CommRing R] → (A : Type u) → [inst_1 : CommRing A
] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class Smooth [CommRing R] (A : Type u) [CommRing A] [Algebra R A] : Prop where
  formallySmooth : FormallySmooth R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Smooth

attribute [instance] formallySmooth finitePresentation

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Being smooth is transported via algebra isomorphisms. -/
/-
**Algebra.Smooth.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smooth`。
形式化陈述：∀ {R : Type u_4} [inst : CommRing R] {A : Type u_5} {B : Type u_6} [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [Algebra.Smooth R A] (e : A ≃ₐ[R] B), Algebra.Smooth R B
参数：e : A ≃ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…

--- 原说明 ---
Being smooth is transported via algebra isomorphisms.
-/
theorem of_equiv [Smooth R A] (e : A ≃ₐ[R] B) : Smooth R B where
  formallySmooth := FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv e

/-- Localization at an element is smooth. -/
/-
**Algebra.Smooth.of_isLocalization_Away** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smoot
h`。
形式化陈述：∀ {R : Type u_4} [inst : CommRing R] {A : Type u_5} [inst_1 : CommRing A] 
[inst_2 : Algebra R A] (r : R)   [IsLocalization.Away r A], Algebra.Smooth R A
参数：r : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S

--- 原说明 ---
Localization at an element is smooth.
-/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Smooth R A where
  formallySmooth := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

section Comp

variable (R A B)

/-- Smooth is stable under composition. -/
/-
**Algebra.Smooth.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smooth`。
形式化陈述：∀ (R : Type u_4) [inst : CommRing R] (A : Type u_5) (B : Type u_6) [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [inst_5 : Algebra A B] [IsScalarTower R A B] [Algebra.Smooth R A]   [Algebr
a.Smooth A B], Algebra.Smooth R B
参数：R : Type u_4；A : Type u_5；B : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…

--- 原说明 ---
Smooth is stable under composition.
-/
theorem comp [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B] : Smooth R B where
  formallySmooth := FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/-- Smooth is stable under base change. -/
/-
**Algebra.Smooth.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Smooth`。
形式化陈述：∀ (R : Type u_4) [inst : CommRing R] (A : Type u_5) (B : Type u_6) [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [Algebra.Smooth R A], Algebra.Smooth B (TensorProduct R B A)
参数：R : Type u_4；A : Type u_5；B : Type u_6；TensorProduct R B A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FormallySmooth.instTensorProduct`：∀ {R : Type u_4} [inst : CommR
ing R] {A : Type u_5} [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6
)   [inst_3 : CommRing B] [ins…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…

--- 原说明 ---
Smooth is stable under base change.
-/
instance baseChange [Smooth R A] : Smooth B (B ⊗[R] A) where

end Comp

end Smooth

end Algebra

