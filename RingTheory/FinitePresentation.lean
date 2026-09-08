/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Data.Finite.Sum
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `Algebra.FiniteType`, `RingHom.FiniteType`, `AlgHom.FiniteType`
  all of these express that some object is finitely generated *as algebra* over some base ring.
- `Algebra.FinitePresentation`, `RingHom.FinitePresentation`, `AlgHom.FinitePresentation`
  all of these express that some object is finitely presented *as algebra* over some base ring.

-/

@[expose] public section

open Function (Surjective)

open Polynomial

section ModuleAndAlgebra

universe w₁ w₂ w₃

variable (R : Type w₁) (A : Type w₂) (B : Type w₃)

/-- An algebra over a commutative semiring is `Algebra.FinitePresentation` if it is the quotient of
a polynomial ring in `n` variables by a finitely generated ideal. -/
/-
**Algebra.FinitePresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type w₁) → (A : Type w₂) → [inst : CommSemiring R] → [inst_1 : Semiri
ng A] → [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra over a commutative semiring is `Algebra.FinitePresentation` if it is 
the quotient of
a polynomial ring in `n` variables by a finitely generated ideal.
-/
class Algebra.FinitePresentation [CommSemiring R] [Semiring A] [Algebra R A] : Prop where
  out : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Surjective f ∧ (RingHom.ker f.toRingHom).FG

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

namespace FiniteType

variable {R A B}

/-- A finitely presented algebra is of finite type. -/
/-
**Algebra.FiniteType.of_finitePresentation** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Fi
niteType`。
形式化陈述：of_finitePresentation [FinitePresentation R A] : FiniteType R A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A finitely presented algebra is of finite type.
-/
instance of_finitePresentation [FinitePresentation R A] : FiniteType R A := by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  apply FiniteType.iff_quotient_mvPolynomial''.2
  exact ⟨n, f, hf.1⟩

end FiniteType

namespace FinitePresentation

variable {R A B}

/-- An algebra over a Noetherian ring is finitely generated if and only if it is finitely
presented. -/
/-
**Algebra.FinitePresentation.of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fi
nitePresentation`。
形式化陈述：of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R
 A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
An algebra over a Noetherian ring is finitely generated if and only if it is fin
itely
presented.
-/
theorem of_finiteType [IsNoetherianRing R] : FiniteType R A ↔ FinitePresentation R A := by
  refine ⟨fun h => ?_, fun hfp => Algebra.FiniteType.of_finitePresentation⟩
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  refine ⟨n, f, hf, ?_⟩
  exact (inferInstance : IsNoetherianRing (MvPolynomial (Fin n) R)).noetherian
    (RingHom.ker f.toRingHom)

/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
/-
**Algebra.FinitePresentation.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FinitePres
entation`。
形式化陈述：equiv [FinitePresentation R A] (e : A ≃ₐ[R] B) : FinitePresentation R B
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.ker_eq_comap_bot`：ker_eq_comap_bot (f : F) : ker f = Ideal.comap
 f ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `RingHom.ker_coe_equiv`：ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) 
= ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`.
-/
theorem equiv [FinitePresentation R A] (e : A ≃ₐ[R] B) : FinitePresentation R B := by
  obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
  use n, AlgHom.comp (↑e) f
  constructor
  · rw [AlgHom.coe_comp]
    exact Function.Surjective.comp e.surjective hf.1
  suffices (RingHom.ker (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom) = RingHom.ker f.toRingHom by
    rw [this]
    exact hf.2
  have hco : (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom = RingHom.comp (e.toRingEquiv : A ≃+* B)
    f.toRingHom := by
    have h : (AlgHom.comp (e : A →ₐ[R] B) f).toRingHom =
      e.toAlgHom.toRingHom.comp f.toRingHom := rfl
    have h1 : ↑e.toRingEquiv = e.toAlgHom.toRingHom := rfl
    rw [h, h1]
  rw [RingHom.ker_eq_comap_bot, hco, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
    RingHom.ker_coe_equiv (AlgEquiv.toRingEquiv e), RingHom.ker_eq_comap_bot]

variable (R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
/-
**Algebra.FinitePresentation.mvPolynomial_aux** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
.FinitePresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of polynomials in finitely many variables is finitely presented.
-/
private lemma mvPolynomial_aux (ι : Type*) [Finite ι] :
    FinitePresentation R (MvPolynomial ι R) where
  out := by
    cases nonempty_fintype ι
    let eqv := (MvPolynomial.renameEquiv R <| Fintype.equivFin ι).symm
    exact
      ⟨Fintype.card ι, eqv, eqv.surjective,
        ((RingHom.injective_iff_ker_eq_bot _).1 eqv.injective).symm ▸ Submodule.fg_bot⟩

variable {R}

/-- The quotient of a finitely presented algebra by a finitely generated ideal is finitely
presented. -/
/-
**Algebra.FinitePresentation.quotient** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteP
resentation`。
形式化陈述：∀ {R : Type w₁} {A : Type w₂} [inst : CommRing R] [inst_1 : CommRing A] [i
nst_2 : Algebra R A] {I : Ideal A},   I.FG → ∀ [Algebra.FinitePresentation R A],
 Algebra.FinitePresentation R (A ⧸ I)
参数：A ⧸ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Ideal.Quotient.mkₐ_surjective`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : 
CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst
_3 : I.IsTwoSided],…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.fg_ker_comp`：fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S]
 [CommRing A] (f : R ->+* S) (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (Rin
gHom.ke…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.mkₐ_ker`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSem
iring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.
IsTwoSided],…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
The quotient of a finitely presented algebra by a finitely generated ideal is fi
nitely
presented.
-/
protected theorem quotient {I : Ideal A} (h : I.FG) [FinitePresentation R A] :
    FinitePresentation R (A ⧸ I) where
  out := by
    obtain ⟨n, f, hf⟩ := FinitePresentation.out (R := R) (A := A)
    refine ⟨n, (Ideal.Quotient.mkₐ R I).comp f, ?_, ?_⟩
    · exact (Ideal.Quotient.mkₐ_surjective R I).comp hf.1
    · refine Ideal.fg_ker_comp _ _ hf.2 ?_ hf.1
      simp [h]

/-- If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finitely presented,
then so is `B`. -/
/-
**Algebra.FinitePresentation.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fi
nitePresentation`。
形式化陈述：of_surjective {f : A ->ₐ[R] B} (hf : Function.Surjective f) (hker : (RingH
om.ker f.toRingHom).FG) [FinitePresentation R A] : FinitePresentation R B
参数：hf : Function.Surjective f；hker : (RingHom.ker f.toRingHom).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `Algebra.FinitePresentation.quotient`：∀ {R : Type w₁} {A : Type w₂} [inst
 : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {I : Ideal A},   I.F
G → ∀ [Algebra.FinitePres…

--- 原说明 ---
If `f : A →ₐ[R] B` is surjective with finitely generated kernel and `A` is finit
ely presented,
then so is `B`.
-/
theorem of_surjective {f : A →ₐ[R] B} (hf : Function.Surjective f)
    (hker : (RingHom.ker f.toRingHom).FG)
    [FinitePresentation R A] : FinitePresentation R B :=
  letI : FinitePresentation R (A ⧸ RingHom.ker f) := FinitePresentation.quotient hker
  equiv (Ideal.quotientKerAlgEquivOfSurjective hf)
/-
**Algebra.FinitePresentation.iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FinitePresen
tation`。
形式化陈述：iff : FinitePresentation R A ↔ exists (n : _) (I : Ideal (MvPolynomial (Fi
n n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.FinitePresentation.quotient`：∀ {R : Type w₁} {A : Type w₂} [inst
 : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {I : Ideal A},   I.F
G → ∀ [Algebra.FinitePres…
· 使用定理 `_private.Mathlib.RingTheory.FinitePresentation.0.Algebra.FinitePresentat
ion.mvPolynomial_aux`：∀ (R : Type w₁) [inst : CommRing R] (ι : Type u_1) [Finite
 ι], Algebra.FinitePresentation R (MvPolynomial ι R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
-/
theorem iff :
    FinitePresentation R A ↔
      ∃ (n : _) (I : Ideal (MvPolynomial (Fin n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG := by
  constructor
  · rintro ⟨n, f, hf⟩
    exact ⟨n, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf.1, hf.2⟩
  · rintro ⟨n, I, e, hfg⟩
    let := (FinitePresentation.mvPolynomial_aux R _).quotient hfg
    exact equiv e

/-- An algebra is finitely presented if and only if it is a quotient of a polynomial ring whose
variables are indexed by a fintype by a finitely generated ideal. -/
/-
**Algebra.FinitePresentation.iff_quotient_mvPolynomial'** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra.FinitePresentation`。
形式化陈述：iff_quotient_mvPolynomial' : FinitePresentation R A ↔ exists (ι : Type*) (
_ : Fintype ι) (f : MvPolynomial ι R ->ₐ[R] A), Surjective f ∧ (RingHom.ker f.to
RingHom).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.fg_ker_comp`：fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S]
 [CommRing A] (f : R ->+* S) (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (Rin
gHom.ke…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.ker_coe_equiv`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Alg
ebra R A] …
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
An algebra is finitely presented if and only if it is a quotient of a polynomial
 ring whose
variables are indexed by a fintype by a finitely generated ideal.
-/
theorem iff_quotient_mvPolynomial' :
    FinitePresentation R A ↔
      ∃ (ι : Type*) (_ : Fintype ι) (f : MvPolynomial ι R →ₐ[R] A),
        Surjective f ∧ (RingHom.ker f.toRingHom).FG := by
  constructor
  · rintro ⟨n, f, hfs, hfk⟩
    set ulift_var := MvPolynomial.renameEquiv R Equiv.ulift
    refine
      ⟨ULift (Fin n), inferInstance, f.comp ulift_var.toAlgHom, hfs.comp ulift_var.surjective,
        Ideal.fg_ker_comp _ _ ?_ hfk ulift_var.surjective⟩
    simpa using! Submodule.fg_bot
  · rintro ⟨ι, hfintype, f, hf⟩
    have equiv := MvPolynomial.renameEquiv R (Fintype.equivFin ι)
    use Fintype.card ι, f.comp equiv.symm, hf.1.comp (AlgEquiv.symm equiv).surjective
    refine Ideal.fg_ker_comp (S := MvPolynomial ι R) (A := A) _ f ?_ hf.2 equiv.symm.surjective
    simpa using! Submodule.fg_bot

universe v in
/-- If `A` is a finitely presented `R`-algebra, then `MvPolynomial (Fin n) A` is finitely presented
as `R`-algebra. -/
/-
**Algebra.FinitePresentation.mvPolynomial_of_finitePresentation** 是 Mathlib 中的一个
定理，位于命名空间 `Algebra.FinitePresentation`。
形式化陈述：mvPolynomial_of_finitePresentation [FinitePresentation R A] (ι : Type v) [
Finite ι] : FinitePresentation R (MvPolynomial ι A)
参数：ι : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FinitePresentation.iff_quotient_mvPolynomial'`：iff_quotient_mvPo
lynomial' : FinitePresentation R A ↔ exists (ι : Type*) (_ : Fintype ι) (f : MvP
olynomial ι R ->ₐ[R] A), Surjective f ∧ (Ri…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MvPolynomial.map_surjective`：map_surjective (hf : Function.Surjective f)
 : Function.Surjective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.fg_ker_comp`：fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S]
 [CommRing A] (f : R ->+* S) (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (Rin
gHom.ke…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `AlgEquiv.toAlgHom_toRingHom`：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : 
A₁ ->+* A₂) = e
· 使用定理 `AlgHom.ker_coe_equiv`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_4} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Alg
ebra R A] …
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `MvPolynomial.mapAlgHom_coe_ringHom`：mapAlgHom_coe_ringHom [CommSemiring 
S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) : ↑(mapAlgHom f : _ ->ₐ[R] 
MvPolynomial σ S₂) = (ma…
· 使用定理 `MvPolynomial.ker_map`：ker_map (f : R ->+* S) : RingHom.ker (map f : MvPo
lynomial σ R ->+* MvPolynomial σ S) = Ideal.map (C : R ->+* MvPolynomial σ R) (R
ingHom.ker…
· 使用定理 `Ideal.FG.map`：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_
1 : Semiring S] {I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG

--- 原说明 ---
If `A` is a finitely presented `R`-algebra, then `MvPolynomial (Fin n) A` is fin
itely presented
as `R`-algebra.
-/
theorem mvPolynomial_of_finitePresentation [FinitePresentation R A] (ι : Type v) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) := by
  have hfp : FinitePresentation R A := inferInstance
  rw [iff_quotient_mvPolynomial'] at hfp ⊢
  -- Make universe level `v` explicit so it matches that of `ι`
  obtain ⟨(ι' : Type v), _, f, hf_surj, hf_ker⟩ := hfp
  let g := (MvPolynomial.mapAlgHom f).comp (MvPolynomial.sumAlgEquiv R ι ι').toAlgHom
  cases nonempty_fintype (ι ⊕ ι')
  refine
    ⟨ι ⊕ ι', by infer_instance, g,
      (MvPolynomial.map_surjective f.toRingHom hf_surj).comp (AlgEquiv.surjective _),
      Ideal.fg_ker_comp _ _ ?_ ?_ (AlgEquiv.surjective _)⟩
  · rw [AlgEquiv.toAlgHom_toRingHom, AlgHom.ker_coe_equiv]
    exact Submodule.fg_bot
  · rw [AlgHom.toRingHom_eq_coe, MvPolynomial.mapAlgHom_coe_ringHom, MvPolynomial.ker_map]
    exact hf_ker.map MvPolynomial.C

variable (R A B)

/-- If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, then `S` is
  finitely presented as `R`-algebra. -/
/-
**Algebra.FinitePresentation.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FinitePres
entation`。
形式化陈述：trans [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A] [Finite
Presentation A B] : FinitePresentation R B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FinitePresentation.iff`：iff : FinitePresentation R A ↔ exists (n
 : _) (I : Ideal (MvPolynomial (Fin n) R)) (_ : (_ ⧸ I) ≃ₐ[R] A), I.FG
· 使用定理 `Algebra.FinitePresentation.quotient`：∀ {R : Type w₁} {A : Type w₂} [inst
 : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {I : Ideal A},   I.F
G → ∀ [Algebra.FinitePres…
· 使用定理 `Algebra.FinitePresentation.mvPolynomial_of_finitePresentation`：mvPolynom
ial_of_finitePresentation [FinitePresentation R A] (ι : Type v) [Finite ι] : Fin
itePresentation R (MvPolynomial ι A)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `A` is an `R`-algebra and `S` is an `A`-algebra, both finitely presented, the
n `S` is
  finitely presented as `R`-algebra.
-/
theorem trans [Algebra A B] [IsScalarTower R A B] [FinitePresentation R A]
    [FinitePresentation A B] : FinitePresentation R B := by
  have hfpB : FinitePresentation A B := inferInstance
  obtain ⟨n, I, e, hfg⟩ := iff.1 hfpB
  let : FinitePresentation R (MvPolynomial (Fin n) A ⧸ I) :=
    (mvPolynomial_of_finitePresentation _).quotient hfg
  exact equiv (e.restrictScalars R)

/-- The ring of polynomials in finitely many variables is finitely presented. -/
/-
**Algebra.FinitePresentation.mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fin
itePresentation`。
形式化陈述：∀ (R : Type w₁) (A : Type w₂) [inst : CommRing R] [inst_1 : CommRing A] [i
nst_2 : Algebra R A]   [Algebra.FinitePresentation R A] (ι : Type u_1) [Finite ι
], Algebra.FinitePresentation R (MvPolynomial ι A)
参数：R : Type w₁；A : Type w₂；ι : Type u_1；MvPolynomial ι A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.FinitePresentation.0.Algebra.FinitePresentat
ion.mvPolynomial_aux`：∀ (R : Type w₁) [inst : CommRing R] (ι : Type u_1) [Finite
 ι], Algebra.FinitePresentation R (MvPolynomial ι R)
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The ring of polynomials in finitely many variables is finitely presented.
-/
protected instance mvPolynomial [FinitePresentation R A] (ι : Type*) [Finite ι] :
    FinitePresentation R (MvPolynomial ι A) :=
  have := FinitePresentation.mvPolynomial_aux A ι; .trans _ A _

/-- `R` is finitely presented as `R`-algebra. -/
/-
**Algebra.FinitePresentation.self** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FinitePrese
ntation`。
形式化陈述：self : FinitePresentation R R
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.FinitePresentation.0.Algebra.FinitePresentat
ion.mvPolynomial_aux`：∀ (R : Type w₁) [inst : CommRing R] (ι : Type u_1) [Finite
 ι], Algebra.FinitePresentation R (MvPolynomial ι R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B

--- 原说明 ---
`R` is finitely presented as `R`-algebra.
-/
instance self : FinitePresentation R R :=
  have := FinitePresentation.mvPolynomial_aux R Empty
  equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

/-- `R[X]` is finitely presented as `R`-algebra. -/
/-
**Algebra.FinitePresentation.polynomial** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Finit
ePresentation`。
形式化陈述：polynomial [FinitePresentation R A] : FinitePresentation R A[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Algebra.FinitePresentation.mvPolynomial`：∀ (R : Type w₁) (A : Type w₂) [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Finit
ePresentation R A] (ι : Type …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
`R[X]` is finitely presented as `R`-algebra.
-/
instance polynomial [FinitePresentation R A] : FinitePresentation R A[X] :=
  letI := FinitePresentation.mvPolynomial R A Unit
  have := equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} A PUnit)
  .trans _ A _

open MvPolynomial

-- TODO: extract out helper lemmas and tidy proof.
@[stacks 0561]
/-
**Algebra.FinitePresentation.of_restrict_scalars_finitePresentation** 是 Mathlib 
中的一个定理，位于命名空间 `Algebra.FinitePresentation`。
形式化陈述：of_restrict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B]
 [FinitePresentation.{w₁, w₃} R B] [FiniteType R A] : FinitePresentation.{w₂, w₃
} A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `Algebra.adjoin_range_eq_range_aeval`：∀ (R : Type u) {S₁ : Type v} {σ : T
ype u_1} [inst : CommSemiring R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R 
S₁]   (f : σ → S₁), Algeb…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Algebra.adjoin_adjoin_of_tower`：adjoin_adjoin_of_tower (s : Set A) : adj
oin S (adjoin R s : Set A) = adjoin S s
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `MvPolynomial.adjoin_range_X`：adjoin_range_X : Algebra.adjoin R (range (X
 : σ -> MvPolynomial σ R)) = ⊤
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.adjoin_union_eq_adjoin_adjoin`：adjoin_union_eq_adjoin_adjoin : a
djoin R (s union t) = (adjoin (adjoin R s) t).restrictScalars R
· 使用定理 `Subalgebra.restrictScalars_top`：restrictScalars_top : restrictScalars R 
(⊤ : Subalgebra S A) = ⊤
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.adjoin_algebraMap`：adjoin_algebraMap (s : Set S) : adjoin R (alg
ebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A)
· 使用定理 `Subalgebra.restrictScalars_injective`：restrictScalars_injective : Functi
on.Injective (restrictScalars R : Subalgebra S A -> Subalgebra R A)
· 使用定理 `Algebra.adjoin_restrictScalars`：adjoin_restrictScalars (C D E : Type*) [
CommSemiring C] [CommSemiring D] [CommSemiring E] [Algebra C D] [Algebra C E] [A
lgebra D E] [IsScala…
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.attach_eq_univ`：Finset.attach_eq_univ {s : Finset α} : s.attach =
 Finset.univ
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
（共 75 条，此处仅展示前 30 条）
-/
theorem of_restrict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B]
    [FinitePresentation.{w₁, w₃} R B] [FiniteType R A] :
    FinitePresentation.{w₂, w₃} A B := by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := FinitePresentation.out (R := R) (A := B)
  let RX := MvPolynomial (Fin n) R
  let AX := MvPolynomial (Fin n) A
  refine ⟨n, MvPolynomial.aeval (f ∘ X), ?_, ?_⟩
  · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval,
      Set.range_comp f MvPolynomial.X, eq_top_iff, ← @adjoin_adjoin_of_tower R A B,
      adjoin_image, adjoin_range_X, Algebra.map_top, (AlgHom.range_eq_top _).mpr hf]
    exact fun {x} => subset_adjoin ⟨⟩
  · obtain ⟨t, ht⟩ := FiniteType.out (R := R) (A := A)
    have := fun i : t => hf (algebraMap A B i)
    choose t' ht' using this
    have ht'' : Algebra.adjoin R (algebraMap A AX '' t ∪ Set.range (X : _ → AX)) = ⊤ := by
      rw [adjoin_union_eq_adjoin_adjoin, ← Subalgebra.restrictScalars_top R (A := AX)
        (S := { x // x ∈ adjoin R ((algebraMap A AX) '' t) })]
      refine congrArg (Subalgebra.restrictScalars R) ?_
      rw [adjoin_algebraMap, ht]
      apply Subalgebra.restrictScalars_injective R
      rw [← adjoin_restrictScalars, adjoin_range_X, Subalgebra.restrictScalars_top,
        Subalgebra.restrictScalars_top]
    let g : t → AX := fun x => MvPolynomial.C (x : A) - map (algebraMap R A) (t' x)
    refine ⟨s.image (map (algebraMap R A)) ∪ t.attach.image g, ?_⟩
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, Finset.attach_eq_univ,
      Finset.coe_univ, Set.image_univ]
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' s ∪ Set.range g
    let I := RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X))
    change Ideal.span s₀ = I
    have leI : Ideal.span ((MvPolynomial.map (algebraMap R A)) '' s ∪ Set.range g) ≤
      RingHom.ker (MvPolynomial.aeval (R := A) (f ∘ MvPolynomial.X)) := by
      rw [Ideal.span_le]
      rintro _ (⟨x, hx, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩) <;>
      rw [SetLike.mem_coe, RingHom.mem_ker]
      · rw [MvPolynomial.aeval_map_algebraMap (R := R) (A := A), ← aeval_unique]
        have := Ideal.subset_span hx
        rwa [hs] at this
      · rw [map_sub, MvPolynomial.aeval_map_algebraMap, ← aeval_unique,
          MvPolynomial.aeval_C, ht', Subtype.coe_mk, sub_self]
    apply leI.antisymm
    intro x hx
    rw [RingHom.mem_ker] at hx
    let s₀ := (MvPolynomial.map (algebraMap R A)) '' ↑s ∪ Set.range g
    change x ∈ Ideal.span s₀
    have : x ∈ (MvPolynomial.map (algebraMap R A) : _ →+* AX).range.toAddSubmonoid ⊔
      (Ideal.span s₀).toAddSubmonoid := by
      have : x ∈ (⊤ : Subalgebra R AX) := trivial
      rw [← ht''] at this
      refine adjoin_induction ?_ ?_ ?_ ?_ this
      · rintro _ (⟨x, hx, rfl⟩ | ⟨i, rfl⟩)
        · rw [MvPolynomial.algebraMap_eq, ← sub_add_cancel (MvPolynomial.C x)
            (map (algebraMap R A) (t' ⟨x, hx⟩)), add_comm]
          apply AddSubmonoid.add_mem_sup
          · exact Set.mem_range_self _
          · apply Ideal.subset_span
            apply Set.mem_union_right
            exact Set.mem_range_self _
        · apply AddSubmonoid.mem_sup_left
          exact ⟨X i, map_X _ _⟩
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, map_C _ _⟩
      · intro _ _ _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro x₁ x₂ _ _ h₁ h₂
        obtain ⟨_, ⟨p₁, rfl⟩, q₁, hq₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨p₂, rfl⟩, q₂, hq₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [add_mul, mul_add, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · refine add_mem (Ideal.mul_mem_left _ _ hq₂) (Ideal.mul_mem_right _ _ hq₁)
    obtain ⟨_, ⟨p, rfl⟩, q, hq, rfl⟩ := AddSubmonoid.mem_sup.mp this
    rw [map_add, aeval_map_algebraMap, ← aeval_unique, show MvPolynomial.aeval (f ∘ X) q = 0
      from leI hq, add_zero] at hx
    suffices Ideal.span (s : Set RX) ≤ (Ideal.span s₀).comap (MvPolynomial.map <| algebraMap R A) by
      refine add_mem ?_ hq
      rw [hs] at this
      exact this hx
    rw [Ideal.span_le]
    intro x hx
    apply Ideal.subset_span
    apply Set.mem_union_left
    exact Set.mem_image_of_mem _ hx

variable {R A B}

-- TODO: extract out helper lemmas and tidy proof.
/-- This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it instead. -/
/-
**Algebra.FinitePresentation.ker_fg_of_mvPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.FinitePresentation`。
形式化陈述：ker_fg_of_mvPolynomial {n : Nat} (f : MvPolynomial (Fin n) R ->ₐ[R] A) (hf
 : Function.Surjective f) [FinitePresentation R A] : (RingHom.ker f.toRingHom).F
G
参数：f : MvPolynomial (Fin n) R ->ₐ[R] A；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `MvPolynomial.aeval_eq_eval₂Hom`：aeval_eq_eval₂Hom (p : MvPolynomial σ R)
 : aeval f p = eval₂Hom (algebraMap R S₁) f p
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MvPolynomial.aeval_unique`：aeval_unique (φ : MvPolynomial σ R ->ₐ[R] S₁)
 : φ = aeval (φ ∘ X)
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
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
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPolynomial.adjoin_range_X`：adjoin_range_X : Algebra.adjoin R (range (X
 : σ -> MvPolynomial σ R)) = ⊤
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
This is used to prove the strictly stronger `ker_fg_of_surjective`. Use it inste
ad.
-/
theorem ker_fg_of_mvPolynomial {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A)
    (hf : Function.Surjective f) [FinitePresentation R A] : (RingHom.ker f.toRingHom).FG := by
  classical
    obtain ⟨m, f', hf', s, hs⟩ := FinitePresentation.out (R := R) (A := A)
    let RXn := MvPolynomial (Fin n) R
    let RXm := MvPolynomial (Fin m) R
    have := fun i : Fin n => hf' (f <| X i)
    choose g hg using this
    have := fun i : Fin m => hf (f' <| X i)
    choose h hh using this
    let aeval_h : RXm →ₐ[R] RXn := aeval h
    let g' : Fin n → RXn := fun i => X i - aeval_h (g i)
    refine ⟨Finset.univ.image g' ∪ s.image aeval_h, ?_⟩
    simp only [Finset.coe_image, Finset.coe_union, Finset.coe_univ, Set.image_univ]
    have hh' : ∀ x, f (aeval_h x) = f' x := by
      intro x
      rw [← f.coe_toRingHom, map_aeval]
      simp_rw [AlgHom.coe_toRingHom, hh]
      rw [AlgHom.comp_algebraMap, ← aeval_eq_eval₂Hom,
        -- Porting note: added line below
        ← funext fun i => Function.comp_apply (f := ↑f') (g := MvPolynomial.X),
        ← aeval_unique]
    let s' := Set.range g' ∪ aeval_h '' s
    have leI : Ideal.span s' ≤ RingHom.ker f.toRingHom := by
      rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨x, hx, rfl⟩)
      · change f (g' i) = 0
        rw [map_sub, ← hg, hh', sub_self]
      · change f (aeval_h x) = 0
        rw [hh']
        change x ∈ RingHom.ker f'.toRingHom
        rw [← hs]
        exact Ideal.subset_span hx
    apply leI.antisymm
    intro x hx
    have : x ∈ aeval_h.range.toAddSubmonoid ⊔ (Ideal.span s').toAddSubmonoid := by
      have : x ∈ adjoin R (Set.range X : Set RXn) := by
        rw [adjoin_range_X]
        trivial
      refine adjoin_induction ?_ ?_ ?_ ?_ this
      · rintro _ ⟨i, rfl⟩
        rw [← sub_add_cancel (X i) (aeval h (g i)), add_comm]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · apply Submodule.subset_span
          apply Set.mem_union_left
          exact Set.mem_range_self _
      · intro r
        apply AddSubmonoid.mem_sup_left
        exact ⟨C r, aeval_C _ _⟩
      · intro _ _ _ _ h₁ h₂
        exact add_mem h₁ h₂
      · intro p₁ p₂ _ _ h₁ h₂
        obtain ⟨_, ⟨x₁, rfl⟩, y₁, hy₁, rfl⟩ := AddSubmonoid.mem_sup.mp h₁
        obtain ⟨_, ⟨x₂, rfl⟩, y₂, hy₂, rfl⟩ := AddSubmonoid.mem_sup.mp h₂
        rw [mul_add, add_mul, add_assoc, ← map_mul]
        apply AddSubmonoid.add_mem_sup
        · exact Set.mem_range_self _
        · exact add_mem (Ideal.mul_mem_right _ _ hy₁) (Ideal.mul_mem_left _ _ hy₂)
    obtain ⟨_, ⟨x, rfl⟩, y, hy, rfl⟩ := AddSubmonoid.mem_sup.mp this
    refine add_mem ?_ hy
    simp only [RXn, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_add,
      show f y = 0 from leI hy, add_zero, hh'] at hx
    suffices Ideal.span (s : Set RXm) ≤ (Ideal.span s').comap aeval_h by
      apply this
      rwa [hs]
    rw [Ideal.span_le]
    intro x hx
    apply Submodule.subset_span
    apply Set.mem_union_right
    exact Set.mem_image_of_mem _ hx

/-- If `f : A →ₐ[R] B` is a surjection between finitely-presented `R`-algebras, then the kernel of
`f` is finitely generated. -/
/-
**Algebra.FinitePresentation.ker_fG_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.FinitePresentation`。
形式化陈述：ker_fG_of_surjective (f : A ->ₐ[R] B) (hf : Function.Surjective f) [Finite
Presentation R A] [FinitePresentation R B] : (RingHom.ker f.toRingHom).FG
参数：f : A ->ₐ[R] B；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.out`：∀ {R : Type w₁} {A : Type w₂} {inst : Co
mmSemiring R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.Fin
itePresentation R A]…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `Ideal.FG.map`：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_
1 : Semiring S] {I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG
· 使用定理 `Algebra.FinitePresentation.ker_fg_of_mvPolynomial`：ker_fg_of_mvPolynomia
l {n : Nat} (f : MvPolynomial (Fin n) R ->ₐ[R] A) (hf : Function.Surjective f) [
FinitePresentation R A] : (RingHom.ker …
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…

--- 原说明 ---
If `f : A →ₐ[R] B` is a surjection between finitely-presented `R`-algebras, then
 the kernel of
`f` is finitely generated.
-/
theorem ker_fG_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f)
    [FinitePresentation R A] [FinitePresentation R B] : (RingHom.ker f.toRingHom).FG := by
  obtain ⟨n, g, hg, _⟩ := FinitePresentation.out (R := R) (A := A)
  convert! (ker_fg_of_mvPolynomial (f.comp g) (hf.comp hg)).map g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom]
  rw [← Ideal.comap_comap, Ideal.map_comap_of_surjective (g : MvPolynomial (Fin n) R →+* A) hg]

end FinitePresentation

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is of `RingHom.FinitePresentation` if `B` is finitely presented as
`A`-algebra. -/
@[algebraize]
/-
**RingHom.FinitePresentation** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FinitePresentation (f : A ->+* B) : Prop
参数：f : A ->+* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring morphism `A →+* B` is of `RingHom.FinitePresentation` if `B` is finitely 
presented as
`A`-algebra.
-/
def FinitePresentation (f : A →+* B) : Prop :=
  @Algebra.FinitePresentation A B _ _ f.toAlgebra

@[simp]
/-
**RingHom.finitePresentation_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：finitePresentation_algebraMap [Algebra A B] : (algebraMap A B).FinitePrese
ntation ↔ Algebra.FinitePresentation A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FinitePresentation.eq_1`：∀ {A : Type u_1} {B : Type u_2} [inst :
 CommRing A] [inst_1 : CommRing B] (f : A →+* B),   f.FinitePresentation = Algeb
ra.FinitePresentation…
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma finitePresentation_algebraMap [Algebra A B] :
    (algebraMap A B).FinitePresentation ↔ Algebra.FinitePresentation A B := by
  rw [RingHom.FinitePresentation, toAlgebra_algebraMap]

namespace FiniteType

/-
**RingHom.FiniteType.of_finitePresentation** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Fi
niteType`。
形式化陈述：of_finitePresentation {f : A ->+* B} (hf : f.FinitePresentation) : f.Finit
eType
参数：hf : f.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_finitePresentation {f : A →+* B} (hf : f.FinitePresentation) : f.FiniteType :=
  @Algebra.FiniteType.of_finitePresentation A B _ _ f.toAlgebra hf

end FiniteType

namespace FinitePresentation

variable (A) in
/-
**RingHom.FinitePresentation.id** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FinitePresent
ation`。
形式化陈述：id : FinitePresentation (RingHom.id A)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id : FinitePresentation (RingHom.id A) :=
  Algebra.FinitePresentation.self A
/-
**RingHom.FinitePresentation.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.
FinitePresentation`。
形式化陈述：comp_surjective {f : A ->+* B} {g : B ->+* C} (hf : f.FinitePresentation) 
(hg : Surjective g) (hker : (RingHom.ker g).FG) : (g.comp f).FinitePresentation
参数：hf : f.FinitePresentation；hg : Surjective g；hker : (RingHom.ker g).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.of_surjective`：of_surjective {f : A ->ₐ[R] B}
 (hf : Function.Surjective f) (hker : (RingHom.ker f.toRingHom).FG) [FinitePrese
ntation R A] : FinitePresentat…
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1
· 使用定理 `MonoidHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOne M] 
[inst_1 : MulOne N] (self : M →* N) (x y : M),   (↑self).toFun (x * y) = (↑self)
.toFun x…
· 使用定理 `RingHom.map_zero'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemir
ing α] [inst_1 : NonAssocSemiring β] (self : α →+* β),   (↑↑self).toFun 0 = 0
· 使用定理 `RingHom.map_add'`：∀ {α : Type u_5} {β : Type u_6} [inst : NonAssocSemiri
ng α] [inst_1 : NonAssocSemiring β] (self : α →+* β) (x y : α),   (↑↑self).toFun
 (x + …
-/
theorem comp_surjective {f : A →+* B} {g : B →+* C} (hf : f.FinitePresentation) (hg : Surjective g)
    (hker : (RingHom.ker g).FG) : (g.comp f).FinitePresentation := by
  algebraize [f, g.comp f]
  exact Algebra.FinitePresentation.of_surjective
    (f :=
      { g with
        toFun := g
        commutes' := fun _ => rfl })
    hg hker
/-
**RingHom.FinitePresentation.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Fi
nitePresentation`。
形式化陈述：of_surjective (f : A ->+* B) (hf : Surjective f) (hker : (RingHom.ker f).F
G) : f.FinitePresentation
参数：f : A ->+* B；hf : Surjective f；hker : (RingHom.ker f).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_id`：comp_id (f : α ->+* β) : f.comp (id α) = f
· 使用定理 `RingHom.FinitePresentation.comp_surjective`：comp_surjective {f : A ->+* 
B} {g : B ->+* C} (hf : f.FinitePresentation) (hg : Surjective g) (hker : (RingH
om.ker g).FG) : (g.comp f).Finit…
· 使用定理 `RingHom.FinitePresentation.id`：id : FinitePresentation (RingHom.id A)
-/
theorem of_surjective (f : A →+* B) (hf : Surjective f) (hker : (RingHom.ker f).FG) :
    f.FinitePresentation := by
  rw [← f.comp_id]
  exact (id A).comp_surjective hf hker
/-
**RingHom.FinitePresentation.of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Fin
itePresentation`。
形式化陈述：of_bijective {f : A ->+* B} (hf : Function.Bijective f) : f.FinitePresenta
tion
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.of_surjective`：of_surjective (f : A ->+* B) (
hf : Surjective f) (hker : (RingHom.ker f).FG) : f.FinitePresentation
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
-/
lemma of_bijective {f : A →+* B} (hf : Function.Bijective f) : f.FinitePresentation :=
  .of_surjective f hf.2 <| by
    have : ker f = ⊥ := by rw [← RingHom.injective_iff_ker_eq_bot]; exact hf.1
    rw [this]
    exact Submodule.fg_bot
/-
**RingHom.FinitePresentation.of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Fi
nitePresentation`。
形式化陈述：of_finiteType [IsNoetherianRing A] {f : A ->+* B} : f.FiniteType ↔ f.Finit
ePresentation
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FinitePresentation.of_finiteType`：of_finiteType [IsNoetherianRin
g R] : FiniteType R A ↔ FinitePresentation R A
-/
theorem of_finiteType [IsNoetherianRing A] {f : A →+* B} : f.FiniteType ↔ f.FinitePresentation :=
  @Algebra.FinitePresentation.of_finiteType A B _ _ f.toAlgebra _
/-
**RingHom.FinitePresentation.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FinitePrese
ntation`。
形式化陈述：comp {g : B ->+* C} {f : A ->+* B} (hg : g.FinitePresentation) (hf : f.Fin
itePresentation) : (g.comp f).FinitePresentation
参数：hg : g.FinitePresentation；hf : f.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
-/
theorem comp {g : B →+* C} {f : A →+* B} (hg : g.FinitePresentation) (hf : f.FinitePresentation) :
    (g.comp f).FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.trans A B C
/-
**RingHom.FinitePresentation.of_comp_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.FinitePresentation`。
形式化陈述：of_comp_finiteType (f : A ->+* B) {g : B ->+* C} (hg : (g.comp f).FinitePr
esentation) (hf : f.FiniteType) : g.FinitePresentation
参数：f : A ->+* B；hg : (g.comp f).FinitePresentation；hf : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`：of_re
strict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B] [FinitePre
sentation.{w₁, w₃} R B] [FiniteType R A] : FinitePresen…
-/
theorem of_comp_finiteType (f : A →+* B) {g : B →+* C} (hg : (g.comp f).FinitePresentation)
    (hf : f.FiniteType) : g.FinitePresentation := by
  algebraize [f, g, g.comp f]
  exact Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C

end FinitePresentation

end RingHom

namespace RingHom.FinitePresentation
universe u v

open Polynomial

/-- Induction principle for finitely presented ring homomorphisms.

For a property to hold for all finitely presented ring homs, it suffices for it to hold for
`Polynomial.C : R → R[X]`, surjective ring homs with finitely generated kernels, and to be closed
under composition.

Note that to state this conveniently for ring homs between rings of different universes, we carry
around two predicates `P` and `Q`, which should be "the same" apart from universes:
* `P`, for ring homs `(R : Type u) → (S : Type u)`.
* `Q`, for ring homs `(R : Type u) → (S : Type v)`.
-/
/-
**RingHom.FinitePresentation.polynomial_induction** 是 Mathlib 中的一个引理，位于命名空间 `Rin
gHom.FinitePresentation`。
形式化陈述：polynomial_induction (P : forall (R : Type u) [CommRing R] (S : Type u) [C
ommRing S], (R ->+* S) -> Prop) (Q : forall (R : Type u) [CommRing R] (S : Type 
v) [CommRing S], (R ->+* S) -> Prop) (polynomial : forall (R) [CommRing R], P R 
R[X] C) (fg_ker : forall (R : Type u) [CommRing R] (S : Type v) [CommRing S] (f 
: R ->+* S), Surjective f -> (ker f).FG -> Q R S f) (comp : forall (R) [CommRing
 R] (S) [CommRing S] (T) [CommRing T] (f : R ->+* S) (g : S ->+* T), P R S f -> 
Q S T g -> Q R T (g.comp f
参数：P : forall (R : Type u) [CommRing R] (S : Type u) [CommRing S], (R ->+* S) ->
 Prop；Q : forall (R : Type u) [CommRing R] (S : Type v) [CommRing S], (R ->+* S)
 -> Prop；polynomial : forall (R) [CommRing R], P R R[X] C；fg_ker : forall (R : T
ype u) [CommRing R] (S : Type v) [CommRing S] (f : R ->+* S), Surjective f -> (k
er f).FG -> Q R S f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MvPolynomial.C_surjective`：C_surjective {R : Type*} [CommSemiring R] (σ 
: Type*) [IsEmpty σ] : Function.Surjective (C : R -> MvPolynomial σ R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Ideal.FG.map`：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_
1 : Semiring S] {I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.optionEquivRight_symm_apply`：∀ (R : Type u) (S₁ : Type v) [
inst : CommSemiring R] (a : MvPolynomial S₁ (Polynomial R)),   (MvPolynomial.opt
ionEquivRight R S₁).symm a =  …
· 使用定理 `MvPolynomial.aevalTower_C`：aevalTower_C (x : R) : aevalTower g y (C x) =
 g x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Induction principle for finitely presented ring homomorphisms.

For a property to hold for all finitely presented ring homs, it suffices for it 
to hold for
`Polynomial.C : R → R[X]`, surjective ring homs with finitely generated kernels,
 and to be closed
under composition.

Note that to state this conveniently for ring homs between rings of different un
iverses, we carry
around two predicates `P` and `Q`, which should be "the same" apart from univers
es:
* `P`, for ring homs `(R : Type u) → (S : Type u)`.
* `Q`, for ring homs `(R : Type u) → (S : Type v)`.
-/
lemma polynomial_induction
    (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S], (R →+* S) → Prop)
    (Q : ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S], (R →+* S) → Prop)
    (polynomial : ∀ (R) [CommRing R], P R R[X] C)
    (fg_ker : ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] (f : R →+* S),
      Surjective f → (ker f).FG → Q R S f)
    (comp : ∀ (R) [CommRing R] (S) [CommRing S] (T) [CommRing T] (f : R →+* S) (g : S →+* T),
      P R S f → Q S T g → Q R T (g.comp f))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.FinitePresentation) :
    Q R S f := by
  let := f.toAlgebra
  obtain ⟨n, g, hg, hg'⟩ := hf
  let g' := g.toRingHom
  change Surjective g' at hg
  change (ker g').FG at hg'
  have : g'.comp MvPolynomial.C = f := g.comp_algebraMap
  clear_value g'
  subst this
  clear g
  induction n generalizing R S with
  | zero =>
    refine fg_ker _ _ _ (hg.comp (MvPolynomial.C_surjective (Fin 0))) ?_
    rw [← comap_ker]
    convert! hg'.map (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom using 1
    simp only [RingEquiv.toRingHom_eq_coe, ← MvPolynomial.isEmptyRingEquiv_symm_toRingHom]
    exact Ideal.comap_symm (MvPolynomial.isEmptyRingEquiv R (Fin 0))
  | succ n IH =>
    let e : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin n) R[X] :=
      (MvPolynomial.renameEquiv R (finSuccEquiv n)).trans (MvPolynomial.optionEquivRight R (Fin n))
    have he : (ker (g'.comp <| RingHomClass.toRingHom e.symm)).FG := by
      rw [← RingHom.comap_ker]
      convert! hg'.map e.toAlgHom.toRingHom using 1
      exact Ideal.comap_symm e.toRingEquiv
    have := IH (R := R[X]) (S := S) (g'.comp e.symm) (hg.comp e.symm.surjective) he
    convert! comp _ _ _ _ _ (polynomial _) this using 1
    rw [comp_assoc, comp_assoc]
    congr 1 with r
    simp [e]

end RingHom.FinitePresentation

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is of `AlgHom.FinitePresentation` if it is of finite
presentation as ring morphism. In other words, if `B` is finitely presented as `A`-algebra. -/
/-
**AlgHom.FinitePresentation** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：FinitePresentation (f : A ->ₐ[R] B) : Prop
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra morphism `A →ₐ[R] B` is of `AlgHom.FinitePresentation` if it is of fi
nite
presentation as ring morphism. In other words, if `B` is finitely presented as `
A`-algebra.
-/
def FinitePresentation (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.FinitePresentation

namespace FiniteType

/-
**AlgHom.FiniteType.of_finitePresentation** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Fini
teType`。
形式化陈述：of_finitePresentation {f : A ->ₐ[R] B} (hf : f.FinitePresentation) : f.Fin
iteType
参数：hf : f.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.of_finitePresentation`：of_finitePresentation {f : A -
>+* B} (hf : f.FinitePresentation) : f.FiniteType
-/
theorem of_finitePresentation {f : A →ₐ[R] B} (hf : f.FinitePresentation) : f.FiniteType :=
  RingHom.FiniteType.of_finitePresentation hf

end FiniteType

namespace FinitePresentation

variable (R A)

/-
**AlgHom.FinitePresentation.id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FinitePresentat
ion`。
形式化陈述：id : FinitePresentation (AlgHom.id R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.id`：id : FinitePresentation (RingHom.id A)
-/
theorem id : FinitePresentation (AlgHom.id R A) :=
  RingHom.FinitePresentation.id A

variable {R A}
/-
**AlgHom.FinitePresentation.comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.FinitePresent
ation`。
形式化陈述：comp {g : B ->ₐ[R] C} {f : A ->ₐ[R] B} (hg : g.FinitePresentation) (hf : f
.FinitePresentation) : (g.comp f).FinitePresentation
参数：hg : g.FinitePresentation；hf : f.FinitePresentation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg 
: g.FinitePresentation) (hf : f.FinitePresentation) : (g.comp f).FinitePresentat
ion
-/
theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.FinitePresentation)
    (hf : f.FinitePresentation) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp hg hf
/-
**AlgHom.FinitePresentation.comp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Fi
nitePresentation`。
形式化陈述：comp_surjective {f : A ->ₐ[R] B} {g : B ->ₐ[R] C} (hf : f.FinitePresentati
on) (hg : Surjective g) (hker : (RingHom.ker g.toRingHom).FG) : (g.comp f).Finit
ePresentation
参数：hf : f.FinitePresentation；hg : Surjective g；hker : (RingHom.ker g.toRingHom).
FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.comp_surjective`：comp_surjective {f : A ->+* 
B} {g : B ->+* C} (hf : f.FinitePresentation) (hg : Surjective g) (hker : (RingH
om.ker g).FG) : (g.comp f).Finit…
-/
theorem comp_surjective {f : A →ₐ[R] B} {g : B →ₐ[R] C} (hf : f.FinitePresentation)
    (hg : Surjective g) (hker : (RingHom.ker g.toRingHom).FG) : (g.comp f).FinitePresentation :=
  RingHom.FinitePresentation.comp_surjective hf hg hker
/-
**AlgHom.FinitePresentation.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Fini
tePresentation`。
形式化陈述：of_surjective (f : A ->ₐ[R] B) (hf : Surjective f) (hker : (RingHom.ker f.
toRingHom).FG) : f.FinitePresentation
参数：f : A ->ₐ[R] B；hf : Surjective f；hker : (RingHom.ker f.toRingHom).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.FinitePresentation.of_surjective`：of_surjective (f : A ->+* B) (
hf : Surjective f) (hker : (RingHom.ker f).FG) : f.FinitePresentation
-/
theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) (hker : (RingHom.ker f.toRingHom).FG) :
    f.FinitePresentation := by
  -- Porting note: added `convert`
  convert! RingHom.FinitePresentation.of_surjective f hf hker
/-
**AlgHom.FinitePresentation.of_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom.Fini
tePresentation`。
形式化陈述：of_finiteType [IsNoetherianRing A] {f : A ->ₐ[R] B} : f.FiniteType ↔ f.Fin
itePresentation
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.of_finiteType`：of_finiteType [IsNoetherianRin
g A] {f : A ->+* B} : f.FiniteType ↔ f.FinitePresentation
-/
theorem of_finiteType [IsNoetherianRing A] {f : A →ₐ[R] B} : f.FiniteType ↔ f.FinitePresentation :=
  RingHom.FinitePresentation.of_finiteType

nonrec theorem of_comp_finiteType (f : A →ₐ[R] B) {g : B →ₐ[R] C}
    (h : (g.comp f).FinitePresentation) (h' : f.FiniteType) : g.FinitePresentation :=
  h.of_comp_finiteType _ h'

end FinitePresentation

end AlgHom

