/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Unramified.Basic

/-!

# Étale morphisms

An `R`-algebra `A` is formally etale if `Ω[A⁄R]` and `H¹(L_{A/R})` both vanish.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly one lift `A →ₐ[R] B`".
An `R`-algebra `A` is étale if it is formally étale and of finite presentation.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

We show that étale is stable under algebra isomorphisms, composition and
localization at an element.

-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

section

variable (R A) in
/-- An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.
For the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`. -/
@[mk_iff, stacks 00UQ]
/-
**Algebra.FormallyEtale** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (A : Type v) → [inst : CommRing R] → [inst_1 : CommRing A] 
→ [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero
.
For the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`
.
-/
class FormallyEtale : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance]
  FormallyEtale.subsingleton_kaehlerDifferential FormallyEtale.subsingleton_h1Cotangent

end

namespace FormallyEtale

section

/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [FormallyEtale R A] :
    FormallyUnramified R A := ⟨inferInstance⟩
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [FormallyEtale R A] : FormallySmooth R A :=
  ⟨inferInstance, inferInstance⟩
/-
**Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth** 是 Mathlib 中的
一个定理，位于命名空间 `Algebra.FormallyEtale`。
形式化陈述：iff_formallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUn
ramified R A ∧ FormallySmooth R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`：∀ {R : Type
 v} {A : Type u} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A
}   [self : Algebra.FormallyUnramified R A], Subs…
· 使用定理 `Algebra.FormallySmooth.subsingleton_h1Cotangent`：∀ {R : Type u} {A : Typ
e v} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : 
Algebra.FormallySmooth R A], Subsingl…
-/
theorem iff_formallyUnramified_and_formallySmooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩
/-
**Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth** 是 Mathlib 中的一
个定理，位于命名空间 `Algebra.FormallyEtale`。
形式化陈述：of_formallyUnramified_and_formallySmooth [FormallyUnramified R A] [Formall
ySmooth R A] : FormallyEtale R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
-/
theorem of_formallyUnramified_and_formallySmooth [FormallyUnramified R A]
    [FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›, ‹_›⟩
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FormallyEtale R R := of_formallyUnramified_and_formallySmooth

variable (R A) in
/-
**Algebra.FormallyEtale.comp_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Formal
lyEtale`。
形式化陈述：comp_bijective [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥) : Functi
on.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I)
参数：I : Ideal B；hI : I ^ 2 = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallySmooth.comp_surjective`：∀ (R : Type u) (A : Type v) [ins
t : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {B : Type u_1}   [i
nst_3 : CommRing B] [inst_4 …
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
-/
lemma comp_bijective [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨FormallyUnramified.comp_injective I hI, FormallySmooth.comp_surjective R A I hI⟩

/--
An `R`-algebra `A` is formally etale iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
a unique lift `A →ₐ[R] B`".
-/
/-
**Algebra.FormallyEtale.iff_comp_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallyEtale`。
形式化陈述：iff_comp_bijective : FormallyEtale R A ↔ forall ⦃B : Type max u v⦄ [CommRi
ng B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ -> Function.Bijective ((Ideal.Quoti
ent.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Algebra.FormallyEtale.comp_bijective`：comp_bijective [FormallyEtale R A]
 (I : Ideal B) (hI : I ^ 2 = ⊥) : Function.Bijective ((Ideal.Quotient.mkₐ R I).c
omp : (A ->ₐ[R] B) -> A ->…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective_of_small`：iff_comp_injecti
ve_of_small [Small.{w} A] : FormallyUnramified R A ↔ forall ⦃B : Type w⦄ [CommRi
ng B], forall [Algebra R B] (I : Ideal B) (_…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.FormallySmooth.of_comp_surjective`：∀ {R : Type u} {A : Type v} [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   (∀ ⦃B : Type 
(max u v)⦄ [inst_3 : CommRing B…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth`：of_forma
llyUnramified_and_formallySmooth [FormallyUnramified R A] [FormallySmooth R A] :
 FormallyEtale R A

--- 原说明 ---
An `R`-algebra `A` is formally etale iff "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
a unique lift `A →ₐ[R] B`".
-/
theorem iff_comp_bijective :
   FormallyEtale R A ↔ ∀ ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ →
      Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  ⟨fun _ _ ↦ comp_bijective R A, fun H ↦
    have : FormallyUnramified R A := FormallyUnramified.iff_comp_injective_of_small.{max u v}.mpr
      (by aesop (add safe Function.Bijective.injective))
    have : FormallySmooth R A := FormallySmooth.of_comp_surjective
      (by aesop (add safe Function.Bijective.surjective))
   .of_formallyUnramified_and_formallySmooth⟩

end

section OfEquiv

/-
**Algebra.FormallyEtale.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyEtal
e`。
形式化陈述：of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Algebra.FormallyUnramified.of_equiv`：of_equiv [FormallyUnramified R A] (
e : A ≃ₐ[R] B) : FormallyUnramified R B
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
-/
theorem of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩
/-
**Algebra.FormallyEtale.iff_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Formally
Etale`。
形式化陈述：iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B
参数：e : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.of_equiv`：of_equiv [FormallyEtale R A] (e : A ≃ₐ[R
] B) : FormallyEtale R B
-/
theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end OfEquiv

section Comp

variable [Algebra A B] [IsScalarTower R A B]

variable (R A B) in
/-
**Algebra.FormallyEtale.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyEtale`。
形式化陈述：comp [FormallyEtale R A] [FormallyEtale A B] : FormallyEtale R B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
-/
theorem comp [FormallyEtale R A] [FormallyEtale A B] :
    FormallyEtale R B :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩
/-
**Algebra.FormallyEtale.of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Fo
rmallyEtale`。
形式化陈述：of_restrictScalars [FormallyUnramified R A] [FormallyEtale R B] : Formally
Etale A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallySmooth.of_restrictScalars`：∀ (R : Type u_4) [inst : Comm
Ring R] (A : Type u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_
6)   [inst_3 : CommRing B] [ins…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth`：of_forma
llyUnramified_and_formallySmooth [FormallyUnramified R A] [FormallySmooth R A] :
 FormallyEtale R A
-/
lemma of_restrictScalars [FormallyUnramified R A] [FormallyEtale R B] :
    FormallyEtale A B :=
  have := FormallyUnramified.of_restrictScalars R A B
  have := FormallySmooth.of_restrictScalars R A B
  .of_formallyUnramified_and_formallySmooth
/-
**Algebra.FormallyEtale.iff_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.F
ormallyEtale`。
形式化陈述：iff_restrictScalars [FormallyEtale R A] : Algebra.FormallyEtale R B ↔ Alge
bra.FormallyEtale A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallyEtale.of_restrictScalars`：of_restrictScalars [FormallyUn
ramified R A] [FormallyEtale R B] : FormallyEtale A B
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallyEtale.comp`：comp [FormallyEtale R A] [FormallyEtale A B]
 : FormallyEtale R B
-/
lemma iff_restrictScalars [FormallyEtale R A] :
    Algebra.FormallyEtale R B ↔ Algebra.FormallyEtale A B :=
  ⟨fun _ ↦ .of_restrictScalars (R := R), fun _ ↦ .comp _ A _⟩
/-
**Algebra.FormallyEtale._root_.Algebra.FormallySmooth.iff_restrictScalars** 是 Ma
thlib 中的一个引理，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.FormallySmooth.iff_restrictScalars [FormallyEtale R A] :
    Algebra.FormallySmooth R B ↔ Algebra.FormallySmooth A B :=
  ⟨fun _ ↦ .of_restrictScalars R _ _, fun _ ↦ .comp _ A _⟩

end Comp

/-
**Algebra.FormallyEtale.iff_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.For
mallyEtale`。
形式化陈述：iff_of_surjective {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (h
 : Function.Surjective (algebraMap R S)) : Algebra.FormallyEtale R S ↔ IsIdempot
entElem (RingHom.ker (algebraMap R S))
参数：h : Function.Surjective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.FormallySmooth.iff_of_surjective`：∀ {R : Type u_4} [inst : CommR
ing R] {A : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A],   Function.S
urjective ⇑(algebraMap R A) → …
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Algebra.FormallyUnramified.of_surjective`：of_surjective [FormallyUnramif
ied R A] (f : A ->ₐ[R] B) (H : Function.Surjective f) : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.inst`：∀ {R : Type u} [inst : CommRing R], Alg
ebra.FormallyUnramified R R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iff_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Surjective (algebraMap R S)) :
    Algebra.FormallyEtale R S ↔ IsIdempotentElem (RingHom.ker (algebraMap R S)) := by
  rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, ← FormallySmooth.iff_of_surjective h,
    and_iff_right (FormallyUnramified.of_surjective (Algebra.ofId R S) h)]

section BaseChange


/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyEtale R A] : FormallyEtale B (B ⊗[R] A) :=
  .of_formallyUnramified_and_formallySmooth

end BaseChange

section Localization

/-!

We now consider a commutative square of commutative rings

```
R -----> S
|        |
|        |
v        v
Rₘ ----> Sₘ
```

where `Rₘ` and `Sₘ` are the localisations of `R` and `S` at a multiplicatively closed
subset `M` of `R`.
-/

/-! Let R, S, Rₘ, Sₘ be commutative rings -/
variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
/-! Let M be a multiplicatively closed subset of `R` -/
variable (M : Submonoid R)
/-! Assume that the rings are in a commutative diagram as above. -/
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
/-! and that Rₘ and Sₘ are localizations of R and S at M. -/
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

/-
**Algebra.FormallyEtale.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.For
mallyEtale`。
形式化陈述：of_isLocalization : FormallyEtale R Rₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Algebra.FormallyUnramified.of_isLocalization`：of_isLocalization [IsLocal
ization M Rₘ] : FormallyUnramified R Rₘ
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
-/
theorem of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyEtale R S] (M : Submonoid S) : FormallyEtale R (Localization M) :=
  .of_formallyUnramified_and_formallySmooth
/-
**Algebra.FormallyEtale.localization_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.For
mallyEtale`。
形式化陈述：localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Algebra.FormallyUnramified.localization_base`：localization_base [Formall
yUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Algebra.FormallySmooth.localization_base`：∀ {R : Type u_4} {Rₘ : Type u_
6} {Sₘ : Type u_7} [inst : CommRing R] [inst_1 : CommRing Rₘ] [inst_2 : CommRing
 Sₘ]   (M : Submonoid R) [inst…
· 使用定理 `Algebra.FormallyEtale.instFormallySmooth`：∀ {R : Type u} {A : Type v} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Formal
lyEtale R A], Algebra.Formally…
-/
theorem localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

/-- The localization of a formally étale map is formally étale. -/
/-
**Algebra.FormallyEtale.localization_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Form
allyEtale`。
形式化陈述：localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.FormallyEtale.of_isLocalization`：of_isLocalization : FormallyEta
le R Rₘ
· 使用定理 `Algebra.FormallyEtale.comp`：comp [FormallyEtale R A] [FormallyEtale A B]
 : FormallyEtale R B
· 使用定理 `Algebra.FormallyEtale.localization_base`：localization_base [FormallyEtal
e R Sₘ] : FormallyEtale Rₘ Sₘ

--- 原说明 ---
The localization of a formally étale map is formally étale.
-/
theorem localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  have : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  have : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M

end Localization

end FormallyEtale

section

variable (R A) in
/-- An `R`-algebra `A` is étale if it is formally étale and of finite presentation. -/
@[mk_iff, stacks 00U1 "Note that this is a different definition from this Stacks entry, but
<https://stacks.math.columbia.edu/tag/00UR> shows that it is equivalent to the definition here."]
/-
**Algebra.Etale** 是 Mathlib 中的一个类，位于命名空间 `Algebra`。
形式化陈述：Etale : Prop where formallyEtale : FormallyEtale R A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class Etale : Prop where
  formallyEtale : FormallyEtale R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance
/-
**Algebra.Etale.iff_formallyUnramified_and_smooth** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.Etale`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommRing R] [inst_1 : CommRing A] [ins
t_2 : Algebra R A],   Algebra.Etale R A ↔ Algebra.FormallyUnramified R A ∧ Algeb
ra.Smooth R A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.etale_iff`：∀ (R : Type u) (A : Type v) [inst : CommRing R] [inst
_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.Etale R A ↔     autoParam (Al
gebra.F…
· 使用定理 `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`：iff_for
mallyUnramified_and_formallySmooth : FormallyEtale R A ↔ FormallyUnramified R A 
∧ FormallySmooth R A
· 使用定理 `Algebra.smooth_iff`：∀ (R : Type u_4) [inst : CommRing R] (A : Type u) [i
nst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.Smooth R A ↔     autoParam
 (Algebr…
-/
lemma Etale.iff_formallyUnramified_and_smooth :
    Etale R A ↔ FormallyUnramified R A ∧ Smooth R A := by
  rw [etale_iff, FormallyEtale.iff_formallyUnramified_and_formallySmooth, smooth_iff]
  tauto

end

namespace Etale

attribute [instance] formallyEtale finitePresentation

/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Etale R R where
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Etale R A] : Smooth R A where
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Etale R A] : Unramified R A where

/-- Being étale is transported via algebra isomorphisms. -/
/-
**Algebra.Etale.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Etale`。
形式化陈述：of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where formallyEtale
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.of_equiv`：of_equiv [FormallyEtale R A] (e : A ≃ₐ[R
] B) : FormallyEtale R B
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.FinitePresentation.equiv`：equiv [FinitePresentation R A] (e : A 
≃ₐ[R] B) : FinitePresentation R B
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…

--- 原说明 ---
Being étale is transported via algebra isomorphisms.
-/
theorem of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where
  formallyEtale := FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

section Comp

variable (R A B)

/-- Étale is stable under composition. -/
/-
**Algebra.Etale.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Etale`。
形式化陈述：comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R
 B where formallyEtale
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.comp`：comp [FormallyEtale R A] [FormallyEtale A B]
 : FormallyEtale R B
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.FinitePresentation.trans`：trans [Algebra A B] [IsScalarTower R A
 B] [FinitePresentation R A] [FinitePresentation A B] : FinitePresentation R B
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…

--- 原说明 ---
Étale is stable under composition.
-/
theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/-- Étale is stable under base change. -/
/-
**Algebra.Etale.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Etale`。
形式化陈述：∀ (R : Type u) (A : Type v) (B : Type u_1) [inst : CommRing R] [inst_1 : C
ommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra R B]
 [Algebra.Etale R A], Algebra.Etale B (TensorProduct R B A)
参数：R : Type u；A : Type v；B : Type u_1；TensorProduct R B A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FormallyEtale.instTensorProduct`：∀ {R : Type u} {A : Type v} {B 
: Type u_1} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [
inst_3 : CommRing B] [inst_4 …
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…

--- 原说明 ---
Étale is stable under base change.
-/
instance baseChange [Etale R A] : Etale B (B ⊗[R] A) where
/-
**Algebra.Etale.of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Etale`。
形式化陈述：of_restrictScalars [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale 
R B] : Etale A B where finitePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallyEtale.of_restrictScalars`：of_restrictScalars [FormallyUn
ramified R A] [FormallyEtale R B] : FormallyEtale A B
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation`：of_re
strict_scalars_finitePresentation [Algebra A B] [IsScalarTower R A B] [FinitePre
sentation.{w₁, w₃} R B] [FiniteType R A] : FinitePresen…
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
-/
lemma of_restrictScalars [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale R B] :
    Etale A B where
  finitePresentation := .of_restrict_scalars_finitePresentation R A B
  formallyEtale := .of_restrictScalars (R := R)

end Comp

/-- Localization at an element is étale. -/
/-
**Algebra.Etale.of_isLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Etale`。
形式化陈述：of_isLocalizationAway (r : R) [IsLocalization.Away r A] : Etale R A where 
formallyEtale
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.of_isLocalization`：of_isLocalization : FormallyEta
le R Rₘ
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S

--- 原说明 ---
Localization at an element is étale.
-/
theorem of_isLocalizationAway (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (s : A) [Algebra.Etale R A] : Algebra.Etale R (Localization.Away s) where
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalizationAway (0, 1)
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Type*) [CommRing S] :
    letI : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
    Algebra.Etale (R × S) R := by
  algebraize [RingHom.fst R S]
  exact Algebra.Etale.of_isLocalizationAway (1, 0)
/-
**Algebra.Etale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Etale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Type*) [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalizationAway (0, 1)

end Etale

end Algebra

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally étale if it is formally unramified and formally smooth.
See `Algebra.FormallyEtale`.
-/
@[algebraize Algebra.FormallyEtale]
/-
**RingHom.FormallyEtale** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FormallyEtale (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `R →+* A` is formally étale if it is formally unramified and
 formally smooth.
See `Algebra.FormallyEtale`.
-/
def FormallyEtale (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyEtale R S
/-
**RingHom.formallyEtale_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：formallyEtale_algebraMap [Algebra R S] : (algebraMap R S).FormallyEtale ↔ 
Algebra.FormallyEtale R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FormallyEtale.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : Comm
Ring R] [inst_1 : CommRing S] (f : R →+* S),   f.FormallyEtale = Algebra.Formall
yEtale R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma formallyEtale_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyEtale ↔ Algebra.FormallyEtale R S := by
  rw [FormallyEtale, toAlgebra_algebraMap]
/-
**RingHom.FormallyEtale.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FormallyEtale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {f : R →+* S} {g : S →+* T}, f.FormallyEt
ale → g.FormallyEtale → (g.comp f).FormallyEtale
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FormallyEtale.comp`：comp [FormallyEtale R A] [FormallyEtale A B]
 : FormallyEtale R B
-/
lemma FormallyEtale.comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyEtale)
    (hg : g.FormallyEtale) :
    (g.comp f).FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.comp R S T

end RingHom

