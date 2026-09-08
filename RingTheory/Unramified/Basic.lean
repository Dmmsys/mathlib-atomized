/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Algebra.Algebra.Shrink

/-!

# Unramified morphisms

An `R`-algebra `A` is formally unramified if `Ω[A⁄R]` is trivial.
This is equivalent to the standard definition "for every `R`-algebra,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at most one lift `A →ₐ[R] B`".
It is unramified if it is formally unramified and of finite type.

Note that there are multiple definitions in the literature. The definition we give is equivalent to
the one in the Stacks Project https://stacks.math.columbia.edu/tag/00US. Note that in EGA unramified
is defined as formally unramified and of finite presentation.

We show that the property extends onto nilpotent ideals, and that it is stable
under `R`-algebra homomorphisms and compositions.

We show that unramified is stable under algebra isomorphisms, composition and
localization at an element.

-/

public section

open scoped TensorProduct

universe w u v

namespace Algebra

section

variable (R : Type v) (A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/--
An `R`-algebra `A` is formally unramified if `Ω[A⁄R]` is trivial.

This is equivalent to "for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`".
See `Algebra.FormallyUnramified.iff_comp_injective`. -/
@[mk_iff, stacks 00UM]
/-
**Algebra.FormallyUnramified** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type v) → (A : Type u) → [inst : CommRing R] → [inst_1 : CommRing A] 
→ [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `A` is formally unramified if `Ω[A⁄R]` is trivial.

This is equivalent to "for every `R`-algebra, every square-zero ideal
`I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists at most one lift `A →ₐ[R] B`
".
See `Algebra.FormallyUnramified.iff_comp_injective`.
-/
class FormallyUnramified : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]

attribute [instance] FormallyUnramified.subsingleton_kaehlerDifferential

end

namespace FormallyUnramified

section

variable {R : Type v} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]
variable {B : Type w} [CommRing B] [Algebra R B] (I : Ideal B)

/-
**Algebra.FormallyUnramified.comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.F
ormallyUnramified`。
形式化陈述：comp_injective [FormallyUnramified R A] (hI : I ^ 2 = ⊥) : Function.Inject
ive ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I)
参数：hI : I ^ 2 = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Function.Surjective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} [Subsingleton α], Function.Surjective f → Subsingleton β
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`：∀ {R : Type
 v} {A : Type u} {inst : CommRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A
}   [self : Algebra.FormallyUnramified R A], Subs…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem comp_injective [FormallyUnramified R A] (hI : I ^ 2 = ⊥) :
    Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  intro f₁ f₂ e
  let := f₁.toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f₁.comp_algebraMap.symm
  have :=
    ((KaehlerDifferential.linearMapEquivDerivation R A).toEquiv.trans
          (derivationToSquareZeroEquivLift I hI)).surjective.subsingleton
  exact Subtype.ext_iff.mp (@Subsingleton.elim _ this ⟨f₁, rfl⟩ ⟨f₂, e.symm⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.FormallyUnramified.iff_comp_injective_of_small** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.FormallyUnramified`。
形式化陈述：iff_comp_injective_of_small [Small.{w} A] : FormallyUnramified R A ↔ foral
l ⦃B : Type w⦄ [CommRing B], forall [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
 Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B 
⧸ I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Shrink.algEquiv_symm_apply`：∀ (R : Type u_1) (α : Type u_2) [inst : Smal
l.{v, u_2} α] [inst_1 : CommSemiring R] [inst_2 : Semiring α]   [inst_3 : Algebr
a R α] (a : α), …
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_symm`：map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.
comap f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_bot`：map_bot : (⊥ : Ideal R).map f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `equivShrink_symm_sub`：∀ {α : Type u_2} [inst : Small.{v, u_2} α] [inst_1
 : Sub α] (x y : Shrink.{v, u_2} α),   (equivShrink α).symm (x - y) = (equivShri
nk α).symm…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.Quotient.instSmallQuotient`：∀ {R : Type u_3} {M : Type u_4} [i
nst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} [Small.{u, u_4}…
· 使用定理 `TensorProduct.instSmall`：∀ {R : Type u_22} {M : Type u_23} {N : Type u_2
4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : …
· 使用定理 `AlgHom.ker_kerSquareLift`：∀ {R : Type u} [inst : CommRing R] {A : Type u
_1} {B : Type u_2} [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algeb
ra R A] [inst_…
· 使用定理 `Ideal.cotangentIdeal_square`：cotangentIdeal_square (I : Ideal R) : I.cot
angentIdeal ^ 2 = ⊥
（共 37 条，此处仅展示前 30 条）
-/
theorem iff_comp_injective_of_small [Small.{w} A] :
    FormallyUnramified R A ↔
      ∀ ⦃B : Type w⦄ [CommRing B],
        ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  constructor
  · intros; exact comp_injective _ ‹_›
  · intro H
    replace H : ∀ ⦃B : Type u⦄ [CommRing B] [Small.{w} B],
        ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
      intro B _ _ _ I hI f g e
      simpa [DFunLike.ext_iff] using H (B := Shrink B) (I.comap (Shrink.ringEquiv _))
        (by rw [← Ideal.map_symm, ← Ideal.map_pow, hI]; simp)
        (a₁ := (Shrink.algEquiv _ _).symm.toAlgHom.comp f)
        (a₂ := (Shrink.algEquiv _ _).symm.toAlgHom.comp g)
        (by simpa [DFunLike.ext_iff, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Shrink.ringEquiv] using e)
    constructor
    by_contra! h
    obtain ⟨f₁, f₂, e⟩ := (KaehlerDifferential.endEquiv R A).injective.nontrivial
    apply e
    ext1
    let f := RingHom.ker (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom
    refine H
      (RingHom.ker (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom) ?_ ?_
    · rw [AlgHom.ker_kerSquareLift]
      exact Ideal.cotangentIdeal_square _
    · ext x
      apply RingHom.kerLift_injective (TensorProduct.lmul' R (S := A)).kerSquareLift.toRingHom
      simpa using DFunLike.congr_fun (f₁.2.trans f₂.2.symm) x

/-- A version without stray universes that is more easy to rewrite with. -/
/-
**Algebra.FormallyUnramified.iff_comp_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.FormallyUnramified`。
形式化陈述：iff_comp_injective : FormallyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRin
g B], forall [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥), Function.Injective ((I
deal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective_of_small`：iff_comp_injecti
ve_of_small [Small.{w} A] : FormallyUnramified R A ↔ forall ⦃B : Type w⦄ [CommRi
ng B], forall [Algebra R B] (I : Ideal B) (_…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
A version without stray universes that is more easy to rewrite with.
-/
theorem iff_comp_injective :
    FormallyUnramified R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B],
        ∀ [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  iff_comp_injective_of_small
/-
**Algebra.FormallyUnramified.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Form
allyUnramified`。
形式化陈述：lift_unique [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g
₁ g₂ : A ->ₐ[R] B) (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R
 I).comp g₂) : g₁ = g₂
参数：I : Ideal B；hI : IsNilpotent I；g₁ g₂ : A ->ₐ[R] B；h : (Ideal.Quotient.mkₐ R I
).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsNilpotent.induction_on`：Ideal.IsNilpotent.induction_on (hI : IsN
ilpotent I) {P : forall ⦃S : Type _⦄ [CommRing S], Ideal S -> Prop} (h₁ : forall
 ⦃S : Type _⦄ [CommR…
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.mem_quotient_iff_mem`：mem_quotient_iff_mem {I J : Ideal R} [I.IsTw
oSided] (hIJ : I <= J) {x : R} : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in
 J
-/
theorem lift_unique
    [FormallyUnramified R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A →ₐ[R] B)
    (h : (Ideal.Quotient.mkₐ R I).comp g₁ = (Ideal.Quotient.mkₐ R I).comp g₂) : g₁ = g₂ := by
  revert g₁ g₂
  change Function.Injective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallyUnramified.comp_injective I hI
  · intro B _ I J hIJ h₁ h₂ _ g₁ g₂ e
    apply h₁
    apply h₂
    ext x
    replace e := AlgHom.congr_fun e x
    dsimp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e ⊢
    rwa [Ideal.Quotient.eq, ← map_sub, Ideal.mem_quotient_iff_mem hIJ, ← Ideal.Quotient.eq]
/-
**Algebra.FormallyUnramified.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyUnra
mified`。
形式化陈述：ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A ->ₐ[R] B} (H 
: forall x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂
参数：hI : IsNilpotent I；H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.
mk I (g₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyUnramified.lift_unique`：lift_unique [FormallyUnramified 
R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A ->ₐ[R] B) (h : (Ideal.Quotien
t.mkₐ R I).comp g₁ = (Ideal.…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
-/
theorem ext [FormallyUnramified R A] (hI : IsNilpotent I) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique I hI g₁ g₂ (AlgHom.ext H)
/-
**Algebra.FormallyUnramified.lift_unique_of_ringHom** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.FormallyUnramified`。
形式化陈述：lift_unique_of_ringHom [FormallyUnramified R A] {C : Type*} [Ring C] (f : 
B ->+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A ->ₐ[R] B) (h : f.comp ↑
g₁ = f.comp (g₂ : A ->+* B)) : g₁ = g₂
参数：f : B ->+* C；hf : IsNilpotent <| RingHom.ker f；g₁ g₂ : A ->ₐ[R] B；h : f.comp 
↑g₁ = f.comp (g₂ : A ->+* B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.FormallyUnramified.lift_unique`：lift_unique [FormallyUnramified 
R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A ->ₐ[R] B) (h : (Ideal.Quotien
t.mkₐ R I).comp g₁ = (Ideal.…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem lift_unique_of_ringHom [FormallyUnramified R A] {C : Type*} [Ring C]
    (f : B →+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B)
    (h : f.comp ↑g₁ = f.comp (g₂ : A →+* B)) : g₁ = g₂ :=
  FormallyUnramified.lift_unique _ hf _ _
    (by
      ext x
      have := RingHom.congr_fun h x
      simpa only [Ideal.Quotient.eq, Function.comp_apply, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        RingHom.mem_ker, map_sub, sub_eq_zero])
/-
**Algebra.FormallyUnramified.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyUnr
amified`。
形式化陈述：ext' [FormallyUnramified R A] {C : Type*} [Ring C] (f : B ->+* C) (hf : Is
Nilpotent <| RingHom.ker f) (g₁ g₂ : A ->ₐ[R] B) (h : forall x, f (g₁ x) = f (g₂
 x)) : g₁ = g₂
参数：f : B ->+* C；hf : IsNilpotent <| RingHom.ker f；g₁ g₂ : A ->ₐ[R] B；h : forall 
x, f (g₁ x) = f (g₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FormallyUnramified.lift_unique_of_ringHom`：lift_unique_of_ringHo
m [FormallyUnramified R A] {C : Type*} [Ring C] (f : B ->+* C) (hf : IsNilpotent
 <| RingHom.ker f) (g₁ g₂ : A ->ₐ[R] B)…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem ext' [FormallyUnramified R A] {C : Type*} [Ring C] (f : B →+* C)
    (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A →ₐ[R] B) (h : ∀ x, f (g₁ x) = f (g₂ x)) :
    g₁ = g₂ :=
  FormallyUnramified.lift_unique_of_ringHom f hf g₁ g₂ (RingHom.ext h)
/-
**Algebra.FormallyUnramified.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.For
mallyUnramified`。
形式化陈述：lift_unique' [FormallyUnramified R A] {C : Type*} [Ring C] [Algebra R C] (
f : B ->ₐ[R] C) (hf : IsNilpotent <| RingHom.ker (f : B ->+* C)) (g₁ g₂ : A ->ₐ[
R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂
参数：f : B ->ₐ[R] C；hf : IsNilpotent <| RingHom.ker (f : B ->+* C)；g₁ g₂ : A ->ₐ[R
] B；h : f.comp g₁ = f.comp g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.FormallyUnramified.ext'`：ext' [FormallyUnramified R A] {C : Type
*} [Ring C] (f : B ->+* C) (hf : IsNilpotent <| RingHom.ker f) (g₁ g₂ : A ->ₐ[R]
 B) (h : forall x, f …
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem lift_unique' [FormallyUnramified R A] {C : Type*} [Ring C]
    [Algebra R C] (f : B →ₐ[R] C) (hf : IsNilpotent <| RingHom.ker (f : B →+* C))
    (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ :=
  FormallyUnramified.ext' _ hf g₁ g₂ (AlgHom.congr_fun h)
/-
**Algebra.FormallyUnramified.ext_of_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Form
allyUnramified`。
形式化陈述：ext_of_iInf [FormallyUnramified R A] (hI : ⨅ i, I ^ i = ⊥) {g₁ g₂ : A ->ₐ[
R] B} (H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : 
g₁ = g₂
参数：hI : ⨅ i, I ^ i = ⊥；H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient
.mk I (g₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Algebra.FormallyUnramified.ext`：ext [FormallyUnramified R A] (hI : IsNil
potent I) {g₁ g₂ : A ->ₐ[R] B} (H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal
.Quotient.mk I (g₂ x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Ideal.mem_iInf`：mem_iInf {ι : Sort*} {I : ι -> Ideal R} {x : R} : x in i
Inf I ↔ forall i, x in I i
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem ext_of_iInf [FormallyUnramified R A] (hI : ⨅ i, I ^ i = ⊥) {g₁ g₂ : A →ₐ[R] B}
    (H : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x)) : g₁ = g₂ := by
  have (i : ℕ) :
      (Ideal.Quotient.mkₐ R (I ^ i)).comp g₁ = (Ideal.Quotient.mkₐ R (I ^ i)).comp g₂ := by
    by_cases hi : i = 0
    · ext x
      have : Subsingleton (B ⧸ I ^ i) := by
        rw [hi, pow_zero, Ideal.one_eq_top]
        infer_instance
      exact Subsingleton.elim _ _
    apply ext (I.map (algebraMap _ _)) ⟨i, by simp [← Ideal.map_pow]⟩
    intro x
    dsimp
    rw [Ideal.Quotient.eq, ← map_sub, ← Ideal.mem_comap, Ideal.comap_map_of_surjective',
      sup_eq_left.mpr, ← Ideal.Quotient.eq]
    · exact H _
    · simpa using Ideal.pow_le_self hi
    · exact Ideal.Quotient.mk_surjective
  ext x
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hI, Ideal.mem_iInf]
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact DFunLike.congr_fun (this i) x

end

/-
**Algebra.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyUnramif
ied`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u} [CommRing R] : FormallyUnramified R R := by
  rw [iff_comp_injective]
  intro B _ _ _ _ f₁ f₂ _
  exact Subsingleton.elim _ _

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-
**Algebra.FormallyUnramified.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Formall
yUnramified`。
形式化陈述：of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) : FormallyUnramified R B
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_id`：comp_id : φ.comp (AlgHom.id R A) = φ
· 使用定理 `AlgEquiv.comp_symm`：comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ ->
ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
-/
theorem of_equiv [FormallyUnramified R A] (e : A ≃ₐ[R] B) :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e'
  rw [← f₁.comp_id, ← f₂.comp_id, ← e.comp_symm, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
  congr 1
  refine FormallyUnramified.comp_injective I hI ?_
  rw [← AlgHom.comp_assoc, e', AlgHom.comp_assoc]

end OfEquiv

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-
**Algebra.FormallyUnramified.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyUnr
amified`。
形式化陈述：comp [FormallyUnramified R A] [FormallyUnramified A B] : FormallyUnramifie
d R B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `Algebra.FormallyUnramified.lift_unique`：lift_unique [FormallyUnramified 
R A] (I : Ideal B) (hI : IsNilpotent I) (g₁ g₂ : A ->ₐ[R] B) (h : (Ideal.Quotien
t.mkₐ R I).comp g₁ = (Ideal.…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Algebra.FormallyUnramified.ext`：ext [FormallyUnramified R A] (hI : IsNil
potent I) {g₁ g₂ : A ->ₐ[R] B} (H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal
.Quotient.mk I (g₂ x…
-/
theorem comp [FormallyUnramified R A] [FormallyUnramified A B] :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e
  have e' :=
    FormallyUnramified.lift_unique I ⟨2, hI⟩ (f₁.comp <| IsScalarTower.toAlgHom R A B)
      (f₂.comp <| IsScalarTower.toAlgHom R A B) (by rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc])
  let := (f₁.domRestrict A).toAlgebra
  let F₁ : B →ₐ[A] C := { f₁ with commutes' := fun r => rfl }
  let F₂ : B →ₐ[A] C := { f₂ with commutes' := AlgHom.congr_fun e'.symm }
  ext1 x
  change F₁ x = F₂ x
  congr
  exact FormallyUnramified.ext I ⟨2, hI⟩ (AlgHom.congr_fun e)
/-
**Algebra.FormallyUnramified.of_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
ra.FormallyUnramified`。
形式化陈述：of_restrictScalars [FormallyUnramified R B] : FormallyUnramified A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `AlgHom.restrictScalars_injective`：restrictScalars_injective : Function.I
njective (restrictScalars R : (A ->ₐ[S] B) -> A ->ₐ[R] B)
· 使用定理 `Algebra.FormallyUnramified.ext`：ext [FormallyUnramified R A] (hI : IsNil
potent I) {g₁ g₂ : A ->ₐ[R] B} (H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal
.Quotient.mk I (g₂ x…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
theorem of_restrictScalars [FormallyUnramified R B] : FormallyUnramified A B := by
  rw [iff_comp_injective]
  intro Q _ _ I e f₁ f₂ e'
  let := ((algebraMap A Q).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A Q := IsScalarTower.of_algebraMap_eq' rfl
  refine AlgHom.restrictScalars_injective R ?_
  refine FormallyUnramified.ext I ⟨2, e⟩ ?_
  intro x
  exact AlgHom.congr_fun e' x

end Comp

section of_surjective

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- This holds in general for epimorphisms. -/
/-
**Algebra.FormallyUnramified.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallyUnramified`。
形式化陈述：of_surjective [FormallyUnramified R A] (f : A ->ₐ[R] B) (H : Function.Surj
ective f) : FormallyUnramified R B
参数：f : A ->ₐ[R] B；H : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `Algebra.FormallyUnramified.comp_injective`：comp_injective [FormallyUnram
ified R A] (hI : I ^ 2 = ⊥) : Function.Injective ((Ideal.Quotient.mkₐ R I).comp 
: (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
This holds in general for epimorphisms.
-/
theorem of_surjective [FormallyUnramified R A] (f : A →ₐ[R] B) (H : Function.Surjective f) :
    FormallyUnramified R B := by
  rw [iff_comp_injective]
  intro Q _ _ I hI f₁ f₂ e
  ext x
  obtain ⟨x, rfl⟩ := H x
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply FormallyUnramified.comp_injective I hI
  ext x; exact DFunLike.congr_fun e (f x)
/-
**Algebra.FormallyUnramified.quotient** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Formall
yUnramified`。
形式化陈述：quotient {A} [CommRing A] [Algebra R A] [FormallyUnramified R A] (I : Idea
l A) : FormallyUnramified R (A ⧸ I)
参数：I : Ideal A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_surjective`：of_surjective [FormallyUnramif
ied R A] (f : A ->ₐ[R] B) (H : Function.Surjective f) : FormallyUnramified R B
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
instance quotient {A} [CommRing A] [Algebra R A] [FormallyUnramified R A] (I : Ideal A) :
    FormallyUnramified R (A ⧸ I) :=
  FormallyUnramified.of_surjective (IsScalarTower.toAlgHom R A (A ⧸ I)) Ideal.Quotient.mk_surjective
/-
**Algebra.FormallyUnramified.iff_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.For
mallyUnramified`。
形式化陈述：iff_of_equiv (e : A ≃ₐ[R] B) : FormallyUnramified R A ↔ FormallyUnramified
 R B
参数：e : A ≃ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_equiv`：of_equiv [FormallyUnramified R A] (
e : A ≃ₐ[R] B) : FormallyUnramified R B
-/
theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyUnramified R A ↔ FormallyUnramified R B :=
  ⟨fun _ ↦ of_equiv e, fun _ ↦ of_equiv e.symm⟩

end of_surjective

section BaseChange


variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

/-
**Algebra.FormallyUnramified.base_change** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Form
allyUnramified`。
形式化陈述：base_change [FormallyUnramified R A] : FormallyUnramified B (B otimes[R] A
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `Algebra.FormallyUnramified.ext`：ext [FormallyUnramified R A] (hI : IsNil
potent I) {g₁ g₂ : A ->ₐ[R] B} (H : forall x, Ideal.Quotient.mk I (g₁ x) = Ideal
.Quotient.mk I (g₂ x…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
-/
instance base_change [FormallyUnramified R A] :
    FormallyUnramified B (B ⊗[R] A) := by
  rw [iff_comp_injective]
  intro C _ _ I hI f₁ f₂ e
  let := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  exact FormallyUnramified.ext I ⟨2, hI⟩ fun x => AlgHom.congr_fun e (1 ⊗ₜ x)
/-
**Algebra.FormallyUnramified.quotient_map** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.For
mallyUnramified`。
形式化陈述：quotient_map [FormallyUnramified R B] (p : Ideal R) : FormallyUnramified (
R ⧸ p) (B ⧸ p.map (algebraMap R B))
参数：p : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_equiv`：of_equiv [FormallyUnramified R A] (
e : A ≃ₐ[R] B) : FormallyUnramified R B
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance quotient_map [FormallyUnramified R B] (p : Ideal R) :
    FormallyUnramified (R ⧸ p) (B ⧸ p.map (algebraMap R B)) :=
  .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p).symm

end BaseChange

section Localization

variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
variable [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

/-- This holds in general for epimorphisms. -/
/-
**Algebra.FormallyUnramified.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.FormallyUnramified`。
形式化陈述：of_isLocalization [IsLocalization M Rₘ] : FormallyUnramified R Rₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `AlgHom.coe_ringHom_injective`：coe_ringHom_injective : Function.Injective
 ((↑) : (A ->ₐ[R] B) -> A ->+* B)
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This holds in general for epimorphisms.
-/
theorem of_isLocalization [IsLocalization M Rₘ] : FormallyUnramified R Rₘ := by
  rw [iff_comp_injective]
  intro Q _ _ I _ f₁ f₂ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp
/-
**Algebra.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyUnramif
ied`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FormallyUnramified R S] (M : Submonoid S) : FormallyUnramified R (Localization M) :=
  have := of_isLocalization (Rₘ := Localization M) M
  .comp _ S _

set_option linter.unusedSectionVars false in
/-- This actually does not need the localization instance, and is stated here again for
consistency. See `Algebra.FormallyUnramified.of_comp` instead.

The intended use is for copying proofs between `Formally{Unramified, Smooth, Etale}`
without the need to change anything (including removing redundant arguments). -/
@[nolint unusedArguments]
/-
**Algebra.FormallyUnramified.localization_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.FormallyUnramified`。
形式化陈述：localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_restrictScalars`：of_restrictScalars [Forma
llyUnramified R B] : FormallyUnramified A B

--- 原说明 ---
This actually does not need the localization instance, and is stated here again 
for
consistency. See `Algebra.FormallyUnramified.of_comp` instead.

The intended use is for copying proofs between `Formally{Unramified, Smooth, Eta
le}`
without the need to change anything (including removing redundant arguments).
-/
theorem localization_base [FormallyUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ :=
  FormallyUnramified.of_restrictScalars R Rₘ Sₘ
/-
**Algebra.FormallyUnramified.localization_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.FormallyUnramified`。
形式化陈述：localization_map [FormallyUnramified R S] : FormallyUnramified Rₘ Sₘ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.FormallyUnramified.of_isLocalization`：of_isLocalization [IsLocal
ization M Rₘ] : FormallyUnramified R Rₘ
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.FormallyUnramified.localization_base`：localization_base [Formall
yUnramified R Sₘ] : FormallyUnramified Rₘ Sₘ
-/
theorem localization_map [FormallyUnramified R S] :
    FormallyUnramified Rₘ Sₘ := by
  have : FormallyUnramified S Sₘ :=
    FormallyUnramified.of_isLocalization (M.map (algebraMap R S))
  have : FormallyUnramified R Sₘ := FormallyUnramified.comp R S Sₘ
  exact FormallyUnramified.localization_base M

end Localization

/-- If `S` is an unramified `R`-algebra, `S ⊗[R] S` splits as `S × T` for some `R`-algebra `T`.
In particular, the diagonal is an open and closed immersion. -/
/-
**Algebra.FormallyUnramified.exists_algEquiv_prod** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.FormallyUnramified`。
形式化陈述：exists_algEquiv_prod (R S : Type u) [CommRing R] [CommRing S] [Algebra R S
] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] : exists (T : Typ
e u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S otimes[R] S ≃ₐ[S] S × T)
参数：R S : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isIdempotentElem_iff_of_fg`：isIdempotentElem_iff_of_fg {R : Type*}
 [CommRing R] (I : Ideal R) (h : I.FG) : IsIdempotentElem I ↔ exists e : R, IsId
empotentElem e ∧ I = R…
· 使用定理 `KaehlerDifferential.ideal_fg`：KaehlerDifferential.ideal_fg [EssFiniteTyp
e R S] : (KaehlerDifferential.ideal R S).FG
· 使用定理 `Ideal.cotangent_subsingleton_iff`：cotangent_subsingleton_iff : Subsingle
ton I.Cotangent ↔ IsIdempotentElem I
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsIdempotentElem.mul_one_sub_self`：mul_one_sub_self (h : IsIdempotentEle
m a) : a * (1 - a) = 0
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
If `S` is an unramified `R`-algebra, `S ⊗[R] S` splits as `S × T` for some `R`-a
lgebra `T`.
In particular, the diagonal is an open and closed immersion.
-/
lemma exists_algEquiv_prod (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T), Nonempty (S ⊗[R] S ≃ₐ[S] S × T) := by
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal R S = S ⊗[R] S ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[S⁄R]
  let e₁ := AlgEquiv.prodQuotientOfIsIdempotentElem (R := S) he he.one_sub (by simp) (by simp [he])
  let e₂ : (S ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[S] S :=
    ((Ideal.span {e}).quotientEquivAlgOfEq S hsp.symm).trans <|
      Ideal.quotientKerAlgEquivOfSurjective <|
        (⟨· ⊗ₜ 1, by simp [Algebra.TensorProduct.lmul'']⟩)
  exact ⟨(S ⊗[R] S) ⧸ Ideal.span {1 - e}, inferInstance, inferInstance,
    ⟨e₁.trans (.prodCongr e₂ .refl)⟩⟩

end FormallyUnramified

section

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- An `R`-algebra `A` is unramified if it is formally unramified and of finite type. -/
@[stacks 00UT "Note that the Stacks project has a different definition of unramified, and tag
<https://stacks.math.columbia.edu/tag/00UU> shows that their definition is the same as this one."]
/-
**Algebra.Unramified** 是 Mathlib 中的一个类，位于命名空间 `Algebra`。
形式化陈述：Unramified : Prop where formallyUnramified : FormallyUnramified R A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class Unramified : Prop where
  formallyUnramified : FormallyUnramified R A := by infer_instance
  finiteType : FiniteType R A := by infer_instance

end

namespace Unramified

attribute [instance] formallyUnramified finiteType

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Being unramified is transported via algebra isomorphisms. -/
/-
**Algebra.Unramified.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Unramified`。
形式化陈述：of_equiv [Unramified R A] (e : A ≃ₐ[R] B) : Unramified R B where formallyU
nramified
参数：e : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_equiv`：of_equiv [FormallyUnramified R A] (
e : A ≃ₐ[R] B) : FormallyUnramified R B
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.FiniteType.equiv`：equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) :
 FiniteType R B
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…

--- 原说明 ---
Being unramified is transported via algebra isomorphisms.
-/
theorem of_equiv [Unramified R A] (e : A ≃ₐ[R] B) : Unramified R B where
  formallyUnramified := FormallyUnramified.of_equiv e
  finiteType := FiniteType.equiv Unramified.finiteType e

/-- Localization at an element is unramified. -/
/-
**Algebra.Unramified.of_isLocalization_Away** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.U
nramified`。
形式化陈述：of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Unramified R A 
where formallyUnramified
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_isLocalization`：of_isLocalization [IsLocal
ization M Rₘ] : FormallyUnramified R Rₘ
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S

--- 原说明 ---
Localization at an element is unramified.
-/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Unramified R A where
  formallyUnramified := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers r)
  finiteType :=
    haveI : FinitePresentation R A := IsLocalization.Away.finitePresentation r
    inferInstance

section Comp

variable (R A B)

/-- Unramified is stable under composition. -/
/-
**Algebra.Unramified.comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Unramified`。
形式化陈述：comp [Algebra A B] [IsScalarTower R A B] [Unramified R A] [Unramified A B]
 : Unramified R B where formallyUnramified
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.comp`：comp [FormallyUnramified R A] [Formally
Unramified A B] : FormallyUnramified R B
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.FiniteType.trans`：trans [Algebra S A] [IsScalarTower R S A] (hRS
 : FiniteType R S) (hSA : FiniteType S A) : FiniteType R A
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…

--- 原说明 ---
Unramified is stable under composition.
-/
theorem comp [Algebra A B] [IsScalarTower R A B] [Unramified R A] [Unramified A B] :
    Unramified R B where
  formallyUnramified := FormallyUnramified.comp R A B
  finiteType := FiniteType.trans (S := A) Unramified.finiteType
    Unramified.finiteType

/-- Unramified is stable under base change. -/
/-
**Algebra.Unramified.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Unramified`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] (A : Type u_2) (B : Type u_3) [inst_1
 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : Algebra 
R B] [Algebra.Unramified R A], Algebra.Unramified B (TensorProduct R B A)
参数：R : Type u_1；A : Type u_2；B : Type u_3；TensorProduct R B A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…

--- 原说明 ---
Unramified is stable under base change.
-/
instance baseChange [Unramified R A] : Unramified B (B ⊗[R] A) where

end Comp

end Unramified

end Algebra

