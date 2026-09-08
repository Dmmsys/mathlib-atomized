/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Algebraic independence persists to the algebraic closure

## Main results

* `AlgebraicIndependent.extendScalars`: if A/S/R is a tower of algebras with S/R algebraic,
  then a family of elements in A that are algebraically independent over R remains algebraically
  independent over S, provided that S has no zero divisors.

* `AlgebraicIndependent.algebraicClosure`: an algebraically independent family remains
  algebraically independent over the algebraic closure.
-/

public section

open Function Algebra

section

variable {ι R S A : Type*} {x : ι → A} (S)
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [NoZeroDivisors S] (hx : AlgebraicIndependent R x)
include hx

namespace AlgebraicIndependent

/-
**AlgebraicIndependent.extendScalars** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndepen
dent`。
形式化陈述：extendScalars [alg : Algebra.IsAlgebraic R S] : AlgebraicIndependent S x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicIndependent_of_finite_type'`：algebraicIndependent_of_finite_typ
e' (hinj : Injective (algebraMap R A)) (H : forall t : Set ι, t.Finite -> Algebr
aicIndependent R (fun i : …
· 使用定理 `Algebra.IsAlgebraic.injective_tower_top`：injective_tower_top (inj : Inje
ctive (algebraMap R A)) : Injective (algebraMap S A)
· 使用定理 `AlgebraicIndependent.algebraMap_injective`：algebraMap_injective : Inject
ive (algebraMap R A)
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Function.Injective.noZeroDivisors`：∀ {M₀ : Type u_1} {M₀' : Type u_3} [i
nst : Mul M₀] [inst_1 : Zero M₀] [inst_2 : Mul M₀'] [inst_3 : Zero M₀']   (f : M
₀ → M₀'),   Function.In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `Subalgebra.inclusion_injective`：inclusion_injective : Function.Injective
 (inclusion h)
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAlgebraic_algHom_iff`：isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Fu
nction.Injective f) {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Algebra.IsAlgebraic.nontrivial`：Algebra.IsAlgebraic.nontrivial [alg : Al
gebra.IsAlgebraic R A] : Nontrivial R
（共 41 条，此处仅展示前 30 条）
-/
theorem extendScalars [alg : Algebra.IsAlgebraic R S] : AlgebraicIndependent S x := by
  refine algebraicIndependent_of_finite_type'
    (Algebra.IsAlgebraic.injective_tower_top S hx.algebraMap_injective) fun t fin ind i hi ↦ ?_
  let Rt := adjoin R (x '' t)
  let St := adjoin S (x '' t)
  let _ : Algebra Rt St :=
    (Rt.inclusion (T := St.restrictScalars R) <| adjoin_le <| by exact subset_adjoin).toAlgebra
  have : IsScalarTower Rt St A := .of_algebraMap_eq fun ⟨y, _⟩ ↦ show y = y from rfl
  have : NoZeroDivisors St := (Set.image_eq_range _ _ ▸ ind.aevalEquiv)
    |>.symm.injective.noZeroDivisors _ (map_zero _) (map_mul _)
  have : NoZeroDivisors Rt := (Subalgebra.inclusion_injective _).noZeroDivisors
    (algebraMap Rt St) (map_zero _) (map_mul _)
  have : Algebra.IsAlgebraic Rt St := ⟨fun ⟨y, hy⟩ ↦ by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom Rt St A) Subtype.val_injective]
    change IsAlgebraic Rt y
    have := Algebra.IsAlgebraic.nontrivial R S
    have := hx.algebraMap_injective.nontrivial
    exact adjoin_induction (fun _ h ↦ isAlgebraic_algebraMap (⟨_, subset_adjoin h⟩ : Rt))
      (fun z ↦ ((alg.1 z).algHom (IsScalarTower.toAlgHom R S A)).extendScalars fun _ _ eq ↦ by
        exact hx.algebraMap_injective congr($eq.1)) (fun _ _ _ _ ↦ .add) (fun _ _ _ _ ↦ .mul) hy⟩
  change Transcendental St (x i)
  exact (hx.transcendental_adjoin hi).extendScalars _
/-
**AlgebraicIndependent.extendScalars_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicIndependent`。
形式化陈述：extendScalars_of_isIntegral [Algebra.IsIntegral R S] : AlgebraicIndependen
t S x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `AlgebraicIndependent.extendScalars`：extendScalars [alg : Algebra.IsAlgeb
raic R S] : AlgebraicIndependent S x
-/
theorem extendScalars_of_isIntegral [Algebra.IsIntegral R S] : AlgebraicIndependent S x := by
  nontriviality S
  have := Module.nontrivial R S
  exact hx.extendScalars S
/-
**AlgebraicIndependent.subalgebraAlgebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicIndependent`。
形式化陈述：subalgebraAlgebraicClosure [IsDomain R] [NoZeroDivisors A] : AlgebraicInde
pendent (Subalgebra.algebraicClosure R A) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.extendScalars`：extendScalars [alg : Algebra.IsAlgeb
raic R S] : AlgebraicIndependent S x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsAlgebraicSubtypeMemSubalgebraAlgebraicClosure`：∀ (R : Type u_1) (S
 : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [i
nst_3 : IsDomain R],   Algebra.IsAlgebrai…
-/
theorem subalgebraAlgebraicClosure [IsDomain R] [NoZeroDivisors A] :
    AlgebraicIndependent (Subalgebra.algebraicClosure R A) x :=
  hx.extendScalars _
/-
**AlgebraicIndependent.integralClosure** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicIndep
endent`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {A : Type u_4} {x : ι → A} [inst : CommRin
g R] [inst_1 : CommRing A]   [inst_2 : Algebra R A],   AlgebraicIndependent R x 
→ ∀ [NoZeroDivisors A], AlgebraicIndependent (↥(integralClosure R A)) x
参数：↥(integralClosure R A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.extendScalars_of_isIntegral`：extendScalars_of_isInt
egral [Algebra.IsIntegral R S] : AlgebraicIndependent S x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
protected theorem integralClosure [NoZeroDivisors A] :
    AlgebraicIndependent (integralClosure R A) x :=
  hx.extendScalars_of_isIntegral _

omit hx in
/-
**AlgebraicIndependent.algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicInde
pendent`。
形式化陈述：∀ {ι : Type u_1} {F : Type u_5} {E : Type u_6} [inst : Field F] [inst_1 : 
Field E] [inst_2 : Algebra F E] {x : ι → E},   AlgebraicIndependent F x → Algebr
aicIndependent (↥(algebraicClosure F E)) x
参数：↥(algebraicClosure F E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.extendScalars`：extendScalars [alg : Algebra.IsAlgeb
raic R S] : AlgebraicIndependent S x
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
protected theorem algebraicClosure {F E : Type*} [Field F] [Field E] [Algebra F E] {x : ι → E}
    (hx : AlgebraicIndependent F x) : AlgebraicIndependent (algebraicClosure F E) x :=
  hx.extendScalars _

end AlgebraicIndependent

namespace Algebra

variable (R) [FaithfulSMul R S]
omit hx

/-
**Algebra.IsIntegral.algebraicIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsIntegral`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) 
[inst : CommRing R] [inst_1 : CommRing S]   [inst_2 : CommRing A] [inst_3 : Alge
bra R S] [inst_4 : Algebra R A] [inst_5 : Algebra S A] [IsScalarTower R S A]   [
NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsIntegral R S], AlgebraicIndepend
ent R x ↔ AlgebraicIndependent S x
参数：R : Type u_2；S : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.extendScalars_of_isIntegral`：extendScalars_of_isInt
egral [Algebra.IsIntegral R S] : AlgebraicIndependent S x
· 使用定理 `AlgebraicIndependent.restrictScalars`：AlgebraicIndependent.restrictScala
rs {K : Type*} [CommRing K] [Algebra R K] [Algebra K A] [IsScalarTower R K A] (h
inj : Function.Injective (…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
protected theorem IsIntegral.algebraicIndependent_iff [Algebra.IsIntegral R S] :
    AlgebraicIndependent R x ↔ AlgebraicIndependent S x :=
  ⟨(·.extendScalars_of_isIntegral _),
    (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
/-
**Algebra.IsIntegral.isTranscendenceBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsIntegral`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) 
[inst : CommRing R] [inst_1 : CommRing S]   [inst_2 : CommRing A] [inst_3 : Alge
bra R S] [inst_4 : Algebra R A] [inst_5 : Algebra S A] [IsScalarTower R S A]   [
NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsIntegral R S], IsTranscendenceBa
sis R x ↔ IsTranscendenceBasis S x
参数：R : Type u_2；S : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.IsIntegral.algebraicIndependent_iff`：∀ {ι : Type u_1} (R : Type 
u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) [inst : CommRing R] [inst_1 : Com
mRing S]   [inst_2 : CommRing A] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem IsIntegral.isTranscendenceBasis_iff [Algebra.IsIntegral R S] :
    IsTranscendenceBasis R x ↔ IsTranscendenceBasis S x := by
  simp_rw [IsTranscendenceBasis, IsIntegral.algebraicIndependent_iff R S]
/-
**Algebra.IsAlgebraic.algebraicIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.IsAlgebraic`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) 
[inst : CommRing R] [inst_1 : CommRing S]   [inst_2 : CommRing A] [inst_3 : Alge
bra R S] [inst_4 : Algebra R A] [inst_5 : Algebra S A] [IsScalarTower R S A]   [
NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S], AlgebraicIndepen
dent R x ↔ AlgebraicIndependent S x
参数：R : Type u_2；S : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicIndependent.extendScalars`：extendScalars [alg : Algebra.IsAlgeb
raic R S] : AlgebraicIndependent S x
· 使用定理 `AlgebraicIndependent.restrictScalars`：AlgebraicIndependent.restrictScala
rs {K : Type*} [CommRing K] [Algebra R K] [Algebra K A] [IsScalarTower R K A] (h
inj : Function.Injective (…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
protected theorem IsAlgebraic.algebraicIndependent_iff [Algebra.IsAlgebraic R S] :
    AlgebraicIndependent R x ↔ AlgebraicIndependent S x :=
  ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩
/-
**Algebra.IsAlgebraic.isTranscendenceBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.IsAlgebraic`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) 
[inst : CommRing R] [inst_1 : CommRing S]   [inst_2 : CommRing A] [inst_3 : Alge
bra R S] [inst_4 : Algebra R A] [inst_5 : Algebra S A] [IsScalarTower R S A]   [
NoZeroDivisors S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S], IsTranscendenceB
asis R x ↔ IsTranscendenceBasis S x
参数：R : Type u_2；S : Type u_5。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.IsAlgebraic.algebraicIndependent_iff`：∀ {ι : Type u_1} (R : Type
 u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) [inst : CommRing R] [inst_1 : Co
mmRing S]   [inst_2 : CommRing A] …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem IsAlgebraic.isTranscendenceBasis_iff [Algebra.IsAlgebraic R S] :
    IsTranscendenceBasis R x ↔ IsTranscendenceBasis S x := by
  simp_rw [IsTranscendenceBasis, IsAlgebraic.algebraicIndependent_iff R S]

end Algebra

end

namespace IntermediateField

variable {ι F E R S : Type*} {s : Set E}
variable [Field F] [Field E] [Algebra F E]
variable [CommRing R] [Algebra R F] [Algebra R E] [IsScalarTower R F E]

open scoped algebraAdjoinAdjoin

section Ring

variable [Ring S] [Algebra E S]

/-
**IntermediateField.isAlgebraic_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：isAlgebraic_adjoin_iff {x : S} : IsAlgebraic (adjoin F s) x ↔ IsAlgebraic 
(Algebra.adjoin F s) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic_iff`：∀ (R : Type u_1) (S : Type u_2) {A 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [inst_
3 : Algebra R S] [inst_4 …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin_1`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fi
eld E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : MulAction …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
-/
theorem isAlgebraic_adjoin_iff {x : S} :
    IsAlgebraic (adjoin F s) x ↔ IsAlgebraic (Algebra.adjoin F s) x :=
  (IsAlgebraic.isAlgebraic_iff ..).symm
/-
**IntermediateField.isAlgebraic_adjoin_iff_top** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：isAlgebraic_adjoin_iff_top : Algebra.IsAlgebraic (adjoin F s) S ↔ Algebra.
IsAlgebraic (Algebra.adjoin F s) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic_iff_top`：∀ (R : Type u_1) (S : Type u_2)
 {A : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [i
nst_3 : Algebra R S] [inst_4 …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin_1`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fi
eld E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : MulAction …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
-/
theorem isAlgebraic_adjoin_iff_top :
    Algebra.IsAlgebraic (adjoin F s) S ↔ Algebra.IsAlgebraic (Algebra.adjoin F s) S :=
  (IsAlgebraic.isAlgebraic_iff_top ..).symm
/-
**IntermediateField.isAlgebraic_adjoin_iff_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：isAlgebraic_adjoin_iff_bot : Algebra.IsAlgebraic R (adjoin F s) ↔ Algebra.
IsAlgebraic R (Algebra.adjoin F s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic_iff_bot`：∀ (R : Type u_1) (S : Type u_2)
 {A : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [i
nst_3 : Algebra R S] [inst_4 …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fiel
d E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : SMul X F] …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
-/
theorem isAlgebraic_adjoin_iff_bot :
    Algebra.IsAlgebraic R (adjoin F s) ↔ Algebra.IsAlgebraic R (Algebra.adjoin F s) :=
  IsAlgebraic.isAlgebraic_iff_bot ..
/-
**IntermediateField.transcendental_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：transcendental_adjoin_iff {x : S} : Transcendental (adjoin F s) x ↔ Transc
endental (Algebra.adjoin F s) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.IsAlgebraic.transcendental_iff`：∀ (R : Type u_1) (S : Type u_2) 
{A : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Ring A]   [in
st_3 : Algebra R S] [inst_4 …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin_1`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fi
eld E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : MulAction …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
-/
theorem transcendental_adjoin_iff {x : S} :
    Transcendental (adjoin F s) x ↔ Transcendental (Algebra.adjoin F s) x :=
  (IsAlgebraic.transcendental_iff ..).symm

end Ring

variable [CommRing S] [Algebra E S]

/-
**IntermediateField.algebraicIndependent_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：algebraicIndependent_adjoin_iff {x : ι -> S} : AlgebraicIndependent (adjoi
n F s) x ↔ AlgebraicIndependent (Algebra.adjoin F s) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.IsAlgebraic.algebraicIndependent_iff`：∀ {ι : Type u_1} (R : Type
 u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) [inst : CommRing R] [inst_1 : Co
mmRing S]   [inst_2 : CommRing A] …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin_1`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fi
eld E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : MulAction …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
-/
theorem algebraicIndependent_adjoin_iff {x : ι → S} :
    AlgebraicIndependent (adjoin F s) x ↔ AlgebraicIndependent (Algebra.adjoin F s) x :=
  (Algebra.IsAlgebraic.algebraicIndependent_iff ..).symm
/-
**IntermediateField.isTranscendenceBasis_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `I
ntermediateField`。
形式化陈述：isTranscendenceBasis_adjoin_iff {x : ι -> S} : IsTranscendenceBasis (adjoi
n F s) x ↔ IsTranscendenceBasis (Algebra.adjoin F s) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.IsAlgebraic.isTranscendenceBasis_iff`：∀ {ι : Type u_1} (R : Type
 u_2) {A : Type u_4} {x : ι → A} (S : Type u_5) [inst : CommRing R] [inst_1 : Co
mmRing S]   [inst_2 : CommRing A] …
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalge
braAdjoinAdjoin_1`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Fi
eld E] [inst_2 : Algebra F E] (S : Set E) (X : Type u_3)   [inst_3 : MulAction …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instFaithfulSMulSubtypeMemSubalgeb
raAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field
 E] [inst_2 : Algebra F E] (S : Set E),   FaithfulSMul ↥(Algebra.adjoin F S)…
· 使用定理 `IntermediateField.algebraAdjoinAdjoin.instIsAlgebraicSubtypeMemSubalgebr
aAdjoinAdjoin`：∀ (F : Type u_1) [inst : Field F] {E : Type u_2} [inst_1 : Field 
E] [inst_2 : Algebra F E] (S : Set E),   Algebra.IsAlgebraic ↥(Algebra.adjo…
-/
theorem isTranscendenceBasis_adjoin_iff {x : ι → S} :
    IsTranscendenceBasis (adjoin F s) x ↔ IsTranscendenceBasis (Algebra.adjoin F s) x :=
  (Algebra.IsAlgebraic.isTranscendenceBasis_iff ..).symm

end IntermediateField

