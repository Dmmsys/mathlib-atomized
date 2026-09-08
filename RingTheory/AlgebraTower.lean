/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `Mathlib/FieldTheory/Tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is an `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

@[expose] public section

open Module
open scoped Pointwise

variable (R S A B : Type*)

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Suppose that `R → S → A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
@[instance_reducible]
/-
**IsScalarTower.Invertible.algebraTower** 是 Mathlib 中的一个定义，位于命名空间 `IsScalarTower
.Invertible`。
形式化陈述：(R : Type u_1) →   (S : Type u_2) →     (A : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring S] →           [inst_2 : Semiring 
A] →             [inst_3 : Algebra R S] →               [inst_4 : Algebra S A] →
                 [inst_5 : Algebra R A] →                   [IsScalarTower R S A
] → (r : R) → [Invertible ((algebraMap R S) r)] → Invertible ((algebraMap R A) r
)
参数：algebraMap R S；algebraMap R A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)

--- 原说明 ---
Suppose that `R → S → A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`.
-/
def Invertible.algebraTower (r : R) [Invertible (algebraMap R S r)] :
    Invertible (algebraMap R A r) :=
  Invertible.copy (Invertible.map (algebraMap S A) (algebraMap R S r)) (algebraMap R A r)
    (IsScalarTower.algebraMap_apply R S A r)

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
@[instance_reducible]
/-
**IsScalarTower.invertibleAlgebraCoeNat** 是 Mathlib 中的一个定义，位于命名空间 `IsScalarTower
`。
形式化陈述：invertibleAlgebraCoeNat (n : Nat) [inv : Invertible (n : R)] : Invertible 
(n : A)
参数：n : Nat；n : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra.
-/
def invertibleAlgebraCoeNat (n : ℕ) [inv : Invertible (n : R)] : Invertible (n : A) :=
  haveI : Invertible (algebraMap ℕ R n) := inv
  fast_instance% Invertible.algebraTower ℕ R A n

end Semiring
end IsScalarTower

section AlgebraMapCoeffs
namespace Module.Basis
variable {R} {ι M : Type*} [CommSemiring R] [Semiring A] [AddCommMonoid M]
variable [Algebra R A] [Module A M] [Module R M] [IsScalarTower R A M]
variable (b : Basis ι R M) (h : Function.Bijective (algebraMap R A))


/-- If `R` and `A` have a bijective `algebraMap R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps! -isSimp repr_apply_apply]
/-
**Module.Basis.algebraMapCoeffs** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：algebraMapCoeffs : Basis ι A M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` and `A` have a bijective `algebraMap R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.
-/
noncomputable def algebraMapCoeffs : Basis ι A M :=
  b.mapCoeffs (RingEquiv.ofBijective _ h) fun c x => by simp

@[simp]
/-
**Module.Basis.algebraMapCoeffs_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：algebraMapCoeffs_repr (m : M) : (b.algebraMapCoeffs A h).repr m = (b.repr 
m).mapRange (algebraMap R A) (map_zero _)
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMapCoeffs_repr (m : M) :
    (b.algebraMapCoeffs A h).repr m = (b.repr m).mapRange (algebraMap R A) (map_zero _) := by
  rfl
/-
**Module.Basis.algebraMapCoeffs_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：algebraMapCoeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mapCoeffs_apply`：mapCoeffs_apply (i : ι) : b.mapCoeffs f h 
i = b i
-/
theorem algebraMapCoeffs_apply (i : ι) : b.algebraMapCoeffs A h i = b i :=
  b.mapCoeffs_apply _ _ _

@[simp]
/-
**Module.Basis.coe_algebraMapCoeffs** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_algebraMapCoeffs : (b.algebraMapCoeffs A h : ι -> M) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mapCoeffs`：coe_mapCoeffs : (b.mapCoeffs f h : ι -> M) =
 b
-/
theorem coe_algebraMapCoeffs : (b.algebraMapCoeffs A h : ι → M) = b :=
  b.coe_mapCoeffs _ _

end Module.Basis
end AlgebraMapCoeffs

section Semiring

open Finsupp

variable {R S A}
variable [Semiring R] [Semiring S] [AddCommMonoid A]
variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

/-
**linearIndependent_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_smul {ι : Type*} {b : ι -> S} {ι' : Type*} {c : ι' -> A}
 (hb : LinearIndependent R b) (hc : LinearIndependent S c) : LinearIndependent R
 fun p : ι × ι' => b p.1 • c p.2
参数：hb : LinearIndependent R b；hc : LinearIndependent S c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv'`：linearIndependent_equiv' (e : ι ≃ ι') {f : ι' 
-> M} {g : ι -> M} (h : f ∘ e = g) : LinearIndependent R g ↔ LinearIndependent R
 f
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Finsupp.linearCombination_smul`：linearCombination_smul [Module R S] [Mod
ule S M] [IsScalarTower R S M] {w : α' -> S} : linearCombination R (fun i : α × 
α' => w i.2 • v i.1)…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
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
· 使用引理 `Finsupp.mapRange_injective`：mapRange_injective (e : M -> N) (he₀ : e 0 =
 0) (he : Injective e) : Injective (Finsupp.mapRange (α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem linearIndependent_smul {ι : Type*} {b : ι → S} {ι' : Type*} {c : ι' → A}
    (hb : LinearIndependent R b) (hc : LinearIndependent S c) :
    LinearIndependent R fun p : ι × ι' ↦ b p.1 • c p.2 := by
  rw [← linearIndependent_equiv' (.prodComm ..) (g := fun p : ι' × ι ↦ b p.2 • c p.1) rfl,
    LinearIndependent, linearCombination_smul]
  simpa using! Function.Injective.comp hc
    ((mapRange_injective _ (map_zero _) hb).comp <| Equiv.injective _)

variable (R)

namespace Module.Basis

-- LinearIndependent is enough if S is a ring rather than semiring.
/-
**Module.Basis.isScalarTower_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis
`。
形式化陈述：isScalarTower_of_nonempty {ι} [Nonempty ι] (b : Basis ι S A) : IsScalarTow
er R S S
参数：b : Basis ι S A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isScalarTower_of_injective`：isScalarTower_of_injective [SMul R
 S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂] (f : M ->ₗ[S] M₂) (hf : Fun
ction.Injective f) : IsSca…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
theorem isScalarTower_of_nonempty {ι} [Nonempty ι] (b : Basis ι S A) : IsScalarTower R S S :=
  (b.repr.symm.comp <| lsingle <| Classical.arbitrary ι).isScalarTower_of_injective R
    (b.repr.symm.injective.comp <| single_injective _)
/-
**Module.Basis.isScalarTower_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：isScalarTower_finsupp {ι} (b : Basis ι S A) : IsScalarTower R S (ι ->₀ S)
参数：b : Basis ι S A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isScalarTower_of_injective`：isScalarTower_of_injective [SMul R
 S] [CompatibleSMul M M₂ R S] [IsScalarTower R S M₂] (f : M ->ₗ[S] M₂) (hf : Fun
ction.Injective f) : IsSca…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem isScalarTower_finsupp {ι} (b : Basis ι S A) : IsScalarTower R S (ι →₀ S) :=
  b.repr.symm.isScalarTower_of_injective R b.repr.symm.injective

variable {R} {ι ι' : Type*} (b : Basis ι R S) (c : Basis ι' S A)

/-- `Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable
/-
**Module.Basis.smulTower** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：smulTower : Basis (ι × ι') R A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
def smulTower : Basis (ι × ι') R A :=
  haveI := c.isScalarTower_finsupp R
  .ofRepr
    (c.repr.restrictScalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((curryLinearEquiv R).symm ≪≫ₗ
          Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]
/-
**Module.Basis.smulTower_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smulTower_repr (x ij) : (b.smulTower c).repr x ij = b.repr (c.repr x ij.2)
 ij.1
参数：x ij。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.curryLinearEquiv_symm_apply`：∀ {α : Type u_9} {β : Type u_10} (R
 : Type u_11) {M : Type u_12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [
inst_2 : _root_.Module R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulTower_repr (x ij) :
    (b.smulTower c).repr x ij = b.repr (c.repr x ij.2) ij.1 := by
  simp [smulTower, Finsupp.uncurry_apply]
/-
**Module.Basis.smulTower_repr_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smulTower_repr_mk (x i j) : (b.smulTower c).repr x (i, j) = b.repr (c.repr
 x j) i
参数：x i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.smulTower_repr`：smulTower_repr (x ij) : (b.smulTower c).rep
r x ij = b.repr (c.repr x ij.2) ij.1
-/
theorem smulTower_repr_mk (x i j) : (b.smulTower c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smulTower_repr c x (i, j)

@[simp]
/-
**Module.Basis.smulTower_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：smulTower_apply (ij) : (b.smulTower c) ij = b ij.1 • c ij.2
参数：ij。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Module.Basis.smulTower_repr`：smulTower_repr (x ij) : (b.smulTower c).rep
r x ij = b.repr (c.repr x ij.2) ij.1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_apply`：smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v :
 α ->₀ M) (a : α) : (b • v) a = b • v a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
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
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
（共 31 条，此处仅展示前 30 条）
-/
theorem smulTower_apply (ij) : (b.smulTower c) ij = b ij.1 • c ij.2 := by
  classical
  obtain ⟨i, j⟩ := ij
  rw [Basis.apply_eq_iff]
  ext ⟨i', j'⟩
  rw [Basis.smulTower_repr, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  dsimp only
  split_ifs with hi
  · simp [hi, Finsupp.single_apply]
  · simp [hi]

/-- `Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b j • c i`. -/
/-
**Module.Basis.smulTower'** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：smulTower' : Basis (ι' × ι) R A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Basis.smulTower (b : Basis ι R S) (c : Basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b j • c i`.
-/
noncomputable def smulTower' : Basis (ι' × ι) R A :=
  (b.smulTower c).reindex (.prodComm ..)
/-
**Module.Basis.smulTower'_repr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : AddCommMonoid A]   [inst_3 : _root_.Module R S] [inst_4
 : _root_.Module S A] [inst_5 : _root_.Module R A] [inst_6 : IsScalarTower R S A
]   {ι : Type u_5} {ι' : Type u_6} (b : Module.Basis ι R S) (c : Module.Basis ι'
 S A) (x : A) (ij : ι' × ι),   ((b.smulTower' c).repr x) ij = (b.repr ((c.repr x
) ij.1)) ij.2
参数：b : Module.Basis ι R S；c : Module.Basis ι' S A；x : A；ij : ι' × ι；(b.smulTower
' c).repr x；b.repr ((c.repr x) ij.1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.smulTower'.eq_1`：∀ {R : Type u_1} {S : Type u_2} {A : Type 
u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid A]   [ins
t_3 : _root_.Modul…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.repr_reindex_apply`：repr_reindex_apply (i' : ι') : (b.reind
ex e).repr x i' = b.repr x (e.symm i')
· 使用定理 `Module.Basis.smulTower_repr`：smulTower_repr (x ij) : (b.smulTower c).rep
r x ij = b.repr (c.repr x ij.2) ij.1
-/
theorem smulTower'_repr (x ij) :
    (b.smulTower' c).repr x ij = b.repr (c.repr x ij.1) ij.2 := by
  rw [smulTower', repr_reindex_apply, smulTower_repr]; rfl
/-
**Module.Basis.smulTower'_repr_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : AddCommMonoid A]   [inst_3 : _root_.Module R S] [inst_4
 : _root_.Module S A] [inst_5 : _root_.Module R A] [inst_6 : IsScalarTower R S A
]   {ι : Type u_5} {ι' : Type u_6} (b : Module.Basis ι R S) (c : Module.Basis ι'
 S A) (x : A) (i : ι') (j : ι),   ((b.smulTower' c).repr x) (i, j) = (b.repr ((c
.repr x) i)) j
参数：b : Module.Basis ι R S；c : Module.Basis ι' S A；x : A；i : ι'；j : ι；(b.smulTowe
r' c).repr x；i, j；b.repr ((c.repr x) i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.smulTower'_repr`：∀ {R : Type u_1} {S : Type u_2} {A : Type 
u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid A]   [ins
t_3 : _root_.Modul…
-/
theorem smulTower'_repr_mk (x i j) : (b.smulTower' c).repr x (i, j) = b.repr (c.repr x i) j :=
  b.smulTower'_repr c x (i, j)
/-
**Module.Basis.smulTower'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} [inst : Semiring R] [inst_1
 : Semiring S] [inst_2 : AddCommMonoid A]   [inst_3 : _root_.Module R S] [inst_4
 : _root_.Module S A] [inst_5 : _root_.Module R A] [inst_6 : IsScalarTower R S A
]   {ι : Type u_5} {ι' : Type u_6} (b : Module.Basis ι R S) (c : Module.Basis ι'
 S A) (ij : ι' × ι),   (b.smulTower' c) ij = b ij.2 • c ij.1
参数：b : Module.Basis ι R S；c : Module.Basis ι' S A；ij : ι' × ι；b.smulTower' c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.smulTower'.eq_1`：∀ {R : Type u_1} {S : Type u_2} {A : Type 
u_3} [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid A]   [ins
t_3 : _root_.Modul…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.reindex_apply`：reindex_apply (i' : ι') : b.reindex e i' = b
 (e.symm i')
· 使用定理 `Module.Basis.smulTower_apply`：smulTower_apply (ij) : (b.smulTower c) ij 
= b ij.1 • c ij.2
-/
theorem smulTower'_apply (ij) : b.smulTower' c ij = b ij.2 • c ij.1 := by
  rw [smulTower', reindex_apply, smulTower_apply]; rfl

end Module.Basis
end Semiring

section Ring

variable {R S}
variable [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [Algebra R S]

/-
**Module.Basis.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.algebraMap_injective {ι : Type*} (b : Basis ι R S) : Function
.Injective (algebraMap R S)
参数：b : Basis ι R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.isTorsionFree`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 (b : Module.Bas…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
theorem Module.Basis.algebraMap_injective {ι : Type*} (b : Basis ι R S) :
    Function.Injective (algebraMap R S) :=
  have : IsTorsionFree R S := b.isTorsionFree
  FaithfulSMul.algebraMap_injective R S

end Ring

section AlgHomTower

variable {A} {C D : Type*} [CommSemiring A] [CommSemiring C] [CommSemiring D] [Algebra A C]
  [Algebra A D]

variable [CommSemiring B] [Algebra A B] [Algebra B C] [IsScalarTower A B C] (f : C →ₐ[A] D)

/-- Restrict the domain of an `AlgHom`. -/
/-
**AlgHom.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.domRestrict : B ->ₐ[A] D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the domain of an `AlgHom`.
-/
def AlgHom.domRestrict : B →ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)

@[deprecated (since := "2026-07-19")] alias AlgHom.restrictDomain := AlgHom.domRestrict

/-- Extend the scalars of an `AlgHom`. -/
/-
**AlgHom.extendScalars** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.domRestrict B).toRingHom.t
oAlgebra where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the scalars of an `AlgHom`.
-/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.domRestrict B).toRingHom.toAlgebra where
  __ := f
  commutes' := fun _ ↦ rfl
  __ := (f.domRestrict B).toRingHom.toAlgebra

variable {B}

/-- `AlgHom`s from the top of a tower are equivalent to a pair of `AlgHom`s. -/
/-
**algHomEquivSigma** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algHomEquivSigma : (C ->ₐ[A] D) ≃ Σ f : B ->ₐ[A] D, @AlgHom B C D _ _ _ _ 
f.toRingHom.toAlgebra where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom`s from the top of a tower are equivalent to a pair of `AlgHom`s.
-/
def algHomEquivSigma :
    (C →ₐ[A] D) ≃ Σ f : B →ₐ[A] D, @AlgHom B C D _ _ _ _ f.toRingHom.toAlgebra where
  toFun f := ⟨f.domRestrict B, f.extendScalars B⟩
  invFun fg :=
    let _ := fg.1.toRingHom.toAlgebra
    fg.2.restrictScalars A
  left_inv f := by
    dsimp only
    ext
    rfl
  right_inv := by
    rintro ⟨⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩, ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, hg⟩⟩
    obtain rfl : f = fun x => g (algebraMap B C x) := by
      ext x
      exact (hg x).symm
    rfl

end AlgHomTower

