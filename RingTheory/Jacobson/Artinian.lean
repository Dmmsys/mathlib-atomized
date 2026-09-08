/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Artinian rings over Jacobson rings

## Main results
- `Module.finite_iff_isArtinianRing`: If `A` is a finite type algebra over an Artinian ring `R`,
  then `A` is finite over `R` if and only if `A` is an Artinian ring.

-/

public section

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/-
**Module.finite_of_isSemisimpleRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A] 
: Module.Finite R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `finite_of_finite_type_of_isJacobsonRing`：finite_of_finite_type_of_isJaco
bsonRing (R S : Type*) [CommRing R] [Field S] [Algebra R S] [IsJacobsonRing R] [
Algebra.FiniteType R S] : Mod…
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `IsArtinianRing.instFiniteMaximalSpectrum`：∀ (R : Type u_1) [inst : CommS
emiring R] [IsArtinianRing R], Finite (MaximalSpectrum R)
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `instIsReducedOfIsSemisimpleRing`：∀ (R : Type u_5) [inst : CommRing R] [I
sSemisimpleRing R], IsReduced R
-/
lemma Module.finite_of_isSemisimpleRing [IsJacobsonRing R] [IsSemisimpleRing A] :
    Module.Finite R A :=
  have (I : MaximalSpectrum A) := finite_of_finite_type_of_isJacobsonRing R (A ⧸ I.asIdeal)
  .equiv ((IsArtinianRing.equivPi A).restrictScalars R).toLinearEquiv.symm

/-- If `A` is a finite type algebra over `R`, then `A` is an Artinian ring and `R` is Jacobson
implies `A` is finite over `R`. -/
/- If made an instance, causes timeouts synthesizing `FaithfulSMul R I.ResidueField` at
`Ideal.algebraMap_residueField_eq_zero` and `Ideal.ker_algebraMap_residueField` during
simpNF linting. -/
/-
**Module.finite_of_isArtinianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] : Mo
dule.Finite R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.finite_of_isSemisimpleRing`：Module.finite_of_isSemisimpleRing [Is
JacobsonRing R] [IsSemisimpleRing A] : Module.Finite R A
· 使用定理 `IsSemiprimaryRing.isSemisimpleRing`：∀ {R : Type u_1} {inst : Ring R} [se
lf : IsSemiprimaryRing R], IsSemisimpleRing (R ⧸ Ring.jacobson R)
· 使用定理 `IsArtinianRing.instIsSemiprimaryRing`：∀ {R : Type u_1} [inst : Ring R] [
IsArtinianRing R], IsSemiprimaryRing R
· 使用定理 `IsSemiprimaryRing.finite_of_isArtinian`：finite_of_isArtinian [IsArtinian
 R M] : Module.Finite R₀ M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If made an instance, causes timeouts synthesizing `FaithfulSMul R I.ResidueField
` at
`Ideal.algebraMap_residueField_eq_zero` and `Ideal.ker_algebraMap_residueField` 
during
simpNF linting.
-/
lemma Module.finite_of_isArtinianRing [IsJacobsonRing R] [IsArtinianRing A] :
    Module.Finite R A :=
  have := finite_of_isSemisimpleRing R (A ⧸ Ring.jacobson A)
  IsSemiprimaryRing.finite_of_isArtinian R A A

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an Artinian ring. -/
/-
**Module.finite_iff_isArtinianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finite_iff_isArtinianRing [IsArtinianRing R] : Module.Finite R A ↔ 
IsArtinianRing A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsArtinianRing.tfae`：IsArtinianRing.tfae [IsArtinianRing R] : List.TFAE 
[Module.Finite R M, IsNoetherian R M, IsArtinian R M, IsFiniteLength R M]
· 使用引理 `Module.finite_of_isArtinianRing`：Module.finite_of_isArtinianRing [IsJaco
bsonRing R] [IsArtinianRing A] : Module.Finite R A
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R

--- 原说明 ---
If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `A` is an Artinian ring.
-/
lemma Module.finite_iff_isArtinianRing [IsArtinianRing R] :
    Module.Finite R A ↔ IsArtinianRing A :=
  ⟨isArtinian_of_tower _ ∘ ((IsArtinianRing.tfae R A).out 0 2).mp,
    fun _ ↦ finite_of_isArtinianRing R A⟩

/-- If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `dim A = 0`. -/
/-
**Module.finite_iff_krullDimLE_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finite_iff_krullDimLE_zero [IsArtinianRing R] : Module.Finite R A ↔
 Ring.KrullDimLE 0 A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.finite_iff_isArtinianRing`：Module.finite_iff_isArtinianRing [IsAr
tinianRing R] : Module.Finite R A ↔ IsArtinianRing A
· 使用定理 `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`：∀ {R : Type u_3} [i
nst : CommRing R], IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `A` is a finite type algebra over an Artinian ring `R`,
then `A` is finite over `R` if and only if `dim A = 0`.
-/
lemma Module.finite_iff_krullDimLE_zero [IsArtinianRing R] :
    Module.Finite R A ↔ Ring.KrullDimLE 0 A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  rw [finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero,
    and_iff_right this]
