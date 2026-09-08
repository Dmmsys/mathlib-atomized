/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is a separably closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characteristic zero,
this hold for all `n ≠ 0`.
-/

public section

variable (F : Type*) [Field F] (n k : ℕ) [NeZero (n : F)]

namespace IsSepClosed

variable [IsSepClosed F]

/-- A separably closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`. -/
/-
**IsSepClosed.hasEnoughRootsOfUnity** 是 Mathlib 中的一个实例，位于命名空间 `IsSepClosed`。
形式化陈述：hasEnoughRootsOfUnity : HasEnoughRootsOfUnity F n where prim
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NeZero.of_neZero_natCast`：of_neZero_natCast (R) [AddMonoidWithOne R] {n 
: Nat} [h : NeZero (n : R)] : NeZero n
· 使用定理 `IsSepClosed.isCyclotomicExtension`：IsSepClosed.isCyclotomicExtension (h 
: forall a in S, a != 0 -> NeZero (a : K)) : IsCyclotomicExtension S K K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `IsCyclotomicExtension.exists_isPrimitiveRoot`：∀ {S : Set ℕ} (A : Type u)
 (B : Type v) {inst : CommRing A} {inst_1 : CommRing B} {inst_2 : Algebra A B}  
 [self : IsCyclotomicExtension S A…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
A separably closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`.
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {n} F fun _ h _ ↦ Set.mem_singleton_iff.mp h ▸ ‹NeZero (n : F)›
    exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) F _ rfl (NeZero.ne _)
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n
/-
**IsSepClosed.hasEnoughRootsOfUnity_pow** 是 Mathlib 中的一个实例，位于命名空间 `IsSepClosed`。
形式化陈述：hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity F (n ^ k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity F (n ^ k) :=
  have : NeZero ((n ^ k : ℕ) : F) := by exact_mod_cast ‹NeZero (n : F)›.pow
  inferInstance

end IsSepClosed

namespace AlgebraicClosure

/-
**AlgebraicClosure.hasEnoughRootsOfUnity** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicClo
sure`。
形式化陈述：hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (AlgebraicClosure F) n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NeZero.of_injective`：of_injective {f : F} (hf : Injective f) [NeZero a] 
: NeZero (f a)
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (AlgebraicClosure F) n :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance
/-
**AlgebraicClosure.hasEnoughRootsOfUnity_pow** 是 Mathlib 中的一个实例，位于命名空间 `Algebrai
cClosure`。
形式化陈述：hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (AlgebraicClosure F) (n 
^ k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `NeZero.of_injective`：of_injective {f : F} (hf : Injective f) [NeZero a] 
: NeZero (f a)
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (AlgebraicClosure F) (n ^ k) :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

end AlgebraicClosure

namespace SeparableClosure

/-
**SeparableClosure.hasEnoughRootsOfUnity** 是 Mathlib 中的一个实例，位于命名空间 `SeparableClo
sure`。
形式化陈述：hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (SeparableClosure F) n
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用引理 `NeZero.of_injective`：of_injective {f : F} (hf : Injective f) [NeZero a] 
: NeZero (f a)
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (SeparableClosure F) n :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance
/-
**SeparableClosure.hasEnoughRootsOfUnity_pow** 是 Mathlib 中的一个实例，位于命名空间 `Separabl
eClosure`。
形式化陈述：hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (SeparableClosure F) (n 
^ k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用引理 `NeZero.of_injective`：of_injective {f : F} (hf : Injective f) [NeZero a] 
: NeZero (f a)
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (SeparableClosure F) (n ^ k) :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

end SeparableClosure

