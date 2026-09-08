/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Ramification index and inertia degree

Given `P : Ideal S` lying over `p : Ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **inertia degree** `Ideal.inertiaDeg' p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Implementation notes

Often the above theory is set up in the case where:
* `R` is the ring of integers of a number field `K`,
* `L` is a finite separable extension of `K`,
* `S` is the integral closure of `R` in `L`,
* `p` and `P` are maximal ideals,
* `P` is an ideal lying over `p`

We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `f` stands for the inertia degree of `P` over `p`, leaving `p` and `P` implicit.

-/

@[expose] public section


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module

open UniqueFactorizationMonoid

attribute [local instance] Ideal.Quotient.field

section DecEq

variable {S₁ : Type*} [CommRing S₁] [Algebra R S₁]

/-- The inertia degree of `P : Ideal S` lying over `p : Ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertiaDeg'_algebraMap` for the common case where `f = algebraMap R S`
and there is an algebra structure `R / p → S / P`.

Note: This definition of inertia degree will eventually be replaced by `Ideal.inertiaDeg`.
-/
/-
**Ideal.inertiaDeg'** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：inertiaDeg' : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The inertia degree of `P : Ideal S` lying over `p : Ideal R` is the degree of th
e
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertiaDeg'_algebraMap` for the common case where `f = algebraMap R S`
and there is an algebra structure `R / p → S / P`.

Note: This definition of inertia degree will eventually be replaced by `Ideal.in
ertiaDeg`.
-/
noncomputable def inertiaDeg' : ℕ :=
  if hPp : comap f P = p then
    letI : Algebra (R ⧸ p) (S ⧸ P) := Quotient.algebraQuotientOfLEComap hPp.ge
    finrank (R ⧸ p) (S ⧸ P)
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
/-
**Ideal.inertiaDeg'_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [hp : p.IsMaximal] [hQ : Subsin
gleton (S ⧸ P)], p.inertiaDeg' P = 0
参数：p : Ideal R；P : Ideal S；S ⧸ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.subsingleton_iff`：∀ {R : Type u_3} [inst : Ring R] {I : I
deal R}, Subsingleton (R ⧸ I) ↔ I = ⊤
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem inertiaDeg'_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg' p P = 0 := by
  have := Ideal.Quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[deprecated (since := "2026-07-03")] alias inertiaDeg_of_subsingleton :=
  inertiaDeg'_of_subsingleton

@[simp]
/-
**Ideal.inertiaDeg'_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [inst_3 : P.LiesOver p], p.iner
tiaDeg' P = Module.finrank (R ⧸ p) (S ⧸ P)
参数：p : Ideal R；P : Ideal S；R ⧸ p；S ⧸ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'.eq_1`：∀ {R : Type u} [inst : CommRing R] {S : Type v} 
[inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   (P : Ideal S),   p.
inertiaDeg' …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem inertiaDeg'_algebraMap [P.LiesOver p] :
    inertiaDeg' p P = finrank (R ⧸ p) (S ⧸ P) := by
  rw [inertiaDeg', dif_pos (over_def P p).symm]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebraMap := inertiaDeg'_algebraMap
/-
**Ideal.inertiaDeg'_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p.IsMaximal] [Module.Finite R 
S] [P.LiesOver p], 0 < p.inertiaDeg' P
参数：p : Ideal R；P : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.nontrivial_of_liesOver_of_isPrime`：nontrivial_of_liesOver
_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
-/
theorem inertiaDeg'_pos [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : Nontrivial (S ⧸ P) := Quotient.nontrivial_of_liesOver_of_isPrime P p
  finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

/-- Variant with a weaker constraint, but on the prime upstairs instead. -/
/-
**Ideal.inertiaDeg'_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [P.IsPrime] [Module.Finite R S]
 [P.LiesOver p], 0 < p.inertiaDeg' P
参数：p : Ideal R；P : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…

--- 原说明 ---
Variant with a weaker constraint, but on the prime upstairs instead.
-/
theorem inertiaDeg'_pos' [P.IsPrime] [Module.Finite R S] [P.LiesOver p] : 0 < inertiaDeg' p P :=
  have : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  Module.finrank_pos.trans_eq (inertiaDeg'_algebraMap p P).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_pos' := inertiaDeg'_pos'
/-
**Ideal.inertiaDeg'_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p.IsMaximal] [Module.Finite R 
S] [P.LiesOver p], p.inertiaDeg' P ≠ 0
参数：p : Ideal R；P : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Ideal.inertiaDeg'_pos`：∀ {R : Type u} [inst : CommRing R] {S : Type v} [
inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   [p.IsM
aximal] [Mo…
-/
theorem inertiaDeg'_ne_zero [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    inertiaDeg' p P ≠ 0 :=
  (Nat.ne_of_lt (inertiaDeg'_pos p P)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_ne_zero := inertiaDeg'_ne_zero
/-
**Ideal.inertiaDeg'_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   {S₁ : Type u_1} [inst_3 : CommRing S₁] [inst_
4 : Algebra R S₁] (e : S ≃ₐ[R] S₁) (P : Ideal S₁),   p.inertiaDeg' (Ideal.comap 
e P) = p.inertiaDeg' P
参数：p : Ideal R；e : S ≃ₐ[R] S₁；P : Ideal S₁；Ideal.comap e P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用引理 `AlgEquiv.toAlgHom_toRingHom`：toAlgHom_toRingHom : ((e : A₁ ->ₐ[R] A₂) : 
A₁ ->+* A₂) = e
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.inertiaDeg'.eq_1`：∀ {R : Type u} [inst : CommRing R] {S : Type v} 
[inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   (P : Ideal S),   p.
inertiaDeg' …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma inertiaDeg'_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    inertiaDeg' p (P.comap e) = inertiaDeg' p P := by
  have he : (P.comap e).comap (algebraMap R S) = p ↔ P.comap (algebraMap R S₁) = p := by
    rw [← comap_coe e, comap_comap, ← e.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  by_cases h : P.LiesOver p
  · rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
    exact (Quotient.algEquivOfEqComap p e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg', dif_neg (fun eq => h ⟨(he.mp eq).symm⟩)]
    rw [inertiaDeg', dif_neg (fun eq => h ⟨eq.symm⟩)]

@[deprecated (since := "2026-07-03")] alias inertiaDeg_comap_eq := inertiaDeg'_comap_eq
/-
**Ideal.inertiaDeg'_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R)   {S₁ : Type u_1} [inst_3 : CommRing S₁] [inst_
4 : Algebra R S₁] (P : Ideal S) {E : Type u_2}   [inst_5 : EquivLike E S S₁] [Al
gEquivClass E R S S₁] (e : E), p.inertiaDeg' (Ideal.map e P) = p.inertiaDeg' P
参数：p : Ideal R；P : Ideal S；e : E；Ideal.map e P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_comap_of_equiv`：map_comap_of_equiv {I : Ideal R} (f : R ≃+* S)
 : I.map (f : R ->+* S) = I.comap f.symm
· 使用定理 `Ideal.inertiaDeg'_comap_eq`：∀ {R : Type u} [inst : CommRing R] {S : Type
 v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   {S₁ : Type u_1}
 [inst_3 : CommR…
-/
lemma inertiaDeg'_map_eq (P : Ideal S)
    {E : Type*} [EquivLike E S S₁] [AlgEquivClass E R S S₁] (e : E) :
    inertiaDeg' p (P.map e) = inertiaDeg' p P := by
  rw [show P.map e = _ from map_comap_of_equiv (RingEquivClass.toRingEquiv e : S ≃+* S₁)]
  exact p.inertiaDeg'_comap_eq (AlgEquivClass.toAlgEquiv e).symm P

@[deprecated (since := "2026-07-03")] alias inertiaDeg_map_eq := inertiaDeg'_map_eq
/-
**Ideal.inertiaDeg'_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (P : Ideal S)   [Nontrivial R] [IsDomain S] [Algebra.IsIntegr
al R S] [hP : P.LiesOver ⊥], ⊥.inertiaDeg' P = Module.finrank R S
参数：P : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'.eq_1`：∀ {R : Type u} [inst : CommRing R] {S : Type v} 
[inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R)   (P : Ideal S),   p.
inertiaDeg' …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Ideal.eq_bot_of_liesOver_bot`：eq_bot_of_liesOver_bot [Nontrivial A] [IsD
omain B] [h : P.LiesOver (⊥ : Ideal A)] : P = ⊥
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `Ideal.instIsTwoSidedBot`：∀ {α : Type u} [inst : Semiring α], ⊥.IsTwoSide
d
-/
theorem inertiaDeg'_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    [hP : P.LiesOver (⊥ : Ideal R)] :
    (⊥ : Ideal R).inertiaDeg' P = finrank R S := by
  rw [inertiaDeg', dif_pos (over_def P (⊥ : Ideal R)).symm]
  replace hP : P = ⊥ := eq_bot_of_liesOver_bot R P
  rw [Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot R).symm
    ((quotEquivOfEq hP).trans (RingEquiv.quotientBot S)).symm]
  rfl

@[deprecated (since := "2026-07-03")] alias inertiaDeg_bot := inertiaDeg'_bot
/-
**Ideal.inertiaDeg'_le_inertiaDeg'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type v} [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (p : Ideal R) (P : Ideal S)   {T : Type u_2} [inst_3 : CommRi
ng T] [inst_4 : Algebra R T] [inst_5 : Algebra S T] [IsScalarTower R S T]   [Mod
ule.Finite R T] (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P] [p.IsPrime], P.inert
iaDeg' Q ≤ p.inertiaDeg' Q
参数：p : Ideal R；P : Ideal S；Q : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.finrank_top_le_finrank_of_isScalarTower`：Module.finrank_top_le_fi
nrank_of_isScalarTower [Module.Finite R M] [Semiring S] [Module S M] [Module R S
] [IsScalarTower R S S] [FaithfulSMu…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem inertiaDeg'_le_inertiaDeg' {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Module.Finite R T] (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P]
    [p.IsPrime] : inertiaDeg' P Q ≤ inertiaDeg' p Q := by
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDeg'_algebraMap, inertiaDeg'_algebraMap]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩
    simp [Submodule.Quotient.quot_mk_eq_mk, IsScalarTower.algebraMap_apply R (S ⧸ P) (T ⧸ Q)]
  exact finrank_top_le_finrank_of_isScalarTower ..

@[deprecated (since := "2026-07-03")] alias inertiaDeg_le_inertiaDeg := inertiaDeg'_le_inertiaDeg'

end DecEq

section absNorm

/-
**Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`
。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {S : Type u_1} [inst_1 : CommRing S] [i
nst_2 : IsDedekindDomain S]   [inst_3 : Module.Free ℤ S] [inst_4 : IsDedekindDom
ain R] [inst_5 : Module.Free ℤ R] [inst_6 : Algebra S R]   [Module.Finite S R] (
P : Ideal R) (p : Ideal S) [P.LiesOver p],   p.IsPrime → p ≠ ⊥ → Ideal.absNorm P
 = Ideal.absNorm p ^ p.inertiaDeg' P
参数：P : Ideal R；p : Ideal S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.cardQuot_apply`：cardQuot_apply (S : Submodule R M) : cardQuot 
S = Nat.card (M ⧸ S)
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `Module.natCard_eq_pow_finrank`：∀ {K : Type u} {V : Type v} [inst : Divis
ionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [Module.Fini
te K V], Nat.card V…
-/
lemma absNorm_eq_pow_inertiaDeg'_of_liesOver {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [IsDedekindDomain R] [Module.Free ℤ R] [Algebra S R] [Module.Finite S R]
    (P : Ideal R) (p : Ideal S) [P.LiesOver p] (hp : p.IsPrime) (hp_ne_bot : p ≠ ⊥) :
    absNorm P = absNorm p ^ (p.inertiaDeg' P) := by
  have : p.IsMaximal := hp.isMaximal hp_ne_bot
  simpa [absNorm_apply, Submodule.cardQuot_apply] using Module.natCard_eq_pow_finrank (K := S ⧸ p)

@[deprecated (since := "2026-07-03")] alias absNorm_eq_pow_inertiaDeg_of_liesOver :=
  absNorm_eq_pow_inertiaDeg'_of_liesOver

/-- The absolute norm of an ideal `P` above a rational prime `p` is
`|p| ^ ((span {p}).inertiaDeg' P)`.
See `absNorm_eq_pow_inertiaDeg'` for a version with `p` of type `ℕ`. -/
/-
**Ideal.absNorm_eq_pow_inertiaDeg** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free Int R] [Module
.Finite Int R] {p : Int} (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) : 
absNorm P = p.natAbs ^ ((span {p}).inertiaDeg' P)
参数：P : Ideal R；span {p}；hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.inertiaDeg'_algebraMap`：∀ {R : Type u} [inst : CommRing R] {S : Ty
pe v} [inst_1 : CommRing S] [inst_2 : Algebra R S] (p : Ideal R) (P : Ideal S)  
 [inst_3 : P.LiesO…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `AddGroup.instFGInt`：AddGroup.FG ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.norm_self`：norm_self : Algebra.norm R = MonoidHom.id R
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver`：∀ {R : Type u} [inst : Com
mRing R] {S : Type u_1} [inst_1 : CommRing S] [inst_2 : IsDedekindDomain S]   [i
nst_3 : Module.Free ℤ S] [inst_4 :…
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The absolute norm of an ideal `P` above a rational prime `p` is
`|p| ^ ((span {p}).inertiaDeg' P)`.
See `absNorm_eq_pow_inertiaDeg'` for a version with `p` of type `ℕ`.
-/
lemma absNorm_eq_pow_inertiaDeg [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
    (P : Ideal R) [P.LiesOver (span {p})] (hp : Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg' P) := by
  simpa using absNorm_eq_pow_inertiaDeg'_of_liesOver P (span {p})
    (by rwa [span_singleton_prime hp.ne_zero]) (by simpa using hp.ne_zero)

/-- The absolute norm of an ideal `P` above a rational (positive) prime `p` is
`p ^ ((span {p}).inertiaDeg' P)`.
See `absNorm_eq_pow_inertiaDeg` for a version with `p` of type `ℤ`. -/
/-
**Ideal.absNorm_eq_pow_inertiaDeg'** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：absNorm_eq_pow_inertiaDeg'_of_liesOver {S : Type*} [CommRing S] [IsDedekin
dDomain S] [Module.Free Int S] [IsDedekindDomain R] [Module.Free Int R] [Algebra
 S R] [Module.Finite S R] (P : Ideal R) (p : Ideal S) [P.LiesOver p] (hp : p.IsP
rime) (hp_ne_bot : p != ⊥) : absNorm P = absNorm p ^ (p.inertiaDeg' P)
参数：P : Ideal R；p : Ideal S；hp : p.IsPrime；hp_ne_bot : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.absNorm_eq_pow_inertiaDeg`：absNorm_eq_pow_inertiaDeg [IsDedekindDo
main R] [Module.Free Int R] [Module.Finite Int R] {p : Int} (P : Ideal R) [P.Lie
sOver (span {p})] (hp…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)

--- 原说明 ---
The absolute norm of an ideal `P` above a rational (positive) prime `p` is
`p ^ ((span {p}).inertiaDeg' P)`.
See `absNorm_eq_pow_inertiaDeg` for a version with `p` of type `ℤ`.
-/
lemma absNorm_eq_pow_inertiaDeg' [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℕ}
    (P : Ideal R) [P.LiesOver (span {(p : ℤ)})] (hp : p.Prime) :
    absNorm P = p ^ ((span {(p : ℤ)}).inertiaDeg' P) :=
  absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)

end absNorm

section tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Let `T / S / R` be a tower of algebras, `p, P, I` be ideals in `R, S, T`, respectively,
  and `p` and `P` are maximal. If `p = P ∩ S` and `P = I ∩ S`,
  then `f (I | p) = f (P | p) * f (I | P)`. -/
/-
**Ideal.inertiaDeg'_algebra_tower** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
S T] [inst_5 : Algebra R T] [IsScalarTower R S T] (p : Ideal R) (P : Ideal S)   
(I : Ideal T) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [I.LiesOver P],   p.ine
rtiaDeg' I = p.inertiaDeg' P * P.inertiaDeg' I
参数：p : Ideal R；P : Ideal S；I : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `Ideal.LiesOver.trans`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type
 u_3} [inst_1 : CommSemiring B] {C : Type u_4} [inst_2 : Semiring C]   [inst_3 :
 Algebra A…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
Let `T / S / R` be a tower of algebras, `p, P, I` be ideals in `R, S, T`, respec
tively,
  and `p` and `P` are maximal. If `p = P ∩ S` and `P = I ∩ S`,
  then `f (I | p) = f (P | p) * f (I | P)`.
-/
theorem inertiaDeg'_algebra_tower (p : Ideal R) (P : Ideal S) (I : Ideal T) [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] : inertiaDeg' p I =
    inertiaDeg' p P * inertiaDeg' P I := by
  have h₁ := P.over_def p
  have h₂ := I.over_def P
  have h₃ := (LiesOver.trans I P p).over
  simp only [inertiaDeg', dif_pos h₁.symm, dif_pos h₂.symm, dif_pos h₃.symm]
  let : Algebra (R ⧸ p) (S ⧸ P) := Ideal.Quotient.algebraQuotientOfLEComap h₁.le
  let : Algebra (S ⧸ P) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₂.le
  let : Algebra (R ⧸ p) (T ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap h₃.le
  let : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ I) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact (finrank_mul_finrank (R ⧸ p) (S ⧸ P) (T ⧸ I)).symm

@[deprecated (since := "2026-07-03")] alias inertiaDeg_algebra_tower := inertiaDeg'_algebra_tower

end tower

end Ideal

