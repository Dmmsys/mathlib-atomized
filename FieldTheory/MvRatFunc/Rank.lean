/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.RingTheory.Algebraic.LinearIndependent
public import Mathlib.RingTheory.Algebraic.MvPolynomial
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.MvPolynomial

/-!
# Rank of multivariate rational function field
-/

public section

noncomputable section

universe u v

open Cardinal in
/-
**MvRatFunc.rank_eq_max_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MvRatFunc.rank_eq_max_lift {σ : Type u} {F : Type v} [Field F] [Nonempty σ
] : Module.rank F (FractionRing (MvPolynomial σ F)) = lift.{u} #F ⊔ lift.{v} #σ 
⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `rank_le_card`：rank_le_card : Module.rank R M <= #M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionRing.cardinalMk`：∀ (R : Type u) [inst : CommRing R], Cardinal.mk
 (FractionRing R) = Cardinal.mk R
· 使用定理 `MvPolynomial.cardinalMk_eq_max_lift`：cardinalMk_eq_max_lift [Nonempty σ]
 [Nontrivial R] : #(MvPolynomial σ R) = lift.{u} #R ⊔ lift.{v} #σ ⊔ ℵ₀
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `transcendental_algebraMap_iff`：transcendental_algebraMap_iff {a : S} (h 
: Function.Injective (algebraMap S A)) : Transcendental R (algebraMap S A a) ↔ T
ranscendental R a
· 使用定理 `MvPolynomial.transcendental_X`：transcendental_X (i : σ) : Transcendental
 R (X i : MvPolynomial σ R)
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `Transcendental.linearIndependent_sub_inv`：Transcendental.linearIndepende
nt_sub_inv {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (H : Transcen
dental F x) : LinearIndependen…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `Cardinal.mk_finsupp_nat`：mk_finsupp_nat (α : Type u) [Nonempty α] : #(α 
->₀ Nat) = max #α ℵ₀
· 使用定理 `MvPolynomial.rank_eq_lift`：rank_eq_lift : Module.rank K (MvPolynomial σ 
K) = lift.{v} #(σ ->₀ Nat)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem MvRatFunc.rank_eq_max_lift
    {σ : Type u} {F : Type v} [Field F] [Nonempty σ] :
    Module.rank F (FractionRing (MvPolynomial σ F)) = lift.{u} #F ⊔ lift.{v} #σ ⊔ ℵ₀ := by
  let R := MvPolynomial σ F
  let K := FractionRing R
  refine ((rank_le_card _ _).trans ?_).antisymm ?_
  · rw [FractionRing.cardinalMk, MvPolynomial.cardinalMk_eq_max_lift]
  have hinj := IsFractionRing.injective R K
  have h1 := (IsScalarTower.toAlgHom F R K).toLinearMap.rank_le_of_injective hinj
  rw [MvPolynomial.rank_eq_lift, mk_finsupp_nat, lift_max, lift_aleph0, max_le_iff] at h1
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hx : Transcendental F (algebraMap R K (MvPolynomial.X i)) :=
    (transcendental_algebraMap_iff hinj).2 (MvPolynomial.transcendental_X F i)
  have h2 := hx.linearIndependent_sub_inv.cardinal_lift_le_rank
  rw [lift_id'.{v, u}, lift_umax.{v, u}] at h2
  exact max_le (max_le h2 h1.1) h1.2
