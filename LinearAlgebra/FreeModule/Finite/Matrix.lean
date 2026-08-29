/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite and free modules using matrices

We provide some instances for finite and free modules involving matrices.

## Main results

* `Module.Free.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `Module.Finite.ofBasis` : A free module with a basis indexed by a `Fintype` is finite.
* `Module.Finite.linearMap` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/

@[expose] public section


universe u u' v w

variable (R : Type u) (S : Type u') (M : Type v) (N : Type w)

open Module.Free (chooseBasis ChooseBasisIndex)

open Module (finrank)

section Ring

variable [Ring R] [Ring S] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
variable [AddCommGroup N] [Module R N] [Module S N] [SMulCommClass R S N]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def linearMapEquivFun
  body: (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S N

中文:
定义 noncomputable
  签名: def linearMapEquivFun
  定义体: (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S N
-/
private noncomputable def linearMapEquivFun : (M ->ₗ[R] N) ≃ₗ[S] ChooseBasisIndex R M -> N :=
  (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S N

/--
Instance `Module.Free.linearMap` / 实例 `Module.Free.linearMap`

English:
instance Module.Free.linearMap
  signature: [Module.Free S N]
  body: Module.Free.of_equiv (linearMapEquivFun R S M N).symm

中文:
实例 Module.Free.linearMap
  签名: [Module.Free S N]
  定义体: Module.Free.of_equiv (linearMapEquivFun R S M N).symm

Depends on / 依赖: Module, Module.Free.of_equiv, linearMapEquivFun, of_equiv
-/
instance Module.Free.linearMap [Module.Free S N] : Module.Free S (M ->ₗ[R] N) :=
  Module.Free.of_equiv (linearMapEquivFun R S M N).symm

/--
Instance `Module.Finite.linearMap` / 实例 `Module.Finite.linearMap`

English:
instance Module.Finite.linearMap
  signature: [Module.Finite S N]
  body: Module.Finite.equiv (linearMapEquivFun R S M N).symm

中文:
实例 Module.Finite.linearMap
  签名: [Module.Finite S N]
  定义体: Module.Finite.equiv (linearMapEquivFun R S M N).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, linearMapEquivFun
-/
instance Module.Finite.linearMap [Module.Finite S N] : Module.Finite S (M ->ₗ[R] N) :=
  Module.Finite.equiv (linearMapEquivFun R S M N).symm

variable [StrongRankCondition R] [StrongRankCondition S] [Module.Free S N]

open Cardinal
/--
theorem `Module.rank_linearMap` / 定理 `Module.rank_linearMap`

English:
theorem Module.rank_linearMap
  proof: by
  rw [(linearMapEquivFun R S M N).rank_eq]; rw [rank_fun_eq_lift_mul]; rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_rank R]; rw [lift_natCast]

中文:
定理 Module.rank_linearMap
  证明: by
  rw [(linearMapEquivFun R S M N).rank_eq]; rw [rank_fun_eq_lift_mul]; rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_rank R]; rw [lift_natCast]

Depends on / 依赖: finrank_eq_card_chooseBasisIndex, finrank_eq_rank, lift_natCast, linearMapEquivFun, rank_eq, rank_fun_eq_lift_mul
-/
theorem Module.rank_linearMap :
    Module.rank S (M ->ₗ[R] N) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N) := by
  rw [(linearMapEquivFun R S M N).rank_eq]; rw [rank_fun_eq_lift_mul]; rw [← finrank_eq_card_chooseBasisIndex]; rw [← finrank_eq_rank R]; rw [lift_natCast]

/--
theorem `Module.finrank_linearMap` / 定理 `Module.finrank_linearMap`

English:
theorem Module.finrank_linearMap
  proof: by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]

中文:
定理 Module.finrank_linearMap
  证明: by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]

Depends on / 依赖: finrank, rank_linearMap, simp_rw, toNat_lift, toNat_mul
-/
theorem Module.finrank_linearMap :
    finrank S (M ->ₗ[R] N) = finrank R M * finrank S N := by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]

variable [Module R S] [SMulCommClass R S S]

/--
theorem `Module.rank_linearMap_self` / 定理 `Module.rank_linearMap_self`

English:
theorem Module.rank_linearMap_self
  proof: by
  rw [rank_linearMap]; rw [rank_self]; rw [lift_one]; rw [mul_one]

中文:
定理 Module.rank_linearMap_self
  证明: by
  rw [rank_linearMap]; rw [rank_self]; rw [lift_one]; rw [mul_one]

Depends on / 依赖: lift_one, mul_one, rank_linearMap, rank_self
-/
theorem Module.rank_linearMap_self :
    Module.rank S (M ->ₗ[R] S) = lift.{u'} (Module.rank R M) := by
  rw [rank_linearMap]; rw [rank_self]; rw [lift_one]; rw [mul_one]

/--
theorem `Module.finrank_linearMap_self` / 定理 `Module.finrank_linearMap_self`

English:
theorem Module.finrank_linearMap_self
  statement: finrank S (M ->ₗ[R] S) = finrank R M
  proof: by
  rw [finrank_linearMap]; rw [finrank_self]; rw [mul_one]

中文:
定理 Module.finrank_linearMap_self
  结论: finrank S (M ->ₗ[R] S) = finrank R M
  证明: by
  rw [finrank_linearMap]; rw [finrank_self]; rw [mul_one]

Depends on / 依赖: finrank_linearMap, finrank_self, mul_one
-/
theorem Module.finrank_linearMap_self : finrank S (M ->ₗ[R] S) = finrank R M := by
  rw [finrank_linearMap]; rw [finrank_self]; rw [mul_one]

end Ring

section AlgHom

variable (K M : Type*) (L : Type v) [CommRing K] [Ring M] [Algebra K M]
  [Module.Free K M] [Module.Finite K M] [CommRing L] [IsDomain L] [Algebra K L]

/--
Instance `Finite.algHom` / 实例 `Finite.algHom`

English:
instance Finite.algHom
  signature: : Finite (M ->ₐ[K] L)
  body: (linearIndependent_algHom_toLinearMap K M L).finite

中文:
实例 Finite.algHom
  签名: : Finite (M ->ₐ[K] L)
  定义体: (linearIndependent_algHom_toLinearMap K M L).finite

Depends on / 依赖: finite, linearIndependent_algHom_toLinearMap
-/
instance Finite.algHom : Finite (M ->ₐ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).finite

open Cardinal

/--
theorem `cardinalMk_algHom_le_rank` / 定理 `cardinalMk_algHom_le_rank`

English:
theorem cardinalMk_algHom_le_rank
  statement: #(M ->ₐ[K] L) <= lift.{v} (Module.rank K M)
  proof: by
  convert! (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id]; rw [Module.rank_linearMap_self]

@[stacks 09HS]

中文:
定理 cardinalMk_algHom_le_rank
  结论: #(M ->ₐ[K] L) <= lift.{v} (Module.rank K M)
  证明: by
  convert! (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id]; rw [Module.rank_linearMap_self]

@[stacks 09HS]

Depends on / 依赖: Module, Module.nontrivial, Module.rank_linearMap_self, cardinal_lift_le_rank, convert, lift_id, linearIndependent_algHom_toLinearMap, nontrivial, rank_linearMap_self
-/
theorem cardinalMk_algHom_le_rank : #(M ->ₐ[K] L) <= lift.{v} (Module.rank K M) := by
  convert! (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id]; rw [Module.rank_linearMap_self]

@[stacks 09HS]
/--
theorem `card_algHom_le_finrank` / 定理 `card_algHom_le_finrank`

English:
theorem card_algHom_le_finrank
  statement: Nat.card (M ->ₐ[K] L) <= finrank K M
  proof: by
  convert! toNat_le_toNat (cardinalMk_algHom_le_rank K M L) ?_
  · rw [toNat_lift, finrank]
  · rw [lift_lt_aleph0]; have := Module.nontrivial K L; apply Module.rank_lt_aleph0

中文:
定理 card_algHom_le_finrank
  结论: 自然数.card (M ->ₐ[K] L) <= finrank K M
  证明: by
  convert! toNat_le_toNat (cardinalMk_algHom_le_rank K M L) ?_
  · rw [toNat_lift, finrank]
  · rw [lift_lt_aleph0]; have := Module.nontrivial K L; apply Module.rank_lt_aleph0

Depends on / 依赖: Module, Module.nontrivial, Module.rank_lt_aleph0, cardinalMk_algHom_le_rank, convert, finrank, lift_lt_aleph0, nontrivial, rank_lt_aleph0, toNat_le_toNat, toNat_lift
-/
theorem card_algHom_le_finrank : Nat.card (M ->ₐ[K] L) <= finrank K M := by
  convert! toNat_le_toNat (cardinalMk_algHom_le_rank K M L) ?_
  · rw [toNat_lift, finrank]
  · rw [lift_lt_aleph0]; have := Module.nontrivial K L; apply Module.rank_lt_aleph0

end AlgHom

section Integer

variable [AddCommGroup M] [Module.Finite Int M] [Module.Free Int M] [AddCommGroup N]

/--
Instance `Module.Finite.addMonoidHom` / 实例 `Module.Finite.addMonoidHom`

English:
instance Module.Finite.addMonoidHom
  signature: [Module.Finite Int N]
  body: Module.Finite.equiv (addMonoidHomLequivInt Int).symm

中文:
实例 Module.Finite.addMonoidHom
  签名: [Module.Finite 整数 N]
  定义体: Module.Finite.equiv (addMonoidHomLequivInt Int).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, addMonoidHomLequivInt
-/
instance Module.Finite.addMonoidHom [Module.Finite Int N] : Module.Finite Int (M ->+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt Int).symm

/--
Instance `Module.Free.addMonoidHom` / 实例 `Module.Free.addMonoidHom`

English:
instance Module.Free.addMonoidHom
  signature: [Module.Free Int N]
  body: letI : Module.Free Int (M ->ₗ[Int] N) := Module.Free.linearMap _ _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt Int).symm

中文:
实例 Module.Free.addMonoidHom
  签名: [Module.Free 整数 N]
  定义体: letI : Module.Free Int (M ->ₗ[Int] N) := Module.Free.linearMap _ _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt Int).symm

Depends on / 依赖: Module, Module.Free, Module.Free.linearMap, Module.Free.of_equiv, addMonoidHomLequivInt, linearMap, of_equiv
-/
instance Module.Free.addMonoidHom [Module.Free Int N] : Module.Free Int (M ->+ N) :=
  letI : Module.Free Int (M ->ₗ[Int] N) := Module.Free.linearMap _ _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt Int).symm

end Integer
