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

/-
**linearMapEquivFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def linearMapEquivFun : (M →ₗ[R] N) ≃ₗ[S] ChooseBasisIndex R M → N :=
  (chooseBasis R M).repr.congrLeft N S ≪≫ₗ (Finsupp.lsum S).symm ≪≫ₗ
    LinearEquiv.piCongrRight fun _ ↦ LinearMap.ringLmapEquivSelf R S N
/-
**Module.Free.linearMap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Free.linearMap [Module.Free S N] : Module.Free S (M ->ₗ[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance Module.Free.linearMap [Module.Free S N] : Module.Free S (M →ₗ[R] N) :=
  Module.Free.of_equiv (linearMapEquivFun R S M N).symm
/-
**Module.Finite.linearMap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.linearMap [Module.Finite S N] : Module.Finite S (M ->ₗ[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance Module.Finite.linearMap [Module.Finite S N] : Module.Finite S (M →ₗ[R] N) :=
  Module.Finite.equiv (linearMapEquivFun R S M N).symm

variable [StrongRankCondition R] [StrongRankCondition S] [Module.Free S N]

open Cardinal
/-
**Module.rank_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.rank_linearMap : Module.rank S (M ->ₗ[R] N) = lift.{w} (Module.rank
 R M) * lift.{v} (Module.rank S N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `rank_fun_eq_lift_mul`：rank_fun_eq_lift_mul : Module.rank R (η -> M) = (F
intype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
-/
theorem Module.rank_linearMap :
    Module.rank S (M →ₗ[R] N) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N) := by
  rw [(linearMapEquivFun R S M N).rank_eq, rank_fun_eq_lift_mul,
    ← finrank_eq_card_chooseBasisIndex, ← finrank_eq_rank R, lift_natCast]

/-- The `finrank` of `M →ₗ[R] N` as an `S`-module is `(finrank R M) * (finrank S N)`. -/
/-
**Module.finrank_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_linearMap : finrank S (M ->ₗ[R] N) = finrank R M * finrank 
S N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_linearMap`：Module.rank_linearMap : Module.rank S (M ->ₗ[R] N
) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N)
· 使用定理 `Cardinal.toNat_mul`：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x
 * toNat y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `finrank` of `M →ₗ[R] N` as an `S`-module is `(finrank R M) * (finrank S N)`
.
-/
theorem Module.finrank_linearMap :
    finrank S (M →ₗ[R] N) = finrank R M * finrank S N := by
  simp_rw [finrank, rank_linearMap, toNat_mul, toNat_lift]

variable [Module R S] [SMulCommClass R S S]
/-
**Module.rank_linearMap_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.rank_linearMap_self : Module.rank S (M ->ₗ[R] S) = lift.{u'} (Modul
e.rank R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_linearMap`：Module.rank_linearMap : Module.rank S (M ->ₗ[R] N
) = lift.{w} (Module.rank R M) * lift.{v} (Module.rank S N)
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Module.rank_linearMap_self :
    Module.rank S (M →ₗ[R] S) = lift.{u'} (Module.rank R M) := by
  rw [rank_linearMap, rank_self, lift_one, mul_one]
/-
**Module.finrank_linearMap_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_linearMap_self : finrank S (M ->ₗ[R] S) = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_linearMap`：Module.finrank_linearMap : finrank S (M ->ₗ[R]
 N) = finrank R M * finrank S N
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Module.finrank_linearMap_self : finrank S (M →ₗ[R] S) = finrank R M := by
  rw [finrank_linearMap, finrank_self, mul_one]

end Ring

section AlgHom

variable (K M : Type*) (L : Type v) [CommRing K] [Ring M] [Algebra K M]
  [Module.Free K M] [Module.Finite K M] [CommRing L] [IsDomain L] [Algebra K L]

/-
**Finite.algHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finite.algHom : Finite (M ->ₐ[K] L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.finite`：finite [Module.Finite R M] {ι : Type*} {f : ι 
-> M} (h : LinearIndependent R f) : Finite ι
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `linearIndependent_algHom_toLinearMap`：linearIndependent_algHom_toLinearM
ap (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L]
 [Algebra K L] : LinearInd…
-/
instance Finite.algHom : Finite (M →ₐ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).finite

open Cardinal
/-
**cardinalMk_algHom_le_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinalMk_algHom_le_rank : #(M ->ₐ[K] L) <= lift.{v} (Module.rank K M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.rank_linearMap_self`：Module.rank_linearMap_self : Module.rank S (
M ->ₗ[R] S) = lift.{u'} (Module.rank R M)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用引理 `linearIndependent_algHom_toLinearMap`：linearIndependent_algHom_toLinearM
ap (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L]
 [Algebra K L] : LinearInd…
-/
theorem cardinalMk_algHom_le_rank : #(M →ₐ[K] L) ≤ lift.{v} (Module.rank K M) := by
  convert! (linearIndependent_algHom_toLinearMap K M L).cardinal_lift_le_rank
  · rw [lift_id]
  · have := Module.nontrivial K L
    rw [lift_id, Module.rank_linearMap_self]

@[stacks 09HS]
/-
**card_algHom_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_algHom_le_finrank : Nat.card (M ->ₐ[K] L) <= finrank K M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `cardinalMk_algHom_le_rank`：cardinalMk_algHom_le_rank : #(M ->ₐ[K] L) <= 
lift.{v} (Module.rank K M)
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
-/
theorem card_algHom_le_finrank : Nat.card (M →ₐ[K] L) ≤ finrank K M := by
  convert! toNat_le_toNat (cardinalMk_algHom_le_rank K M L) ?_
  · rw [toNat_lift, finrank]
  · rw [lift_lt_aleph0]; have := Module.nontrivial K L; apply Module.rank_lt_aleph0

end AlgHom

section Integer

variable [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M] [AddCommGroup N]

/-
**Module.Finite.addMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.addMonoidHom [Module.Finite Int N] : Module.Finite Int (M ->
+ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
-/
instance Module.Finite.addMonoidHom [Module.Finite ℤ N] : Module.Finite ℤ (M →+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm
/-
**Module.Free.addMonoidHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Free.addMonoidHom [Module.Free Int N] : Module.Free Int (M ->+ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
instance Module.Free.addMonoidHom [Module.Free ℤ N] : Module.Free ℤ (M →+ N) :=
  letI : Module.Free ℤ (M →ₗ[ℤ] N) := Module.Free.linearMap _ _ _ _
  Module.Free.of_equiv (addMonoidHomLequivInt ℤ).symm

end Integer

