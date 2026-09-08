/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective objects in category of (additive) abelian
groups. The proof that the category of abelian groups has enough injective objects can be found
in `Mathlib/Algebra/Category/Grp/EnoughInjectives.lean`.

## Main results

- `AddCommGrpCat.injective_of_divisible` : a divisible group is also an injective object.

-/

public section

open CategoryTheory

universe u

variable (A : Type u) [AddCommGroup A]

/-
**Module.Baer.of_divisible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Baer.of_divisible [DivisibleBy A Int] : Module.Baer Int A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `DivisibleBy.div_cancel`：∀ {A : Type u_1} {α : Type u_2} {inst : AddMonoi
d A} {inst_1 : SMul α A} {inst_2 : Zero α} [self : DivisibleBy A α]   {n : α} (a
 : A), n ≠ 0…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `SetLike.mk_smul_mk`：mk_smul_mk (r : R) (x : M) (hx : x in s) : r • (⟨x, 
hx⟩ : s) = ⟨r • x, smul_mem r hx⟩
-/
theorem Module.Baer.of_divisible [DivisibleBy A ℤ] : Module.Baer ℤ A := fun I g ↦ by
  rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
  obtain rfl | h0 := eq_or_ne m 0
  · refine ⟨0, fun n hn ↦ ?_⟩
    rw [Submodule.span_zero_singleton] at hn
    subst hn
    exact (map_zero g).symm
  let gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩
  refine ⟨LinearMap.toSpanSingleton ℤ A (DivisibleBy.div gₘ m), fun n hn ↦ ?_⟩
  rcases Submodule.mem_span_singleton.mp hn with ⟨n, rfl⟩
  rw [map_zsmul, LinearMap.toSpanSingleton_apply, DivisibleBy.div_cancel gₘ h0, ← map_zsmul g,
    SetLike.mk_smul_mk]

namespace AddCommGrpCat

/-
**AddCommGrpCat.injective_as_module_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat
`。
形式化陈述：injective_as_module_iff : Injective (ModuleCat.of Int A) ↔ Injective (C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ModuleCat.forget₂AddCommGroupIsEquivalence`：(CategoryTheory.forget₂ (Mod
uleCat ℤ) AddCommGrpCat).IsEquivalence
· 使用定理 `CategoryTheory.Equivalence.map_injective_iff`：map_injective_iff (P : C) 
: Injective (F.functor.obj P) ↔ Injective P
-/
theorem injective_as_module_iff : Injective (ModuleCat.of ℤ A) ↔
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of A) :=
  ((forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.map_injective_iff (ModuleCat.of ℤ A)).symm
/-
**AddCommGrpCat.injective_of_divisible** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`
。
形式化陈述：injective_of_divisible [DivisibleBy A Int] : Injective (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddCommGrpCat.injective_as_module_iff`：injective_as_module_iff : Injecti
ve (ModuleCat.of Int A) ↔ Injective (C
· 使用定理 `Module.injective_object_of_injective_module`：injective_object_of_injecti
ve_module [inj : Injective R M] : CategoryTheory.Injective (ModuleCat.of R M) wh
ere factors g f m
· 使用定理 `Module.Baer.injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [inst
_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q],   Module.Baer R Q → Module.In
jective R Q
· 使用定理 `Module.Baer.of_divisible`：Module.Baer.of_divisible [DivisibleBy A Int] :
 Module.Baer Int A
-/
instance injective_of_divisible [DivisibleBy A ℤ] :
    Injective (C := AddCommGrpCat) (AddCommGrpCat.of A) :=
  (injective_as_module_iff A).mp <|
    Module.injective_object_of_injective_module (inj := (Module.Baer.of_divisible A).injective)

end AddCommGrpCat

