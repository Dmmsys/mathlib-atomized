/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[IsDomain R] [IsPrincipalIdealRing R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `Fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

- `Submodule.inductionOnRank`: if `P` holds for `⊥ : Submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
  on all submodules

- `Submodule.exists_basis_of_pid`: if `R` is a PID, then `N : Submodule R M` is
  free and finitely generated. This is the first part of the structure theorem
  for modules.

- `Submodule.smithNormalForm`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/

@[expose] public section

open Module

universe u v

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {ι : Type*} (b : Basis ι R M)

open Submodule.IsPrincipal Submodule

/-
**eq_bot_of_generator_maximal_map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R
 M} {ϕ : M ->ₗ[R] R} (hϕ : forall ψ : M ->ₗ[R] R, ¬N.map ϕ < N.map ψ) [(N.map ϕ)
.IsPrincipal] (hgen : generator (N.map ϕ) = (0 : R)) : N = ⊥
参数：b : Basis ι R M；hϕ : forall ψ : M ->ₗ[R] R, ¬N.map ϕ < N.map ψ；N.map ϕ；hgen :
 generator (N.map ϕ) = (0 : R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_bot_lt_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBo
t α] {a : α}, ¬⊥ < a ↔ a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
-/
theorem eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R M}
    {ϕ : M →ₗ[R] R} (hϕ : ∀ ψ : M →ₗ[R] R, ¬N.map ϕ < N.map ψ) [(N.map ϕ).IsPrincipal]
    (hgen : generator (N.map ϕ) = (0 : R)) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine b.ext_elem fun i ↦ ?_
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero, Finsupp.zero_apply]
  exact
    (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _
      ⟨x, hx, rfl⟩
/-
**eq_bot_of_generator_maximal_submoduleImage_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：eq_bot_of_generator_maximal_submoduleImage_eq_zero {N O : Submodule R M} (
b : Basis ι R O) (hNO : N <= O) {ϕ : O ->ₗ[R] R} (hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ
.submoduleImage N < ψ.submoduleImage N) [(ϕ.submoduleImage N).IsPrincipal] (hgen
 : generator (ϕ.submoduleImage N) = 0) : N = ⊥
参数：b : Basis ι R O；hNO : N <= O；hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ.submoduleImage N 
< ψ.submoduleImage N；ϕ.submoduleImage N；hgen : generator (ϕ.submoduleImage N) = 
0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mk_eq_zero`：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x
 = 0
· 使用定理 `Module.Basis.ext_elem`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_12}
 [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (
b : Module.…
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.zero_apply`：zero_apply {a : α} : (0 : α ->₀ M) a = 0
· 使用定理 `not_bot_lt_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBo
t α] {a : α}, ¬⊥ < a ↔ a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
· 使用定理 `LinearMap.mem_submoduleImage_of_le`：mem_submoduleImage_of_le {M' : Type*
} [AddCommMonoid M'] [Module R M'] {O : Submodule R M} {ϕ : O ->ₗ[R] M'} {N : Su
bmodule R M} (hNO : N <=…
-/
theorem eq_bot_of_generator_maximal_submoduleImage_eq_zero {N O : Submodule R M} (b : Basis ι R O)
    (hNO : N ≤ O) {ϕ : O →ₗ[R] R} (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (hgen : generator (ϕ.submoduleImage N) = 0) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine (mk_eq_zero _ _).mp (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i ↦ ?_)
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero, Finsupp.zero_apply]
  refine (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _ ?_
  exact (LinearMap.mem_submoduleImage_of_le hNO).mpr ⟨x, hx, rfl⟩

end Ring

open Submodule.IsPrincipal in
/-
**dvd_generator_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_generator_iff {R : Type*} [CommSemiring R] {I : Ideal R} [I.IsPrincipa
l] {x : R} (hx : x in I) : x ∣ generator I ↔ I = Ideal.span {x}
参数：hx : x in I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem dvd_generator_iff {R : Type*} [CommSemiring R] {I : Ideal R} [I.IsPrincipal] {x : R}
    (hx : x ∈ I) : x ∣ generator I ↔ I = Ideal.span {x} := by
  simp_rw [le_antisymm_iff, I.span_singleton_le_iff_mem.2 hx, and_true, ← Ideal.mem_span_singleton]
  conv_rhs => rw [← span_singleton_generator I, Submodule.span_singleton_le_iff_mem]

section PrincipalIdealDomain

open Submodule.IsPrincipal Set Submodule

variable {ι : Type*} {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {b : ι → M}

section StrongRankCondition

variable [IsPrincipalIdealRing R]

open Submodule.IsPrincipal

/-
**generator_maximal_submoduleImage_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：generator_maximal_submoduleImage_dvd {N O : Submodule R M} (hNO : N <= O) 
{ϕ : O ->ₗ[R] R} (hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleI
mage N) [(ϕ.submoduleImage N).IsPrincipal] (y : M) (yN : y in N) (ϕy_eq : ϕ ⟨y, 
hNO yN⟩ = generator (ϕ.submoduleImage N)) (ψ : O ->ₗ[R] R) : generator (ϕ.submod
uleImage N) ∣ ψ ⟨y, hNO yN⟩
参数：hNO : N <= O；hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleIma
ge N；ϕ.submoduleImage N；y : M；yN : y in N；ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.s
ubmoduleImage N)；ψ : O ->ₗ[R] R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.IsPrincipal.mem_iff_generator_dvd`：mem_iff_generator_dvd (S : 
Ideal R) [S.IsPrincipal] {x : R} : x in S ↔ generator S ∣ x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_generator_iff`：dvd_generator_iff {R : Type*} [CommSemiring R] {I : I
deal R} [I.IsPrincipal] {x : R} (hx : x in I) : x ∣ generator I ↔ I = Ideal.span
 {x}
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `Submodule.mem_span_insert`：mem_span_insert {y} : x in span R (insert y s
) ↔ exists a : R, exists z in span R s, x = a • y + z
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LinearMap.mem_submoduleImage_of_le`：mem_submoduleImage_of_le {M' : Type*
} [AddCommMonoid M'] [Module R M'] {O : Submodule R M} {ϕ : O ->ₗ[R] M'} {N : Su
bmodule R M} (hNO : N <=…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.eq_of_not_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 b ≤ a → ¬b < a → a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
-/
theorem generator_maximal_submoduleImage_dvd {N O : Submodule R M} (hNO : N ≤ O) {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (y : M) (yN : y ∈ N)
    (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submoduleImage N)) (ψ : O →ₗ[R] R) :
    generator (ϕ.submoduleImage N) ∣ ψ ⟨y, hNO yN⟩ := by
  let a : R := generator (ϕ.submoduleImage N)
  let d : R := IsPrincipal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))
  refine dvd_trans ?_ d_dvd_right
  rw [dvd_generator_iff, Ideal.span, ←
    span_singleton_generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})]
  · obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩ := by
      obtain ⟨r₁, r₂', hr₂', hr₁⟩ :=
        mem_span_insert.mp (IsPrincipal.generator_mem (Submodule.span R {a, ψ ⟨y, hNO yN⟩}))
      obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂'
      exact ⟨r₁, r₂, hr₁⟩
    let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ
    have : span R {d} ≤ ψ'.submoduleImage N := by
      rw [span_le, singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_submoduleImage_of_le hNO]
      refine ⟨y, yN, ?_⟩
      change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d
      rw [d_eq, ϕy_eq]
    refine
      le_antisymm (this.trans (le_of_eq ?_)) (Ideal.span_singleton_le_span_singleton.mpr d_dvd_left)
    rw [span_singleton_generator]
    apply (le_trans _ this).eq_of_not_lt' (hϕ ψ')
    rw [← span_singleton_generator (ϕ.submoduleImage N)]
    exact Ideal.span_singleton_le_span_singleton.mpr d_dvd_left
  · exact subset_span (mem_insert _ _)

variable [IsDomain R]

set_option backward.isDefEq.respectTransparency false in
/-- The induction hypothesis of `Submodule.basisOfPid` and `Submodule.smithNormalForm`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction going.
-/
/-
**Submodule.basis_of_pid_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.basis_of_pid_aux [Finite ι] {O : Type*} [AddCommGroup O] [Module
 R O] (M N : Submodule R O) (b'M : Basis ι R M) (N_bot : N != ⊥) (N_le_M : N <= 
M) : exists y in M, exists a : R, a • y in N ∧ exists M' <= M, exists N' <= N, N
' <= M' ∧ (forall (c : R) (z : O), z in M' -> c • y + z = 0 -> c = 0) ∧ (forall 
(c : R) (z : O), z in N' -> c • a • y + z = 0 -> c = 0) ∧ forall (n') (bN' : Bas
is (Fin n') R N'), exists bN : Basis (Fin (n' + 1)) R N, forall (m') (hn'm' : n'
 <= m') (bM' : Basis (Fin 
参数：M N : Submodule R O；b'M : Basis ι R M；N_bot : N != ⊥；N_le_M : N <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_has_maximal_iff_noetherian`：set_has_maximal_iff_noetherian : (forall
 a : Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬M' < I)
 ↔ IsNoetherian R M
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `eq_bot_of_generator_maximal_submoduleImage_eq_zero`：eq_bot_of_generator_
maximal_submoduleImage_eq_zero {N O : Submodule R M} (b : Basis ι R O) (hNO : N 
<= O) {ϕ : O ->ₗ[R] R} (hϕ : forall ψ : …
· 使用定理 `LinearMap.mem_submoduleImage_of_le`：mem_submoduleImage_of_le {M' : Type*
} [AddCommMonoid M'] [Module R M'] {O : Submodule R M} {ϕ : O ->ₗ[R] M'} {N : Su
bmodule R M} (hNO : N <=…
· 使用定理 `generator_maximal_submoduleImage_dvd`：generator_maximal_submoduleImage_d
vd {N O : Submodule R M} (hNO : N <= O) {ϕ : O ->ₗ[R] R} (hϕ : forall ψ : O ->ₗ[
R] R, ¬ϕ.submoduleImage N …
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
The induction hypothesis of `Submodule.basisOfPid` and `Submodule.smithNormalFor
m`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair
 of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get 
a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'
`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction
 going.
-/
theorem Submodule.basis_of_pid_aux [Finite ι] {O : Type*} [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M, ∃ a : R, a • y ∈ N ∧ ∃ M' ≤ M, ∃ N' ≤ N,
      N' ≤ M' ∧ (∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0) ∧
      (∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0) ∧
      ∀ (n') (bN' : Basis (Fin n') R N'),
        ∃ bN : Basis (Fin (n' + 1)) R N,
          ∀ (m') (hn'm' : n' ≤ m') (bM' : Basis (Fin m') R M'),
            ∃ (hnm : n' + 1 ≤ m' + 1) (bM : Basis (Fin (m' + 1)) R M),
              ∀ as : Fin n' → R,
                (∀ i : Fin n', (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)) →
                  ∃ as' : Fin (n' + 1) → R,
                    ∀ i : Fin (n' + 1), (bN i : O) = as' i • (bM (Fin.castLE hnm i) : O) := by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : ∃ ϕ : M →ₗ[R] R, ∀ ψ : M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M →ₗ[R] R ↦ ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ ↦ P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.choose
  have ϕ_max := this.choose_spec
  -- Since `ϕ(N)` is an `R`-submodule of the PID `R`,
  -- it is principal and generated by some `a`.
  let a := generator (ϕ.submoduleImage N)
  have a_mem : a ∈ ϕ.submoduleImage N := generator_mem _
  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases a_zero : a = 0
  · have := eq_bot_of_generator_maximal_submoduleImage_eq_zero b'M N_le_M ϕ_max a_zero
    contradiction
  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i ↦
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  cases nonempty_fintype ι
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' ∈ M := M.sum_mem fun i _ ↦ M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [map_sum, map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_smul, ← hc]
    rfl
  -- We found a `y` and an `a`!
  refine ⟨y', y'M, a, a_smul_y'.symm ▸ yN, ?_⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm)
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero
  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`.
  let M' : Submodule R O := (LinearMap.ker ϕ).map M.subtype
  let N' : Submodule R O := (LinearMap.ker (ϕ.comp (inclusion N_le_M))).map N.subtype
  have M'_le_M : M' ≤ M := M.map_subtype_le (LinearMap.ker ϕ)
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [N', mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N := N.map_subtype_le (LinearMap.ker (ϕ.comp (inclusion N_le_M)))
  -- So fill in those results as well.
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', ?_⟩
  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', c • y' + z = 0 → c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by exact @Subtype.coe_injective O (· ∈ M) _ _ hc
    simpa only [map_add, map_zero, map_smul, smul_eq_mul, add_zero, mul_eq_zero, ϕy'_ne_zero, hx',
      or_false] using congr_arg ϕ hc'
  -- And `a • y'` is orthogonal to `N'`.
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hc
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') ?_)).resolve_left a_zero
    rw [mul_comm, mul_smul, hc]
  -- So we can extend a basis for `N'` with `y`
  refine ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' ↦ ⟨?_, ?_⟩⟩
  · refine Basis.mkFinConsOfLE y yN bN' N'_le_N ?_ ?_
    · intro c z zN' hc
      refine ay'_ortho_N' c z zN' ?_
      rwa [← a_smul_y'] at hc
    · intro z zN
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
      refine ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, ?_, ?_⟩⟩
      · refine LinearMap.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from ?_)
        rw [map_sub, map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm, sub_self]
      · simp only [sub_eq_add_neg, neg_smul, coe_subtype]
  -- And extend a basis for `M'` with `y'`
  intro m' hn'm' bM'
  refine ⟨Nat.succ_le_succ hn'm', ?_, ?_⟩
  · refine Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M' ?_
    intro z zM
    refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr ?_, ?_⟩⟩
    · rw [map_sub, map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
    · rw [map_sub, map_smul, sub_eq_add_neg, neg_smul]
      rfl
  -- It remains to show the extended bases are compatible with each other.
  intro as h
  refine ⟨Fin.cons a as, ?_⟩
  intro i
  rw [Basis.coe_mkFinConsOfLE, Basis.coe_mkFinConsOfLE]
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp only [Fin.cons_zero, Fin.castLE_zero]
    exact a_smul_y'.symm
  · rw [Fin.castLE_succ]
    simp only [Fin.cons_succ, Function.comp_apply, coe_inclusion, h i]

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the basis,
see `Submodule.basisOfPid`.

See also the stronger version `Submodule.smithNormalForm`.
-/
/-
**Submodule.nonempty_basis_of_pid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.nonempty_basis_of_pid {ι : Type*} [Finite ι] (b : Basis ι R M) (
N : Submodule R M) : exists n : Nat, Nonempty (Basis (Fin n) R N)
参数：b : Basis ι R M；N : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.basis_of_pid_aux`：Submodule.basis_of_pid_aux [Finite ι] {O : T
ype*} [AddCommGroup O] [Module R O] (M N : Submodule R O) (b'M : Basis ι R M) (N
_bot : N != ⊥) (…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
A submodule of a free `R`-module of finite rank is also a free `R`-module of fin
ite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the bas
is,
see `Submodule.basisOfPid`.

See also the stronger version `Submodule.smithNormalForm`.
-/
theorem Submodule.nonempty_basis_of_pid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : ∃ n : ℕ, Nonempty (Basis (Fin n) R N) := by
  have := Classical.decEq M
  cases nonempty_fintype ι
  induction N using inductionOnRank b with | ih N ih =>
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, ⟨Basis.empty _⟩⟩
  obtain ⟨y, -, a, hay, M', -, N', N'_le_N, -, -, ay_ortho, h'⟩ :=
    Submodule.basis_of_pid_aux ⊤ N b' N_bot le_top
  obtain ⟨n', ⟨bN'⟩⟩ := ih N' N'_le_N _ hay ay_ortho
  obtain ⟨bN, _hbN⟩ := h' n' bN'
  exact ⟨n' + 1, ⟨bN⟩⟩

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalForm`.
-/
/-
**Submodule.basisOfPid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.basisOfPid {ι : Type*} [Finite ι] (b : Basis ι R M) (N : Submodu
le R M) : Σ n : Nat, Basis (Fin n) R N
参数：b : Basis ι R M；N : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.nonempty_basis_of_pid`：Submodule.nonempty_basis_of_pid {ι : Ty
pe*} [Finite ι] (b : Basis ι R M) (N : Submodule R M) : exists n : Nat, Nonempty
 (Basis (Fin n) R N)

--- 原说明 ---
A submodule of a free `R`-module of finite rank is also a free `R`-module of fin
ite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalForm`.
-/
noncomputable def Submodule.basisOfPid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : Σ n : ℕ, Basis (Fin n) R N :=
  ⟨_, (N.nonempty_basis_of_pid b).choose_spec.some⟩
/-
**Submodule.basisOfPid_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.basisOfPid_bot {ι : Type*} [Finite ι] (b : Basis ι R M) : Submod
ule.basisOfPid b ⊥ = ⟨0, Basis.empty _⟩
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Sigma.eq`：∀ {α : Type u_7} {β : α → Type u_8} {p₁ p₂ : (a : α) × β a} (h
₁ : p₁.fst = p₂.fst),   Eq.recOn h₁ p₁.snd = p₂.snd → p₁ = p₂
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
-/
theorem Submodule.basisOfPid_bot {ι : Type*} [Finite ι] (b : Basis ι R M) :
    Submodule.basisOfPid b ⊥ = ⟨0, Basis.empty _⟩ := by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  let e : Fin n ≃ Fin 0 := b'.indexEquiv (Basis.empty _ : Basis (Fin 0) R (⊥ : Submodule R M))
  obtain rfl : n = 0 := by simpa using Fintype.card_eq.mpr ⟨e⟩
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalFormOfLE`.
-/
/-
**Submodule.basisOfPidOfLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.basisOfPidOfLE {ι : Type*} [Finite ι] {N O : Submodule R M} (hNO
 : N <= O) (b : Basis ι R O) : Σ n : Nat, Basis (Fin n) R N
参数：hNO : N <= O；b : Basis ι R O。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule inside a free `R`-submodule of finite rank is also a free `R`-module
 of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalFormOfLE`.
-/
noncomputable def Submodule.basisOfPidOfLE {ι : Type*} [Finite ι] {N O : Submodule R M}
    (hNO : N ≤ O) (b : Basis ι R O) : Σ n : ℕ, Basis (Fin n) R N :=
  let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
/-
**Submodule.basisOfPidOfLESpan** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.basisOfPidOfLESpan {ι : Type*} [Finite ι] {b : ι -> M} (hb : Lin
earIndependent R b) {N : Submodule R M} (le : N <= Submodule.span R (Set.range b
)) : Σ n : Nat, Basis (Fin n) R N
参数：hb : LinearIndependent R b；le : N <= Submodule.span R (Set.range b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule inside the span of a linear independent family is a free `R`-module 
of finite rank,
if `R` is a principal ideal domain.
-/
noncomputable def Submodule.basisOfPidOfLESpan {ι : Type*} [Finite ι] {b : ι → M}
    (hb : LinearIndependent R b) {N : Submodule R M} (le : N ≤ Submodule.span R (Set.range b)) :
    Σ n : ℕ, Basis (Fin n) R N :=
  Submodule.basisOfPidOfLE le (Basis.span hb)

/-- A finite type torsion free module over a PID admits a basis. -/
/-
**Module.basisOfFiniteTypeTorsionFree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.basisOfFiniteTypeTorsionFree [Fintype ι] {s : ι -> M} (hs : span R 
(range s) = ⊤) [IsTorsionFree R M] : Σ n : Nat, Basis (Fin n) R M
参数：hs : span R (range s) = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_lsmul`：ker_lsmul [IsTorsionFree R M] {a : R} (ha : a != 0)
 : LinearMap.ker (LinearMap.lsmul R M a) = ⊥

--- 原说明 ---
A finite type torsion free module over a PID admits a basis.
-/
noncomputable def Module.basisOfFiniteTypeTorsionFree [Fintype ι] {s : ι → M}
    (hs : span R (range s) = ⊤) [IsTorsionFree R M] : Σ n : ℕ, Basis (Fin n) R M := by
  classical
    -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
    have := exists_maximal_linearIndepOn R s
    let I : Set ι := this.choose
    obtain
      ⟨indepI : LinearIndependent R (s ∘ (fun x => x) : I → M), hI :
        ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I)⟩ :=
      this.choose_spec
    let N := span R (range <| (s ∘ (fun x => x) : I → M))
    -- same as `span R (s '' I)` but more convenient
    let _sI : I → N := fun i ↦ ⟨s i.1, subset_span (mem_range_self i)⟩
    -- `s` restricted to `I` is a basis of `N`
    let sI_basis : Basis I R N := Basis.span indepI
    -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
    have exists_a : ∀ i : ι, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
      intro i
      by_cases hi : i ∈ I
      · use 1, zero_ne_one.symm
        rw [one_smul]
        exact subset_span (mem_range_self (⟨i, hi⟩ : I))
      · simpa [image_eq_range s I] using! hI i hi
    choose a ha ha' using exists_a
    let A := ∏ i, a i
    have hA : A ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      simpa using! ha
    -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
    let φ : M →ₗ[R] M := LinearMap.lsmul R M A
    have : LinearMap.ker φ = ⊥ := LinearMap.ker_lsmul hA
    let ψ := LinearEquiv.ofInjective φ (LinearMap.ker_eq_bot.mp this)
    have : LinearMap.range φ ≤ N := by
      -- as announced, `A • M ⊆ N`
      suffices ∀ i, φ (s i) ∈ N by
        rw [LinearMap.range_eq_map, ← hs, map_span_le]
        rintro _ ⟨i, rfl⟩
        apply this
      intro i
      calc
        (∏ j ∈ {i}ᶜ, a j) • a i • s i ∈ N := N.smul_mem _ (ha' i)
        _ = (∏ j, a j) • s i := by rw [Fintype.prod_eq_prod_compl_mul i, mul_smul]
    -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
    obtain ⟨n, b : Basis (Fin n) R (LinearMap.range φ)⟩ := Submodule.basisOfPidOfLE this sI_basis
    -- hence `M` is free.
    exact ⟨n, b.map ψ.symm⟩
/-
**Module.free_of_finite_type_torsion_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.free_of_finite_type_torsion_free [_root_.Finite ι] {s : ι -> M} (hs
 : span R (range s) = ⊤) [IsTorsionFree R M] : Module.Free R M
参数：hs : span R (range s) = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
theorem Module.free_of_finite_type_torsion_free [_root_.Finite ι] {s : ι → M}
    (hs : span R (range s) = ⊤) [IsTorsionFree R M] : Module.Free R M := by
  cases nonempty_fintype ι
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree hs
  exact Module.Free.of_basis b

/-- A finite type torsion free module over a PID admits a basis. -/
/-
**Module.basisOfFiniteTypeTorsionFree'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.basisOfFiniteTypeTorsionFree' [Module.Finite R M] [IsTorsionFree R 
M] : Σ n : Nat, Basis (Fin n) R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite type torsion free module over a PID admits a basis.
-/
noncomputable def Module.basisOfFiniteTypeTorsionFree' [Module.Finite R M]
    [IsTorsionFree R M] : Σ n : ℕ, Basis (Fin n) R M :=
  Module.basisOfFiniteTypeTorsionFree Module.Finite.exists_fin.choose_spec.choose_spec
/-
**Module.free_of_finite_type_torsion_free'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.free_of_finite_type_torsion_free' [Module.Finite R M] [IsTorsionFre
e R M] : Module.Free R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
instance Module.free_of_finite_type_torsion_free' [Module.Finite R M] [IsTorsionFree R M] :
    Module.Free R M := by
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree'
  exact Module.Free.of_basis b
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [CommRing S] [Algebra R S] {I : Ideal S} [hI₁ : Module.Finite R I]
    [hI₂ : IsTorsionFree R I] : Free R I := by
  have : Module.Finite R (restrictScalars R I) := hI₁
  have : IsTorsionFree R (restrictScalars R I) := hI₂
  change Module.Free R (restrictScalars R I)
  exact Module.free_of_finite_type_torsion_free'
/-
**Module.free_iff_isTorsionFree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.free_iff_isTorsionFree [Module.Finite R M] : Free R M ↔ IsTorsionFr
ee R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.instIsTorsionFree`：∀ (R : Type u) (M : Type v) [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Module.Free R 
M], Module.IsTorsio…
-/
theorem Module.free_iff_isTorsionFree [Module.Finite R M] : Free R M ↔ IsTorsionFree R M :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end StrongRankCondition

section SmithNormal

/-- A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form. -/
/-
**Module.Basis.SmithNormalForm** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module.Basis`。
形式化陈述：{R : Type u_2} →   [inst : CommRing R] →     {M : Type u_3} →       [inst_
1 : AddCommGroup M] →         [inst_2 : _root_.Module R M] → Submodule R M → Typ
e u_4 → ℕ → Type (max (max u_2 u_3) u_4)
参数：max (max u_2 u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form.
-/
structure Module.Basis.SmithNormalForm (N : Submodule R M) (ι : Type*) (n : ℕ) where
  /-- The basis of M. -/
  bM : Basis ι R M
  /-- The basis of N. -/
  bN : Basis (Fin n) R N
  /-- The mapping between the vectors of the bases. -/
  f : Fin n ↪ ι
  /-- The (diagonal) entries of the matrix. -/
  a : Fin n → R
  /-- The SNF relation between the vectors of the bases. -/
  snf : ∀ i, (bN i : M) = a i • bM (f i)

namespace Module.Basis.SmithNormalForm

variable {n : ℕ} {N : Submodule R M} (snf : Basis.SmithNormalForm N ι n) (m : N)

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.SmithNormalForm.repr_eq_zero_of_notMem_range** 是 Mathlib 中的一个引理，位
于命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：repr_eq_zero_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) : snf.bM.r
epr m i = 0
参数：hi : i ∉ Set.range snf.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.mem_submodule_iff`：mem_submodule_iff {P : Submodule R M} (b
 : Basis ι R P) {x : M} : x in P ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x
 => x • (b i : M)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.SmithNormalForm.snf`：∀ {R : Type u_2} [inst : CommRing R] {
M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} {ι : Type u…
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.sum_fun_zero`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M),   (f.sum fun x x_1 => 0) 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma repr_eq_zero_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    snf.bM.repr m i = 0 := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hi : ∀ j, snf.f j ≠ i := by simpa using hi
  simp [hi, snf.snf, map_finsuppSum]
/-
**Module.Basis.SmithNormalForm.le_ker_coord_of_notMem_range** 是 Mathlib 中的一个引理，位
于命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：le_ker_coord_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) : N <= Lin
earMap.ker (snf.bM.coord i)
参数：hi : i ∉ Set.range snf.f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Basis.SmithNormalForm.repr_eq_zero_of_notMem_range`：repr_eq_zero_
of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) : snf.bM.repr m i = 0
-/
lemma le_ker_coord_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    N ≤ LinearMap.ker (snf.bM.coord i) :=
  fun m hm ↦ snf.repr_eq_zero_of_notMem_range ⟨m, hm⟩ hi

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.SmithNormalForm.repr_apply_embedding_eq_repr_smul** 是 Mathlib 中的一
个定理，位于命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Submodule R M} (s
nf : Module.Basis.SmithNormalForm N ι n) (m : ↥N)   {i : Fin n}, (snf.bM.repr ↑m
) (snf.f i) = (snf.bN.repr (snf.a i • m)) i
参数：snf : Module.Basis.SmithNormalForm N ι n；m : ↥N；snf.bM.repr ↑m；snf.f i；snf.bN
.repr (snf.a i • m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.mem_submodule_iff`：mem_submodule_iff {P : Submodule R M} (b
 : Basis ι R P) {x : M} : x in P ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x
 => x • (b i : M)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `Module.Basis.SmithNormalForm.snf`：∀ {R : Type u_2} [inst : CommRing R] {
M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} {ι : Type u…
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Finsupp.sum_ite_eq'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) 
(a : α) (…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
（共 33 条，此处仅展示前 30 条）
-/
@[simp] lemma repr_apply_embedding_eq_repr_smul {i : Fin n} :
    snf.bM.repr m (snf.f i) = snf.bN.repr (snf.a i • m) i := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hm : (⟨Finsupp.sum c fun i t ↦ t • (↑(snf.bN i) : M), hm⟩ : N) =
      Finsupp.sum c fun i t ↦ t • ⟨snf.bN i, (snf.bN i).2⟩ := by
    ext; change _ = N.subtype _; simp [map_finsuppSum]
  classical
  simp_rw [hm, map_smul, map_finsuppSum, map_smul, Subtype.coe_eta, repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single, Finsupp.smul_apply, snf.snf,
    map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_apply,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Finsupp.sum_ite_eq',
    Finsupp.mem_support_iff, ite_not, mul_comm, ite_eq_right_iff]
  exact fun a ↦ (mul_eq_zero_of_right _ a).symm

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.SmithNormalForm.repr_comp_embedding_eq_smul** 是 Mathlib 中的一个定理，位于
命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Submodule R M} (s
nf : Module.Basis.SmithNormalForm N ι n) (m : ↥N),   ⇑(snf.bM.repr ↑m) ∘ ⇑snf.f 
= snf.a • ⇑(snf.bN.repr m)
参数：snf : Module.Basis.SmithNormalForm N ι n；m : ↥N；snf.bM.repr ↑m；snf.bN.repr m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.SmithNormalForm.repr_apply_embedding_eq_repr_smul`：∀ {ι : T
ype u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Sub…
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
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma repr_comp_embedding_eq_smul :
    snf.bM.repr m ∘ snf.f = snf.a • (snf.bN.repr m : Fin n → R) := by
  ext i
  simp [Pi.smul_apply (snf.a i)]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.SmithNormalForm.coord_apply_embedding_eq_smul_coord** 是 Mathlib 中
的一个定理，位于命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Submodule R M} (s
nf : Module.Basis.SmithNormalForm N ι n) {i : Fin n},   snf.bM.coord (snf.f i) ∘
ₗ N.subtype = snf.a i • snf.bN.coord i
参数：snf : Module.Basis.SmithNormalForm N ι n；snf.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.SmithNormalForm.repr_apply_embedding_eq_repr_smul`：∀ {ι : T
ype u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Sub…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `Pi.smul_apply`：∀ {ι : Type u_1} {α : Type u_2} {M : ι → Type u_5} [inst 
: (i : ι) → SMul α (M i)] (a : α) (f : (i : ι) → M i) (i : ι),   (a • f) i = a •
 f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coord_apply_embedding_eq_smul_coord {i : Fin n} :
    snf.bM.coord (snf.f i) ∘ₗ N.subtype = snf.a i • snf.bN.coord i := by
  ext m
  simp [Pi.smul_apply (snf.a i)]

/-- Given a Smith-normal-form pair of bases for `N ⊆ M`, and a linear endomorphism `f` of `M`
that preserves `N`, the diagonal of the matrix of the restriction `f` to `N` does not depend on
which of the two bases for `N` is used. -/
@[simp]
/-
**Module.Basis.SmithNormalForm.toMatrix_restrict_eq_toMatrix** 是 Mathlib 中的一个引理，
位于命名空间 `Module.Basis.SmithNormalForm`。
形式化陈述：toMatrix_restrict_eq_toMatrix [Fintype ι] [DecidableEq ι] (f : M ->ₗ[R] M)
 (hf : forall x, f x in N) (hf' : forall x in N, f x in N
参数：f : M ->ₗ[R] M；hf : forall x, f x in N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.SmithNormalForm.repr_apply_embedding_eq_repr_smul`：∀ {ι : T
ype u_1} {R : Type u_2} [inst : CommRing R] {M : Type u_3} [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] {n : ℕ} {N : Sub…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.SmithNormalForm.snf`：∀ {R : Type u_2} [inst : CommRing R] {
M : Type u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} {ι : Type u…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a Smith-normal-form pair of bases for `N ⊆ M`, and a linear endomorphism `
f` of `M`
that preserves `N`, the diagonal of the matrix of the restriction `f` to `N` doe
s not depend on
which of the two bases for `N` is used.
-/
lemma toMatrix_restrict_eq_toMatrix [Fintype ι] [DecidableEq ι]
    (f : M →ₗ[R] M) (hf : ∀ x, f x ∈ N) (hf' : ∀ x ∈ N, f x ∈ N := fun x _ ↦ hf x) {i : Fin n} :
    LinearMap.toMatrix snf.bN snf.bN (LinearMap.restrict f hf') i i =
    LinearMap.toMatrix snf.bM snf.bM f (snf.f i) (snf.f i) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    snf.repr_apply_embedding_eq_repr_smul ⟨_, (hf _)⟩]
  congr
  ext
  simp [snf.snf]

end Module.Basis.SmithNormalForm

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `Submodule.smithNormalFormOfLE` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

This is a strengthening of `Submodule.basisOfPidOfLE`.
-/
/-
**Submodule.exists_smith_normal_form_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_smith_normal_form_of_le [Finite ι] (b : Basis ι R M) (N O
 : Submodule R M) (N_le_O : N <= O) : exists (n o : Nat) (hno : n <= o) (bO : Ba
sis (Fin o) R O) (bN : Basis (Fin n) R N) (a : Fin n -> R), forall i, (bN i : M)
 = a i • bO (Fin.castLE hno i)
参数：b : Basis ι R M；N O : Submodule R M；N_le_O : N <= O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.basis_of_pid_aux`：Submodule.basis_of_pid_aux [Finite ι] {O : T
ype*} [AddCommGroup O] [Module R O] (M N : Submodule R O) (b'M : Basis ι R M) (N
_bot : N != ⊥) (…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagona
l matrix
in Smith normal form.

See `Submodule.smithNormalFormOfLE` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

This is a strengthening of `Submodule.basisOfPidOfLE`.
-/
theorem Submodule.exists_smith_normal_form_of_le [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N ≤ O) :
    ∃ (n o : ℕ) (hno : n ≤ o) (bO : Basis (Fin o) R O) (bN : Basis (Fin n) R N) (a : Fin n → R),
      ∀ i, (bN i : M) = a i • bO (Fin.castLE hno i) := by
  cases nonempty_fintype ι
  induction O using inductionOnRank b generalizing N with | ih M0 ih =>
  obtain ⟨m, b'M⟩ := M0.basisOfPid b
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
  obtain ⟨y, hy, a, _, M', M'_le_M, N', _, N'_le_M', y_ortho, _, h⟩ :=
    Submodule.basis_of_pid_aux M0 N b'M N_bot N_le_O
  obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M'
  obtain ⟨bN, h'⟩ := h n' bN'
  obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
  obtain ⟨as, has⟩ := h'' as' has'
  exact ⟨_, _, hmn, bM, bN, as, has⟩

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `Submodule.exists_smith_normal_form_of_le` for a version of this theorem that doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `Submodule.basisOfPidOfLe`.
-/
/-
**Submodule.smithNormalFormOfLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormOfLE [Finite ι] (b : Basis ι R M) (N O : Submodul
e R M) (N_le_O : N <= O) : Σ o n : Nat, Basis.SmithNormalForm (N.comap O.subtype
) (Fin o) n
参数：b : Basis ι R M；N O : Submodule R M；N_le_O : N <= O。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_smith_normal_form_of_le`：Submodule.exists_smith_normal_
form_of_le [Finite ι] (b : Basis ι R M) (N O : Submodule R M) (N_le_O : N <= O) 
: exists (n o : Nat) (hno : n …

--- 原说明 ---
If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagona
l matrix
in Smith normal form.

See `Submodule.exists_smith_normal_form_of_le` for a version of this theorem tha
t doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `Submodule.basisOfPidOfLe`.
-/
noncomputable def Submodule.smithNormalFormOfLE [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N ≤ O) : Σ o n : ℕ, Basis.SmithNormalForm (N.comap O.subtype) (Fin o) n := by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  refine
    ⟨o, n, bO, bN.map (comapSubtypeEquivOfLe N_le_O).symm, (Fin.castLEEmb hno), a,
      fun i ↦ ?_⟩
  ext
  simp only [snf, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_symm_apply,
    Submodule.coe_smul_of_tower, Fin.castLEEmb_apply]

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

This is a strengthening of `Submodule.basisOfPid`.

See also `Ideal.smithNormalForm`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
/-
**Submodule.smithNormalForm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalForm [Finite ι] (b : Basis ι R M) (N : Submodule R M)
 : Σ n : Nat, Basis.SmithNormalForm N ι n
参数：b : Basis ι R M；N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagona
l matrix
in Smith normal form.

This is a strengthening of `Submodule.basisOfPid`.

See also `Ideal.smithNormalForm`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
noncomputable def Submodule.smithNormalForm [Finite ι] (b : Basis ι R M) (N : Submodule R M) :
    Σ n : ℕ, Basis.SmithNormalForm N ι n :=
  let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLE b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i ↦ by
    simp only [bM', snf, Basis.map_apply, LinearEquiv.ofTop_apply, Submodule.coe_smul_of_tower,
      Submodule.comapSubtypeEquivOfLe_apply_coe, Basis.reindex_apply,
      Equiv.toEmbedding_apply, Function.Embedding.trans_apply, Equiv.symm_apply_apply]⟩

section full_rank

variable {N : Submodule R M}

/--
If `M` is finite free over a PID `R`, then for any submodule `N` of the same rank,
we can find basis for `M` and `N` with the same indexing such that the inclusion map
is a square diagonal matrix.

See `Submodule.exists_smith_normal_form_of_rank_eq` for a version that states the
existence of the basis.
-/
/-
**Submodule.smithNormalFormOfRankEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormOfRankEq [Fintype ι] (b : Basis ι R M) (h : Modul
e.finrank R N = Module.finrank R M) : Basis.SmithNormalForm N ι (Fintype.card ι)
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `M` is finite free over a PID `R`, then for any submodule `N` of the same ran
k,
we can find basis for `M` and `N` with the same indexing such that the inclusion
 map
is a square diagonal matrix.

See `Submodule.exists_smith_normal_form_of_rank_eq` for a version that states th
e
existence of the basis.
-/
noncomputable def Submodule.smithNormalFormOfRankEq [Fintype ι] (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Basis.SmithNormalForm N ι (Fintype.card ι) :=
  let ⟨n, bM, bN, f, a, snf⟩ := N.smithNormalForm b
  let e : Fin n ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, ← Module.finrank_eq_card_basis bM, ← h,
      Module.finrank_eq_card_basis bN])
  ⟨bM, bN.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i ↦ by
    simp only [snf, Basis.coe_reindex, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      (· ∘ ·)]⟩

variable [Finite ι]

/--
If `M` is finite free over a PID `R`, then for any submodule `N` of the same rank,
we can find basis for `M` and `N` with the same indexing such that the inclusion map
is a square diagonal matrix.

See also `Submodule.smithNormalFormOfRankEq` for a version of this theorem that returns
a `Basis.SmithNormalForm`.
-/
/-
**Submodule.exists_smith_normal_form_of_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_smith_normal_form_of_rank_eq (b : Basis ι R M) (h : Modul
e.finrank R N = Module.finrank R M) : exists (b' : Basis ι R M) (a : ι -> R) (ab
' : Basis ι R N), forall i, (ab' i : M) = a i • b' i
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` is finite free over a PID `R`, then for any submodule `N` of the same ran
k,
we can find basis for `M` and `N` with the same indexing such that the inclusion
 map
is a square diagonal matrix.

See also `Submodule.smithNormalFormOfRankEq` for a version of this theorem that 
returns
a `Basis.SmithNormalForm`.
-/
theorem Submodule.exists_smith_normal_form_of_rank_eq (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∃ (b' : Basis ι R M) (a : ι → R) (ab' : Basis ι R N), ∀ i, (ab' i : M) = a i • b' i := by
  cases nonempty_fintype ι
  let ⟨bM, bN, f, a, snf⟩ := N.smithNormalFormOfRankEq b h
  let e : Fin (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : ∀ i, f (e.symm i) = i := e.apply_symm_apply
  exact
    ⟨bM, a ∘ e.symm, bN.reindex e, fun i ↦ by
      simp only [snf, fe,
          Basis.coe_reindex, (· ∘ ·)]⟩

/--
If `M` is finite free over a PID `R`, then for any submodule `N` of the same rank,
we can find basis for `M` and `N` with the same indexing such that the inclusion map
is a square diagonal matrix; this is the basis for `M`. See:
* `Submodule.smithNormalFormBotBasis` for the basis on `N`,
* `Submodule.smithNormalFormCoeffs` for the entries of the diagonal matrix
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
/-
**Submodule.smithNormalFormTopBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormTopBasis (b : Basis ι R M) (h : Module.finrank R 
N = Module.finrank R M) : Basis ι R M
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_smith_normal_form_of_rank_eq`：Submodule.exists_smith_no
rmal_form_of_rank_eq (b : Basis ι R M) (h : Module.finrank R N = Module.finrank 
R M) : exists (b' : Basis ι R M) (a…

--- 原说明 ---
If `M` is finite free over a PID `R`, then for any submodule `N` of the same ran
k,
we can find basis for `M` and `N` with the same indexing such that the inclusion
 map
is a square diagonal matrix; this is the basis for `M`. See:
* `Submodule.smithNormalFormBotBasis` for the basis on `N`,
* `Submodule.smithNormalFormCoeffs` for the entries of the diagonal matrix
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
noncomputable def Submodule.smithNormalFormTopBasis (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : Basis ι R M :=
  (exists_smith_normal_form_of_rank_eq b h).choose

/--
If `M` is finite free over a PID `R`, then for any submodule `N` of the same rank,
we can find basis for `M` and `N` with the same indexing such that the inclusion map
is a square diagonal matrix; this is the basis for `N`. See:
* `Submodule.smithNormalFormTopBasis` for the basis on `M`,
* `Submodule.smithNormalFormCoeffs` for the entries of the diagonal matrix
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
/-
**Submodule.smithNormalFormBotBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormBotBasis (b : Basis ι R M) (h : Module.finrank R 
N = Module.finrank R M) : Basis ι R N
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_smith_normal_form_of_rank_eq`：Submodule.exists_smith_no
rmal_form_of_rank_eq (b : Basis ι R M) (h : Module.finrank R N = Module.finrank 
R M) : exists (b' : Basis ι R M) (a…

--- 原说明 ---
If `M` is finite free over a PID `R`, then for any submodule `N` of the same ran
k,
we can find basis for `M` and `N` with the same indexing such that the inclusion
 map
is a square diagonal matrix; this is the basis for `N`. See:
* `Submodule.smithNormalFormTopBasis` for the basis on `M`,
* `Submodule.smithNormalFormCoeffs` for the entries of the diagonal matrix
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
noncomputable def Submodule.smithNormalFormBotBasis (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : Basis ι R N :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose

/--
If `M` is finite free over a PID `R`, then for any submodule `N` of the same rank,
we can find basis for `M` and `N` with the same indexing such that the inclusion map
is a square diagonal matrix; these are the entries of the diagonal matrix. See:
* `Submodule.smithNormalFormTopBasis` for the basis on `M`,
* `Submodule.smithNormalFormBotBasis` for the basis on `N`,
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
/-
**Submodule.smithNormalFormCoeffs** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormCoeffs (b : Basis ι R M) (h : Module.finrank R N 
= Module.finrank R M) : ι -> R
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_smith_normal_form_of_rank_eq`：Submodule.exists_smith_no
rmal_form_of_rank_eq (b : Basis ι R M) (h : Module.finrank R N = Module.finrank 
R M) : exists (b' : Basis ι R M) (a…

--- 原说明 ---
If `M` is finite free over a PID `R`, then for any submodule `N` of the same ran
k,
we can find basis for `M` and `N` with the same indexing such that the inclusion
 map
is a square diagonal matrix; these are the entries of the diagonal matrix. See:
* `Submodule.smithNormalFormTopBasis` for the basis on `M`,
* `Submodule.smithNormalFormBotBasis` for the basis on `N`,
* `Submodule.smithNormalFormBotBasis_def` for the proof that the inclusion map
  forms a square diagonal matrix.
-/
noncomputable def Submodule.smithNormalFormCoeffs (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : ι → R :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose

@[simp]
/-
**Submodule.smithNormalFormBotBasis_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormBotBasis_def (b : Basis ι R M) (h : Module.finran
k R N = Module.finrank R M) : forall i, (smithNormalFormBotBasis b h i : M) = sm
ithNormalFormCoeffs b h i • smithNormalFormTopBasis b h i
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Submodule.exists_smith_normal_form_of_rank_eq`：Submodule.exists_smith_no
rmal_form_of_rank_eq (b : Basis ι R M) (h : Module.finrank R N = Module.finrank 
R M) : exists (b' : Basis ι R M) (a…
-/
theorem Submodule.smithNormalFormBotBasis_def (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    ∀ i, (smithNormalFormBotBasis b h i : M) =
      smithNormalFormCoeffs b h i • smithNormalFormTopBasis b h i :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose_spec

@[simp]
/-
**Submodule.smithNormalFormCoeffs_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.smithNormalFormCoeffs_ne_zero (b : Basis ι R M) (h : Module.finr
ank R N = Module.finrank R M) (i : ι) : smithNormalFormCoeffs b h i != 0
参数：b : Basis ι R M；h : Module.finrank R N = Module.finrank R M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ne_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smithNormalFormBotBasis_def`：Submodule.smithNormalFormBotBasis
_def (b : Basis ι R M) (h : Module.finrank R N = Module.finrank R M) : forall i,
 (smithNormalFormBotBasis b…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Submodule.smithNormalFormCoeffs_ne_zero (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) (i : ι) :
    smithNormalFormCoeffs b h i ≠ 0 := by
  intro hi
  apply Basis.ne_zero (smithNormalFormBotBasis b h) i
  refine Subtype.coe_injective ?_
  simp [hi]

end full_rank

section Ideal

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]

/-
**Ideal.finrank_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.finrank_eq_finrank [Finite ι] (b : Basis ι R S) (I : Ideal S) (hI : 
I != ⊥) : Module.finrank R (restrictScalars R I) = Module.finrank R S
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `Ideal.rank_eq`：Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondi
tion R] [Ring S] [IsDomain S] [Algebra R S] {n m : Type*} [Fintype n] [Fintype m
] (…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Submodule.restrictScalars.isScalarTower`：∀ (S : Type u_1) (R : Type u_2)
 (M : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semirin
g S]   [inst_3 : _root_.Modul…
-/
theorem Ideal.finrank_eq_finrank [Finite ι] (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    Module.finrank R (restrictScalars R I) = Module.finrank R S := by
  obtain ⟨_, bS, bI, _, _, _⟩ := (I.restrictScalars R).smithNormalForm b
  cases nonempty_fintype ι
  rw [Module.finrank_eq_card_basis bS, Module.finrank_eq_card_basis bI]
  exact Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars R))

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `Ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `Submodule.basisOfPid`.
-/
/-
**Ideal.smithNormalForm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.smithNormalForm [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I 
!= ⊥) : Basis.SmithNormalForm (I.restrictScalars R) ι (Fintype.card ι)
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `Ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `Submodule.basisOfPid`.
-/
noncomputable def Ideal.smithNormalForm [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    Basis.SmithNormalForm (I.restrictScalars R) ι (Fintype.card ι) :=
  Submodule.smithNormalFormOfRankEq b (finrank_eq_finrank b I hI)

variable [Finite ι]

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `Ideal.smithNormalForm` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

The definitions `Ideal.ringBasis`, `Ideal.selfBasis`, `Ideal.smithCoeffs` are (noncomputable)
choices of values for this existential quantifier.
-/
/-
**Ideal.exists_smith_normal_form** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.exists_smith_normal_form (b : Basis ι R S) (I : Ideal S) (hI : I != 
⊥) : exists (b' : Basis ι R S) (a : ι -> R) (ab' : Basis ι R I), forall i, (ab' 
i : S) = a i • b' i
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_smith_normal_form_of_rank_eq`：Submodule.exists_smith_no
rmal_form_of_rank_eq (b : Basis ι R M) (h : Module.finrank R N = Module.finrank 
R M) : exists (b' : Basis ι R M) (a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.finrank_eq_finrank`：Ideal.finrank_eq_finrank [Finite ι] (b : Basis
 ι R S) (I : Ideal S) (hI : I != ⊥) : Module.finrank R (restrictScalars R I) = M
odule.finrank …

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `Ideal.smithNormalForm` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

The definitions `Ideal.ringBasis`, `Ideal.selfBasis`, `Ideal.smithCoeffs` are (n
oncomputable)
choices of values for this existential quantifier.
-/
theorem Ideal.exists_smith_normal_form (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ (b' : Basis ι R S) (a : ι → R) (ab' : Basis ι R I), ∀ i, (ab' i : S) = a i • b' i :=
  Submodule.exists_smith_normal_form_of_rank_eq b (finrank_eq_finrank b I hI)

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `S`. See
* `Ideal.selfBasis` for the basis on `I`,
* `Ideal.smithCoeffs` for the entries of the diagonal matrix
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
/-
**Ideal.ringBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.ringBasis (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : Basis ι R 
S
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_smith_normal_form`：Ideal.exists_smith_normal_form (b : Basi
s ι R S) (I : Ideal S) (hI : I != ⊥) : exists (b' : Basis ι R S) (a : ι -> R) (a
b' : Basis ι R I), f…

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `S`. See
* `Ideal.selfBasis` for the basis on `I`,
* `Ideal.smithCoeffs` for the entries of the diagonal matrix
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diag
onal matrix.
-/
noncomputable def Ideal.ringBasis (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis ι R S :=
  (Ideal.exists_smith_normal_form b I hI).choose

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `I`. See:
* `Ideal.ringBasis` for the basis on `S`,
* `Ideal.smithCoeffs` for the entries of the diagonal matrix
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
/-
**Ideal.selfBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.selfBasis (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : Basis ι R 
I
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_smith_normal_form`：Ideal.exists_smith_normal_form (b : Basi
s ι R S) (I : Ideal S) (hI : I != ⊥) : exists (b' : Basis ι R S) (a : ι -> R) (a
b' : Basis ι R I), f…

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `I`. See:
* `Ideal.ringBasis` for the basis on `S`,
* `Ideal.smithCoeffs` for the entries of the diagonal matrix
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diag
onal matrix.
-/
noncomputable def Ideal.selfBasis (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis ι R I :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; these are the entries of the diagonal matrix. See :
* `Ideal.ringBasis` for the basis on `S`,
* `Ideal.selfBasis` for the basis on `I`,
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
/-
**Ideal.smithCoeffs** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.smithCoeffs (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : ι -> R
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_smith_normal_form`：Ideal.exists_smith_normal_form (b : Basi
s ι R S) (I : Ideal S) (hI : I != ⊥) : exists (b' : Basis ι R S) (a : ι -> R) (a
b' : Basis ι R I), f…

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; these are the entries of the diagonal matrix. See :
* `Ideal.ringBasis` for the basis on `S`,
* `Ideal.selfBasis` for the basis on `I`,
* `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diag
onal matrix.
-/
noncomputable def Ideal.smithCoeffs (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : ι → R :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.
-/
@[simp]
/-
**Ideal.selfBasis_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.selfBasis_def (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : forall
 i, (Ideal.selfBasis b I hI i : S) = Ideal.smithCoeffs b I hI i • Ideal.ringBasi
s b I hI i
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.exists_smith_normal_form`：Ideal.exists_smith_normal_form (b : Basi
s ι R S) (I : Ideal S) (hI : I != ⊥) : exists (b' : Basis ι R S) (a : ι -> R) (a
b' : Basis ι R I), f…

--- 原说明 ---
If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-
module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.
-/
theorem Ideal.selfBasis_def (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    ∀ i, (Ideal.selfBasis b I hI i : S) = Ideal.smithCoeffs b I hI i • Ideal.ringBasis b I hI i :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose_spec

@[simp]
/-
**Ideal.smithCoeffs_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.smithCoeffs_ne_zero (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) (i
) : Ideal.smithCoeffs b I hI i != 0
参数：b : Basis ι R S；I : Ideal S；hI : I != ⊥；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ne_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.selfBasis_def`：Ideal.selfBasis_def (b : Basis ι R S) (I : Ideal S)
 (hI : I != ⊥) : forall i, (Ideal.selfBasis b I hI i : S) = Ideal.smithCoeffs b 
I hI i • …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ideal.smithCoeffs_ne_zero (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) (i) :
    Ideal.smithCoeffs b I hI i ≠ 0 := by
  intro hi
  apply Basis.ne_zero (Ideal.selfBasis b I hI) i
  refine Subtype.coe_injective ?_
  simp [hi]

end Ideal

end SmithNormal

end PrincipalIdealDomain

