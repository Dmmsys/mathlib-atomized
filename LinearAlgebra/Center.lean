/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Center of the algebra of linear endomorphisms

If `V` is an `R`-module, we say that an endomorphism `f : Module.End R V`
is a *homothety* with central ratio if there exists `a ∈ Set.center R`
such that `f x = a • x` for all `x`.
By `Module.End.mem_subsemiringCenter_iff`, these linear maps constitute
the center of `Module.End R V`.
(When `R` is commutative, we can write `f = a • LinearMap.id`.)

In what follows, `V` is assumed to be a free `R`-module.

* `LinearMap.commute_transvections_iff_of_basis`:
  if an endomorphism `f : V →ₗ[R] V` commutes with every elementary transvection
  (in a given basis), then it is a homothety with central ratio.
  (Assumes that the basis is provided and has a non trivial set of indices.)

* `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`:
  over a commutative ring `R` which is a domain, an endomorphism `f : V →ₗ[R] V`
  of a free module such that `v` and `f v` are not linearly independent,
  for all `v : V`, is a homothety.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent`:
  a variant that does not assume that `R` is commutative.
  Then the homothety has central ratio.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis`:
  a variant that does not assume that `R` has the strong rank condition,
  but requires a basis.

Note. In the noncommutative case, the last two results do not hold
when the rank is equal to 1. Indeed, right multiplications
with noncentral ratio of the `R`-module `R` satisfy the property
that `f v` and `v` are linearly dependent, for all `v : V`,
but they are not left multiplication by some element.

-/

public section

open Module LinearMap LinearEquiv Set Finsupp

namespace LinearMap

variable {R V : Type*}

/-
**LinearMap.mem_center_of_apply_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_center_of_apply_eq_smul [Semiring R] [AddCommMonoid V] [Module R V] {f
 : V ->ₗ[R] V} {a : R} (hf : forall x, f x = a • x) : f in center (End R V)
参数：hf : forall x, f x = a • x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mem_center_of_apply_eq_smul [Semiring R] [AddCommMonoid V]
    [Module R V] {f : V →ₗ[R] V} {a : R}
    (hf : ∀ x, f x = a • x) :
    f ∈ center (End R V) := by
  simp [mem_center_iff, isMulCentral_iff, commute_iff_eq, mul_assoc, LinearMap.ext_iff, hf]

/-- A linear endomorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio. -/
/-
**LinearMap.commute_transvections_iff_of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：commute_transvections_iff_of_basis [Ring R] [AddCommGroup V] [Module R V] 
{ι : Type*} [Nontrivial ι] (b : Basis ι R V) {f : V ->ₗ[R] V} (hcomm : forall i 
j (r : R) (_ : i != j), Commute f (transvection (b.coord i) (r • b j))) : exists
 a : Subring.center R, f = a • 1
参数：b : Basis ι R V；hcomm : forall i j (r : R) (_ : i != j), Commute f (transvect
ion (b.coord i) (r • b j))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSMulCommClassSubtypeMemCenter`：∀ {R : Type u_3} {M : Type u_
4} [inst : Ring R] [inst_1 : MulAction R M], SMulCommClass R (↥(Subring.center R
)) M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
A linear endomorphism of a free module of rank at least 2
that commutes with transvections consists of homotheties with central ratio.
-/
theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V →ₗ[R] V}
    (hcomm : ∀ i j (r : R) (_ : i ≠ j), Commute f (transvection (b.coord i) (r • b j))) :
    ∃ a : Subring.center R, f = a • 1 := by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i ≠ j) (r : R) :
      r • f (b j) = b.coord i (f (b i)) • r • b j := by
    have := hcomm i j r hij
    rw [LinearMap.ext_iff] at this
    simpa [LinearMap.transvection.apply] using this (b i)
  have h_allEq (i j : ι) : b.coord i (f (b i)) = b.coord j (f (b j)) := by
    by_cases hij : j = i
    · simp [hij]
    simpa using congr_arg (b.coord i) (hcomm j i hij 1)
  replace hcomm (i : ι) (r : R) : r • f (b i) = b.coord i (f (b i)) • r • b i := by
    obtain ⟨j, hji⟩ := exists_ne i
    simpa [h_allEq j i] using hcomm j i hji r
  let i : ι := Classical.ofNonempty
  refine ⟨b.coord i (f (b i)), fun r ↦ by simpa using congr(b.coord i $(hcomm i r)), ?_⟩
  ext x
  rw [← b.linearCombination_repr x, linearCombination_apply, map_finsuppSum]
  simp only [smul_apply, End.one_apply, smul_sum]
  apply sum_congr
  intro j _
  simp [Subring.smul_def, h_allEq i j, hcomm j]

/-- Over a domain, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

In the commutative case, use `LinearMap.exists_eq_smul_id`.

This is a variant of `LinearMap.exists_mem_center_apply_smul`
which switches the use of `StrongRankInduction` and `finrank`
for the cardinality of a given basis.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`. -/
/-
**LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_ba
sis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis [R
ing R] [IsDomain R] [AddCommGroup V] [Module R V] {f : V ->ₗ[R] V} {ι : Type*} [
Nontrivial ι] (b : Basis ι R V) (h : forall v, ¬ LinearIndependent R ![v, f v]) 
: exists a : Subring.center R, f = a • 1
参数：b : Basis ι R V；h : forall v, ¬ LinearIndependent R ![v, f v]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
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
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
Over a domain, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

In the commutative case, use `LinearMap.exists_eq_smul_id`.

This is a variant of `LinearMap.exists_mem_center_apply_smul`
which switches the use of `StrongRankInduction` and `finrank`
for the cardinality of a given basis.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`.
-/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis
    [Ring R] [IsDomain R] [AddCommGroup V] [Module R V]
    {f : V →ₗ[R] V}
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : Subring.center R, f = a • 1 := by
  -- We make the linear dependence condition explicit
  have feq (i) : f (b i) = (b.coord i) (f (b i)) • b i := by
    classical
    rw [b.ext_elem_iff]
    intro j
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨s, t, ⟨h, h'⟩⟩ := h (b i)
    simp only [Basis.coord_apply, _root_.map_smul, Basis.repr_self, smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply]
    split_ifs with hj
    · simp [hj]
    · have : t = 0 ∨ b.repr (f (b i)) j = 0 := by
        rw [b.ext_elem_iff] at h
        simpa [single_eq_of_ne' hj] using h j
      apply Or.resolve_left this
      contrapose h'
      refine ⟨?_, h'⟩
      simp only [h', zero_smul, add_zero] at h
      contrapose hj
      apply b.linearIndependent.eq_of_smul_apply_eq_smul_apply s 0 i j hj
      simpa using h
  have h' (i j) (hij : i ≠ j) (r : R) : b.coord i (f (b i)) * r = r * b.coord j (f (b j)) := by
    -- we use that `f (b i + r • b j)` is a multiple of `b i + r • b j`
    let x := b.repr.symm ((Finsupp.single i 1).update j r)
    specialize h x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearIndependent.pair_iff, not_forall, not_and] at h
    obtain ⟨s, t, h, hst⟩ := h
    simp only [b.ext_elem_iff, map_add, _root_.map_smul, coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    have hx : x = b i + r • b j := by
      simp only [Basis.repr_symm_apply, linearCombination_apply, x]
      rw [← add_right_cancel_iff, sum_update_add] <;>
        simp [single_eq_of_ne' hij, add_smul]
    have h1 : s + t * (b.coord i (f (b i))) = 0 := by
      suffices s + t * ((b.repr (f (b i))) i + r * (b.repr (f (b j))) i) = 0 by
        rw [mul_add, ← add_assoc, ← mul_assoc, add_eq_zero_iff_eq_neg] at this
        rw [Basis.coord_apply, this, feq]
        simp [single_eq_of_ne hij]
      simpa [hx, single_eq_of_ne hij] using h i
    have h2 : s * r + t * r * b.coord j (f (b j)) = 0 := by
      suffices s * r + t * ((b.repr (f (b i))) j + r * (b.repr (f (b j))) j) = 0 by
        rw [mul_add, ← add_assoc, add_right_comm, add_eq_zero_iff_eq_neg, ← mul_assoc] at this
        rw [Basis.coord_apply, this, feq]
        simp [single_eq_of_ne' hij]
      simpa [hx, single_eq_same, single_eq_of_ne' hij] using h j
    rw [add_eq_zero_iff_eq_neg] at h1
    rw [h1, neg_mul, neg_add_eq_sub, mul_assoc, mul_assoc,
      ← mul_sub, mul_eq_zero, sub_eq_zero] at h2
    symm
    apply Or.resolve_left h2
    contrapose hst; simp [h1, hst]
  -- This generalizes the equality formerly known as `feq`
  replace feq (i j) : f (b j) = b.coord i (f (b i)) • b j := by
    by_cases hij : i = j
    · rw [← hij, ← feq]
    · have := h' i j hij 1
      simp only [mul_one, one_mul] at this
      rw [feq, ← this]
  let i : ι := Classical.ofNonempty
  have ha (r) : Commute (b.coord i (f (b i))) r := by
    obtain ⟨j, hij⟩ := exists_ne i
    rw [commute_iff_eq, h' i j (Ne.symm hij), feq i j, feq i i]
    simp
  refine ⟨⟨b.coord i (f (b i)), ?_⟩, ?_⟩
  · simpa [Subring.mem_center_iff, commute_iff_eq, eq_comm] using ha
  apply b.ext
  simpa only [smul_apply, End.one_apply, Subring.smul_def] using feq i

/-- Over a domain `R`, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

When `R` does not satisfy `StrongRankCondition`, use
`LinearMap.exists_mem_center_apply_eq_smul_of_basis`.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`. -/
/-
**LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent** 是 M
athlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent [Ring R] [I
sDomain R] [StrongRankCondition R] [AddCommGroup V] [Module R V] [Free R V] {f :
 V ->ₗ[R] V} (hV1 : finrank R V != 1) (h : forall v, ¬ LinearIndependent R ![v, 
f v]) : exists a : Subring.center R, f = a • 1
参数：hV1 : finrank R V != 1；h : forall v, ¬ LinearIndependent R ![v, f v]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instSMulCommClassSubtypeMemCenter`：∀ {R : Type u_3} {M : Type u_
4} [inst : Ring R] [inst_1 : MulAction R M], SMulCommClass R (↥(Subring.center R
)) M
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
_of_basis`：exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_bas
is [Ring R] [IsDomain R] [AddCommGroup V] [Module R V] {f : V ->ₗ[R] V}…

--- 原说明 ---
Over a domain `R`, an endomorphism `f` of a free module `V`
of rank ≠ 1 such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties with central ratio.

When `R` does not satisfy `StrongRankCondition`, use
`LinearMap.exists_mem_center_apply_eq_smul_of_basis`.

When `finrank R V = 1`, up to a linear equivalence `V ≃ₗ[R] R`,
then any `f` is *right*-multiplication by some `a : R`,
but not necessarily *left*-multiplication by an element of the center of `R`.
-/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
    [Ring R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V]
    {f : V →ₗ[R] V}
    (hV1 : finrank R V ≠ 1)
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : Subring.center R, f = a • 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R V
    have : Fintype ι := Fintype.ofFinite ι
    simp_all [finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
  exact exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis b h

/-- Over a commutative domain, an endomorphism `f` of a free module `V`
such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties. -/
/-
**LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap`。
形式化陈述：exists_eq_smul_id_of_forall_notLinearIndependent [CommRing R] [IsDomain R]
 [AddCommGroup V] [Module R V] [Free R V] {f : V ->ₗ[R] V} (h : forall v, ¬ Line
arIndependent R ![v, f v]) : exists a : R, f = a • 1
参数：h : forall v, ¬ LinearIndependent R ![v, f v]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_eq_one_iff`：finrank_eq_one_iff [Module.Free K V] (ι : Type*) [Un
ique ι] : finrank K V = 1 ↔ Nonempty (Basis ι K V)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.linearCombination_unique`：linearCombination_unique [Unique α] (l
 : α ->₀ R) (v : α -> M) : linearCombination R v l = l default • v default
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subring.instSMulCommClassSubtypeMemCenter`：∀ {R : Type u_3} {M : Type u_
4} [inst : Ring R] [inst_1 : MulAction R M], SMulCommClass R (↥(Subring.center R
)) M
· 使用定理 `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
`：exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent [Ring R] [IsDom
ain R] [StrongRankCondition R] [AddCommGroup V] [Module R V] […

--- 原说明 ---
Over a commutative domain, an endomorphism `f` of a free module `V`
such that `f v` and `v` are collinear, for all `v : V`,
consists of homotheties.
-/
theorem exists_eq_smul_id_of_forall_notLinearIndependent
    [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] [Free R V] {f : V →ₗ[R] V}
    (h : ∀ v, ¬ LinearIndependent R ![v, f v]) :
    ∃ a : R, f = a • 1 := by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent hV1 h
  refine ⟨a, by simp [Subring.smul_def]⟩

end LinearMap

