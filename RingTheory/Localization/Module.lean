/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

* `LinearIndependent.localization`: `b` is linear independent over a localization of `R`
  if it is linear independent over `R` itself
* `Basis.ofIsLocalizedModule` / `Basis.localizationLocalization`: promote an `R`-basis `b` of `A`
  to an `Rₛ`-basis of `Aₛ`, where `Rₛ` and `Aₛ` are localizations of `R` and `A` at `s`
  respectively
* `LinearIndependent.iff_fractionRing`: `b` is linear independent over `R` iff it is
  linear independent over `Frac(R)`
-/

@[expose] public section


open nonZeroDivisors

section Localization
variable {R : Type*} (Rₛ : Type*)

section IsLocalizedModule

open Submodule

variable [CommSemiring R] (S : Submonoid R) [CommSemiring Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
  {M Mₛ : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Mₛ] [Module R Mₛ]
  [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]

include S

/-
**span_eq_top_of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_eq_top_of_isLocalizedModule {v : Set M} (hv : span R v = ⊤) : span Rₛ
 (f '' v) = ⊤
参数：hv : span R v = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `LinearMap.map_span`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ 
: Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M…
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Units.smul_isUnit`：smul_isUnit [Monoid M] [SMul M α] {m : M} (hm : IsUni
t m) (a : α) : hm.unit • a = m • a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
-/
theorem span_eq_top_of_isLocalizedModule {v : Set M} (hv : span R v = ⊤) :
    span Rₛ (f '' v) = ⊤ := top_unique fun x _ ↦ by
  obtain ⟨⟨m, s⟩, h⟩ := IsLocalizedModule.surj S f x
  rw [Submonoid.smul_def, ← algebraMap_smul Rₛ, ← Units.smul_isUnit (IsLocalization.map_units Rₛ s),
    eq_comm, ← inv_smul_eq_iff] at h
  refine h ▸ smul_mem _ _ (span_subset_span R Rₛ _ ?_)
  rw [← LinearMap.coe_restrictScalars R, ← LinearMap.map_span, hv]
  exact mem_map_of_mem mem_top

set_option backward.isDefEq.respectTransparency false in
/-
**LinearIndependent.of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_isLocalizedModule {ι : Type*} {v : ι -> M} (hv : Line
arIndependent R v) : LinearIndependent Rₛ (f ∘ v)
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsUnit.mul_right_inj`：mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b =
 c
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `IsLocalization.exist_integer_multiples`：exist_integer_multiples {ι : Typ
e*} (s : Finset ι) (f : ι -> S) : exists b : M, forall i in s, IsLocalization.Is
Integer R ((b : R) • f i)
-/
theorem LinearIndependent.of_isLocalizedModule {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (f ∘ v) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro t g₁ g₂ eq i hi
  choose! a fg hfg using IsLocalization.exist_integer_multiples S (t.disjSum t) (Sum.elim g₁ g₂)
  simp_rw [Sum.forall, Finset.inl_mem_disjSum, Sum.elim_inl, Finset.inr_mem_disjSum, Sum.elim_inr,
    Subtype.forall'] at hfg
  apply_fun ((a : R) • ·) at eq
  simp_rw [← t.sum_coe_sort, Finset.smul_sum, ← smul_assoc, ← hfg,
    algebraMap_smul, Function.comp_def, ← map_smul, ← map_sum,
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inl x) • v x),
    t.sum_coe_sort (f := fun x ↦ fg (Sum.inr x) • v x)] at eq
  have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
  simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at eq
  have := congr(algebraMap R Rₛ $(hv t _ _ eq i hi))
  simpa only [map_mul, (IsLocalization.map_units Rₛ s).mul_right_inj, hfg.1 ⟨i, hi⟩, hfg.2 ⟨i, hi⟩,
    Algebra.smul_def, (IsLocalization.map_units Rₛ a).mul_right_inj] using this

set_option backward.isDefEq.respectTransparency false in
/-
**LinearIndependent.of_isLocalizedModule_of_isRegular** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：LinearIndependent.of_isLocalizedModule_of_isRegular {ι : Type*} {v : ι -> 
M} (hv : LinearIndependent R v) (h : forall s : S, IsRegular (s : R)) : LinearIn
dependent R (f ∘ v)
参数：hv : LinearIndependent R v；h : forall s : S, IsRegular (s : R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem LinearIndependent.of_isLocalizedModule_of_isRegular {ι : Type*} {v : ι → M}
    (hv : LinearIndependent R v) (h : ∀ s : S, IsRegular (s : R)) : LinearIndependent R (f ∘ v) :=
  hv.map_injOn _ <| by
    rw [← Finsupp.range_linearCombination]
    rintro _ ⟨_, r, rfl⟩ _ ⟨_, r', rfl⟩ eq
    congr; ext i
    have ⟨s, eq⟩ := IsLocalizedModule.exists_of_eq (S := S) eq
    simp_rw [Submonoid.smul_def, ← map_smul] at eq
    exact (h s).1 (DFunLike.congr_fun (hv eq) i)
/-
**LinearIndependent.localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.localization [Module Rₛ M] [IsScalarTower R Rₛ M] {ι : T
ype*} {b : ι -> M} (hli : LinearIndependent R b) : LinearIndependent Rₛ b
参数：hli : LinearIndependent R b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLocalizedModule_id`：isLocalizedModule_id (R') [CommSemiring R'] [Algeb
ra R R'] [IsLocalization S R'] [Module R' M] [IsScalarTower R R' M] : IsLocalize
dModule S …
· 使用定理 `LinearIndependent.of_isLocalizedModule`：LinearIndependent.of_isLocalized
Module {ι : Type*} {v : ι -> M} (hv : LinearIndependent R v) : LinearIndependent
 Rₛ (f ∘ v)
-/
theorem LinearIndependent.localization [Module Rₛ M] [IsScalarTower R Rₛ M]
    {ι : Type*} {b : ι → M} (hli : LinearIndependent R b) :
    LinearIndependent Rₛ b := by
  have := isLocalizedModule_id S M Rₛ
  exact hli.of_isLocalizedModule Rₛ S .id

set_option backward.isDefEq.respectTransparency false in
include f in
/-
**IsLocalizedModule.linearIndependent_lift** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.linearIndependent_lift {ι} {v : ι -> Mₛ} (hf : LinearInd
ependent R v) : exists w : ι -> M, LinearIndependent R w
参数：hf : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `linearIndependent_empty_type`：linearIndependent_empty_type [IsEmpty ι] :
 LinearIndependent R v
· 使用定理 `LinearIndependent.smul_left_injective`：LinearIndependent.smul_left_injec
tive (hv : LinearIndependent R v) (i : ι) : Injective fun r : R => r • v i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'ₛ`：∀ {ι : Type u'} {R : Type u_2} {M : Type u_4} {
v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M],   L…
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用引理 `IsLocalizedModule.isRegular_of_smul_left_injective`：isRegular_of_smul_le
ft_injective {m : M'} (inj : Function.Injective fun r : R => r • m) (s : S) : Is
Regular (s : R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsLocalizedModule.linearIndependent_lift {ι} {v : ι → Mₛ} (hf : LinearIndependent R v) :
    ∃ w : ι → M, LinearIndependent R w := by
  cases isEmpty_or_nonempty ι
  · exact ⟨isEmptyElim, linearIndependent_empty_type⟩
  have inj := hf.smul_left_injective (Classical.arbitrary ι)
  choose sec hsec using surj S f
  use fun i ↦ (sec (v i)).1
  rw [linearIndependent_iff'ₛ] at hf ⊢
  intro t g g' eq i hit
  refine (isRegular_of_smul_left_injective f inj (sec (v i)).2).2 <|
    hf t (fun i ↦ _ * (sec (v i)).2) (fun i ↦ _ * (sec (v i)).2) ?_ i hit
  simp_rw [mul_smul, ← Submonoid.smul_def, hsec, ← map_smul, ← map_sum, eq]

namespace Module.Basis

variable {ι : Type*} (b : Basis ι R M)

/-- If `M` has an `R`-basis, then localizing `M` at `S` has a basis over `R` localized at `S`. -/
/-
**Module.Basis.ofIsLocalizedModule** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofIsLocalizedModule : Basis ι Rₛ Mₛ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` has an `R`-basis, then localizing `M` at `S` has a basis over `R` localiz
ed at `S`.
-/
noncomputable def ofIsLocalizedModule : Basis ι Rₛ Mₛ :=
  .mk (b.linearIndependent.of_isLocalizedModule Rₛ S f) <| by
    rw [Set.range_comp, span_eq_top_of_isLocalizedModule Rₛ S _ b.span_eq]

@[simp]
/-
**Module.Basis.ofIsLocalizedModule_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis
`。
形式化陈述：ofIsLocalizedModule_apply (i : ι) : b.ofIsLocalizedModule Rₛ S f i = f (b 
i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.ofIsLocalizedModule.eq_1`：∀ {R : Type u_1} (Rₛ : Type u_2) 
[inst : CommSemiring R] (S : Submonoid R) [inst_1 : CommSemiring Rₛ]   [inst_2 :
 Algebra R Rₛ] [inst_3 : Is…
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem ofIsLocalizedModule_apply (i : ι) : b.ofIsLocalizedModule Rₛ S f i = f (b i) := by
  rw [ofIsLocalizedModule, coe_mk, Function.comp_apply]

@[simp]
/-
**Module.Basis.ofIsLocalizedModule_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Basis`。
形式化陈述：ofIsLocalizedModule_repr_apply (m : M) (i : ι) : ((b.ofIsLocalizedModule R
ₛ S f).repr (f m)) i = algebraMap R Rₛ (b.repr m i)
参数：m : M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.ofIsLocalizedModule_apply`：ofIsLocalizedModule_apply (i : ι
) : b.ofIsLocalizedModule Rₛ S f i = f (b i)
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem ofIsLocalizedModule_repr_apply (m : M) (i : ι) :
    ((b.ofIsLocalizedModule Rₛ S f).repr (f m)) i = algebraMap R Rₛ (b.repr m i) := by
  suffices ((b.ofIsLocalizedModule Rₛ S f).repr.toLinearMap.restrictScalars R) ∘ₗ f =
      Finsupp.mapRange.linearMap (Algebra.linearMap R Rₛ) ∘ₗ b.repr.toLinearMap by
    exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine ext b fun i ↦ ?_
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, ← b.ofIsLocalizedModule_apply Rₛ S f, repr_self, LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, repr_self, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, Algebra.linearMap_apply, map_one]
/-
**Module.Basis.ofIsLocalizedModule_span** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：ofIsLocalizedModule_span : span R (Set.range (b.ofIsLocalizedModule Rₛ S f
)) = LinearMap.range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.ofIsLocalizedModule_apply`：ofIsLocalizedModule_apply (i : ι
) : b.ofIsLocalizedModule Rₛ S f i = f (b i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
-/
theorem ofIsLocalizedModule_span :
    span R (Set.range (b.ofIsLocalizedModule Rₛ S f)) = LinearMap.range f := by
  calc span R (Set.range (b.ofIsLocalizedModule Rₛ S f))
    _ = span R (f '' (Set.range b)) := by congr; ext; simp
    _ = map f (span R (Set.range b)) := by rw [Submodule.map_span]
    _ = LinearMap.range f := by rw [b.span_eq, Submodule.map_top]

end Module.Basis

end IsLocalizedModule

section LocalizationLocalization

variable [CommSemiring R] (S : Submonoid R) [CommSemiring Rₛ] [Algebra R Rₛ]
variable [IsLocalization S Rₛ]
variable {A : Type*} [CommSemiring A] [Algebra R A]
variable (Aₛ : Type*) [CommSemiring Aₛ] [Algebra A Aₛ]
variable [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]
variable [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ]

open Submodule

include S

/-
**LinearIndependent.localization_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.localization_localization {ι : Type*} {v : ι -> A} (hv :
 LinearIndependent R v) : LinearIndependent Rₛ (algebraMap A Aₛ ∘ v)
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.of_isLocalizedModule`：LinearIndependent.of_isLocalized
Module {ι : Type*} {v : ι -> M} (hv : LinearIndependent R v) : LinearIndependent
 Rₛ (f ∘ v)
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
-/
theorem LinearIndependent.localization_localization {ι : Type*} {v : ι → A}
    (hv : LinearIndependent R v) : LinearIndependent Rₛ (algebraMap A Aₛ ∘ v) :=
  hv.of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap
/-
**span_eq_top_localization_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_eq_top_localization_localization {v : Set A} (hv : span R v = ⊤) : sp
an Rₛ (algebraMap A Aₛ '' v) = ⊤
参数：hv : span R v = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `span_eq_top_of_isLocalizedModule`：span_eq_top_of_isLocalizedModule {v : 
Set M} (hv : span R v = ⊤) : span Rₛ (f '' v) = ⊤
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
-/
theorem span_eq_top_localization_localization {v : Set A} (hv : span R v = ⊤) :
    span Rₛ (algebraMap A Aₛ '' v) = ⊤ :=
  span_eq_top_of_isLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap hv

namespace Module.Basis

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[Algebra A Aₛ]` is `localizationAlgebra`.
-/
/-
**Module.Basis.localizationLocalization** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`
。
形式化陈述：localizationLocalization {ι : Type*} (b : Basis ι R A) : Basis ι Rₛ Aₛ
参数：b : Basis ι R A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…

--- 原说明 ---
If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localiz
ed at `S`.

A suitable instance for `[Algebra A Aₛ]` is `localizationAlgebra`.
-/
noncomputable def localizationLocalization {ι : Type*} (b : Basis ι R A) : Basis ι Rₛ Aₛ :=
  b.ofIsLocalizedModule Rₛ S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap

@[simp]
/-
**Module.Basis.localizationLocalization_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.
Basis`。
形式化陈述：localizationLocalization_apply {ι : Type*} (b : Basis ι R A) (i) : b.local
izationLocalization Rₛ S Aₛ i = algebraMap A Aₛ (b i)
参数：b : Basis ι R A；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ofIsLocalizedModule_apply`：ofIsLocalizedModule_apply (i : ι
) : b.ofIsLocalizedModule Rₛ S f i = f (b i)
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
-/
theorem localizationLocalization_apply {ι : Type*} (b : Basis ι R A) (i) :
    b.localizationLocalization Rₛ S Aₛ i = algebraMap A Aₛ (b i) :=
  b.ofIsLocalizedModule_apply Rₛ S _ i

@[simp]
/-
**Module.Basis.localizationLocalization_repr_algebraMap** 是 Mathlib 中的一个定理，位于命名空
间 `Module.Basis`。
形式化陈述：localizationLocalization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x 
i) : (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i = algebraMa
p R Rₛ (b.repr x i)
参数：b : Basis ι R A；x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ofIsLocalizedModule_repr_apply`：ofIsLocalizedModule_repr_ap
ply (m : M) (i : ι) : ((b.ofIsLocalizedModule Rₛ S f).repr (f m)) i = algebraMap
 R Rₛ (b.repr m i)
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
-/
theorem localizationLocalization_repr_algebraMap {ι : Type*} (b : Basis ι R A) (x i) :
    (b.localizationLocalization Rₛ S Aₛ).repr (algebraMap A Aₛ x) i =
      algebraMap R Rₛ (b.repr x i) := b.ofIsLocalizedModule_repr_apply Rₛ S _ _ i
/-
**Module.Basis.localizationLocalization_span** 是 Mathlib 中的一个定理，位于命名空间 `Module.B
asis`。
形式化陈述：localizationLocalization_span {ι : Type*} (b : Basis ι R A) : Submodule.sp
an R (Set.range (b.localizationLocalization Rₛ S Aₛ)) = LinearMap.range (IsScala
rTower.toAlgHom R A Aₛ : A ->ₗ[R] Aₛ)
参数：b : Basis ι R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ofIsLocalizedModule_span`：ofIsLocalizedModule_span : span R
 (Set.range (b.ofIsLocalizedModule Rₛ S f)) = LinearMap.range f
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
-/
theorem localizationLocalization_span {ι : Type*} (b : Basis ι R A) :
    Submodule.span R (Set.range (b.localizationLocalization Rₛ S Aₛ)) =
      LinearMap.range (IsScalarTower.toAlgHom R A Aₛ : A →ₗ[R] Aₛ) :=
  b.ofIsLocalizedModule_span Rₛ S _

end Module.Basis
end LocalizationLocalization


section FractionRing

variable (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-
**LinearIndependent.iff_fractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.iff_fractionRing {ι : Type*} {b : ι -> V} : LinearIndepe
ndent R b ↔ LinearIndependent K b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.localization`：LinearIndependent.localization [Module R
ₛ M] [IsScalarTower R Rₛ M] {ι : Type*} {b : ι -> M} (hli : LinearIndependent R 
b) : LinearIndepende…
· 使用定理 `LinearIndependent.restrict_scalars`：LinearIndependent.restrict_scalars [
Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] (hinj : Inject
ive fun r : R => r • (1 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
-/
theorem LinearIndependent.iff_fractionRing {ι : Type*} {b : ι → V} :
    LinearIndependent R b ↔ LinearIndependent K b :=
  ⟨.localization K R⁰,
    .restrict_scalars <| (faithfulSMul_iff_injective_smul_one ..).mp inferInstance⟩

end FractionRing

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
variable {M N : Type*}
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

open IsLocalization

/-- An `R`-linear map between two `S⁻¹R`-modules is actually `S⁻¹R`-linear. -/
/-
**LinearMap.extendScalarsOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.extendScalarsOfIsLocalization (f : M ->ₗ[R] N) : M ->ₗ[A] N wher
e toFun
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-linear map between two `S⁻¹R`-modules is actually `S⁻¹R`-linear.
-/
def LinearMap.extendScalarsOfIsLocalization (f : M →ₗ[R] N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := (IsLocalization.linearMap_compatibleSMul S A M N).map_smul _
/-
**LinearMap.restrictScalars_extendScalarsOfIsLocalization** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_4) 
[inst_1 : CommSemiring A]   [inst_2 : Algebra R A] [inst_3 : IsLocalization S A]
 {M : Type u_5} {N : Type u_6} [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Mod
ule R M] [inst_6 : _root_.Module A M] [inst_7 : IsScalarTower R A M] [inst_8 : A
ddCommMonoid N]   [inst_9 : _root_.Module R N] [inst_10 : _root_.Module A N] [in
st_11 : IsScalarTower R A N] (f : M →ₗ[R] N),   ↑R (LinearMap.extendScalarsOfIsL
ocalization S A f) = f
参数：S : Submonoid R；A : Type u_4；f : M →ₗ[R] N；LinearMap.extendScalarsOfIsLocaliz
ation S A f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
@[simp] lemma LinearMap.restrictScalars_extendScalarsOfIsLocalization (f : M →ₗ[R] N) :
    (f.extendScalarsOfIsLocalization S A).restrictScalars R = f := rfl
/-
**LinearMap.extendScalarsOfIsLocalization_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_4) 
[inst_1 : CommSemiring A]   [inst_2 : Algebra R A] [inst_3 : IsLocalization S A]
 {M : Type u_5} {N : Type u_6} [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Mod
ule R M] [inst_6 : _root_.Module A M] [inst_7 : IsScalarTower R A M] [inst_8 : A
ddCommMonoid N]   [inst_9 : _root_.Module R N] [inst_10 : _root_.Module A N] [in
st_11 : IsScalarTower R A N] (f : M →ₗ[A] N),   LinearMap.extendScalarsOfIsLocal
ization S A (↑R f) = f
参数：S : Submonoid R；A : Type u_4；f : M →ₗ[A] N；↑R f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
@[simp] lemma LinearMap.extendScalarsOfIsLocalization_apply (f : M →ₗ[A] N) :
    f.extendScalarsOfIsLocalization S A = f := rfl
/-
**LinearMap.extendScalarsOfIsLocalization_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：∀ {R : Type u_3} [inst : CommSemiring R] (S : Submonoid R) (A : Type u_4) 
[inst_1 : CommSemiring A]   [inst_2 : Algebra R A] [inst_3 : IsLocalization S A]
 {M : Type u_5} {N : Type u_6} [inst_4 : AddCommMonoid M]   [inst_5 : _root_.Mod
ule R M] [inst_6 : _root_.Module A M] [inst_7 : IsScalarTower R A M] [inst_8 : A
ddCommMonoid N]   [inst_9 : _root_.Module R N] [inst_10 : _root_.Module A N] [in
st_11 : IsScalarTower R A N] (f : M →ₗ[R] N) (x : M),   (LinearMap.extendScalars
OfIsLocalization S A f) x = f x
参数：S : Submonoid R；A : Type u_4；f : M →ₗ[R] N；x : M；LinearMap.extendScalarsOfIsL
ocalization S A f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma LinearMap.extendScalarsOfIsLocalization_apply' (f : M →ₗ[R] N) (x : M) :
    (f.extendScalarsOfIsLocalization S A) x = f x := rfl

/-- The `S⁻¹R`-linear maps between two `S⁻¹R`-modules are exactly the `R`-linear maps. -/
@[simps]
/-
**LinearMap.extendScalarsOfIsLocalizationEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.extendScalarsOfIsLocalizationEquiv : (M ->ₗ[R] N) ≃ₗ[A] (M ->ₗ[A
] N) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S⁻¹R`-linear maps between two `S⁻¹R`-modules are exactly the `R`-linear map
s.
-/
def LinearMap.extendScalarsOfIsLocalizationEquiv : (M →ₗ[R] N) ≃ₗ[A] (M →ₗ[A] N) where
  toFun := LinearMap.extendScalarsOfIsLocalization S A
  invFun := LinearMap.restrictScalars R
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp
  left_inv := by intro _; ext; simp
  right_inv := by intro _; ext; simp

/-- An `R`-linear isomorphism between `S⁻¹R`-modules is actually `S⁻¹R`-linear. -/
@[simps!]
/-
**LinearEquiv.extendScalarsOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.extendScalarsOfIsLocalization (f : M ≃ₗ[R] N) : M ≃ₗ[A] N
参数：f : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-linear isomorphism between `S⁻¹R`-modules is actually `S⁻¹R`-linear.
-/
def LinearEquiv.extendScalarsOfIsLocalization (f : M ≃ₗ[R] N) : M ≃ₗ[A] N :=
  .ofLinearMap (LinearMap.extendScalarsOfIsLocalization S A f)
    (LinearMap.extendScalarsOfIsLocalization S A f.symm)
    (by ext; simp) (by ext; simp)

/-- The `S⁻¹R`-linear isomorphisms between two `S⁻¹R`-modules are exactly the `R`-linear
isomorphisms. -/
@[simps]
/-
**LinearEquiv.extendScalarsOfIsLocalizationEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.extendScalarsOfIsLocalizationEquiv : (M ≃ₗ[R] N) ≃ M ≃ₗ[A] N w
here toFun e
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S⁻¹R`-linear isomorphisms between two `S⁻¹R`-modules are exactly the `R`-li
near
isomorphisms.
-/
def LinearEquiv.extendScalarsOfIsLocalizationEquiv : (M ≃ₗ[R] N) ≃ M ≃ₗ[A] N where
  toFun e := e.extendScalarsOfIsLocalization S A
  invFun e := e.restrictScalars R
  left_inv e := by ext; simp
  right_inv e := by ext; simp

end

end Localization

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (f : M →ₗ[R] M') [IsLocalizedModule S f]
variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
variable (g : N →ₗ[R] N') [IsLocalizedModule S g]
variable (Rₛ) [CommSemiring Rₛ] [Algebra R Rₛ] [Module Rₛ M'] [Module Rₛ N']
variable [IsScalarTower R Rₛ M'] [IsScalarTower R Rₛ N'] [IsLocalization S Rₛ]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[Rₛ] Nₛ`. -/
@[simps!]
noncomputable
/-
**IsLocalizedModule.mapExtendScalars** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModul
e`。
形式化陈述：mapExtendScalars : (M ->ₗ[R] N) ->ₗ[R] (M' ->ₗ[Rₛ] N')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapExtendScalars : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[Rₛ] N') :=
  ((LinearMap.extendScalarsOfIsLocalizationEquiv S Rₛ).restrictScalars R).toLinearMap ∘ₗ map S f g

/-- An `R`-module isomorphism `M ≃ₗ[R] N` gives an `Rₛ`-module isomorphism `Mₛ ≃ₗ[Rₛ] Nₛ`. -/
@[simps!]
noncomputable
/-
**IsLocalizedModule.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：mapEquiv (e : M ≃ₗ[R] N) : M' ≃ₗ[Rₛ] N'
参数：e : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapEquiv (e : M ≃ₗ[R] N) : M' ≃ₗ[Rₛ] N' :=
  LinearEquiv.ofLinearMap
    (IsLocalizedModule.mapExtendScalars S f g Rₛ e)
    (IsLocalizedModule.mapExtendScalars S g f Rₛ e.symm)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S g g
      ext; simp)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S f f
      ext; simp)

end IsLocalizedModule

section LocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {N} [AddCommMonoid N] [Module R N]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[Rₛ] Nₛ`. -/
noncomputable
/-
**LocalizedModule.map** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocalizedModule.map : (M ->ₗ[R] N) ->ₗ[R] (LocalizedModule S M ->ₗ[Localiz
ation S] LocalizedModule S N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LocalizedModule.map :
    (M →ₗ[R] N) →ₗ[R] (LocalizedModule S M →ₗ[Localization S] LocalizedModule S N) :=
  IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) (Localization S)

@[simp]
/-
**LocalizedModule.map_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.map_mk (f : M ->ₗ[R] N) (x y) : map S f (.mk x y) = Locali
zedModule.mk (f x) y
参数：f : M ->ₗ[R] N；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk_eq_mk'`：mk_eq_mk' (s : S) (m : M) : LocalizedModule
.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s
· 使用引理 `IsLocalizedModule.map_mk'`：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S 
f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s)
-/
lemma LocalizedModule.map_mk (f : M →ₗ[R] N) (x y) :
    map S f (.mk x y) = LocalizedModule.mk (f x) y := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk_eq_mk']
  exact IsLocalizedModule.map_mk' _ _ _ _ _ _

@[simp]
/-
**LocalizedModule.map_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.map_id : LocalizedModule.map S (.id (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用引理 `IsLocalizedModule.map_id`：map_id : map S f f .id = .id
-/
lemma LocalizedModule.map_id :
    LocalizedModule.map S (.id (R := R) (M := M)) = LinearMap.id :=
  LinearMap.ext fun x ↦ LinearMap.congr_fun (IsLocalizedModule.map_id S (mkLinearMap S M)) x
/-
**LocalizedModule.map_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.map_injective (l : M ->ₗ[R] N) (hl : Function.Injective l)
 : Function.Injective (map S l)
参数：l : M ->ₗ[R] N；hl : Function.Injective l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_injective`：map_injective (h : M ->ₗ[R] N) (h_inj :
 Function.Injective h) : Function.Injective (map S f g h)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma LocalizedModule.map_injective (l : M →ₗ[R] N) (hl : Function.Injective l) :
    Function.Injective (map S l) :=
  IsLocalizedModule.map_injective S (mkLinearMap S M) (mkLinearMap S N) l hl
/-
**LocalizedModule.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.map_surjective (l : M ->ₗ[R] N) (hl : Function.Surjective 
l) : Function.Surjective (map S l)
参数：l : M ->ₗ[R] N；hl : Function.Surjective l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_surjective`：map_surjective (h : M ->ₗ[R] N) (h_sur
j : Function.Surjective h) : Function.Surjective (map S f g h)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma LocalizedModule.map_surjective (l : M →ₗ[R] N) (hl : Function.Surjective l) :
    Function.Surjective (map S l) :=
  IsLocalizedModule.map_surjective S (mkLinearMap S M) (mkLinearMap S N) l hl
/-
**LocalizedModule.restrictScalars_map_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.restrictScalars_map_eq {M' N' : Type*} [AddCommMonoid M'] 
[AddCommMonoid N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] M') (g₂ : N ->ₗ[R]
 N') [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M ->ₗ[R] N) : (map S
 l).restrictScalars R = (IsLocalizedModule.iso S g₂).symm ∘ₗ IsLocalizedModule.m
ap S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁
参数：g₁ : M ->ₗ[R] M'；g₂ : N ->ₗ[R] N'；l : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.eq_toLinearMap_symm_comp`：eq_toLinearMap_symm_comp (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLin
earMap.comp f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
· 使用定理 `IsLocalizedModule.linearMap_ext`：linearMap_ext {N N'} [AddCommMonoid N] 
[Module R N] [AddCommMonoid N'] [Module R N'] (f' : N ->ₗ[R] N') [IsLocalizedMod
ule S f'] ⦃g g' : M' …
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `IsLocalizedModule.iso_symm_comp`：iso_symm_comp : (iso S f).symm.toLinear
Map.comp f = LocalizedModule.mkLinearMap S M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用引理 `LocalizedModule.map_mk`：LocalizedModule.map_mk (f : M ->ₗ[R] N) (x y) : 
map S f (.mk x y) = LocalizedModule.mk (f x) y
· 使用引理 `IsLocalizedModule.iso_mk_one`：iso_mk_one (x : M) : (iso S f) (LocalizedM
odule.mk x 1) = f x
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LocalizedModule.restrictScalars_map_eq {M' N' : Type*} [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M'] [Module R N'] (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂]
    (l : M →ₗ[R] N) :
    (map S l).restrictScalars R = (IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁ := by
  rw [LinearEquiv.eq_toLinearMap_symm_comp, ← LinearEquiv.comp_toLinearMap_symm_eq]
  apply IsLocalizedModule.linearMap_ext S g₁ g₂
  rw [LinearMap.comp_assoc, IsLocalizedModule.iso_symm_comp]
  ext
  simp

variable {S} in
/-
**LocalizedModule.coe_map_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.coe_map_eq {M' N' : Type*} [AddCommMonoid M'] [AddCommMono
id N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] M') (g₂ : N ->ₗ[R] N') [IsLoca
lizedModule S g₁] [IsLocalizedModule S g₂] (l : M ->ₗ[R] N) : ⇑(map S l) = (IsLo
calizedModule.iso S g₂).symm ∘ IsLocalizedModule.map S g₁ g₂ l ∘ IsLocalizedModu
le.iso S g₁
参数：g₁ : M ->ₗ[R] M'；g₂ : N ->ₗ[R] N'；l : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用引理 `LocalizedModule.restrictScalars_map_eq`：LocalizedModule.restrictScalars_
map_eq {M' N' : Type*} [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Modu
le R N'] (g₁ : M ->ₗ[R] M') …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LocalizedModule.coe_map_eq {M' N' : Type*} [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M'] [Module R N'] (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    ⇑(map S l) = (IsLocalizedModule.iso S g₂).symm ∘
      IsLocalizedModule.map S g₁ g₂ l ∘ IsLocalizedModule.iso S g₁ := by
  rw [← LinearMap.coe_restrictScalars R, restrictScalars_map_eq _ g₁ g₂ l]
  simp

end LocalizedModule

namespace IsLocalizedModule

variable {R M N M' N' : Type*} [CommSemiring R] {S : Submonoid R}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
  [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] {l : M →ₗ[R] N}

/-
**IsLocalizedModule.map_injective_iff_localizedModuleMap_injective** 是 Mathlib 中
的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_injective_iff_localizedModuleMap_injective : Function.Injective (IsLoc
alizedModule.map S g₁ g₂ l) ↔ Function.Injective (LocalizedModule.map S l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.coe_map_eq`：LocalizedModule.coe_map_eq {M' N' : Type*} [
AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] 
M') (g₂ : N ->ₗ[…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_injective_iff_localizedModuleMap_injective :
    Function.Injective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Injective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]
/-
**IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective** 是 Mathlib
 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_surjective_iff_localizedModuleMap_surjective : Function.Surjective (Is
LocalizedModule.map S g₁ g₂ l) ↔ Function.Surjective (LocalizedModule.map S l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.coe_map_eq`：LocalizedModule.coe_map_eq {M' N' : Type*} [
AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] 
M') (g₂ : N ->ₗ[…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_surjective_iff_localizedModuleMap_surjective :
    Function.Surjective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Surjective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]
/-
**IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective** 是 Mathlib 中
的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_bijective_iff_localizedModuleMap_bijective : Function.Bijective (IsLoc
alizedModule.map S g₁ g₂ l) ↔ Function.Bijective (LocalizedModule.map S l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.coe_map_eq`：LocalizedModule.coe_map_eq {M' N' : Type*} [
AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] 
M') (g₂ : N ->ₗ[…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_bijective_iff_localizedModuleMap_bijective :
    Function.Bijective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Bijective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]

end IsLocalizedModule

