/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.GroupTheory.CosetCover

/-!
# Algebraic extensions are determined by their sets of minimal polynomials up to isomorphism

## Main results

`Field.nonempty_algHom_of_exists_root` says if `E/F` and `K/F` are field extensions
with `E/F` algebraic, and if the minimal polynomial of every element of `E` over `F` has a root
in `K`, then there exists an `F`-embedding of `E` into `K`. If `E/F` and `K/F` have the same
set of minimal polynomials, then `E` and `K` are isomorphic as `F`-algebras. As a corollary:

`IsAlgClosure.of_exists_root`: if `E/F` is algebraic and every monic irreducible polynomial
in `F[X]` has a root in `E`, then `E` is an algebraic closure of `F`.

## Reference

[Isaacs1980] *Roots of Polynomials in Algebraic Extensions of Fields*,
The American Mathematical Monthly

-/

public section

namespace Field

open Polynomial IntermediateField

variable {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
variable [alg : Algebra.IsAlgebraic F E]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Field.nonempty_algHom_of_exists_root** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：nonempty_algHom_of_exists_root (h : forall x : E, exists y : K, aeval y (m
inpoly F x) = 0) : Nonempty (E ->ₐ[F] K)
参数：h : forall x : E, exists y : K, aeval y (minpoly F x) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.Lifts.nonempty_algHom_of_exist_lifts_finset`：nonempty_
algHom_of_exist_lifts_finset [alg : Algebra.IsAlgebraic F E] (h : forall S : Fin
set E, exists σ : Lifts F E K, (S : Set E) subseteq…
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.SplittingField.instIsScalarTower`：∀ {K : Type u_2} [inst : Fi
eld K] (f : Polynomial K) {R : Type u_1} [inst_1 : CommSemiring R] [inst_2 : Alg
ebra R K],   IsScalarTower R K f.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `IntermediateField.finiteDimensional_adjoin`：finiteDimensional_adjoin {S 
: Set L} [Finite S] (hS : forall x in S, IsIntegral K x) : FiniteDimensional K (
adjoin K S)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `IntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff {K : Interm
ediateField F E} : F⟮α⟯ <= K ↔ α in K
· 使用定理 `IntermediateField.exists_algHom_adjoin_of_splits`：exists_algHom_adjoin_o
f_splits : exists φ : adjoin F S ->ₐ[F] K, φ.comp (inclusion hL) = f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
（共 45 条，此处仅展示前 30 条）
-/
theorem nonempty_algHom_of_exists_root (h : ∀ x : E, ∃ y : K, aeval y (minpoly F x) = 0) :
    Nonempty (E →ₐ[F] K) := by
  refine Lifts.nonempty_algHom_of_exist_lifts_finset fun S ↦ ⟨⟨adjoin F S, ?_⟩, subset_adjoin _ _⟩
  let p := (S.prod <| fun x ↦ (minpoly F x).map (algebraMap F K))
  let K' := SplittingField p
  have splits s (hs : s ∈ S) : ((minpoly F s).map (algebraMap F K')).Splits := by
    apply (SplittingField.splits p).of_dvd (map_ne_zero (Finset.prod_ne_zero_iff.mpr
      fun _ _ ↦ Polynomial.map_ne_zero (minpoly.ne_zero <| alg.isIntegral.1 _))) ?_
    rw [IsScalarTower.algebraMap_eq F K K', ← Polynomial.map_map, map_dvd_map']
    exact Finset.dvd_prod_of_mem _ hs
  let K₀ := (⊥ : IntermediateField K K').restrictScalars F
  let FS := adjoin F (S : Set E)
  let Ω := FS →ₐ[F] K'
  have := finiteDimensional_adjoin (S := (S : Set E)) fun _ _ ↦ (alg.isIntegral).1 _
  let M (ω : Ω) := Subalgebra.toSubmodule (K₀.comap ω).toSubalgebra
  have : ⋃ ω : Ω, (M ω : Set FS) = Set.univ :=
    Set.eq_univ_of_forall fun ⟨α, hα⟩ ↦ Set.mem_iUnion.mpr <| by
      have ⟨β, hβ⟩ := h α
      let ϕ : F⟮α⟯ →ₐ[F] K' := (IsScalarTower.toAlgHom _ _ _).comp
        ((AdjoinRoot.liftAlgHom _ _ _ hβ).comp
        (adjoinRootEquivAdjoin F <| (alg.isIntegral).1 _).symm.toAlgHom)
      have ⟨ω, hω⟩ := exists_algHom_adjoin_of_splits
        (fun s hs ↦ ⟨(alg.isIntegral).1 _, splits s hs⟩) ϕ (adjoin_simple_le_iff.mpr hα)
      refine ⟨ω, β, ((DFunLike.congr_fun hω <| AdjoinSimple.gen F α).trans ?_).symm⟩
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        adjoinRootEquivAdjoin_symm_apply_gen, AdjoinRoot.liftAlgHom_root]
      rfl
  have ω : ∃ ω : Ω, ⊤ ≤ M ω := by
    cases finite_or_infinite F
    · have ⟨α, hα⟩ := exists_primitive_element_of_finite_bot F FS
      have ⟨ω, hω⟩ := Set.mem_iUnion.mp (this ▸ Set.mem_univ α)
      exact ⟨ω, show ⊤ ≤ K₀.comap ω by rwa [← hα, adjoin_simple_le_iff]⟩
    · simp_rw [top_le_iff, Subspace.exists_eq_top_of_iUnion_eq_univ this]
  exact ((botEquiv K K').toAlgHom.restrictScalars F).comp
    (ω.choose.codRestrict K₀.toSubalgebra fun x ↦ ω.choose_spec trivial)

@[deprecated (since := "2026-01-31")]
alias nonempty_algHom_of_exist_roots := nonempty_algHom_of_exists_root
/-
**Field.nonempty_algHom_of_minpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：nonempty_algHom_of_minpoly_eq (h : forall x : E, exists y : K, minpoly F x
 = minpoly F y) : Nonempty (E ->ₐ[F] K)
参数：h : forall x : E, exists y : K, minpoly F x = minpoly F y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.nonempty_algHom_of_exists_root`：nonempty_algHom_of_exists_root (h 
: forall x : E, exists y : K, aeval y (minpoly F x) = 0) : Nonempty (E ->ₐ[F] K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
-/
theorem nonempty_algHom_of_minpoly_eq
    (h : ∀ x : E, ∃ y : K, minpoly F x = minpoly F y) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_exists_root fun x ↦ have ⟨y, hy⟩ := h x; ⟨y, by rw [hy, minpoly.aeval]⟩
/-
**Field.nonempty_algHom_of_range_minpoly_subset** 是 Mathlib 中的一个定理，位于命名空间 `Field
`。
形式化陈述：nonempty_algHom_of_range_minpoly_subset (h : Set.range (@minpoly F E _ _ _
) subseteq Set.range (@minpoly F K _ _ _)) : Nonempty (E ->ₐ[F] K)
参数：h : Set.range (@minpoly F E _ _ _) subseteq Set.range (@minpoly F K _ _ _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.nonempty_algHom_of_minpoly_eq`：nonempty_algHom_of_minpoly_eq (h : 
forall x : E, exists y : K, minpoly F x = minpoly F y) : Nonempty (E ->ₐ[F] K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nonempty_algHom_of_range_minpoly_subset
    (h : Set.range (@minpoly F E _ _ _) ⊆ Set.range (@minpoly F K _ _ _)) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x ↦ have ⟨y, hy⟩ := h ⟨x, rfl⟩; ⟨y, hy.symm⟩
/-
**Field.nonempty_algEquiv_of_range_minpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：nonempty_algEquiv_of_range_minpoly_eq (h : Set.range (@minpoly F E _ _ _) 
= Set.range (@minpoly F K _ _ _)) : Nonempty (E ≃ₐ[F] K)
参数：h : Set.range (@minpoly F E _ _ _) = Set.range (@minpoly F K _ _ _)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.nonempty_algHom_of_range_minpoly_subset`：nonempty_algHom_of_range_
minpoly_subset (h : Set.range (@minpoly F E _ _ _) subseteq Set.range (@minpoly 
F K _ _ _)) : Nonempty (E ->ₐ[F] K)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_zero`：eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.IsAlgebraic.algHom_bijective₂`：algHom_bijective₂ [IsTorsionFree 
K L] [DivisionRing R] [Algebra K R] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] R) (
g : R ->ₐ[K] L) : Function.…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem nonempty_algEquiv_of_range_minpoly_eq
    (h : Set.range (@minpoly F E _ _ _) = Set.range (@minpoly F K _ _ _)) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_range_minpoly_subset h.le
  have : Algebra.IsAlgebraic F K := ⟨fun y ↦ IsIntegral.isAlgebraic <| by
    by_contra hy
    have ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
    rw [minpoly.eq_zero hy] at hx
    exact minpoly.ne_zero ((alg.isIntegral).1 x) hx⟩
  have ⟨τ⟩ := nonempty_algHom_of_range_minpoly_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩
/-
**Field.nonempty_algHom_of_aeval_eq_zero_subset** 是 Mathlib 中的一个定理，位于命名空间 `Field
`。
形式化陈述：nonempty_algHom_of_aeval_eq_zero_subset (h : {p : F[X] | exists x : E, aev
al x p = 0} subseteq {p | exists y : K, aeval y p = 0}) : Nonempty (E ->ₐ[F] K)
参数：h : {p : F[X] | exists x : E, aeval x p = 0} subseteq {p | exists y : K, aeva
l y p = 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.nonempty_algHom_of_minpoly_eq`：nonempty_algHom_of_minpoly_eq (h : 
forall x : E, exists y : K, minpoly F x = minpoly F y) : Nonempty (E ->ₐ[F] K)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `minpoly.eq_iff_aeval_minpoly_eq_zero`：eq_iff_aeval_minpoly_eq_zero [IsDo
main B] {C} [Ring C] [Algebra A C] [Nontrivial C] {b : B} (h : IsIntegral A b) {
c : C} : minpoly A b = min…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
-/
theorem nonempty_algHom_of_aeval_eq_zero_subset
    (h : {p : F[X] | ∃ x : E, aeval x p = 0} ⊆ {p | ∃ y : K, aeval y p = 0}) :
    Nonempty (E →ₐ[F] K) :=
  nonempty_algHom_of_minpoly_eq fun x ↦
    have ⟨y, hy⟩ := h ⟨_, minpoly.aeval F x⟩
    ⟨y, (minpoly.eq_iff_aeval_minpoly_eq_zero <| (alg.isIntegral).1 x).mpr hy⟩
/-
**Field.nonempty_algEquiv_of_aeval_eq_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
形式化陈述：nonempty_algEquiv_of_aeval_eq_zero_eq [Algebra.IsAlgebraic F K] (h : {p : 
F[X] | exists x : E, aeval x p = 0} = {p | exists y : K, aeval y p = 0}) : Nonem
pty (E ≃ₐ[F] K)
参数：h : {p : F[X] | exists x : E, aeval x p = 0} = {p | exists y : K, aeval y p =
 0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Field.nonempty_algHom_of_aeval_eq_zero_subset`：nonempty_algHom_of_aeval_
eq_zero_subset (h : {p : F[X] | exists x : E, aeval x p = 0} subseteq {p | exist
s y : K, aeval y p = 0}) : Nonempty…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.IsAlgebraic.algHom_bijective₂`：algHom_bijective₂ [IsTorsionFree 
K L] [DivisionRing R] [Algebra K R] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] R) (
g : R ->ₐ[K] L) : Function.…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem nonempty_algEquiv_of_aeval_eq_zero_eq [Algebra.IsAlgebraic F K]
    (h : {p : F[X] | ∃ x : E, aeval x p = 0} = {p | ∃ y : K, aeval y p = 0}) :
    Nonempty (E ≃ₐ[F] K) :=
  have ⟨σ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.le
  have ⟨τ⟩ := nonempty_algHom_of_aeval_eq_zero_subset h.ge
  ⟨.ofBijective _ (Algebra.IsAlgebraic.algHom_bijective₂ σ τ).1⟩
/-
**Field._root_.IsAlgClosure.of_exists_root** 是 Mathlib 中的一个定理，位于命名空间 `Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAlgClosure.of_exists_root
    (h : ∀ p : F[X], p.Monic → Irreducible p → ∃ x : E, aeval x p = 0) :
    IsAlgClosure F E :=
  .of_splits fun p _ _ ↦
    have ⟨σ⟩ := nonempty_algHom_of_exists_root fun x : p.SplittingField ↦
      have := Algebra.IsAlgebraic.isIntegral (K := F).1 x
      h _ (minpoly.monic this) (minpoly.irreducible this)
    Splits.of_algHom (SplittingField.splits _) σ

@[deprecated (since := "2026-01-31")]
alias _root_.IsAlgClosure.of_exist_roots := IsAlgClosure.of_exists_root

end Field

