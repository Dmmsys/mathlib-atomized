/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Embeddings of number fields

This file defines the embeddings of a number field and, in particular, the embeddings into
the field of complex numbers.

## Main Definitions and Results

* `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`: let `x ∈ K` with `K` a number field and
  let `A` be an algebraically closed field of char. 0. Then the images of `x` under the
  embeddings of `K` in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `NumberField.Embeddings.pow_eq_one_of_norm_le_one`: A non-zero algebraic integer whose conjugates
  are all inside the closed unit disk is a root of unity, this is also known as Kronecker's theorem.
* `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags

number field, embeddings
-/

@[expose] public section

open scoped Finset

namespace NumberField.Embeddings

section Fintype

open Module

variable (K : Type*) [Field K]
variable (A : Type*) [Field A] [CharZero A]

/-
**NumberField.Embeddings.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Embeddings`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CharZero K] [Algebra.IsAlgebraic ℚ K] [IsAlgClosed A] : Nonempty (K →+* A) := by
  obtain ⟨f⟩ : Nonempty (K →ₐ[ℚ] A) := by
    apply IntermediateField.nonempty_algHom_of_splits
    exact fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  exact ⟨f.toRingHom⟩

variable [NumberField K]

/-- There are finitely many embeddings of a number field. -/
/-
**NumberField.Embeddings.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Embeddings`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There are finitely many embeddings of a number field.
-/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) (RingHom.equivRatAlgHom K A).symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
/-
**NumberField.Embeddings.card** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Embeddings`
。
形式化陈述：card : Fintype.card (K ->+* A) = finrank Rat K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `AlgHom.card`：AlgHom.card (K : Type*) [Field K] [IsAlgClosed K] [Algebra 
F K] : Fintype.card (E ->ₐ[F] K) = finrank F E

--- 原说明 ---
The number of embeddings of a number field is equal to its finrank.
-/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.ofEquiv_card (RingHom.equivRatAlgHom K A).symm, AlgHom.card]
/-
**NumberField.Embeddings.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Embeddings`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (K →+* A) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K A]
  exact Module.finrank_pos

end Fintype

section Roots

open Set Polynomial

variable (K A : Type*) [Field K] [NumberField K] [Field A] [Algebra ℚ A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
/-
**NumberField.Embeddings.range_eval_eq_rootSet_minpoly** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.Embeddings`。
形式化陈述：range_eval_eq_rootSet_minpoly : (range fun φ : K ->+* A => φ x) = (minpoly
 Rat x).rootSet A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly`：Algebra.IsAlgebraic.r
ange_eval_eq_rootSet_minpoly [IsAlgClosed A] (x : K) : (Set.range fun ψ : K ->ₐ[
F] A => ψ x) = (minpoly F x).rootSet A
· 使用定理 `NumberField.isAlgebraic`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Num
berField K], Algebra.IsAlgebraic ℚ K

--- 原说明 ---
Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number fiel
d.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` o
f
the minimal polynomial of `x` over `ℚ`.
-/
theorem range_eval_eq_rootSet_minpoly :
    (range fun φ : K →+* A => φ x) = (minpoly ℚ x).rootSet A := by
  convert! (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

end Roots

section Bounded

open Module Polynomial Set

variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

/-
**NumberField.Embeddings.coeff_bdd_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.Embeddings`。
形式化陈述：coeff_bdd_of_norm_le {B : Real} {x : K} (h : forall φ : K ->+* A, ‖φ x‖ <=
 B) (i : Nat) : ‖(minpoly Rat x).coeff i‖ <= max B 1 ^ finrank Rat K * (finrank 
Rat K).choose (finrank Rat K / 2)
参数：h : forall φ : K ->+* A, ‖φ x‖ <= B；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Algebra.IsSeparable.isIntegral`：Algebra.IsSeparable.isIntegral [Algebra.
IsSeparable F K] : forall x : K, IsIntegral F x
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_bdd_of_roots_le`：coeff_bdd_of_roots_le {B : Real} {d : 
Nat} (f : F ->+* K) {p : F[X]} (h1 : p.Monic) (h2 : Splits (p.map f)) (h3 : p.na
tDegree <= d) (h4 : fo…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`：range_eval_eq_root
Set_minpoly : (range fun φ : K ->+* A => φ x) = (minpoly Rat x).rootSet A
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
-/
theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx := Algebra.IsSeparable.isIntegral ℚ x
  rw [← norm_algebraMap' A, ← coeff_map (algebraMap ℚ A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
/-
**NumberField.Embeddings.finite_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.Embeddings`。
形式化陈述：finite_of_norm_le (B : Real) : {x : K | IsIntegral Int x ∧ forall φ : K ->
+* A, ‖φ x‖ <= B}.Finite
参数：B : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.bUnion_roots_finite`：bUnion_roots_finite {R S : Type*} [Semir
ing R] [CommRing S] [IsDomain S] [DecidableEq S] (m : R ->+* S) (d : Nat) {U : S
et R} (h : U.Finite)…
· 使用引理 `Set.finite_Icc`：finite_Icc : (Icc a b).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions'`：isIntegrallyClosed_eq_fi
eld_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S} (hs : Is
Integral R s) : minpoly K s = (minpo…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.natDegree_le`：natDegree_le [Module.Free A B] : (minpoly A x).nat
Degree <= Module.finrank A B
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Let `B` be a real number. The set of algebraic integers in `K` whose conjugates 
are all
smaller in norm than `B` is finite.
-/
theorem finite_of_norm_le (B : ℝ) : {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.Finite := by
  classical
  let C := Nat.ceil (max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2))
  have := bUnion_roots_finite (algebraMap ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_ℚ_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap ℤ ℚ), ← h_map_ℚ_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_ℚ_minpoly, coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]

/-- **Kronecker's Theorem:** A non-zero algebraic integer whose conjugates are all inside the closed
unit disk is a root of unity. -/
/-
**NumberField.Embeddings.pow_eq_one_of_norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.Embeddings`。
形式化陈述：pow_eq_one_of_norm_le_one {x : K} (hx₀ : x != 0) (hxi : IsIntegral Int x) 
(hx : forall φ : K ->+* A, ‖φ x‖ <= 1) : exists (n : Nat) (_ : 0 < n), x ^ n = 1
参数：hx₀ : x != 0；hxi : IsIntegral Int x；hx : forall φ : K ->+* A, ‖φ x‖ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_ne_map_eq_of_mapsTo`：∀ {α : Type u} {β : Type v} {s 
: Set α} {t : Set β} {f : α → β},   s.Infinite → Set.MapsTo f s t → t.Finite → ∃
 x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x …
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NumberField.Embeddings.finite_of_norm_le`：finite_of_norm_le (B : Real) :
 {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `mul_left_eq_self₀`：mul_left_eq_self₀ [IsRightCancelMulZero M₀] : a * b =
 b ↔ a = 1 ∨ b = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
**Kronecker's Theorem:** A non-zero algebraic integer whose conjugates are all i
nside the closed
unit disk is a root of unity.
-/
theorem pow_eq_one_of_norm_le_one {x : K} (hx₀ : x ≠ 0) (hxi : IsIntegral ℤ x)
    (hx : ∀ φ : K →+* A, ‖φ x‖ ≤ 1) : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (f := (x ^ · : ℕ → K)) Set.infinite_univ
      (fun a _ => mem_ofPred.mpr <|
        ⟨hxi.pow a, fun φ => by simp [pow_le_one₀ (norm_nonneg (φ x)) <| hx φ]⟩)
      (finite_of_norm_le K A (1 : ℝ))
  wlog hlt : b < a
  · exact this K A hx₀ hxi hx b a habne.symm h.symm (habne.lt_or_gt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h
  refine h.resolve_right fun hp ↦ hx₀ (eq_zero_of_pow_eq_zero hp)

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
/-
**NumberField.Embeddings.pow_eq_one_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.Embeddings`。
形式化陈述：pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral Int x) (hx : forall φ 
: K ->+* A, ‖φ x‖ = 1) : exists (n : Nat) (_ : 0 < n), x ^ n = 1
参数：hxi : IsIntegral Int x；hx : forall φ : K ->+* A, ‖φ x‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.Embeddings.pow_eq_one_of_norm_le_one`：pow_eq_one_of_norm_le_
one {x : K} (hx₀ : x != 0) (hxi : IsIntegral Int x) (hx : forall φ : K ->+* A, ‖
φ x‖ <= 1) : exists (n : Nat) (_ : 0 <…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
An algebraic integer whose conjugates are all of norm one is a root of unity.
-/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by
  apply pow_eq_one_of_norm_le_one K A _ hxi fun φ ↦ le_of_eq <| hx φ
  intro rfl
  simp_rw [map_zero, norm_zero, zero_ne_one] at hx
  exact hx (IsAlgClosed.lift (R := ℚ)).toRingHom

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
/-
**NumberField.place** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NumberField.place : AbsoluteValue K Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding into a normed division ring defines a place of `K`
-/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.injective

@[simp]
/-
**NumberField.place_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x)
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) := rfl

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open scoped ComplexConjugate

variable (K : Type*) [Field K] {k : Type*} [Field k]

/--
A (random) lift of the complex embedding `φ : k →+* ℂ` to an extension `K` of `k`.
-/
/-
**NumberField.ComplexEmbedding.lift** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Compl
exEmbedding`。
形式化陈述：lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) : K ->+*
 Complex
参数：φ : k ->+* Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (random) lift of the complex embedding `φ : k →+* ℂ` to an extension `K` of `k
`.
-/
noncomputable def lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) : K →+* ℂ := by
  letI := φ.toAlgebra
  exact (IsAlgClosed.lift (R := k)).toRingHom

@[simp]
/-
**NumberField.ComplexEmbedding.lift_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.ComplexEmbedding`。
形式化陈述：lift_comp_algebraMap [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* C
omplex) : (lift K φ).comp (algebraMap k K) = φ
参数：φ : k ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `RingHom.algebraMap_toAlgebra'`：RingHom.algebraMap_toAlgebra' {R S} [Comm
Semiring R] [Semiring S] (i : R ->+* S) (h : forall c x, i c * x = x * i c) : @a
lgebraMap R S _ _ (…
-/
theorem lift_comp_algebraMap [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) :
    (lift K φ).comp (algebraMap k K) = φ := by
  unfold lift
  let := φ.toAlgebra
  rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, RingHom.algebraMap_toAlgebra']

@[simp]
/-
**NumberField.ComplexEmbedding.lift_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.ComplexEmbedding`。
形式化陈述：lift_algebraMap_apply [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* 
Complex) (x : k) : lift K φ (algebraMap k K x) = φ x
参数：φ : k ->+* Complex；x : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `NumberField.ComplexEmbedding.lift_comp_algebraMap`：lift_comp_algebraMap 
[Algebra k K] [Algebra.IsAlgebraic k K] (φ : k ->+* Complex) : (lift K φ).comp (
algebraMap k K) = φ
-/
theorem lift_algebraMap_apply [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) (x : k) :
    lift K φ (algebraMap k K x) = φ x :=
  RingHom.congr_fun (lift_comp_algebraMap K φ) x

variable {K}

/-- The conjugate of a complex embedding as a complex embedding. -/
/-
**NumberField.ComplexEmbedding.conjugate** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFiel
d.ComplexEmbedding`。
形式化陈述：conjugate (φ : K ->+* Complex) : K ->+* Complex
参数：φ : K ->+* Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate of a complex embedding as a complex embedding.
-/
abbrev conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ

@[simp]
/-
**NumberField.ComplexEmbedding.conjugate_comp** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.ComplexEmbedding`。
形式化陈述：conjugate_comp (φ : K ->+* Complex) (σ : k ->+* K) : (conjugate φ).comp σ 
= conjugate (φ.comp σ)
参数：φ : K ->+* Complex；σ : k ->+* K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjugate_comp (φ : K →+* ℂ) (σ : k →+* K) :
    (conjugate φ).comp σ = conjugate (φ.comp σ) :=
  rfl

variable (K) in
/-
**NumberField.ComplexEmbedding.involutive_conjugate** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.ComplexEmbedding`。
形式化陈述：involutive_conjugate : Function.Involutive (conjugate : (K ->+* Complex) -
> (K ->+* Complex))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem involutive_conjugate :
    Function.Involutive (conjugate : (K →+* ℂ) → (K →+* ℂ)) := by
  intro; simp

@[simp]
/-
**NumberField.ComplexEmbedding.conjugate_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.ComplexEmbedding`。
形式化陈述：conjugate_coe_eq (φ : K ->+* Complex) (x : K) : (conjugate φ) x = conj (φ 
x)
参数：φ : K ->+* Complex；x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl
/-
**NumberField.ComplexEmbedding.place_conjugate** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.ComplexEmbedding`。
形式化陈述：place_conjugate (φ : K ->+* Complex) : place (conjugate φ) = place φ
参数：φ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.ext`：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x)
 -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_conj`：norm_conj (z : Complex) : ‖conj z‖ = ‖z‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ := by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

/-- An embedding into `ℂ` is real if it is fixed by complex conjugation. -/
/-
**NumberField.ComplexEmbedding.IsReal** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.C
omplexEmbedding`。
形式化陈述：IsReal (φ : K ->+* Complex) : Prop
参数：φ : K ->+* Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding into `ℂ` is real if it is fixed by complex conjugation.
-/
abbrev IsReal (φ : K →+* ℂ) : Prop := IsSelfAdjoint φ
/-
**NumberField.ComplexEmbedding.isReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.ComplexEmbedding`。
形式化陈述：isReal_iff {φ : K ->+* Complex} : IsReal φ ↔ conjugate φ = φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
-/
theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ := isSelfAdjoint_iff
/-
**NumberField.ComplexEmbedding.isReal_conjugate_iff** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.ComplexEmbedding`。
形式化陈述：isReal_conjugate_iff {φ : K ->+* Complex} : IsReal (conjugate φ) ↔ IsReal 
φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_iff`：star_iff [InvolutiveStar R] {x : R} : IsSelfAdjo
int (star x) ↔ IsSelfAdjoint x
-/
theorem isReal_conjugate_iff {φ : K →+* ℂ} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
/-
**NumberField.ComplexEmbedding.IsReal.embedding** 是 Mathlib 中的一个定义，位于命名空间 `Numbe
rField.ComplexEmbedding.IsReal`。
形式化陈述：{K : Type u_1} → [inst : Field K] → {φ : K →+* ℂ} → NumberField.ComplexEmb
edding.IsReal φ → K →+* ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real embedding as a ring homomorphism from `K` to `ℝ` .
-/
def IsReal.embedding {φ : K →+* ℂ} (hφ : IsReal φ) : K →+* ℝ where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, forall_const]

@[simp]
/-
**NumberField.ComplexEmbedding.IsReal.coe_embedding_apply** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.ComplexEmbedding.IsReal`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {φ : K →+* ℂ} (hφ : NumberField.ComplexE
mbedding.IsReal φ) (x : K),   ↑(hφ.embedding x) = φ x
参数：hφ : NumberField.ComplexEmbedding.IsReal φ；x : K；hφ.embedding x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.conj_eq_iff_im`：conj_eq_iff_im {z : Complex} : conj z = z ↔ z.im
 = 0
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
theorem IsReal.coe_embedding_apply {φ : K →+* ℂ} (hφ : IsReal φ) (x : K) :
    (hφ.embedding x : ℂ) = φ x := by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x
/-
**NumberField.ComplexEmbedding.IsReal.comp** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.ComplexEmbedding.IsReal`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] (f : k
 →+* K) {φ : K →+* ℂ},   NumberField.ComplexEmbedding.IsReal φ → NumberField.Com
plexEmbedding.IsReal (φ.comp f)
参数：f : k →+* K；φ.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
lemma IsReal.comp (f : k →+* K) {φ : K →+* ℂ} (hφ : IsReal φ) :
    IsReal (φ.comp f) := by ext1 x; simpa using RingHom.congr_fun hφ (f x)
/-
**NumberField.ComplexEmbedding.isReal_comp_iff** 是 Mathlib 中的一个引理，位于命名空间 `Number
Field.ComplexEmbedding`。
形式化陈述：isReal_comp_iff {f : k ≃+* K} {φ : K ->+* Complex} : IsReal (φ.comp (f : k
 ->+* K)) ↔ IsReal φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.ComplexEmbedding.IsReal.comp`：∀ {K : Type u_1} [inst : Field
 K] {k : Type u_2} [inst_1 : Field k] (f : k →+* K) {φ : K →+* ℂ},   NumberField
.ComplexEmbedding.IsReal φ → N…
-/
lemma isReal_comp_iff {f : k ≃+* K} {φ : K →+* ℂ} :
    IsReal (φ.comp (f : k →+* K)) ↔ IsReal φ :=
  ⟨fun H ↦ by convert! H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩
/-
**NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq** 是 Mathlib 中的一个引理
，位于命名空间 `NumberField.ComplexEmbedding`。
形式化陈述：exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K ->+* 
Complex) (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) : exists σ : Ga
l(K/k), φ.comp σ.symm = ψ
参数：φ ψ : K ->+* Complex；h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
-/
lemma exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : Gal(K/k), φ.comp σ.symm = ψ := by
  let := (φ.comp (algebraMap k K)).toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

variable [Algebra k K] (φ : K →+* ℂ) (σ : Gal(K/k))

/--
`IsConj φ σ` states that `σ : Gal(K/k)` is the conjugation under the embedding `φ : K →+* ℂ`.
-/
/-
**NumberField.ComplexEmbedding.IsConj** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Com
plexEmbedding`。
形式化陈述：IsConj : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsConj φ σ` states that `σ : Gal(K/k)` is the conjugation under the embedding `
φ : K →+* ℂ`.
-/
def IsConj : Prop := conjugate φ = φ.comp σ

variable {φ σ}
/-
**NumberField.ComplexEmbedding.IsConj.eq** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)},   NumberField.ComplexEmbedding.Is
Conj φ σ → ∀ (x : K), φ (σ x) = star (φ x)
参数：K/k；x : K；σ x；φ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsConj.eq (h : IsConj φ σ) (x) : φ (σ x) = star (φ x) := RingHom.congr_fun h.symm x
/-
**NumberField.ComplexEmbedding.IsConj.ext** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ}   {σ₁ σ₂ : Gal(K/k)}, NumberField.ComplexEmbeddin
g.IsConj φ σ₁ → NumberField.ComplexEmbedding.IsConj φ σ₂ → σ₁ = σ₂
参数：K/k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.ComplexEmbedding.IsConj.eq`：∀ {K : Type u_1} [inst : Field K
] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ} {σ : Ga
l(K/k)},   NumberField.Compl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsConj.ext {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂) : σ₁ = σ₂ :=
  AlgEquiv.ext fun x ↦ φ.injective ((h₁.eq x).trans (h₂.eq x).symm)
/-
**NumberField.ComplexEmbedding.IsConj.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ}   {σ₁ σ₂ : Gal(K/k)}, NumberField.ComplexEmbeddin
g.IsConj φ σ₁ → (σ₁ = σ₂ ↔ NumberField.ComplexEmbedding.IsConj φ σ₂)
参数：K/k；σ₁ = σ₂ ↔ NumberField.ComplexEmbedding.IsConj φ σ₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.IsConj.ext`：∀ {K : Type u_1} [inst : Field 
K] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ}   {σ₁ 
σ₂ : Gal(K/k)}, NumberField.C…
-/
lemma IsConj.ext_iff {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) : σ₁ = σ₂ ↔ IsConj φ σ₂ :=
  ⟨fun e ↦ e ▸ h₁, h₁.ext⟩
/-
**NumberField.ComplexEmbedding.IsConj.isReal_comp** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)},   NumberField.ComplexEmbedding.Is
Conj φ σ → NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap k K))
参数：K/k；φ.comp (algebraMap k K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.IsConj.eq`：∀ {K : Type u_1} [inst : Field K
] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ} {σ : Ga
l(K/k)},   NumberField.Compl…
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsConj.isReal_comp (h : IsConj φ σ) : IsReal (φ.comp (algebraMap k K)) := by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]
/-
**NumberField.ComplexEmbedding.isConj_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `NumberF
ield.ComplexEmbedding`。
形式化陈述：isConj_one_iff : IsConj φ (1 : Gal(K/k)) ↔ IsReal φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isConj_one_iff : IsConj φ (1 : Gal(K/k)) ↔ IsReal φ := Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff
/-
**NumberField.ComplexEmbedding.isConj_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Numb
erField.ComplexEmbedding`。
形式化陈述：isConj_ne_one_iff (hσ : IsConj φ σ) : σ != 1 ↔ ¬ IsReal φ
参数：hσ : IsConj φ σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `NumberField.ComplexEmbedding.isConj_one_iff`：isConj_one_iff : IsConj φ (
1 : Gal(K/k)) ↔ IsReal φ
· 使用定理 `NumberField.ComplexEmbedding.IsConj.ext_iff`：∀ {K : Type u_1} [inst : Fi
eld K] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ}   
{σ₁ σ₂ : Gal(K/k)}, NumberField.C…
· 使用定理 `NumberField.ComplexEmbedding.IsReal.isConjGal_one`：∀ {K : Type u_1} [ins
t : Field K] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+*
 ℂ},   NumberField.ComplexEmbedding.IsR…
-/
lemma isConj_ne_one_iff (hσ : IsConj φ σ) :
    σ ≠ 1 ↔ ¬ IsReal φ :=
  not_iff_not.mpr ⟨fun h ↦ isConj_one_iff.mp (h ▸ hσ),
    fun h ↦ (IsConj.ext_iff hσ).mpr h.isConjGal_one⟩
/-
**NumberField.ComplexEmbedding.IsConj.symm** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)},   NumberField.ComplexEmbedding.Is
Conj φ σ → NumberField.ComplexEmbedding.IsConj φ σ.symm
参数：K/k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NumberField.ComplexEmbedding.IsConj.eq`：∀ {K : Type u_1} [inst : Field K
] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ} {σ : Ga
l(K/k)},   NumberField.Compl…
-/
lemma IsConj.symm (hσ : IsConj φ σ) :
    IsConj φ σ.symm := RingHom.ext fun x ↦ by simpa using congr_arg star (hσ.eq (σ.symm x))
/-
**NumberField.ComplexEmbedding.isConj_symm** 是 Mathlib 中的一个引理，位于命名空间 `NumberFiel
d.ComplexEmbedding`。
形式化陈述：isConj_symm : IsConj φ σ.symm ↔ IsConj φ σ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.IsConj.symm`：∀ {K : Type u_1} [inst : Field
 K] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ} {σ : 
Gal(K/k)},   NumberField.Compl…
-/
lemma isConj_symm : IsConj φ σ.symm ↔ IsConj φ σ :=
  ⟨IsConj.symm, IsConj.symm⟩
/-
**NumberField.ComplexEmbedding.isConj_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Num
berField.ComplexEmbedding`。
形式化陈述：isConj_apply_apply (hσ : IsConj φ σ) (x : K) : σ (σ x) = x
参数：hσ : IsConj φ σ；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.ComplexEmbedding.IsConj.eq`：∀ {K : Type u_1} [inst : Field K
] {k : Type u_2} [inst_1 : Field k] [inst_2 : Algebra k K] {φ : K →+* ℂ} {σ : Ga
l(K/k)},   NumberField.Compl…
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isConj_apply_apply (hσ : IsConj φ σ) (x : K) :
    σ (σ x) = x := by
  simp [← φ.injective.eq_iff, hσ.eq]
/-
**NumberField.ComplexEmbedding.IsConj.comp** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.ComplexEmbedding.IsConj`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {k : Type u_2} [inst_1 : Field k] [inst_
2 : Algebra k K] {φ : K →+* ℂ} {σ : Gal(K/k)},   NumberField.ComplexEmbedding.Is
Conj φ σ →     ∀ (ν : Gal(K/k)), NumberField.ComplexEmbedding.IsConj (φ.comp ↑ν)
 (ν⁻¹ * σ * ν)
参数：K/k；ν : Gal(K/k)；φ.comp ↑ν；ν⁻¹ * σ * ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
theorem IsConj.comp (hσ : IsConj φ σ) (ν : Gal(K/k)) :
    IsConj (φ.comp ν) (ν⁻¹ * σ * ν) := by
  ext
  simpa [← AlgEquiv.mul_apply, ← mul_assoc] using! RingHom.congr_fun hσ _
/-
**NumberField.ComplexEmbedding.orderOf_isConj_two_of_ne_one** 是 Mathlib 中的一个引理，位
于命名空间 `NumberField.ComplexEmbedding`。
形式化陈述：orderOf_isConj_two_of_ne_one (hσ : IsConj φ σ) (hσ' : σ != 1) : orderOf σ 
= 2
参数：hσ : IsConj φ σ；hσ' : σ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_prime_iff`：orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧
 x != 1
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用引理 `NumberField.ComplexEmbedding.isConj_apply_apply`：isConj_apply_apply (hσ 
: IsConj φ σ) (x : K) : σ (σ x) = x
-/
lemma orderOf_isConj_two_of_ne_one (hσ : IsConj φ σ) (hσ' : σ ≠ 1) :
    orderOf σ = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simpa using isConj_apply_apply hσ _, hσ'⟩

section Extension

variable {K : Type*} {L : Type*} [Field K] [Field L] (ψ : K →+* ℂ) [Algebra K L]

/-- If `L/K`, `ψ : K →+* ℂ`, and `φ : L →+* ℂ`, then `φ` lies over `ψ` if the restriction of
`φ` to `K` is `ψ`. -/
/-
**NumberField.ComplexEmbedding.LiesOver** 是 Mathlib 中的一个归纳类型，位于命名空间 `NumberField
.ComplexEmbedding`。
形式化陈述：{K : Type u_3} → {L : Type u_4} → [inst : Field K] → [inst_1 : Field L] → 
[Algebra K L] → (L →+* ℂ) → (K →+* ℂ) → Prop
参数：L →+* ℂ；K →+* ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K`, `ψ : K →+* ℂ`, and `φ : L →+* ℂ`, then `φ` lies over `ψ` if the restri
ction of
`φ` to `K` is `ψ`.
-/
protected class LiesOver (φ : L →+* ℂ) (ψ : K →+* ℂ) : Prop where
  over (φ ψ) : φ.comp (algebraMap K L) = ψ
/-
**NumberField.ComplexEmbedding.LiesOver.over_apply** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.ComplexEmbedding.LiesOver`。
形式化陈述：∀ {K : Type u_3} {L : Type u_4} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] (φ : L →+* ℂ) (ψ : K →+* ℂ)   [NumberField.ComplexEmbedding.Lie
sOver φ ψ] {x : K}, φ ((algebraMap K L) x) = ψ x
参数：φ : L →+* ℂ；ψ : K →+* ℂ；(algebraMap K L) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
-/
theorem LiesOver.over_apply (φ : L →+* ℂ) (ψ : K →+* ℂ) [ComplexEmbedding.LiesOver φ ψ] {x : K} :
    φ (algebraMap K L x) = ψ x := RingHom.ext_iff.1 (LiesOver.over φ ψ) _
/-
**NumberField.ComplexEmbedding.liesOver_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.ComplexEmbedding`。
形式化陈述：liesOver_iff {φ : L ->+* Complex} {ψ : K ->+* Complex} : ComplexEmbedding.
LiesOver φ ψ ↔ φ.comp (algebraMap K L) = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
-/
theorem liesOver_iff {φ : L →+* ℂ} {ψ : K →+* ℂ} :
    ComplexEmbedding.LiesOver φ ψ ↔ φ.comp (algebraMap K L) = ψ :=
  ⟨fun _ ↦ LiesOver.over φ ψ, fun h ↦ ⟨h⟩⟩

variable (L)

/-- If `L/K` and `ψ : K →+* ℂ`, then the type of `ComplexEmbedding.Extension L ψ` consists of all
`φ : L →+* ℂ` such that `φ.comp (algebraMap K L) = ψ`. -/
/-
**NumberField.ComplexEmbedding.Extension** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.
ComplexEmbedding`。
形式化陈述：{K : Type u_3} → (L : Type u_4) → [inst : Field K] → [inst_1 : Field L] → 
(K →+* ℂ) → [Algebra K L] → Type (max 0 u_4)
参数：L : Type u_4；K →+* ℂ；max 0 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K` and `ψ : K →+* ℂ`, then the type of `ComplexEmbedding.Extension L ψ` co
nsists of all
`φ : L →+* ℂ` such that `φ.comp (algebraMap K L) = ψ`.
-/
protected abbrev Extension := { φ : L →+* ℂ // ComplexEmbedding.LiesOver φ ψ }

namespace Extension

variable (φ : ComplexEmbedding.Extension L ψ) {L ψ}

/-
**NumberField.ComplexEmbedding.Extension.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.ComplexEmbedding.Extension`。
形式化陈述：comp_eq : φ.1.comp (algebraMap K L) = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.ComplexEmbedding.LiesOver.over`：∀ {K : Type u_3} {L : Type u
_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L} (φ : L →+* ℂ) (ψ 
: K →+* ℂ)   [self : NumberField…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem comp_eq : φ.1.comp (algebraMap K L) = ψ := φ.2.over
/-
**NumberField.ComplexEmbedding.Extension.conjugate_comp_ne** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.ComplexEmbedding.Extension`。
形式化陈述：conjugate_comp_ne (h : ¬IsReal ψ) : (conjugate φ).comp (algebraMap K L) !=
 ψ
参数：h : ¬IsReal ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.ComplexEmbedding.Extension.comp_eq`：comp_eq : φ.1.comp (alge
braMap K L) = ψ
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem conjugate_comp_ne (h : ¬IsReal ψ) : (conjugate φ).comp (algebraMap K L) ≠ ψ := by
  simp_all [ComplexEmbedding.isReal_iff, comp_eq]
/-
**NumberField.ComplexEmbedding.Extension.not_isReal_of_not_isReal** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.ComplexEmbedding.Extension`。
形式化陈述：not_isReal_of_not_isReal (h : ¬IsReal ψ) : ¬IsReal φ.1
参数：h : ¬IsReal ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `NumberField.ComplexEmbedding.IsReal.comp`：∀ {K : Type u_1} [inst : Field
 K] {k : Type u_2} [inst_1 : Field k] (f : k →+* K) {φ : K →+* ℂ},   NumberField
.ComplexEmbedding.IsReal φ → N…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.ComplexEmbedding.Extension.comp_eq`：comp_eq : φ.1.comp (alge
braMap K L) = ψ
-/
theorem not_isReal_of_not_isReal (h : ¬IsReal ψ) : ¬IsReal φ.1 :=
  mt (IsReal.comp _) (comp_eq φ ▸ h)

end Extension

variable (K) {L ψ}

/-- If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if the image of `φ` is complex while the image
of `φ` restricted to `K` is real.

This is the complex embedding analogue of `InfinitePlace.IsRamified K w`, where
`w : InfinitePlace L`. It is not the same concept because conjugation of `φ` in this case
leads to two distinct mixed embeddings but only a single ramified place `w`, leading to a
two-to-one isomorphism between them. -/
/-
**NumberField.ComplexEmbedding.IsMixed** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField.
ComplexEmbedding`。
形式化陈述：IsMixed (φ : L ->+* Complex)
参数：φ : L ->+* Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if the image of `φ` is complex wh
ile the image
of `φ` restricted to `K` is real.

This is the complex embedding analogue of `InfinitePlace.IsRamified K w`, where
`w : InfinitePlace L`. It is not the same concept because conjugation of `φ` in 
this case
leads to two distinct mixed embeddings but only a single ramified place `w`, lea
ding to a
two-to-one isomorphism between them.
-/
abbrev IsMixed (φ : L →+* ℂ) :=
  ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ∧ ¬ComplexEmbedding.IsReal φ

/-- If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if `φ` is not mixed in `K`, i.e., `φ` is real
if and only if it's restriction to `K` is.

This is the complex embedding analogue of `InfinitePlace.IsUnramified K w`, where
`w : InfinitePlace L`. In this case there is an isomorphism between unmixed embeddings and
unramified infinite places. -/
/-
**NumberField.ComplexEmbedding.IsUnmixed** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFiel
d.ComplexEmbedding`。
形式化陈述：IsUnmixed (φ : L ->+* Complex)
参数：φ : L ->+* Complex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if `φ` is not mixed in `K`, i.e.,
 `φ` is real
if and only if it's restriction to `K` is.

This is the complex embedding analogue of `InfinitePlace.IsUnramified K w`, wher
e
`w : InfinitePlace L`. In this case there is an isomorphism between unmixed embe
ddings and
unramified infinite places.
-/
abbrev IsUnmixed (φ : L →+* ℂ) := IsReal (φ.comp (algebraMap K L)) → IsReal φ
/-
**NumberField.ComplexEmbedding.IsUnmixed.isReal_iff_isReal** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.ComplexEmbedding.IsUnmixed`。
形式化陈述：∀ (K : Type u_3) {L : Type u_4} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L] {φ : L →+* ℂ},   NumberField.ComplexEmbedding.IsUnmixed K φ →  
   (NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ↔ NumberField.
ComplexEmbedding.IsReal φ)
参数：K : Type u_3；NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ↔ 
NumberField.ComplexEmbedding.IsReal φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem IsUnmixed.isReal_iff_isReal {φ : L →+* ℂ} (h : IsUnmixed K φ) :
    IsReal (φ.comp (algebraMap K L)) ↔ IsReal φ := by
  aesop (add simp [IsReal.comp])

variable {K} (L) (ψ)

/-- The set of all complex embeddings of `L` that lie over `ψ` and are mixed. -/
/-
**NumberField.ComplexEmbedding.mixedEmbeddingsOver** 是 Mathlib 中的一个定义，位于命名空间 `Nu
mberField.ComplexEmbedding`。
形式化陈述：mixedEmbeddingsOver : Set (L ->+* Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all complex embeddings of `L` that lie over `ψ` and are mixed.
-/
def mixedEmbeddingsOver : Set (L →+* ℂ) := { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsMixed K φ }
/-- The set of all complex embeddings of `L` that lie over `ψ` and are unmixed. -/
/-
**NumberField.ComplexEmbedding.unmixedEmbeddingsOver** 是 Mathlib 中的一个定义，位于命名空间 `
NumberField.ComplexEmbedding`。
形式化陈述：unmixedEmbeddingsOver : Set (L ->+* Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all complex embeddings of `L` that lie over `ψ` and are unmixed.
-/
def unmixedEmbeddingsOver : Set (L →+* ℂ) := { φ | ComplexEmbedding.LiesOver φ ψ ∧ IsUnmixed K φ }
/-
**NumberField.ComplexEmbedding.disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOve
r** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.ComplexEmbedding`。
形式化陈述：disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver : Disjoint (unmixedEmbe
ddingsOver L ψ) (mixedEmbeddingsOver L ψ)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver :
    Disjoint (unmixedEmbeddingsOver L ψ) (mixedEmbeddingsOver L ψ) := by
  grind [mixedEmbeddingsOver, unmixedEmbeddingsOver]
/-
**NumberField.ComplexEmbedding.union_unmixedEmbeddingsOver_mixedEmbeddingsOver**
 是 Mathlib 中的一个定理，位于命名空间 `NumberField.ComplexEmbedding`。
形式化陈述：union_unmixedEmbeddingsOver_mixedEmbeddingsOver : (unmixedEmbeddingsOver L
 ψ) union (mixedEmbeddingsOver L ψ) = { φ | ComplexEmbedding.LiesOver φ ψ }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem union_unmixedEmbeddingsOver_mixedEmbeddingsOver :
    (unmixedEmbeddingsOver L ψ) ∪ (mixedEmbeddingsOver L ψ) =
      { φ | ComplexEmbedding.LiesOver φ ψ } := by
  grind [unmixedEmbeddingsOver, mixedEmbeddingsOver, ← Set.ofPred_or]

end Extension

end NumberField.ComplexEmbedding

