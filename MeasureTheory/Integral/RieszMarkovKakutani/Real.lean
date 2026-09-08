/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Oliver Butterley
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Basic
public import Mathlib.Order.Interval.Set.Union

/-!
# Riesz–Markov–Kakutani representation theorem for real-linear functionals

The Riesz–Markov–Kakutani representation theorem relates linear functionals on spaces of continuous
functions on a locally compact space to measures.

There are many closely related variations of the theorem. This file contains the proof of the
version where the space is a locally compact T2 space, the linear functionals are real and the
continuous functions have compact support.

## Main definitions & statements

* `RealRMK.rieszMeasure`: the measure induced by a real linear positive functional.
* `RealRMK.integral_rieszMeasure`: the Riesz–Markov–Kakutani representation theorem for a real
  linear positive functional.
* `RealRMK.rieszMeasure_integralPositiveLinearMap`: the uniqueness of the representing measure in
  the Riesz–Markov–Kakutani representation theorem.

## Implementation notes

The measure is defined through `rieszContent` which is for `NNReal` using the `toNNRealLinear`
version of `Λ`.

The Riesz–Markov–Kakutani representation theorem is first proved for `Real`-linear `Λ` because
equality is proven using two inequalities by considering `Λ f` and `Λ (-f)` for all functions
`f`, yet on `C_c(X, ℝ≥0)` there is no negation.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

@[expose] public section

open scoped ENNReal BoundedContinuousFunction
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)

section Construction

variable [LocallyCompactSpace X]

/-- The measure induced for `Real`-linear positive functional `Λ`, defined through `toNNRealLinear`
and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK`, while
`rieszMeasure` without namespace is for `NNReal`-linear `Λ`. -/
/-
**RealRMK.rieszMeasure** 是 Mathlib 中的一个定义，位于命名空间 `RealRMK`。
形式化陈述：rieszMeasure
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X

--- 原说明 ---
The measure induced for `Real`-linear positive functional `Λ`, defined through `
toNNRealLinear`
and the `NNReal`-version of `rieszContent`. This is under the namespace `RealRMK
`, while
`rieszMeasure` without namespace is for `NNReal`-linear `Λ`.
-/
noncomputable def rieszMeasure := (rieszContent (toNNRealLinear Λ)).measure

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` assumes values between `0` and `1` and the support is contained in `V`, then
`Λ f ≤ rieszMeasure V`. -/
/-
**RealRMK.le_rieszMeasure_tsupport_subset** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
形式化陈述：le_rieszMeasure_tsupport_subset {f : C_c(X, Real)} (hf : forall (x : X), 0
 <= f x ∧ f x <= 1) {V : Set X} (hV : tsupport f subseteq V) : ENNReal.ofReal (Λ
 f) <= rieszMeasure Λ V
参数：X, Real；hf : forall (x : X), 0 <= f x ∧ f x <= 1；hV : tsupport f subseteq V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `CompactlySupportedContinuousMap.hasCompactSupport`：∀ {α : Type u_2} {β :
 Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : Z
ero β]   (f : CompactlySupportedContinu…
· 使用定理 `MeasureTheory.Content.measure_eq_content_of_regular`：measure_eq_content_
of_regular (H : MeasureTheory.Content.ContentRegular μ) (K : TopologicalSpace.Co
mpacts G) : μ.measure ↑K = μ K
· 使用引理 `contentRegular_rieszContent`：contentRegular_rieszContent : (rieszContent
 Λ).ContentRegular
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Compacts.coe_mk`：coe_mk (s : Set α) (h) : (mk s h : Set
 α) = s
· 使用定理 `RealRMK.rieszMeasure.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[inst_1 : T2Space X] [inst_2 : MeasurableSpace X] [inst_3 : BorelSpace X]   (Λ :
 CompactlySuppo…
· 使用定理 `rieszContentAux_mono`：rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ 
<= K₂) : rieszContentAux Λ K₁ <= rieszContentAux Λ K₂
· 使用引理 `rieszContentAux_union`：rieszContentAux_union {K₁ K₂ : TopologicalSpace.C
ompacts X} (disj : Disjoint (K₁ : Set X) K₂) : rieszContentAux Λ (K₁ ⊔ K₂) = rie
szContentAu…
· 使用定理 `rieszContentAux_sup_le`：rieszContentAux_sup_le (K1 K2 : Compacts X) : ri
eszContentAux Λ (K1 ⊔ K2) <= rieszContentAux Λ K1 + rieszContentAux Λ K2
· 使用定理 `rieszContent.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 
: T2Space X] [inst_2 : LocallyCompactSpace X]   (Λ : CompactlySupportedContinuou
sMap X …
· 使用定理 `PositiveLinearMap.map_nonneg`：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Typ
e u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder 
E₁] [inst_3 : AddC…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.ofReal_eq_coe_nnreal`：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= 
x) : ENNReal.ofReal x = ofNNReal (NNReal.mk x h)
· 使用引理 `MeasureTheory.Content.mk_apply`：mk_apply (toFun : Compacts G -> Real>=0)
 (mono' sup_disjoint' sup_le') (K : Compacts G) : mk toFun mono' sup_disjoint' s
up_le' K = toFun K
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [Densely
Ordered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b 
: α} [AddLeftS…
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` assumes values between `0` and `1` and the support is contained in `V`, t
hen
`Λ f ≤ rieszMeasure V`.
-/
lemma le_rieszMeasure_tsupport_subset {f : C_c(X, ℝ)} (hf : ∀ (x : X), 0 ≤ f x ∧ f x ≤ 1)
    {V : Set X} (hV : tsupport f ⊆ V) : ENNReal.ofReal (Λ f) ≤ rieszMeasure Λ V := by
  apply le_trans _ (measure_mono hV)
  have := Content.measure_eq_content_of_regular (rieszContent (toNNRealLinear Λ))
    (contentRegular_rieszContent (toNNRealLinear Λ)) (⟨tsupport f, f.hasCompactSupport⟩)
  rw [← Compacts.coe_mk (tsupport f) f.hasCompactSupport, rieszMeasure, this, rieszContent,
    ENNReal.ofReal_eq_coe_nnreal (Λ.map_nonneg fun x ↦ (hf x).1), Content.mk_apply,
    ENNReal.coe_le_coe]
  apply le_iff_forall_pos_le_add.mpr
  intro _ hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos (toNNRealLinear Λ)
    ⟨tsupport f, f.hasCompactSupport⟩ (Real.toNNReal_pos.mpr hε)
  simp_rw [NNReal.val_eq_coe, Real.toNNReal_coe] at hg
  refine (Λ.mono ?_).trans hg.2.le
  intro x
  by_cases hx : x ∈ tsupport f
  · simpa using le_trans (hf x).2 (hg.1 x hx)
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`. -/
/-
**RealRMK.rieszMeasure_le_of_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
形式化陈述：rieszMeasure_le_of_eq_one {f : C_c(X, Real)} (hf : forall x, 0 <= f x) {K 
: Set X} (hK : IsCompact K) (hfK : forall x in K, f x = 1) : rieszMeasure Λ K <=
 ENNReal.ofReal (Λ f)
参数：X, Real；hf : forall x, 0 <= f x；hK : IsCompact K；hfK : forall x in K, f x = 1
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Compacts.coe_mk`：coe_mk (s : Set α) (h) : (mk s h : Set
 α) = s
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `RealRMK.rieszMeasure.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[inst_1 : T2Space X] [inst_2 : MeasurableSpace X] [inst_3 : BorelSpace X]   (Λ :
 CompactlySuppo…
· 使用定理 `MeasureTheory.Content.measure_eq_content_of_regular`：measure_eq_content_
of_regular (H : MeasureTheory.Content.ContentRegular μ) (K : TopologicalSpace.Co
mpacts G) : μ.measure ↑K = μ K
· 使用引理 `contentRegular_rieszContent`：contentRegular_rieszContent : (rieszContent
 Λ).ContentRegular
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_iff`：coe_le_iff : ↑r <= a ↔ forall p : Real>=0, a = p -> 
r <= p
· 使用定理 `csInf_le'`：csInf_le' (h : a in s) : sInf s <= a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用引理 `CompactlySupportedContinuousMap.toNNRealLinear_apply`：toNNRealLinear_app
ly (Λ : C_c(α, Real) ->ₚ[Real] Real) (f : C_c(α, Real>=0)) : toNNRealLinear Λ f 
= Λ (toReal f)
· 使用定理 `CompactlySupportedContinuousMap.ext`：ext {f g : C_c(α, β)} (h : forall x
, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CompactlySupportedContinuousMap.toReal_apply`：∀ {α : Type u_2} [inst : T
opologicalSpace α] (f : CompactlySupportedContinuousMap α NNReal) (x : α), f.toR
eal x = ↑(f x)
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` assumes the value `1` on a compact set `K` then `rieszMeasure K ≤ Λ f`.
-/
lemma rieszMeasure_le_of_eq_one {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) {K : Set X}
    (hK : IsCompact K) (hfK : ∀ x ∈ K, f x = 1) : rieszMeasure Λ K ≤ ENNReal.ofReal (Λ f) := by
  rw [← Compacts.coe_mk K hK, rieszMeasure,
    Content.measure_eq_content_of_regular _ (contentRegular_rieszContent (toNNRealLinear Λ))]
  apply ENNReal.coe_le_iff.mpr
  intro p hp
  rw [← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_eq_ofReal_iff (Λ.map_nonneg hf) NNReal.zero_le_coe] at hp
  apply csInf_le'
  rw [Set.mem_image]
  use f.nnrealPart
  simp_rw [Set.mem_ofPred_eq, nnrealPart_apply, Real.one_le_toNNReal]
  refine ⟨(fun x hx ↦ Eq.ge (hfK x hx)), ?_⟩
  apply NNReal.eq
  rw [toNNRealLinear_apply, show f.nnrealPart.toReal = f by ext z; simp [hf z], hp]

omit [T2Space X] [LocallyCompactSpace X] in
/-- Given `f : C_c(X, ℝ)` such that `range f ⊆ [a, b]` we obtain a partition of the support of `f`
determined by partitioning `[a, b]` into `N` pieces. -/
/-
**RealRMK.range_cut_partition** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
形式化陈述：range_cut_partition (f : C_c(X, Real)) (a : Real) {ε : Real} (hε : 0 < ε) 
(N : Nat) (hf : range f subseteq Ioo a (a + N * ε)) : exists (E : Fin N -> Set X
), tsupport f = ⋃ j, E j ∧ univ.PairwiseDisjoint E ∧ (forall n : Fin N, forall x
 in E n, a + ε * n < f x ∧ f x <= a + ε * (n + 1)) ∧ forall n : Fin N, Measurabl
eSet (E n)
参数：f : C_c(X, Real)；a : Real；hε : 0 < ε；N : Nat；hf : range f subseteq Ioo a (a +
 N * ε)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_three`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] 
[AddLeftMono α] [AddRightMono α] {a b c d e f : α},   a ≤ d → b ≤ e → c ≤ f → a 
+ b + …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Ioc_subset_biUnion_Ioc`：Ioc_subset_biUnion_Ioc {X : Type*} [LinearOrder 
X] (N : Nat) (a : Nat -> X) : Ioc (a 0) (a N) subseteq ⋃ i in Finset.range N, Io
c (a i) (a (…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 98 条，此处仅展示前 30 条）

--- 原说明 ---
Given `f : C_c(X, ℝ)` such that `range f ⊆ [a, b]` we obtain a partition of the 
support of `f`
determined by partitioning `[a, b]` into `N` pieces.
-/
lemma range_cut_partition (f : C_c(X, ℝ)) (a : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hf : range f ⊆ Ioo a (a + N * ε)) : ∃ (E : Fin N → Set X), tsupport f = ⋃ j, E j ∧
    univ.PairwiseDisjoint E ∧ (∀ n : Fin N, ∀ x ∈ E n, a + ε * n < f x ∧ f x ≤ a + ε * (n + 1)) ∧
    ∀ n : Fin N, MeasurableSet (E n) := by
  let b := a + N * ε
  let y : Fin N → ℝ := fun n ↦ a + ε * (n + 1)
  -- By definition `y n` and `y m` are separated by at least `ε`.
  have hy {n m : Fin N} (h : n < m) : y n + ε ≤ y m := calc
    _ ≤ a + ε * m + ε := by
      exact add_le_add_three (by rfl) ((mul_le_mul_iff_of_pos_left hε).mpr (by norm_cast)) (by rfl)
    _ = _ := by dsimp [y]; rw [mul_add, mul_one, add_assoc]
  -- Define `E n` as the inverse image of the interval `(y n - ε, y n]`.
  let E (n : Fin N) := (f ⁻¹' Ioc (y n - ε) (y n)) ∩ (tsupport f)
  use E
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The sets `E n` are a partition of the support of `f`.
    have partition_aux : range f ⊆ ⋃ n, Ioc (y n - ε) (y n) := calc
      _ ⊆ Ioc (a + (0 : ℕ) * ε) (a + N * ε) := by
        intro _ hz
        simpa using Ioo_subset_Ioc_self (hf hz)
      _ ⊆ ⋃ i ∈ Finset.range N, Ioc (a + ↑i * ε) (a + ↑(i + 1) * ε) :=
        Ioc_subset_biUnion_Ioc N (fun n ↦ a + n * ε)
      _ ⊆ _ := by
        intro z
        simp only [Finset.mem_range, mem_iUnion, mem_Ioc, forall_exists_index, and_imp, y]
        refine fun n hn _ _ ↦ ⟨⟨n, hn⟩, ⟨by linarith, by simp_all [mul_comm ε _]⟩⟩
    simp only [E, ← iUnion_inter, ← preimage_iUnion, eq_comm (a := tsupport _), inter_eq_right]
    exact fun x _ ↦ partition_aux (mem_range_self x)
  · -- The sets `E n` are pairwise disjoint.
    intro m _ n _ hmn
    apply Disjoint.preimage
    simp_rw [mem_preimage, mem_Ioc, disjoint_left]
    intro x hx
    rw [mem_ofPred_eq, and_assoc] at hx
    simp_rw [mem_ofPred_eq, not_and_or, not_lt, not_le, or_assoc]
    rcases (by lia : m < n ∨ n < m) with hc | hc
    · left
      exact le_trans hx.2.1 (le_tsub_of_add_le_right (hy hc))
    · right; left
      exact lt_of_le_of_lt (le_tsub_of_add_le_right (hy hc)) hx.1
  · -- Upper and lower bound on `f x` follow from the definition of `E n` .
    intro _ _ hx
    simp only [mem_inter_iff, mem_preimage, mem_Ioc, E, y] at hx
    constructor <;> linarith
  · exact fun _ ↦ (f.1.measurable measurableSet_Ioc).inter measurableSet_closure

omit [LocallyCompactSpace X] in
/-- Given a set `E`, a function `f : C_c(X, ℝ)`, `0 < ε` and `∀ x ∈ E, f x < c`, there exists an
open set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V, f x < c`. -/
/-
**RealRMK.exists_open_approx** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
形式化陈述：exists_open_approx (f : C_c(X, Real)) {ε : Real} (hε : 0 < ε) (E : Set X) 
{μ : Content X} (hμ : μ.outerMeasure E != ∞) (hμ' : MeasurableSet E) {c : Real} 
(hfE : forall x in E, f x < c) : exists (V : Opens X), E subseteq V ∧ (forall x 
in V, f x < c) ∧ μ.measure V <= μ.measure E + ENNReal.ofReal ε
参数：f : C_c(X, Real)；hε : 0 < ε；E : Set X；hμ : μ.outerMeasure E != ∞；hμ' : Measur
ableSet E；hfE : forall x in E, f x < c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `MeasureTheory.Content.outerMeasure_exists_open`：outerMeasure_exists_open
 {A : Set G} (hA : μ.outerMeasure A != ∞) {ε : Real>=0} (hε : ε != 0) : exists U
 : Opens G, A subseteq U ∧ μ.outerMe…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Content.measure_apply`：measure_apply {s : Set G} (hs : Mea
surableSet s) : μ.measure s = μ.outerMeasure s
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofNNReal_toNNReal`：ofNNReal_toNNReal (x : Real) : (Real.toNNReal
 x : Real>=0∞) = ENNReal.ofReal x

--- 原说明 ---
Given a set `E`, a function `f : C_c(X, ℝ)`, `0 < ε` and `∀ x ∈ E, f x < c`, the
re exists an
open set `V` such that `E ⊆ V` and the sets are similar in measure and `∀ x ∈ V,
 f x < c`.
-/
lemma exists_open_approx (f : C_c(X, ℝ)) {ε : ℝ} (hε : 0 < ε) (E : Set X) {μ : Content X}
    (hμ : μ.outerMeasure E ≠ ∞) (hμ' : MeasurableSet E) {c : ℝ} (hfE : ∀ x ∈ E, f x < c) :
    ∃ (V : Opens X), E ⊆ V ∧ (∀ x ∈ V, f x < c) ∧ μ.measure V ≤ μ.measure E + ENNReal.ofReal ε := by
  have hε' := ne_of_gt <| Real.toNNReal_pos.mpr hε
  obtain ⟨V₁ : Opens X, hV₁⟩ := Content.outerMeasure_exists_open μ hμ hε'
  let V₂ : Opens X := ⟨(f ⁻¹' Iio c), IsOpen.preimage f.1.2 isOpen_Iio⟩
  use V₁ ⊓ V₂
  refine ⟨subset_inter hV₁.1 hfE, ?_, ?_⟩
  · intro x hx
    suffices ∀ x ∈ V₂.carrier, f x < c from this x (mem_of_mem_inter_right hx)
    exact fun _ a ↦ a
  · calc
      _ ≤ μ.measure V₁ := by simp [measure_mono]
      _ = μ.outerMeasure V₁ := Content.measure_apply μ (V₁.2.measurableSet)
      _ ≤ μ.outerMeasure E + ε.toNNReal := hV₁.2
      _ = _ := by rw [Content.measure_apply μ hμ', ENNReal.ofNNReal_toNNReal]

/-- Choose `N` sufficiently large such that a particular quantity is small. -/
/-
**RealRMK.exists_nat_large** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choose `N` sufficiently large such that a particular quantity is small.
-/
private lemma exists_nat_large (a' b' : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ (N : ℕ), 0 < N ∧
    a' / N * (b' + a' / N) ≤ ε := by
  have A : Tendsto (fun (N : ℝ) ↦ a' / N * (b' + a' / N)) atTop (𝓝 (0 * (b' + 0))) := by
    apply Tendsto.mul
    · exact Tendsto.div_atTop tendsto_const_nhds tendsto_id
    · exact Tendsto.add tendsto_const_nhds (Tendsto.div_atTop tendsto_const_nhds tendsto_id)
  have B := A.comp tendsto_natCast_atTop_atTop
  simp only [add_zero, zero_mul] at B
  obtain ⟨N, hN, h'N⟩ := (((tendsto_order.1 B).2 _ hε).and (Ici_mem_atTop 1)).exists
  exact ⟨N, h'N, hN.le⟩

set_option backward.isDefEq.respectTransparency false in
/-- The main estimate in the proof of the Riesz-Markov-Kakutani: `Λ f` is bounded above by the
integral of `f` with respect to the `rieszMeasure` associated to `Λ`. -/
/-
**RealRMK.integral_riesz_aux** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The main estimate in the proof of the Riesz-Markov-Kakutani: `Λ f` is bounded ab
ove by the
integral of `f` with respect to the `rieszMeasure` associated to `Λ`.
-/
private lemma integral_riesz_aux (f : C_c(X, ℝ)) : Λ f ≤ ∫ x, f x ∂(rieszMeasure Λ) := by
  let μ := rieszMeasure Λ
  let K := tsupport f
  -- Suffices to show that `Λ f ≤ ∫ x, f x ∂μ + ε` for arbitrary `ε`.
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  -- Choose an interval `(a, b)` which contains the range of `f`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, a < b ∧ range f ⊆ Ioo a b := by
    obtain ⟨r, hr⟩ := (Metric.isCompact_iff_isClosed_bounded.mp
      (HasCompactSupport.isCompact_range f.2 f.1.2)).2.subset_ball_lt 0 0
    exact ⟨-r, r, by linarith, hr.2.trans_eq (by simp [Real.ball_eq_Ioo])⟩
  -- Choose `N` positive and sufficiently large such that `ε'` is sufficiently small
  obtain ⟨N, hN, hε'⟩ := exists_nat_large (b - a) (2 * μ.real K + |a| + b) hε
  let ε' := (b - a) / N
  replace hε' : 0 < ε' ∧ ε' * (2 * μ.real K + |a| + b + ε') ≤ ε :=
    ⟨div_pos (sub_pos.mpr hab.1) (Nat.cast_pos'.mpr hN), hε'⟩
  -- Take a partition of the support of `f` into sets `E` by partitioning the range.
  obtain ⟨E, hE⟩ := range_cut_partition f a hε'.1 N <| by
    dsimp [ε']
    field_simp
    simp [hab.2]
  -- Introduce notation for the partition of the range.
  let y : Fin N → ℝ := fun n ↦ a + ε' * (n + 1)
  -- The measure of each `E n` is finite.
  have hE' (n : Fin N) : μ (E n) ≠ ∞ := by
    have h : E n ⊆ tsupport f := by rw [hE.1]; exact subset_iUnion _ _
    refine lt_top_iff_ne_top.mp ?_
    apply lt_of_le_of_lt <| measure_mono h
    dsimp [μ]
    rw [rieszMeasure, ← coe_toContinuousMap, ← ContinuousMap.toFun_eq_coe,
      Content.measure_apply _ f.2.measurableSet]
    exact Content.outerMeasure_lt_top_of_isCompact _ f.2
  -- Define sets `V` which are open approximations to the sets `E`
  obtain ⟨V, hV⟩ : ∃ V : Fin N → Opens X, ∀ n, E n ⊆ (V n) ∧ (∀ x ∈ V n, f x < y n + ε') ∧
      μ (V n) ≤ μ (E n) + ENNReal.ofReal (ε' / N) := by
    have h_ε' := (div_pos hε'.1 (Nat.cast_pos'.mpr hN))
    have h n x (hx : x ∈ E n) := lt_add_of_le_of_pos ((hE.2.2.1 n x hx).right) hε'.1
    have h' n := Eq.trans_ne
      (Content.measure_apply (rieszContent (toNNRealLinear Λ)) (hE.2.2.2 n)).symm (hE' n)
    choose V hV using fun n ↦ exists_open_approx f h_ε' (E n) (h' n) (hE.2.2.2 n) (h n)
    exact ⟨V, hV⟩
  -- Define a partition of unity subordinated to the sets `V`
  obtain ⟨g, hg⟩ : ∃ g : Fin N → C_c(X, ℝ), (∀ n, tsupport (g n) ⊆ (V n).carrier) ∧
      EqOn (∑ n : Fin N, (g n)) 1 (tsupport f.toFun) ∧ (∀ n x, (g n) x ∈ Icc 0 1) ∧
      ∀ n, HasCompactSupport (g n) := by
    have : tsupport f ⊆ ⋃ n, (V n).carrier := calc
      _ = ⋃ j, E j := hE.1
      _ ⊆ _ := by gcongr with n; exact (hV n).1
    obtain ⟨g', hg⟩ := exists_continuous_sum_one_of_isOpen_isCompact (fun n ↦ (V n).2) f.2 this
    exact ⟨fun n ↦ ⟨g' n, hg.2.2.2 n⟩, hg⟩
  -- The proof is completed by a chain of inequalities.
  calc Λ f
    _ = Λ (∑ n, g n • f) := ?_
    _ = ∑ n, Λ (g n • f) := by simp
    _ ≤ ∑ n, Λ ((y n + ε') • g n) := ?_
    _ = ∑ n, (y n + ε') * Λ (g n) := by simp
    -- That `y n + ε'` can be negative is bad in the inequalities so we artificially include `|a|`.
    _ = ∑ n, (|a| + y n + ε') * Λ (g n) - |a| * ∑ n, Λ (g n) := by
      simp [add_assoc, add_mul |a|, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * ∑ n, Λ (g n) := ?_
    _ ≤ ∑ n, (|a| + y n + ε') * (μ.real (E n) + ε' / N) - |a| * μ.real K := ?_
    _ = ∑ n, (y n - ε') * μ.real (E n) +
      2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + 2 * ε' * μ.real K + ε' / N * ∑ n, (|a| + y n + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + ε' * (2 * μ.real K + |a| + b + ε') := ?_
    _ ≤ ∫ x, f x ∂μ + ε := by simp [hε'.2]
  · -- Equality since `∑ i : Fin N, (g i)` is equal to unity on the support of `f`
    congr; ext x
    simp only [coe_sum, smul_eq_mul, coe_mul, Pi.mul_apply,
      ← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · simp [hg.2.1 hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `f ≤ y n + ε'` on `V n`
    gcongr with n hn
    intro x
    by_cases hx : x ∈ tsupport (g n)
    · rw [smul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right ?_ (hg.2.2.1 n x).1
      exact le_of_lt <| (hV n).2.1 x <| mem_of_subset_of_mem (hg.1 n) hx
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · -- Use that `Λ (g n) ≤ μ (V n)).toReal ≤ μ (E n)).toReal + ε' / N`
    gcongr with n hn
    · calc
        _ ≤ |a| + a := neg_le_iff_add_nonneg'.mp <| neg_abs_le a
        _ ≤ |a| + a + ε' * (n + 1) := (le_add_iff_nonneg_right (|a| + a)).mpr <| Left.mul_nonneg
          (le_of_lt hε'.1) <| Left.add_nonneg (Nat.cast_nonneg' n) (zero_le_one' ℝ)
        _ ≤ _ := by rw [← add_assoc, le_add_iff_nonneg_right]; exact le_of_lt hε'.1
    · calc
        _ ≤ μ.real (V n) := by
          apply (ENNReal.ofReal_le_iff_le_toReal _).mp
          · exact le_rieszMeasure_tsupport_subset Λ (fun x ↦ hg.2.2.1 n x) (hg.1 n)
          · rw [← lt_top_iff_ne_top]
            apply lt_of_le_of_lt (hV n).2.2
            rw [WithTop.add_lt_top]
            exact ⟨WithTop.lt_top_iff_ne_top.mpr (hE' n), ENNReal.ofReal_lt_top⟩
        _ ≤ _ := by
          rw [← ENNReal.toReal_ofReal (div_nonneg (le_of_lt hε'.1) (Nat.cast_nonneg _))]
          apply ENNReal.toReal_le_add (hV n).2.2 (hE' n)
          · finiteness
  · -- Use that `μ K ≤ Λ (∑ n, g n)`
    gcongr
    rw [← map_sum Λ g _]
    have h x : 0 ≤ (∑ n, g n) x := by simpa using Fintype.sum_nonneg fun n ↦ (hg.2.2.1 n x).1
    apply ENNReal.toReal_le_of_le_ofReal
    · exact Λ.map_nonneg (fun x ↦ h x)
    · have h' x (hx : x ∈ K) : (∑ n, g n) x = 1 := by simp [hg.2.1 hx]
      refine rieszMeasure_le_of_eq_one Λ h f.2 h'
  · -- Rearrange the sums
    have (n : Fin N) : (|a| + y n + ε') * μ.real (E n) =
        (|a| + 2 * ε') * μ.real (E n) + (y n - ε') * μ.real (E n) := by linarith
    simp_rw [mul_add, this]
    have : ∑ i, μ.real (E i) = μ.real K := by
      suffices h : μ K = ∑ i, (μ (E i)) by
        simp only [measureReal_def, h]
        exact Eq.symm <| ENNReal.toReal_sum <| fun n _ ↦ hE' n
      dsimp [K]; rw [hE.1]
      rw [measure_iUnion (fun m n hmn ↦ hE.2.1 trivial trivial hmn) hE.2.2.2]
      exact tsum_fintype fun b ↦ μ (E b)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, this, ← Finset.sum_mul]
    linarith
  · -- Use that `y n - ε' ≤ f x` on `E n`
    gcongr
    have h : ∀ n, (y n - ε') * μ.real (E n) ≤ ∫ x in (E n), f x ∂μ := by
      intro n
      apply setIntegral_ge_of_const_le_real (hE.2.2.2 n) (hE' n)
      · intro x hx
        dsimp [y]; linarith [(hE.2.2.1 n x hx).1]
      · apply Integrable.integrableOn
        dsimp [μ, rieszMeasure]
        exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    calc
      _ ≤ ∑ n, ∫ (x : X) in E n, f x ∂μ := Finset.sum_le_sum fun i a ↦ h i
      _ = ∫ x in (⋃ n, E n), f x ∂μ := by
        refine Eq.symm <| integral_iUnion_fintype hE.2.2.2 (fun _ _ ↦ hE.2.1 trivial trivial) ?_
        dsimp [μ, rieszMeasure]
        exact fun _ ↦
          Integrable.integrableOn <| Continuous.integrable_of_hasCompactSupport f.1.2 f.2
      _ = ∫ x in tsupport f, f x ∂μ := by simp_rw [hE.1]
      _ = _ := setIntegral_tsupport
  · -- Rough bound of the sum
    have h : ∑ n : Fin N, y n ≤ N * b := by
      have (n : Fin N) := calc y n
        _ ≤ a + ε' * N := by simp_all [y, show (n : ℝ) + 1 ≤ N by norm_cast; lia]
        _ = b := by simp [field, ε']
      have : ∑ n, y n ≤ ∑ n, b := Finset.sum_le_sum (fun n ↦ fun _ ↦ this n)
      simp_all
    simp only [Finset.sum_add_distrib, Finset.sum_add_distrib,
               Fin.sum_const, Fin.sum_const, nsmul_eq_mul, ← add_assoc, mul_add, ← mul_assoc]
    simpa [show (N : ℝ) ≠ 0 by simp [hN.ne.symm], mul_comm _ ε', div_eq_mul_inv, mul_assoc]
      using (mul_le_mul_iff_of_pos_left hε'.1).mpr <| (inv_mul_le_iff₀ (Nat.cast_pos'.mpr hN)).mpr h

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal to `Λ f`. -/
@[simp]
/-
**RealRMK.integral_rieszMeasure** 是 Mathlib 中的一个定理，位于命名空间 `RealRMK`。
形式化陈述：integral_rieszMeasure (f : C_c(X, Real)) : ∫ x, f x ∂(rieszMeasure Λ) = Λ 
f
参数：f : C_c(X, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `MeasureTheory.integral_neg'`：integral_neg' (f : α -> G) : ∫ a, (-f) a ∂μ
 = -∫ a, f a ∂μ
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real.0.RealR
MK.integral_riesz_aux`：∀ {X : Type u_1} [inst : TopologicalSpace X] [inst_1 : T2
Space X] [inst_2 : MeasurableSpace X] [inst_3 : BorelSpace X]   (Λ : CompactlySu
ppo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **Riesz-Markov-Kakutani representation theorem**: given a positive linear fu
nctional `Λ`,
the integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equa
l to `Λ f`.
-/
theorem integral_rieszMeasure (f : C_c(X, ℝ)) : ∫ x, f x ∂(rieszMeasure Λ) = Λ f := by
  -- We apply the result `Λ f ≤ ∫ x, f x ∂(rieszMeasure hΛ)` to `f` and `-f`.
  apply le_antisymm
  -- prove the inequality for `- f`
  · calc
      _ = - ∫ x, (-f) x ∂(rieszMeasure Λ) := by simpa using integral_neg' (-f)
      _ ≤ - Λ (-f) := neg_le_neg (integral_riesz_aux Λ (-f))
      _ = _ := by simp
  -- prove the inequality for `f`
  · exact integral_riesz_aux Λ f

/-- The Riesz measure induced by a positive linear functional on `C_c(X, ℝ)` is regular. -/
/-
**RealRMK.regular_rieszMeasure** 是 Mathlib 中的一个实例，位于命名空间 `RealRMK`。
形式化陈述：regular_rieszMeasure : (rieszMeasure Λ).Regular
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X

--- 原说明 ---
The Riesz measure induced by a positive linear functional on `C_c(X, ℝ)` is regu
lar.
-/
instance regular_rieszMeasure : (rieszMeasure Λ).Regular :=
  (rieszContent _).regular

end Construction

section integralPositiveLinearMap

variable {μ ν : Measure X} [LocallyCompactSpace X]

/-! We show that `RealRMK.rieszMeasure` is a bijection between positive linear functionals on
`C_c(X, ℝ)` and regular measures with inverse `RealRMK.integralPositiveLinearMap`. -/

/-- Note: the assumption `IsFiniteMeasureOnCompacts μ` cannot be removed. For example, if
`μ` is infinite on any nonempty set and `ν = 0`, then the hypotheses are satisfied. -/
/-
**RealRMK.measure_le_of_isCompact_of_integral** 是 Mathlib 中的一个引理，位于命名空间 `RealRMK
`。
形式化陈述：measure_le_of_isCompact_of_integral [ν.OuterRegular] [IsFiniteMeasureOnCom
pacts ν] [IsFiniteMeasureOnCompacts μ] (hμν : forall f : C_c(X, Real), ∫ x, f x 
∂μ <= ∫ x, f x ∂ν) ⦃K : Set X⦄ (hK : IsCompact K) : μ K <= ν K
参数：hμν : forall f : C_c(X, Real), ∫ x, f x ∂μ <= ∫ x, f x ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `Set.exists_isOpen_le_add`：∀ {α : Type u_1} [inst : MeasurableSpace α] [i
nst_1 : TopologicalSpace α] (A : Set α) (μ : MeasureTheory.Measure α)   [μ.Outer
Regular] {ε : …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.Finiteness.add_ne_top`：∀ {a b : ENNReal}, a ≠ ⊤ → b ≠ ⊤ → a + b 
≠ ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用引理 `exists_continuousMap_one_of_isCompact_subset_isOpen`：exists_continuousMa
p_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCompactSpace X] {K V : Set 
X} (hK : IsCompact K) (hV : IsOpen V) (hK…
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `hasCompactSupport_def`：∀ {α : Type u_2} {β : Type u_4} [inst : Topologic
alSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ IsCompact (clo
sure (Funct…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
Note: the assumption `IsFiniteMeasureOnCompacts μ` cannot be removed. For exampl
e, if
`μ` is infinite on any nonempty set and `ν = 0`, then the hypotheses are satisfi
ed.
-/
lemma measure_le_of_isCompact_of_integral [ν.OuterRegular]
    [IsFiniteMeasureOnCompacts ν] [IsFiniteMeasureOnCompacts μ]
    (hμν : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    ⦃K : Set X⦄ (hK : IsCompact K) : μ K ≤ ν K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
  have hνK : ν K ≠ ⊤ := hν.ne
  have hμK : μ K ≠ ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : ∃ V ⊇ K, IsOpen V ∧ ν V ≤ ν K + ε :=
    exists_isOpen_le_add K ν (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices μ.real K ≤ ν.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  have VltTop : ν V < ⊤ := pV3.trans_lt <| by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      ∃ f : C_c(X, ℝ), Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧ ∀ (x : X), f x ∈ Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : X) : f x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : X) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
    μ.real K = ∫ x, K.indicator 1 x ∂μ := integral_indicator_one hK.measurableSet |>.symm
    _ ≤ ∫ x, f x ∂μ := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ ≤ ∫ x, f x ∂ν := hμν f
    _ ≤ ∫ x, V.indicator 1 x ∂ν := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ ≤ (ν K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

/-- If two regular measures give the same integral for every function in `C_c(X, ℝ)`,
then they are equal. -/
/-
**RealRMK._root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported*
* 是 Mathlib 中的一个定理，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two regular measures give the same integral for every function in `C_c(X, ℝ)`
,
then they are equal.
-/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    [μ.Regular] [ν.Regular] (hμν : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  apply le_antisymm
  · exact measure_le_of_isCompact_of_integral (fun f ↦ (hμν f).le) hK
  · exact measure_le_of_isCompact_of_integral (fun f ↦ (hμν f).ge) hK

/-- Two regular measures are equal iff they induce the same positive linear functional
on `C_c(X, ℝ)`. -/
/-
**RealRMK.integralPositiveLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `RealRMK`。
形式化陈述：integralPositiveLinearMap_inj [μ.Regular] [ν.Regular] : integralPositiveLi
nearMap μ = integralPositiveLinearMap ν ↔ μ = ν where mp hμν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`：∀ {X : T
ype u_1} [inst : TopologicalSpace X] [T2Space X] [inst_2 : MeasurableSpace X] [B
orelSpace X]   {μ ν : MeasureTheory.Measure X} [Loca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Two regular measures are equal iff they induce the same positive linear function
al
on `C_c(X, ℝ)`.
-/
theorem integralPositiveLinearMap_inj [μ.Regular] [ν.Regular] :
    integralPositiveLinearMap μ = integralPositiveLinearMap ν ↔ μ = ν where
  mp hμν := Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ congr($hμν f)
  mpr _ := by congr

/-- Every regular measure is induced by a positive linear functional on `C_c(X, ℝ)`.
That is, `RealRMK.rieszMeasure` is a surjective function onto regular measures. -/
@[simp]
/-
**RealRMK.rieszMeasure_integralPositiveLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Real
RMK`。
形式化陈述：rieszMeasure_integralPositiveLinearMap [μ.Regular] : rieszMeasure (integra
lPositiveLinearMap μ) = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`：∀ {X : T
ype u_1} [inst : TopologicalSpace X] [T2Space X] [inst_2 : MeasurableSpace X] [B
orelSpace X]   {μ ν : MeasureTheory.Measure X} [Loca…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `RealRMK.integral_rieszMeasure`：integral_rieszMeasure (f : C_c(X, Real)) 
: ∫ x, f x ∂(rieszMeasure Λ) = Λ f
· 使用定理 `CompactlySupportedContinuousMap.integralPositiveLinearMap_apply`：∀ {X : 
Type u_1} [inst : TopologicalSpace X] [inst_1 : MeasurableSpace X] [inst_2 : Ope
nsMeasurableSpace X]   (μ : MeasureTheory.Measure X) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Every regular measure is induced by a positive linear functional on `C_c(X, ℝ)`.
That is, `RealRMK.rieszMeasure` is a surjective function onto regular measures.
-/
theorem rieszMeasure_integralPositiveLinearMap [μ.Regular] :
    rieszMeasure (integralPositiveLinearMap μ) = μ :=
  Measure.ext_of_integral_eq_on_compactlySupported (by simp)

@[simp]
/-
**RealRMK.integralPositiveLinearMap_rieszMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Real
RMK`。
形式化陈述：integralPositiveLinearMap_rieszMeasure : integralPositiveLinearMap (rieszM
easure Λ) = Λ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `PositiveLinearMap.ext`：ext {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x
) : f = g
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompactlySupportedContinuousMap.integralPositiveLinearMap_apply`：∀ {X : 
Type u_1} [inst : TopologicalSpace X] [inst_1 : MeasurableSpace X] [inst_2 : Ope
nsMeasurableSpace X]   (μ : MeasureTheory.Measure X) …
· 使用定理 `RealRMK.integral_rieszMeasure`：integral_rieszMeasure (f : C_c(X, Real)) 
: ∫ x, f x ∂(rieszMeasure Λ) = Λ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralPositiveLinearMap_rieszMeasure :
    integralPositiveLinearMap (rieszMeasure Λ) = Λ := by ext; simp

end integralPositiveLinearMap

section Compact

/-
**RealRMK.** 是 Mathlib 中的一个实例，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompactSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) : IsFiniteMeasure (rieszMeasure Λ) := by
  constructor
  let o : C_c(X, ℝ) := ⟨1, HasCompactSupport.of_compactSpace 1⟩
  calc rieszMeasure Λ univ
  _ ≤ ENNReal.ofReal (Λ o) :=
    rieszMeasure_le_of_eq_one _ (fun x ↦ zero_le_one) isCompact_univ (fun x hx ↦ rfl)
  _ < ⊤ := by simp

/-- Given a finite measure on a compact space, there exists another finite measure which
integrates in the same way bounded continuous functions, and is regular. -/
/-
**RealRMK._root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace** 是 Mat
hlib 中的一个引理，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite measure on a compact space, there exists another finite measure w
hich
integrates in the same way bounded continuous functions, and is regular.
-/
lemma _root_.MeasureTheory.Measure.exists_regular_eq_of_compactSpace [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∃ (ν : Measure X), ν.Regular ∧ IsFiniteMeasure ν ∧
      ∀ g : X →ᵇ ℝ, ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := ∫ x, g x ∂μ
    map_add' g g' := integral_add g.integrable g'.integrable
    map_smul' c g := integral_smul c g
    monotone' g g' hgg' := integral_mono g.integrable g'.integrable hgg' }
  refine ⟨RealRMK.rieszMeasure Λ, by infer_instance, by infer_instance, fun g ↦ ?_⟩
  let g' : C_c(X, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  exact (integral_rieszMeasure Λ g').symm

/-- Given a finite measure supported on a compact set, there exists another finite measure which
integrates in the same way bounded continuous functions, and is regular. -/
/-
**RealRMK._root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact** 是 M
athlib 中的一个引理，位于命名空间 `RealRMK`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite measure supported on a compact set, there exists another finite m
easure which
integrates in the same way bounded continuous functions, and is regular.
-/
lemma _root_.MeasureTheory.Measure.exists_innerRegular_eq_of_isCompact
    (μ : Measure X) [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K) (h : μ Kᶜ = 0) :
    ∃ (ν : Measure X), ν.InnerRegular ∧ IsFiniteMeasure ν ∧ ν Kᶜ = 0 ∧
      ∀ g : X →ᵇ ℝ, ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  let μ' : Measure K := μ.comap Subtype.val
  obtain ⟨ν', ν'_reg, ν'_fin, hν'⟩ : ∃ (ν : Measure K), ν.Regular ∧ IsFiniteMeasure ν ∧
      ∀ g : K →ᵇ ℝ, ∫ x, g x ∂μ' = ∫ x, g x ∂ν := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact Measure.exists_regular_eq_of_compactSpace μ'
  refine ⟨ν'.map Subtype.val, Measure.InnerRegular.map_of_continuous (by fun_prop),
    by infer_instance, ?_, fun g ↦ ?_⟩
  · rw [Measure.map_apply (by fun_prop) hK.measurableSet.compl]
    simp
  convert! hν' (g.compContinuous ⟨Subtype.val, by fun_prop⟩)
  · simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [← integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp only [map_comap_subtype_coe hK.measurableSet, μ', Measure.restrict_eq_self_of_ae_mem h]
  · rw [integral_map (φ := Subtype.val) (by fun_prop) (by fun_prop)]
    simp

end Compact

end RealRMK

