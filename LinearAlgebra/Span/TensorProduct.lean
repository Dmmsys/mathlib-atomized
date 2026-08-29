/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# The interaction of linear span and tensor product for mixed scalars.
-/

@[expose] public section

open Function TensorProduct

namespace Submodule

variable {R : Type*} (A : Type*) {M : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M)

/--
Definition of `tensorToSpan` / `tensorToSpan` 的定义

English:
definition tensorToSpan
  signature: : A otimes[R] p ->ₗ[A] span A (p : Set M)
  body: AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }

中文:
定义 tensorToSpan
  签名: : A otimes[R] p ->ₗ[A] span A (p : 集合 M)
  定义体: AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, add_smul, inclusionSpan, map_add, map_smul, p.inclusionSpan, smul_assoc
-/
def tensorToSpan : A otimes[R] p ->ₗ[A] span A (p : Set M) :=
  AlgebraTensorModule.lift
    { toFun a := a • p.inclusionSpan A
      map_add' a b := add_smul a b _
      map_smul' a b := smul_assoc a b _ }

/--
lemma `tensorToSpan_apply_tmul` / 引理 `tensorToSpan_apply_tmul`

English:
lemma tensorToSpan_apply_tmul
  given: (a : A) (x : p)
  proof: rfl

中文:
引理 tensorToSpan_apply_tmul
  条件: (a : A) (x : p)
  证明: rfl
-/
@[simp] lemma tensorToSpan_apply_tmul (a : A) (x : p) :
    p.tensorToSpan A (a otimesₜ x) = a • (x : M) :=
  rfl

/--
lemma `surjective_tensorToSpan` / 引理 `surjective_tensorToSpan`

English:
lemma surjective_tensorToSpan
  statement: Surjective (p.tensorToSpan A)
  proof: by
  intro v
  obtain ⟨f, hf⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp v.property
  use f.sum fun x a => a otimesₜ x
  rw [map_finsuppSum]; rw [Subtype.ext_iff]; rw [← Submodule.subtype_apply]; rw [map_finsuppSum]
  simpa using! hf

中文:
引理 surjective_tensorToSpan
  结论: 满射 (p.tensorToSpan A)
  证明: by
  intro v
  obtain ⟨f, hf⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp v.property
  use f.sum fun x a => a otimesₜ x
  rw [map_finsuppSum]; rw [Subtype.ext_iff]; rw [← Submodule.subtype_apply]; rw [map_finsuppSum]
  simpa using! hf

Depends on / 依赖: Finsupp, Finsupp.mem_span_iff_linearCombination, Submodule, Submodule.subtype_apply, Subtype, Subtype.ext_iff, ext_iff, f.sum, map_finsuppSum, mem_span_iff_linearCombination, property, subtype_apply, v.property
-/
lemma surjective_tensorToSpan : Surjective (p.tensorToSpan A) := by
  intro v
  obtain ⟨f, hf⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp v.property
  use f.sum fun x a => a otimesₜ x
  rw [map_finsuppSum]; rw [Subtype.ext_iff]; rw [← Submodule.subtype_apply]; rw [map_finsuppSum]
  simpa using! hf

variable [Algebra.IsEpi R A] [Module.Flat R A]

open Module.Flat LinearMap in
/--
lemma `injective_tensorToSpan` / 引理 `injective_tensorToSpan`

English:
lemma injective_tensorToSpan
  statement: Injective (p.tensorToSpan A)
  proof: by
  let f : A otimes[R] (span A (p : Set M)) ->ₗ[A] span A (p : Set M) :=
AlgebraTensorModule.lift (restrictScalarsₗ R A _ _ A) ∘ₗ lsmul A (span A (p : Set M))
  let g : A otimes[R] p ->ₗ[R] A otimes[R] span A (p : Set M) := (p.inclusionSpan A).lTensor A
  have hf : Injective f := Algebra.injective_lift_lsmul R A _
  have hg : Injective g := lTensor_preserves_injective_linearMap _ (p.injective_inclusionSpan A)
  have : p.tensorToSpan A = f.restrictScalars R ∘ₗ g := by ext; simp [tensorToSpan, f, g]
  rw [← LinearMap.coe_restrictScalars R]; rw [this]; rw [coe_comp]
  exact hf.comp hg

中文:
引理 injective_tensorToSpan
  结论: 单射 (p.tensorToSpan A)
  证明: by
  let f : A otimes[R] (span A (p : Set M)) ->ₗ[A] span A (p : Set M) :=
AlgebraTensorModule.lift (restrictScalarsₗ R A _ _ A) ∘ₗ lsmul A (span A (p : Set M))
  let g : A otimes[R] p ->ₗ[R] A otimes[R] span A (p : Set M) := (p.inclusionSpan A).lTensor A
  have hf : Injective f := Algebra.injective_lift_lsmul R A _
  have hg : Injective g := lTensor_preserves_injective_linearMap _ (p.injective_inclusionSpan A)
  have : p.tensorToSpan A = f.restrictScalars R ∘ₗ g := by ext; simp [tensorToSpan, f, g]
  rw [← LinearMap.coe_restrictScalars R]; rw [this]; rw [coe_comp]
  exact hf.comp hg

Depends on / 依赖: Algebra, Algebra.injective_lift_lsmul, AlgebraTensorModule, AlgebraTensorModule.lift, Injective, f.restrictScalars, inclusionSpan, injective_inclusionSpan, injective_lift_lsmul, lTensor, lTensor_preserves_injective_linearMap, otimes, p.inclusionSpan, p.injective_inclusionSpan, p.tensorToSpan, restrictScalars, tensorToSpan
-/
lemma injective_tensorToSpan : Injective (p.tensorToSpan A) := by
  let f : A otimes[R] (span A (p : Set M)) ->ₗ[A] span A (p : Set M) :=
AlgebraTensorModule.lift (restrictScalarsₗ R A _ _ A) ∘ₗ lsmul A (span A (p : Set M))
  let g : A otimes[R] p ->ₗ[R] A otimes[R] span A (p : Set M) := (p.inclusionSpan A).lTensor A
  have hf : Injective f := Algebra.injective_lift_lsmul R A _
  have hg : Injective g := lTensor_preserves_injective_linearMap _ (p.injective_inclusionSpan A)
  have : p.tensorToSpan A = f.restrictScalars R ∘ₗ g := by ext; simp [tensorToSpan, f, g]
  rw [← LinearMap.coe_restrictScalars R]; rw [this]; rw [coe_comp]
  exact hf.comp hg

/--
Definition of `tensorEquivSpan` / `tensorEquivSpan` 的定义

English:
definition tensorEquivSpan
  signature: : A otimes[R] p ≃ₗ[A] span A (p : Set M)
  body: .ofBijective (p.tensorToSpan A) ⟨p.injective_tensorToSpan A, p.surjective_tensorToSpan A⟩

中文:
定义 tensorEquivSpan
  签名: : A otimes[R] p ≃ₗ[A] span A (p : 集合 M)
  定义体: .ofBijective (p.tensorToSpan A) ⟨p.injective_tensorToSpan A, p.surjective_tensorToSpan A⟩

Depends on / 依赖: injective_tensorToSpan, ofBijective, p.injective_tensorToSpan, p.surjective_tensorToSpan, p.tensorToSpan, surjective_tensorToSpan, tensorToSpan
-/
noncomputable def tensorEquivSpan : A otimes[R] p ≃ₗ[A] span A (p : Set M) :=
  .ofBijective (p.tensorToSpan A) ⟨p.injective_tensorToSpan A, p.surjective_tensorToSpan A⟩

/--
lemma `tensorEquivSpan_apply_tmul` / 引理 `tensorEquivSpan_apply_tmul`

English:
lemma tensorEquivSpan_apply_tmul
  given: (a : A) (x : p)
  proof: rfl

中文:
引理 tensorEquivSpan_apply_tmul
  条件: (a : A) (x : p)
  证明: rfl
-/
@[simp] lemma tensorEquivSpan_apply_tmul (a : A) (x : p) :
    p.tensorEquivSpan A (a otimesₜ x) = a • (x : M) :=
  rfl

variable (R) in
/--
Definition of `tensorSpanEquivSpan` / `tensorSpanEquivSpan` 的定义

English:
definition tensorSpanEquivSpan
  signature: (s : Set M)
  body: ((span R s).tensorEquivSpan A).trans .ofEq _ _ span_span_of_tower R A s

中文:
定义 tensorSpanEquivSpan
  签名: (s : 集合 M)
  定义体: ((span R s).tensorEquivSpan A).trans .ofEq _ _ span_span_of_tower R A s

Depends on / 依赖: span_span_of_tower, tensorEquivSpan
-/
noncomputable def tensorSpanEquivSpan (s : Set M) : A otimes[R] span R s ≃ₗ[A] span A s :=
((span R s).tensorEquivSpan A).trans .ofEq _ _ span_span_of_tower R A s

/--
lemma `coe_tensorSpanEquivSpan_apply_tmul` / 引理 `coe_tensorSpanEquivSpan_apply_tmul`

English:
lemma coe_tensorSpanEquivSpan_apply_tmul
  given: {s : Set M} (a : A) (x : span R s)
  proof: rfl

中文:
引理 coe_tensorSpanEquivSpan_apply_tmul
  条件: {s : 集合 M} (a : A) (x : span R s)
  证明: rfl
-/
@[simp] lemma coe_tensorSpanEquivSpan_apply_tmul {s : Set M} (a : A) (x : span R s) :
    tensorSpanEquivSpan R A s (a otimesₜ x) = a • (x : M) :=
  rfl

end CommSemiring

section CommRing

open Module

variable [CommRing R] [CommRing A] [Nontrivial A]
  [Algebra R A] [Algebra.IsEpi R A] [Module.Flat R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (p : Submodule R M) [Free R p] [Module.Finite R p]

/--
lemma `finrank_span_eq_finrank` / 引理 `finrank_span_eq_finrank`

English:
lemma finrank_span_eq_finrank
  proof: by
  rcases subsingleton_or_nontrivial R; · simp [Algebra.subsingleton R A]
  let ι := Free.ChooseBasisIndex R p
  let b₁ : Basis ι R p := Free.chooseBasis R p
let b₂ : Basis ι A (span A (p : Set M)) := (b₁.baseChange A).map p.tensorEquivSpan A
  rw [finrank_eq_card_basis b₁]; rw [finrank_eq_card_basis b₂]

中文:
引理 finrank_span_eq_finrank
  证明: by
  rcases subsingleton_or_nontrivial R; · simp [Algebra.subsingleton R A]
  let ι := Free.ChooseBasisIndex R p
  let b₁ : Basis ι R p := Free.chooseBasis R p
let b₂ : Basis ι A (span A (p : Set M)) := (b₁.baseChange A).map p.tensorEquivSpan A
  rw [finrank_eq_card_basis b₁]; rw [finrank_eq_card_basis b₂]
-/
@[simp] lemma finrank_span_eq_finrank :
    finrank A (span A (p : Set M)) = finrank R p := by
  rcases subsingleton_or_nontrivial R; · simp [Algebra.subsingleton R A]
  let ι := Free.ChooseBasisIndex R p
  let b₁ : Basis ι R p := Free.chooseBasis R p
let b₂ : Basis ι A (span A (p : Set M)) := (b₁.baseChange A).map p.tensorEquivSpan A
  rw [finrank_eq_card_basis b₁]; rw [finrank_eq_card_basis b₂]

variable (R) in
/--
lemma `finrank_span_eq_finrank_span` / 引理 `finrank_span_eq_finrank_span`

English:
lemma finrank_span_eq_finrank_span
  statement: [IsPrincipalIdealRing R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  rw [← span_span_of_tower R]; rw [finrank_span_eq_finrank]

中文:
引理 finrank_span_eq_finrank_span
  结论: [是主理想环 R] [是整环 R] [是无挠 R M]
  证明: by
  rw [← span_span_of_tower R]; rw [finrank_span_eq_finrank]

Depends on / 依赖: finrank_span_eq_finrank, span_span_of_tower
-/
lemma finrank_span_eq_finrank_span [IsPrincipalIdealRing R] [IsDomain R] [IsTorsionFree R M]
    (s : Set M) [Module.Finite R (span R s)] :
    finrank A (span A s) = finrank R (span R s) := by
  rw [← span_span_of_tower R]; rw [finrank_span_eq_finrank]

end CommRing

end Submodule
