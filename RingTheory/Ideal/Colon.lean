/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The colon ideal

This file defines `Submodule.colon N P` as the ideal of all elements `r : R` such that `r • P ⊆ N`.
The normal notation for this would be `N : P` which has already been taken by type theory.

-/

@[expose] public section

namespace Submodule

open scoped Pointwise

variable {R M : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {N N₁ N₂ : Submodule R M} {S S₁ S₂ : Set M}

/--
Definition of `colon` / `colon` 的定义

English:
definition colon
  signature: (N : Submodule R M) (S : Set M)
  body: {r : R | (r • S : Set M) subseteq N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_

中文:
定义 colon
  签名: (N : 子模 R M) (S : 集合 M)
  定义体: {r : R | (r • S : Set M) subseteq N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_

Depends on / 依赖: SecondCountableTopology, SecondCountableTopology.to_firstCountableTopology, subseteq, to_firstCountableTopology
-/
def colon (N : Submodule R M) (S : Set M) : Ideal R where
  carrier := {r : R | (r • S : Set M) subseteq N}
  add_mem' ha hb :=
    (Set.add_smul_subset _ _ _).trans ((Set.add_subset_add ha hb).trans_eq (by simp))
  zero_mem' := (Set.zero_smul_set_subset S).trans (by simp)
  smul_mem' r := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, mul_smul, Set.smul_set_subset_iff]
    intro x hx y hy
    exact N.smul_mem _ (hx hy)

/--
theorem `mem_colon` / 定理 `mem_colon`

English:
theorem mem_colon
  given: {r}
  statement: r in N.colon S ↔ forall s in S, r • s in N
  proof: Set.smul_set_subset_iff

@[simp]

中文:
定理 mem_colon
  条件: {r}
  结论: r in N.colon S ↔ 对任意 s in S, r • s in N
  证明: Set.smul_set_subset_iff

@[simp]

Depends on / 依赖: Countable, FirstCountableTopology, Set.smul_set_subset_iff, smul_set_subset_iff
-/
theorem mem_colon {r} : r in N.colon S ↔ forall s in S, r • s in N := Set.smul_set_subset_iff

@[simp]
/--
theorem `mem_colon_singleton` / 定理 `mem_colon_singleton`

English:
theorem mem_colon_singleton
  given: {x : M} {r : R}
  statement: r in N.colon {x} ↔ r • x in N
  proof: by
  simp [mem_colon, forall_eq]

中文:
定理 mem_colon_singleton
  条件: {x : M} {r : R}
  结论: r in N.colon {x} ↔ r • x in N
  证明: by
  simp [mem_colon, forall_eq]

Depends on / 依赖: forall_eq, mem_colon
-/
theorem mem_colon_singleton {x : M} {r : R} : r in N.colon {x} ↔ r • x in N := by
  simp [mem_colon, forall_eq]

instance (priority := low) (P : Submodule R M) : (N.colon (P : Set M)).IsTwoSided where
  mul_mem_of_left {r} s hr p hp := by
    obtain ⟨p, hp, rfl⟩ := hp
    exact hr ⟨_, P.smul_mem _ hp, (mul_smul ..).symm⟩

@[simp]
/--
theorem `colon_univ` / 定理 `colon_univ`

English:
theorem colon_univ
  given: {I : Ideal R} [I.IsTwoSided]
  statement: I.colon Set.univ = I
  proof: by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x => ⟨fun h => mul_one x ▸ h 1 trivial, fun h _ _ => I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]

中文:
定理 colon_univ
  条件: {I : 理想 R} [I.是TwoSided]
  结论: I.colon 集合.univ = I
  证明: by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x => ⟨fun h => mul_one x ▸ h 1 trivial, fun h _ _ => I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]

Depends on / 依赖: I.mul_mem_right, SetLike, SetLike.ext_iff, ext_iff, mem_colon, mul_mem_right, mul_one, simp_rw, smul_eq_mul
-/
theorem colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon Set.univ = I := by
  simp_rw [SetLike.ext_iff, mem_colon, smul_eq_mul]
  exact fun x => ⟨fun h => mul_one x ▸ h 1 trivial, fun h _ _ => I.mul_mem_right _ h⟩

@[deprecated (since := "2026-01-11")] alias colon_top := colon_univ

@[simp]
/--
theorem `bot_colon` / 定理 `bot_colon`

English:
theorem bot_colon
  statement: colon (⊥ : Submodule R M) (N : Set M) = N.annihilator
  proof: by
  ext x
  simp [mem_colon, mem_annihilator]

中文:
定理 bot_colon
  结论: colon (⊥ : 子模 R M) (N : 集合 M) = N.annihilator
  证明: by
  ext x
  simp [mem_colon, mem_annihilator]

Depends on / 依赖: mem_annihilator, mem_colon
-/
theorem bot_colon : colon (⊥ : Submodule R M) (N : Set M) = N.annihilator := by
  ext x
  simp [mem_colon, mem_annihilator]

/--
theorem `colon_mono` / 定理 `colon_mono`

English:
theorem colon_mono
  given: (hn : N₁ <= N₂) (hs : S₁ subseteq S₂)
  statement: N₁.colon S₂ <= N₂.colon S₁
  proof: fun _ hrns => mem_colon.mpr fun s₁ hs₁ => hn mem_colon.mp hrns s₁ hs hs₁

中文:
定理 colon_mono
  条件: (hn : N₁ <= N₂) (hs : S₁ subseteq S₂)
  结论: N₁.colon S₂ <= N₂.colon S₁
  证明: fun _ hrns => mem_colon.mpr fun s₁ hs₁ => hn mem_colon.mp hrns s₁ hs hs₁

Depends on / 依赖: countable_countableBasis, image2, isBasis_countableBasis, mem_colon, mem_colon.mp, mem_colon.mpr, secondCountableTopology
-/
theorem colon_mono (hn : N₁ <= N₂) (hs : S₁ subseteq S₂) : N₁.colon S₂ <= N₂.colon S₁ :=
fun _ hrns => mem_colon.mpr fun s₁ hs₁ => hn mem_colon.mp hrns s₁ hs hs₁

/--
theorem `_root_.Ideal.le_colon` / 定理 `_root_.Ideal.le_colon`

English:
theorem _root_.Ideal.le_colon
  given: {I : Ideal R} {S : Set R} [I.IsTwoSided]
  statement: I <= I.colon S
  proof: colon_univ.symm.trans_le (colon_mono le_rfl S.subset_univ)

中文:
定理 _root_.理想.le_colon
  条件: {I : 理想 R} {S : 集合 R} [I.是TwoSided]
  结论: I <= I.colon S
  证明: colon_univ.symm.trans_le (colon_mono le_rfl S.subset_univ)

Depends on / 依赖: S.subset_univ, colon_mono, colon_univ, colon_univ.symm.trans_le, le_rfl, secondCountableTopology_iInf, secondCountableTopology_induced, subset_univ, trans_le
-/
theorem _root_.Ideal.le_colon {I : Ideal R} {S : Set R} [I.IsTwoSided] : I <= I.colon S :=
  colon_univ.symm.trans_le (colon_mono le_rfl S.subset_univ)

/--
theorem `iInf_colon_iUnion` / 定理 `iInf_colon_iUnion`

English:
theorem iInf_colon_iUnion
  given: (ι₁ : Sort*) (f : ι₁ -> Submodule R M) (ι₂ : Sort*) (g : ι₂ -> Set M)
  proof: by
  aesop (add simp mem_colon)

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

中文:
定理 iInf_colon_iUnion
  条件: (ι₁ : 类型层*) (f : ι₁ -> 子模 R M) (ι₂ : 类型层*) (g : ι₂ -> 集合 M)
  证明: by
  aesop (add simp mem_colon)

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

Depends on / 依赖: SecondCountableTopology, SecondCountableTopology.to_separableSpace, mem_colon, to_separableSpace
-/
theorem iInf_colon_iUnion (ι₁ : Sort*) (f : ι₁ -> Submodule R M) (ι₂ : Sort*) (g : ι₂ -> Set M) :
    (⨅ i, f i).colon (⋃ j, g j) = ⨅ (i) (j), (f i).colon (g j) := by
  aesop (add simp mem_colon)

@[deprecated (since := "2026-01-11")] alias iInf_colon_iSup := iInf_colon_iUnion

/--
lemma `colon_inf_eq_left_of_subset` / 引理 `colon_inf_eq_left_of_subset`

English:
lemma colon_inf_eq_left_of_subset
  given: (h : S subseteq (N₂ : Set M))
  statement: (N₁ ⊓ N₂).colon S = N₁.colon S
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 colon_inf_eq_left_of_subset
  条件: (h : S subseteq (N₂ : 集合 M))
  结论: (N₁ ⊓ N₂).colon S = N₁.colon S
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma colon_inf_eq_left_of_subset (h : S subseteq (N₂ : Set M)) : (N₁ ⊓ N₂).colon S = N₁.colon S := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `colon_eq_top_iff_subset` / 引理 `colon_eq_top_iff_subset`

English:
lemma colon_eq_top_iff_subset
  given: (S : Set M)
  statement: N.colon S = ⊤ ↔ S subseteq N
  proof: by
  aesop (add simp [mem_colon, Ideal.eq_top_iff_one])

@[simp]

中文:
引理 colon_eq_top_iff_subset
  条件: (S : 集合 M)
  结论: N.colon S = ⊤ ↔ S subseteq N
  证明: by
  aesop (add simp [mem_colon, Ideal.eq_top_iff_one])

@[simp]

Depends on / 依赖: Ideal.eq_top_iff_one, eq_top_iff_one, mem_colon
-/
lemma colon_eq_top_iff_subset (S : Set M) : N.colon S = ⊤ ↔ S subseteq N := by
  aesop (add simp [mem_colon, Ideal.eq_top_iff_one])

@[simp]
/--
lemma `inf_colon` / 引理 `inf_colon`

English:
lemma inf_colon
  statement: (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 inf_colon
  结论: (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma inf_colon : (N₁ ⊓ N₂).colon S = N₁.colon S ⊓ N₂.colon S := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `iInf_colon` / 引理 `iInf_colon`

English:
lemma iInf_colon
  given: {ι : Sort*} (f : ι -> Submodule R M)
  statement: (⨅ i, f i).colon S = ⨅ i, (f i).colon S
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 iInf_colon
  条件: {ι : 类型层*} (f : ι -> 子模 R M)
  结论: (⨅ i, f i).colon S = ⨅ i, (f i).colon S
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma iInf_colon {ι : Sort*} (f : ι -> Submodule R M) : (⨅ i, f i).colon S = ⨅ i, (f i).colon S := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `colon_finsetInf` / 引理 `colon_finsetInf`

English:
lemma colon_finsetInf
  given: {ι : Type*} (s : Finset ι) (f : ι -> Submodule R M)
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 colon_finsetInf
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> 子模 R M)
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma colon_finsetInf {ι : Type*} (s : Finset ι) (f : ι -> Submodule R M) :
    (s.inf f).colon S = s.inf (fun i => (f i).colon S) := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `top_colon` / 引理 `top_colon`

English:
lemma top_colon
  statement: (⊤ : Submodule R M).colon S = ⊤
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 top_colon
  结论: (⊤ : 子模 R M).colon S = ⊤
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma top_colon : (⊤ : Submodule R M).colon S = ⊤ := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `colon_union` / 引理 `colon_union`

English:
lemma colon_union
  statement: N.colon (S₁ union S₂) = N.colon S₁ ⊓ N.colon S₂
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 colon_union
  结论: N.colon (S₁ union S₂) = N.colon S₁ ⊓ N.colon S₂
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma colon_union : N.colon (S₁ union S₂) = N.colon S₁ ⊓ N.colon S₂ := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `colon_iUnion` / 引理 `colon_iUnion`

English:
lemma colon_iUnion
  given: {ι : Sort*} (f : ι -> Set M)
  statement: N.colon (⋃ i, f i) = ⨅ i, N.colon (f i)
  proof: by
  aesop (add simp mem_colon)

@[simp]

中文:
引理 colon_iUnion
  条件: {ι : 类型层*} (f : ι -> 集合 M)
  结论: N.colon (⋃ i, f i) = ⨅ i, N.colon (f i)
  证明: by
  aesop (add simp mem_colon)

@[simp]

Depends on / 依赖: mem_colon
-/
lemma colon_iUnion {ι : Sort*} (f : ι -> Set M) : N.colon (⋃ i, f i) = ⨅ i, N.colon (f i) := by
  aesop (add simp mem_colon)

@[simp]
/--
lemma `colon_empty` / 引理 `colon_empty`

English:
lemma colon_empty
  statement: N.colon (∅ : Set M) = ⊤
  proof: by
  aesop (add simp mem_colon)

中文:
引理 colon_empty
  结论: N.colon (∅ : 集合 M) = ⊤
  证明: by
  aesop (add simp mem_colon)

Depends on / 依赖: mem_colon
-/
lemma colon_empty : N.colon (∅ : Set M) = ⊤ := by
  aesop (add simp mem_colon)

/--
lemma `colon_singleton_zero` / 引理 `colon_singleton_zero`

English:
lemma colon_singleton_zero
  statement: N.colon {0} = ⊤
  proof: by
  simp

中文:
引理 colon_singleton_zero
  结论: N.colon {0} = ⊤
  证明: by
  simp
-/
lemma colon_singleton_zero : N.colon {0} = ⊤ := by
  simp

/--
lemma `colon_bot` / 引理 `colon_bot`

English:
lemma colon_bot
  statement: N.colon ((⊥ : Submodule R M) : Set M) = ⊤
  proof: by
  simp

中文:
引理 colon_bot
  结论: N.colon ((⊥ : 子模 R M) : 集合 M) = ⊤
  证明: by
  simp
-/
lemma colon_bot : N.colon ((⊥ : Submodule R M) : Set M) = ⊤ := by
  simp

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {N N' : Submodule R M} {S : Set M}

@[deprecated mem_colon (since := "2026-01-15")]
/--
theorem `mem_colon'` / 定理 `mem_colon'`

English:
theorem mem_colon'
  given: {r}
  statement: r in N.colon S ↔ S <= comap (r • (LinearMap.id : M ->ₗ[R] M)) N
  proof: mem_colon

中文:
定理 mem_colon'
  条件: {r}
  结论: r in N.colon S ↔ S <= comap (r • (线性映射.id : M ->ₗ[R] M)) N
  证明: mem_colon

Depends on / 依赖: mem_colon
-/
theorem mem_colon' {r} : r in N.colon S ↔ S <= comap (r • (LinearMap.id : M ->ₗ[R] M)) N :=
  mem_colon

/--
theorem `mem_colon_iff_le` / 定理 `mem_colon_iff_le`

English:
theorem mem_colon_iff_le
  given: {r}
  statement: r in N.colon N' ↔ r • N' <= N
  proof: by
  aesop (add simp SetLike.coe_subset_coe)

中文:
定理 mem_colon_iff_le
  条件: {r}
  结论: r in N.colon N' ↔ r • N' <= N
  证明: by
  aesop (add simp SetLike.coe_subset_coe)

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, coe_subset_coe
-/
theorem mem_colon_iff_le {r} : r in N.colon N' ↔ r • N' <= N := by
  aesop (add simp SetLike.coe_subset_coe)

/--
theorem `bot_colon'` / 定理 `bot_colon'`

English:
theorem bot_colon'
  statement: (⊥ : Submodule R M).colon S = (span R S).annihilator
  proof: by
  aesop (add simp [mem_colon, mem_annihilator_span])

@[simp]

中文:
定理 bot_colon'
  结论: (⊥ : 子模 R M).colon S = (span R S).annihilator
  证明: by
  aesop (add simp [mem_colon, mem_annihilator_span])

@[simp]

Depends on / 依赖: mem_annihilator_span, mem_colon
-/
theorem bot_colon' : (⊥ : Submodule R M).colon S = (span R S).annihilator := by
  aesop (add simp [mem_colon, mem_annihilator_span])

@[simp]
/--
theorem `colon_span` / 定理 `colon_span`

English:
theorem colon_span
  statement: N.colon (span R S) = N.colon S
  proof: by
  refine (colon_mono le_rfl subset_span).antisymm fun r h => mem_colon.mpr fun s hs => ?_
  induction hs using Submodule.span_induction with
  | mem => aesop (add simp mem_colon)
  | zero => simp
  | add => aesop
  | smul => simp_all [smul_mem, smul_comm r]

中文:
定理 colon_span
  结论: N.colon (span R S) = N.colon S
  证明: by
  refine (colon_mono le_rfl subset_span).antisymm fun r h => mem_colon.mpr fun s hs => ?_
  induction hs using Submodule.span_induction with
  | mem => aesop (add simp mem_colon)
  | zero => simp
  | add => aesop
  | smul => simp_all [smul_mem, smul_comm r]

Depends on / 依赖: Submodule, Submodule.span_induction, antisymm, colon_mono, le_rfl, mem_colon, mem_colon.mpr, smul_comm, smul_mem, span_induction, subset_span
-/
theorem colon_span : N.colon (span R S) = N.colon S := by
  refine (colon_mono le_rfl subset_span).antisymm fun r h => mem_colon.mpr fun s hs => ?_
  induction hs using Submodule.span_induction with
  | mem => aesop (add simp mem_colon)
  | zero => simp
  | add => aesop
  | smul => simp_all [smul_mem, smul_comm r]

/--
theorem `_root_.Ideal.colon_span` / 定理 `_root_.Ideal.colon_span`

English:
theorem _root_.Ideal.colon_span
  given: {I : Ideal R} {S : Set R}
  statement: I.colon (Ideal.span S) = I.colon S
  proof: by
  simp

中文:
定理 _root_.理想.colon_span
  条件: {I : 理想 R} {S : 集合 R}
  结论: I.colon (理想.span S) = I.colon S
  证明: by
  simp
-/
theorem _root_.Ideal.colon_span {I : Ideal R} {S : Set R} : I.colon (Ideal.span S) = I.colon S := by
  simp

/--
theorem `mem_colon_span_singleton` / 定理 `mem_colon_span_singleton`

English:
theorem mem_colon_span_singleton
  given: {x : M} {r : R}
  statement: r in N.colon (span R {x}) ↔ r • x in N
  proof: by
  simp

中文:
定理 mem_colon_span_singleton
  条件: {x : M} {r : R}
  结论: r in N.colon (span R {x}) ↔ r • x in N
  证明: by
  simp
-/
theorem mem_colon_span_singleton {x : M} {r : R} : r in N.colon (span R {x}) ↔ r • x in N := by
  simp

/--
theorem `_root_.Ideal.mem_colon_span_singleton` / 定理 `_root_.Ideal.mem_colon_span_singleton`

English:
theorem _root_.Ideal.mem_colon_span_singleton
  given: {I : Ideal R} {x r : R}
  proof: by
  simp

中文:
定理 _root_.理想.mem_colon_span_singleton
  条件: {I : 理想 R} {x r : R}
  证明: by
  simp
-/
theorem _root_.Ideal.mem_colon_span_singleton {I : Ideal R} {x r : R} :
    r in I.colon (Ideal.span {x}) ↔ r * x in I := by
  simp

end CommSemiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
variable {N P : Submodule R M}

@[simp]
/--
lemma `annihilator_map_mkQ_eq_colon` / 引理 `annihilator_map_mkQ_eq_colon`

English:
lemma annihilator_map_mkQ_eq_colon
  statement: annihilator (P.map N.mkQ) = N.colon (P : Set M)
  proof: by
  ext
  rw [mem_annihilator]; rw [mem_colon]
  exact ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ => hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

中文:
引理 annihilator_map_mkQ_eq_colon
  结论: annihilator (P.map N.mkQ) = N.colon (P : 集合 M)
  证明: by
  ext
  rw [mem_annihilator]; rw [mem_colon]
  exact ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ => hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

Depends on / 依赖: Quotient, Quotient.mk, Quotient.mk_eq_zero, mem_annihilator, mem_colon, mem_map_of_mem, mk_eq_zero
-/
lemma annihilator_map_mkQ_eq_colon : annihilator (P.map N.mkQ) = N.colon (P : Set M) := by
  ext
  rw [mem_annihilator]; rw [mem_colon]
  exact ⟨fun H p hp => (Quotient.mk_eq_zero N).1 (H (Quotient.mk p) (mem_map_of_mem hp)),
    fun H _ ⟨p, hp, hpm⟩ => hpm ▸ ((Quotient.mk_eq_zero N).2 <| H p hp)⟩

/--
theorem `annihilator_quotient` / 定理 `annihilator_quotient`

English:
theorem annihilator_quotient
  statement: Module.annihilator R (M ⧸ N) = N.colon Set.univ
  proof: by
  ext r
  have htop : (⊤ : Submodule R (M ⧸ N)) = (⊤ : Submodule R M).map N.mkQ := by
    simpa [map_top] using (LinearMap.range_eq_top.mpr (mkQ_surjective N)).symm
  rw [← annihilator_top (R := R) (M := M ⧸ N)]; rw [htop]; rw [annihilator_map_mkQ_eq_colon (N := N) (P := ⊤)]; rw [Submodule.top_co

中文:
定理 annihilator_quotient
  结论: 模.annihilator R (M ⧸ N) = N.colon 集合.univ
  证明: by
  ext r
  have htop : (⊤ : Submodule R (M ⧸ N)) = (⊤ : Submodule R M).map N.mkQ := by
    simpa [map_top] using (LinearMap.range_eq_top.mpr (mkQ_surjective N)).symm
  rw [← annihilator_top (R := R) (M := M ⧸ N)]; rw [htop]; rw [annihilator_map_mkQ_eq_colon (N := N) (P := ⊤)]; rw [Submodule.top_co

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, N.mkQ, Submodule, Submodule.top_coe, annihilator_map_mkQ_eq_colon, annihilator_top, map_top, mkQ_surjective, range_eq_top, top_coe
-/
theorem annihilator_quotient : Module.annihilator R (M ⧸ N) = N.colon Set.univ := by
  ext r
  have htop : (⊤ : Submodule R (M ⧸ N)) = (⊤ : Submodule R M).map N.mkQ := by
    simpa [map_top] using (LinearMap.range_eq_top.mpr (mkQ_surjective N)).symm
  rw [← annihilator_top (R := R) (M := M ⧸ N)]; rw [htop]; rw [annihilator_map_mkQ_eq_colon (N := N) (P := ⊤)]; rw [Submodule.top_coe]

/--
theorem `_root_.Ideal.annihilator_quotient` / 定理 `_root_.Ideal.annihilator_quotient`

English:
theorem _root_.Ideal.annihilator_quotient
  given: {I : Ideal R} [I.IsTwoSided]
  proof: by
  rw [Submodule.annihilator_quotient]; rw [colon_univ]

中文:
定理 _root_.理想.annihilator_quotient
  条件: {I : 理想 R} [I.是TwoSided]
  证明: by
  rw [Submodule.annihilator_quotient]; rw [colon_univ]

Depends on / 依赖: Submodule, Submodule.annihilator_quotient, annihilator_quotient, colon_univ
-/
theorem _root_.Ideal.annihilator_quotient {I : Ideal R} [I.IsTwoSided] :
    Module.annihilator R (R ⧸ I) = I := by
  rw [Submodule.annihilator_quotient]; rw [colon_univ]

end Ring

end Submodule
