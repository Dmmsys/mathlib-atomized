/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Topological entropy of subsets: monotonicity, closure, union

This file contains general results about the topological entropy of various subsets of the same
dynamical system `(X, T)`. We prove that:
- the topological entropy `CoverEntropy T F` of `F` is monotone in `F`: the larger the subset,
  the larger its entropy.
- the topological entropy of a subset equals the entropy of its closure.
- the entropy of the union of two sets is the maximum of their entropies. We generalize
  the latter property to finite unions.

## Implementation notes

Most results are proved using only the definition of the topological entropy by covers. Some lemmas
of general interest are also proved for nets.

## TODO

One may implement a notion of Hausdorff convergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of the lemmas on closures.

## Tags

closure, entropy, subset, union
-/

@[expose] public section

namespace Dynamics

open ExpGrowth Set UniformSpace
open scoped SetRel Uniformity

variable {X : Type*} {T : X → X} {F G s t : Set X} {U V : SetRel X X} {n : ℕ}

/-! ### Monotonicity of entropy as a function of the subset -/

section Subset

/-
**Dynamics.IsDynCoverOf.monotone_subset** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDy
nCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {F G s : Set X} {U : SetRel X X} {n : ℕ},   F
 ⊆ G → Dynamics.IsDynCoverOf T G U n s → Dynamics.IsDynCoverOf T F U n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma IsDynCoverOf.monotone_subset (F_G : F ⊆ G) (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s :=
  F_G.trans h
/-
**Dynamics.IsDynNetIn.monotone_subset** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynN
etIn`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {F G s : Set X} {U : SetRel X X} {n : ℕ},   F
 ⊆ G → Dynamics.IsDynNetIn T F U n s → Dynamics.IsDynNetIn T G U n s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsDynNetIn.monotone_subset (F_G : F ⊆ G) (h : IsDynNetIn T F U n s) : IsDynNetIn T G U n s :=
  ⟨h.1.trans F_G, h.2⟩
/-
**Dynamics.coverMincard_monotone_subset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_monotone_subset (T : X -> X) (U : SetRel X X) (n : Nat) : Mon
otone fun F : Set X => coverMincard T F U n
参数：T : X -> X；U : SetRel X X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `Dynamics.IsDynCoverOf.monotone_subset`：∀ {X : Type u_1} {T : X → X} {F G
 s : Set X} {U : SetRel X X} {n : ℕ},   F ⊆ G → Dynamics.IsDynCoverOf T G U n s 
→ Dynamics.IsDynCoverOf T F…
-/
lemma coverMincard_monotone_subset (T : X → X) (U : SetRel X X) (n : ℕ) :
    Monotone fun F : Set X ↦ coverMincard T F U n :=
  fun _ _ F_G ↦ biInf_mono fun _ h ↦ h.monotone_subset F_G
/-
**Dynamics.netMaxcard_monotone_subset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netMaxcard_monotone_subset (T : X -> X) (U : SetRel X X) (n : Nat) : Monot
one fun F : Set X => netMaxcard T F U n
参数：T : X -> X；U : SetRel X X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `biSup_mono`：biSup_mono {p q : ι -> Prop} (hpq : forall i, p i -> q i) : 
⨆ (i) (_ : p i), f i <= ⨆ (i) (_ : q i), f i
· 使用定理 `Dynamics.IsDynNetIn.monotone_subset`：∀ {X : Type u_1} {T : X → X} {F G s
 : Set X} {U : SetRel X X} {n : ℕ},   F ⊆ G → Dynamics.IsDynNetIn T F U n s → Dy
namics.IsDynNetIn T G U n…
-/
lemma netMaxcard_monotone_subset (T : X → X) (U : SetRel X X) (n : ℕ) :
    Monotone fun F : Set X ↦ netMaxcard T F U n :=
  fun _ _ F_G ↦ biSup_mono fun _ h ↦ h.monotone_subset F_G
/-
**Dynamics.coverEntropyInfEntourage_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics
`。
形式化陈述：coverEntropyInfEntourage_monotone (T : X -> X) (U : SetRel X X) : Monotone
 fun F : Set X => coverEntropyInfEntourage T F U
参数：T : X -> X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_monotone_subset`：coverMincard_monotone_subset (T :
 X -> X) (U : SetRel X X) (n : Nat) : Monotone fun F : Set X => coverMincard T F
 U n
-/
lemma coverEntropyInfEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ coverEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)
/-
**Dynamics.coverEntropyEntourage_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_monotone (T : X -> X) (U : SetRel X X) : Monotone fu
n F : Set X => coverEntropyEntourage T F U
参数：T : X -> X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_monotone_subset`：coverMincard_monotone_subset (T :
 X -> X) (U : SetRel X X) (n : Nat) : Monotone fun F : Set X => coverMincard T F
 U n
-/
lemma coverEntropyEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ coverEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)
/-
**Dynamics.netEntropyInfEntourage_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyInfEntourage_monotone (T : X -> X) (U : SetRel X X) : Monotone f
un F : Set X => netEntropyInfEntourage T F U
参数：T : X -> X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_monotone_subset`：netMaxcard_monotone_subset (T : X -
> X) (U : SetRel X X) (n : Nat) : Monotone fun F : Set X => netMaxcard T F U n
-/
lemma netEntropyInfEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ netEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)
/-
**Dynamics.netEntropyEntourage_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：netEntropyEntourage_monotone (T : X -> X) (U : SetRel X X) : Monotone fun 
F : Set X => netEntropyEntourage T F U
参数：T : X -> X；U : SetRel X X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.netMaxcard_monotone_subset`：netMaxcard_monotone_subset (T : X -
> X) (U : SetRel X X) (n : Nat) : Monotone fun F : Set X => netMaxcard T F U n
-/
lemma netEntropyEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ netEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)
/-
**Dynamics.coverEntropyInf_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_monotone [UniformSpace X] (T : X -> X) : Monotone fun F : 
Set X => coverEntropyInf T F
参数：T : X -> X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用引理 `Dynamics.coverEntropyInfEntourage_monotone`：coverEntropyInfEntourage_mon
otone (T : X -> X) (U : SetRel X X) : Monotone fun F : Set X => coverEntropyInfE
ntourage T F U
-/
lemma coverEntropyInf_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropyInf T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyInfEntourage_monotone T U F_G
/-
**Dynamics.coverEntropy_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_monotone [UniformSpace X] (T : X -> X) : Monotone fun F : Set
 X => coverEntropy T F
参数：T : X -> X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用引理 `Dynamics.coverEntropyEntourage_monotone`：coverEntropyEntourage_monotone 
(T : X -> X) (U : SetRel X X) : Monotone fun F : Set X => coverEntropyEntourage 
T F U
-/
lemma coverEntropy_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropy T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyEntourage_monotone T U F_G

end Subset

/-! ### Closure -/

section Closure

variable [UniformSpace X]

/-
**Dynamics.IsDynCoverOf.closure** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynCoverOf
`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {F s : Set X} {U V : SetRel X X} {n : ℕ} [ins
t : UniformSpace X],   Continuous T → V ∈ uniformity X → Dynamics.IsDynCoverOf T
 F U n s → Dynamics.IsDynCoverOf T (closure F) (V.comp U) n s
参数：closure F；V.comp U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff'`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (t : Set α), t ∈ l ↔ ∃ i, 
p i ∧ s i ⊆ t
· 使用定理 `UniformSpace.hasBasis_symmetric`：UniformSpace.hasBasis_symmetric : (𝓤 α)
.HasBasis (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) id
· 使用定理 `Dynamics.IsDynCoverOf.of_entourage_subset`：∀ {X : Type u_1} {T : X → X} 
{U V : SetRel X X} {F s : Set X} {n : ℕ},   U ⊆ V → Dynamics.IsDynCoverOf T F U 
n s → Dynamics.IsDynCoverOf T F…
· 使用引理 `SetRel.comp_subset_comp_left`：comp_subset_comp_left {S : SetRel β γ} (hR
 : R₁ subseteq R₂) : R₁ ○ S subseteq R₂ ○ S
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用引理 `Dynamics.ball_dynEntourage_mem_nhds`：ball_dynEntourage_mem_nhds [Uniform
Space X] (h : Continuous T) (U_uni : U in 𝓤 X) (n : Nat) (x : X) : ball x (dynEn
tourage T U n) in 𝓝 x
· 使用引理 `Dynamics.dynEntourage_comp_subset`：dynEntourage_comp_subset (T : X -> X)
 (U V : SetRel X X) (n : Nat) : (dynEntourage T U n) ○ (dynEntourage T V n) subs
eteq dynEntourage T (U …
-/
lemma IsDynCoverOf.closure (h : Continuous T)
    (V_uni : V ∈ 𝓤 X) (s_cover : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (V ○ U) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (SetRel.comp_subset_comp_left W_V) fun x hx ↦ ?_
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_nhds.1 hx _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, hz, hyz⟩ := s_cover hy
  exact ⟨z, hz, dynEntourage_comp_subset _ _ _ _ ⟨y, hxy, hyz⟩⟩
/-
**Dynamics.coverMincard_closure_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_closure_le (h : Continuous T) (F : Set X) (U : SetRel X X) (V
_uni : V in 𝓤 X) (n : Nat) : coverMincard T (closure F) (V ○ U) n <= coverMincar
d T F U n
参数：h : Continuous T；F : Set X；U : SetRel X X；V_uni : V in 𝓤 X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Dynamics.IsDynCoverOf.closure`：∀ {X : Type u_1} {T : X → X} {F s : Set X
} {U V : SetRel X X} {n : ℕ} [inst : UniformSpace X],   Continuous T → V ∈ unifo
rmity X → Dynamics.…
-/
lemma coverMincard_closure_le (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    coverMincard T (closure F) (V ○ U) n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card
/-
**Dynamics.coverEntropyInfEntourage_closure** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`
。
形式化陈述：coverEntropyInfEntourage_closure (h : Continuous T) (F : Set X) (U : SetRe
l X X) (V_uni : V in 𝓤 X) : coverEntropyInfEntourage T (closure F) (V ○ U) <= co
verEntropyInfEntourage T F U
参数：h : Continuous T；F : Set X；U : SetRel X X；V_uni : V in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_closure_le`：coverMincard_closure_le (h : Continuou
s T) (F : Set X) (U : SetRel X X) (V_uni : V in 𝓤 X) (n : Nat) : coverMincard T 
(closure F) (V ○ U) n …
-/
lemma coverEntropyInfEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) :
    coverEntropyInfEntourage T (closure F) (V ○ U) ≤ coverEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)
/-
**Dynamics.coverEntropyEntourage_closure** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X
 X) (V_uni : V in 𝓤 X) : coverEntropyEntourage T (closure F) (V ○ U) <= coverEnt
ropyEntourage T F U
参数：h : Continuous T；F : Set X；U : SetRel X X；V_uni : V in 𝓤 X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_closure_le`：coverMincard_closure_le (h : Continuou
s T) (F : Set X) (U : SetRel X X) (V_uni : V in 𝓤 X) (n : Nat) : coverMincard T 
(closure F) (V ○ U) n …
-/
lemma coverEntropyEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) :
    coverEntropyEntourage T (closure F) (V ○ U) ≤ coverEntropyEntourage T F U :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)
/-
**Dynamics.coverEntropyInf_closure** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_closure (h : Continuous T) : coverEntropyInf T (closure F)
 = coverEntropyInf T F
参数：h : Continuous T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyInfEntourage_antitone`：coverEntropyInfEntourage_ant
itone (T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyInfE
ntourage T F U
· 使用引理 `Dynamics.coverEntropyInfEntourage_closure`：coverEntropyInfEntourage_clos
ure (h : Continuous T) (F : Set X) (U : SetRel X X) (V_uni : V in 𝓤 X) : coverEn
tropyInfEntourage T (closure F)…
· 使用引理 `Dynamics.coverEntropyInf_monotone`：coverEntropyInf_monotone [UniformSpac
e X] (T : X -> X) : Monotone fun F : Set X => coverEntropyInf T F
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma coverEntropyInf_closure (h : Continuous T) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))
/-
**Dynamics.coverEntropy_closure** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_closure (h : Continuous T) : coverEntropy T (closure F) = cov
erEntropy T F
参数：h : Continuous T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `comp_mem_uniformity_sets`：comp_mem_uniformity_sets {s : SetRel α α} (hs 
: s in 𝓤 α) : exists t in 𝓤 α, t ○ t subseteq s
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_antitone`：coverEntropyEntourage_antitone 
(T : X -> X) (F : Set X) : Antitone fun U : SetRel X X => coverEntropyEntourage 
T F U
· 使用引理 `Dynamics.coverEntropyEntourage_closure`：coverEntropyEntourage_closure (h
 : Continuous T) (F : Set X) (U : SetRel X X) (V_uni : V in 𝓤 X) : coverEntropyE
ntourage T (closure F) (V ○ …
· 使用引理 `Dynamics.coverEntropy_monotone`：coverEntropy_monotone [UniformSpace X] (
T : X -> X) : Monotone fun F : Set X => coverEntropy T F
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem coverEntropy_closure (h : Continuous T) :
    coverEntropy T (closure F) = coverEntropy T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

end Closure

/-! ### Finite unions -/

section Union

/-
**Dynamics.IsDynCoverOf.union** 是 Mathlib 中的一个定理，位于命名空间 `Dynamics.IsDynCoverOf`。
形式化陈述：∀ {X : Type u_1} {T : X → X} {F G s t : Set X} {U : SetRel X X} {n : ℕ},  
 Dynamics.IsDynCoverOf T F U n s → Dynamics.IsDynCoverOf T G U n t → Dynamics.Is
DynCoverOf T (F ∪ G) U n (s ∪ t)
参数：F ∪ G；s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetRel.IsCover.union`：∀ {X : Type u_1} {U : SetRel X X} {s t N₁ N₂ : Set
 X}, U.IsCover s N₁ → U.IsCover t N₂ → U.IsCover (s ∪ t) (N₁ ∪ N₂)
-/
lemma IsDynCoverOf.union (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F ∪ G) U n (s ∪ t) := SetRel.IsCover.union hs ht
/-
**Dynamics.coverMincard_union_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverMincard_union_le (T : X -> X) (F G : Set X) (U : SetRel X X) (n : Nat
) : coverMincard T (F union G) U n <= coverMincard T F U n + coverMincard T G U 
n
参数：T : X -> X；F G : Set X；U : SetRel X X；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Dynamics.coverMincard_finite_iff`：coverMincard_finite_iff (T : X -> X) (
F : Set X) (U : SetRel X X) (n : Nat) : coverMincard T F U n < ⊤ ↔ exists s : Fi
nset X, IsDynCoverOf T…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Dynamics.IsDynCoverOf.coverMincard_le_card`：∀ {X : Type u_1} {T : X → X}
 {U : SetRel X X} {F : Set X} {n : ℕ} {s : Finset X},   Dynamics.IsDynCoverOf T 
F U n ↑s → Dynamics.coverMincard…
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Dynamics.IsDynCoverOf.union`：∀ {X : Type u_1} {T : X → X} {F G s t : Set
 X} {U : SetRel X X} {n : ℕ},   Dynamics.IsDynCoverOf T F U n s → Dynamics.IsDyn
CoverOf T G U n t…
· 使用定理 `WithTop.coe_mono`：∀ {α : Type u_1} [inst : Preorder α], Monotone fun a =
> ↑a
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
-/
lemma coverMincard_union_le (T : X → X) (F G : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T (F ∪ G) U n ≤ coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard, ← t_coverMincard, ← ENat.natCast_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover
/-
**Dynamics.coverEntropyEntourage_union** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyEntourage_union : coverEntropyEntourage T (F union G) U = max 
(coverEntropyEntourage T F U) (coverEntropyEntourage T G U)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.toENNReal_add`：toENNReal_add (m n : Nat∞) : ↑(m + n) = (m + n : Rea
l>=0∞)
· 使用定理 `ENat.toENNReal_mono`：toENNReal_mono : Monotone ((↑) : Nat∞ -> Real>=0∞)
· 使用引理 `Dynamics.coverMincard_union_le`：coverMincard_union_le (T : X -> X) (F G 
: Set X) (U : SetRel X X) (n : Nat) : coverMincard T (F union G) U n <= coverMin
card T F U n + cover…
· 使用引理 `ExpGrowth.expGrowthSup_add`：expGrowthSup_add : expGrowthSup (u + v) = ex
pGrowthSup u ⊔ expGrowthSup v
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `Dynamics.coverEntropyEntourage_monotone`：coverEntropyEntourage_monotone 
(T : X -> X) (U : SetRel X X) : Monotone fun F : Set X => coverEntropyEntourage 
T F U
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
lemma coverEntropyEntourage_union :
    coverEntropyEntourage T (F ∪ G) U
      = max (coverEntropyEntourage T F U) (coverEntropyEntourage T G U) := by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n ↦ ?_) expGrowthSup_add
    rw [Pi.add_apply, ← ENat.toENNReal_add]
    exact ENat.toENNReal_mono (coverMincard_union_le T F G U n)
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

variable {ι : Type*} [UniformSpace X]
/-
**Dynamics.coverEntropy_union** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_union : coverEntropy T (F union G) = max (coverEntropy T F) (
coverEntropy T G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `biSup_congr`：biSup_congr {p : ι -> Prop} (h : forall i, p i -> f i = g i
) : ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i
· 使用引理 `Dynamics.coverEntropyEntourage_union`：coverEntropyEntourage_union : cove
rEntropyEntourage T (F union G) U = max (coverEntropyEntourage T F U) (coverEntr
opyEntourage T G U)
-/
lemma coverEntropy_union :
    coverEntropy T (F ∪ G) = max (coverEntropy T F) (coverEntropy T G) := by
  simp only [coverEntropy, ← iSup_sup_eq]
  exact biSup_congr fun _ _ ↦ coverEntropyEntourage_union
/-
**Dynamics.coverEntropyInf_iUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_iUnion_le (T : X -> X) (F : ι -> Set X) : ⨆ i, coverEntrop
yInf T (F i) <= coverEntropyInf T (⋃ i, F i)
参数：T : X -> X；F : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `Dynamics.coverEntropyInf_monotone`：coverEntropyInf_monotone [UniformSpac
e X] (T : X -> X) : Monotone fun F : Set X => coverEntropyInf T F
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
lemma coverEntropyInf_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropyInf_monotone T (subset_iUnion F i)
/-
**Dynamics.coverEntropy_iUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_iUnion_le (T : X -> X) (F : ι -> Set X) : ⨆ i, coverEntropy T
 (F i) <= coverEntropy T (⋃ i, F i)
参数：T : X -> X；F : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用引理 `Dynamics.coverEntropy_monotone`：coverEntropy_monotone [UniformSpace X] (
T : X -> X) : Monotone fun F : Set X => coverEntropy T F
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
lemma coverEntropy_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropy T (F i) ≤ coverEntropy T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropy_monotone T (subset_iUnion F i)
/-
**Dynamics.coverEntropyInf_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropyInf_biUnion_le (s : Set ι) (T : X -> X) (F : ι -> Set X) : ⨆ i
 in s, coverEntropyInf T (F i) <= coverEntropyInf T (⋃ i in s, F i)
参数：s : Set ι；T : X -> X；F : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用引理 `Dynamics.coverEntropyInf_monotone`：coverEntropyInf_monotone [UniformSpac
e X] (T : X -> X) : Monotone fun F : Set X => coverEntropyInf T F
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
lemma coverEntropyInf_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)
/-
**Dynamics.coverEntropy_biUnion_le** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_biUnion_le (s : Set ι) (T : X -> X) (F : ι -> Set X) : ⨆ i in
 s, coverEntropy T (F i) <= coverEntropy T (⋃ i in s, F i)
参数：s : Set ι；T : X -> X；F : ι -> Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用引理 `Dynamics.coverEntropy_monotone`：coverEntropy_monotone [UniformSpace X] (
T : X -> X) : Monotone fun F : Set X => coverEntropy T F
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
-/
lemma coverEntropy_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropy T (F i) ≤ coverEntropy T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropy_monotone T (subset_biUnion_of_mem i_s)

/-- Topological entropy `CoverEntropy T` as a `SupBotHom` function of the subset. -/
/-
**Dynamics.coverEntropySupBotHom** 是 Mathlib 中的一个定义，位于命名空间 `Dynamics`。
形式化陈述：coverEntropySupBotHom (T : X -> X) : SupBotHom (Set X) EReal where toFun
参数：T : X -> X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Dynamics.coverEntropy_union`：coverEntropy_union : coverEntropy T (F unio
n G) = max (coverEntropy T F) (coverEntropy T G)
· 使用引理 `Dynamics.coverEntropy_empty`：coverEntropy_empty : coverEntropy T ∅ = ⊥

--- 原说明 ---
Topological entropy `CoverEntropy T` as a `SupBotHom` function of the subset.
-/
noncomputable def coverEntropySupBotHom (T : X → X) :
    SupBotHom (Set X) EReal where
  toFun := coverEntropy T
  map_sup' := fun _ _ ↦ coverEntropy_union
  map_bot' := coverEntropy_empty

@[deprecated (since := "2026-07-25")]
alias coverEntropy_supBotHom := coverEntropySupBotHom
/-
**Dynamics.coverEntropy_iUnion_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_iUnion_of_finite [Finite ι] {T : X -> X} {F : ι -> Set X} : c
overEntropy T (⋃ i : ι, F i) = ⨆ i : ι, coverEntropy T (F i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.map_finite_iSup`：map_finite_iSup {F ι : Type*} [CompleteLattice α] [
CompleteLattice β] [FunLike F α β] [SupBotHomClass F α β] [Finite ι] (f : F) (g 
: ι -> α)…
· 使用定理 `SupBotHom.instSupBotHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Ma
x α] [inst_1 : Bot α] [inst_2 : Max β] [inst_3 : Bot β],   SupBotHomClass (SupBo
tHom α β) α β
-/
lemma coverEntropy_iUnion_of_finite [Finite ι] {T : X → X} {F : ι → Set X} :
    coverEntropy T (⋃ i : ι, F i) = ⨆ i : ι, coverEntropy T (F i) :=
  map_finite_iSup (coverEntropySupBotHom T) F
/-
**Dynamics.coverEntropy_biUnion_finset** 是 Mathlib 中的一个引理，位于命名空间 `Dynamics`。
形式化陈述：coverEntropy_biUnion_finset {T : X -> X} {F : ι -> Set X} {s : Finset ι} :
 coverEntropy T (⋃ i in s, F i) = ⨆ i in s, coverEntropy T (F i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `SupBotHom.instSupBotHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Ma
x α] [inst_1 : Bot α] [inst_2 : Max β] [inst_3 : Bot β],   SupBotHomClass (SupBo
tHom α β) α β
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Dynamics.coverEntropy_union`：coverEntropy_union : coverEntropy T (F unio
n G) = max (coverEntropy T F) (coverEntropy T G)
· 使用引理 `SupHom.coe_mk`：coe_mk (f : α -> β) (hf) : ⇑(mk f hf) = f
· 使用引理 `Dynamics.coverEntropy_empty`：coverEntropy_empty : coverEntropy T ∅ = ⊥
· 使用定理 `SupBotHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1
 : Bot α] [inst_2 : Max β] [inst_3 : Bot β] (f : SupHom α β)   (hf : f.toFun ⊥ =
 ⊥), ⇑…
· 使用定理 `Dynamics.coverEntropySupBotHom.eq_1`：∀ {X : Type u_1} [inst : UniformSpa
ce X] (T : X → X),   Dynamics.coverEntropySupBotHom T = { toFun := Dynamics.cove
rEntropy T, map_sup' := ⋯…
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
-/
lemma coverEntropy_biUnion_finset {T : X → X} {F : ι → Set X} {s : Finset ι} :
    coverEntropy T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropy T (F i) := by
  have := map_finset_sup (coverEntropySupBotHom T) s F
  rw [s.sup_set_eq_biUnion, s.sup_eq_iSup, coverEntropySupBotHom, SupBotHom.coe_mk,
    SupHom.coe_mk] at this
  rw [this]
  congr

end Union

end Dynamics

