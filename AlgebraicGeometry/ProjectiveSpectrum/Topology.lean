/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Johan Commelin
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Data.Set.Subsingleton

/-!
# Projective spectrum of a graded ring

The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals that
are prime and do not contain the irrelevant ideal.
It is naturally endowed with a topology: the Zariski topology.

## Notation
- `A` is a commutative ring
- `σ` is a class of additive submonoids of `A`
- `𝒜 : ℕ → σ` is the grading of `A`;

## Main definitions

* `ProjectiveSpectrum 𝒜`: The projective spectrum of a graded ring `A`, or equivalently, the set of
  all homogeneous ideals of `A` that is both prime and relevant i.e. not containing irrelevant
  ideal. Henceforth, we call elements of projective spectrum *relevant homogeneous prime ideals*.
* `ProjectiveSpectrum.zeroLocus 𝒜 s`: The zero locus of a subset `s` of `A`
  is the subset of `ProjectiveSpectrum 𝒜` consisting of all relevant homogeneous prime ideals that
  contain `s`.
* `ProjectiveSpectrum.vanishingIdeal t`: The vanishing ideal of a subset `t` of
  `ProjectiveSpectrum 𝒜` is the intersection of points in `t` (viewed as relevant homogeneous prime
  ideals).
* `ProjectiveSpectrum.Top`: the topological space of `ProjectiveSpectrum 𝒜` endowed with the
  Zariski topology.
-/

@[expose] public section


noncomputable section

open DirectSum Pointwise SetLike TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : Nat -> σ) [GradedRing 𝒜]

/-- The projective spectrum of a graded commutative ring is the subtype of all homogeneous ideals
that are prime and do not contain the irrelevant ideal. -/
@[ext]
/--
Definition of `ProjectiveSpectrum` / `ProjectiveSpectrum` 的定义

English:
structure ProjectiveSpectrum
  parameters: where
  axioms and operations (3):
    - asHomogeneousIdeal : HomogeneousIdeal 𝒜
    - isPrime : asHomogeneousIdeal.toIdeal.IsPrime
    - not_irrelevant_le : ¬HomogeneousIdeal.irrelevant 𝒜 <= asHomogeneousIdeal

中文:
结构 射影谱
  参数: where
  公理与运算 (3 个):
    - asHomogeneousIdeal : HomogeneousIdeal 𝒜
    - isPrime : asHomogeneousIdeal.toIdeal.是素
    - not_irrelevant_le : ¬HomogeneousIdeal.irrelevant 𝒜 <= asHomogeneousIdeal
-/
structure ProjectiveSpectrum where
  asHomogeneousIdeal : HomogeneousIdeal 𝒜
  isPrime : asHomogeneousIdeal.toIdeal.IsPrime
  not_irrelevant_le : ¬HomogeneousIdeal.irrelevant 𝒜 <= asHomogeneousIdeal

attribute [instance] ProjectiveSpectrum.isPrime

namespace ProjectiveSpectrum

instance (x : ProjectiveSpectrum 𝒜) : Ideal.IsPrime x.asHomogeneousIdeal.toIdeal := x.isPrime

/--
Definition of `zeroLocus` / `zeroLocus` 的定义

English:
definition zeroLocus
  signature: (s : Set A)
  body: { x | s subseteq x.asHomogeneousIdeal }

@[simp]

中文:
定义 zeroLocus
  签名: (s : 集合 A)
  定义体: { x | s subseteq x.asHomogeneousIdeal }

@[simp]

Depends on / 依赖: Functor, Functor.PullbackObjObj.ofIsInitial, MonoidalClosed, MonoidalClosed.internalHom, PullbackObjObj, asHomogeneousIdeal, initial, initial.to, initialIsInitial, internalHom, ofIsInitial, subseteq, x.asHomogeneousIdeal
-/
def zeroLocus (s : Set A) : Set (ProjectiveSpectrum 𝒜) :=
  { x | s subseteq x.asHomogeneousIdeal }

@[simp]
/--
theorem `mem_zeroLocus` / 定理 `mem_zeroLocus`

English:
theorem mem_zeroLocus
  given: (x : ProjectiveSpectrum 𝒜) (s : Set A)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_zeroLocus
  条件: (x : 射影谱 𝒜) (s : 集合 A)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Functor, Functor.PullbackObjObj.ofIsTerminal, Iff.rfl, MonoidalClosed, MonoidalClosed.internalHom, PullbackObjObj, internalHom, ofIsTerminal, terminal, terminal.from, terminalIsTerminal
-/
theorem mem_zeroLocus (x : ProjectiveSpectrum 𝒜) (s : Set A) :
    x in zeroLocus 𝒜 s ↔ s subseteq x.asHomogeneousIdeal :=
  Iff.rfl

@[simp]
/--
theorem `zeroLocus_span` / 定理 `zeroLocus_span`

English:
theorem zeroLocus_span
  given: (s : Set A)
  statement: zeroLocus 𝒜 (Ideal.span s) = zeroLocus 𝒜 s
  proof: by
  ext x
  exact (Submodule.gi _ _).gc s x.asHomogeneousIdeal.toIdeal

中文:
定理 zeroLocus_span
  条件: (s : 集合 A)
  结论: zeroLocus 𝒜 (理想.span s) = zeroLocus 𝒜 s
  证明: by
  ext x
  exact (Submodule.gi _ _).gc s x.asHomogeneousIdeal.toIdeal

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalObj, Submodule, Submodule.gi, asHomogeneousIdeal, infer_instance, isIso_of_isTerminal, isTerminalObj, terminal, terminal.from, terminalIsTerminal, toIdeal, x.asHomogeneousIdeal.toIdeal
-/
theorem zeroLocus_span (s : Set A) : zeroLocus 𝒜 (Ideal.span s) = zeroLocus 𝒜 s := by
  ext x
  exact (Submodule.gi _ _).gc s x.asHomogeneousIdeal.toIdeal

variable {𝒜}

/--
Definition of `vanishingIdeal` / `vanishingIdeal` 的定义

English:
definition vanishingIdeal
  signature: (t : Set (ProjectiveSpectrum 𝒜))
  body: ⨅ (x : ProjectiveSpectrum 𝒜) (_ : x in t), x.asHomogeneousIdeal

中文:
定义 vanishingIdeal
  签名: (t : 集合 (射影谱 𝒜))
  定义体: ⨅ (x : ProjectiveSpectrum 𝒜) (_ : x in t), x.asHomogeneousIdeal

Depends on / 依赖: ProjectiveSpectrum, asHomogeneousIdeal, isFibrant_of_fibration, terminal, terminal.from, x.asHomogeneousIdeal
-/
def vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) : HomogeneousIdeal 𝒜 :=
  ⨅ (x : ProjectiveSpectrum 𝒜) (_ : x in t), x.asHomogeneousIdeal

/--
theorem `coe_vanishingIdeal` / 定理 `coe_vanishingIdeal`

English:
theorem coe_vanishingIdeal
  given: (t : Set (ProjectiveSpectrum 𝒜))
  proof: by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]; rw [HomogeneousIdeal.mem_iff]

中文:
定理 coe_vanishingIdeal
  条件: (t : 集合 (射影谱 𝒜))
  证明: by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]; rw [HomogeneousIdeal.mem_iff]

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_iInf, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_iInf, forall_congr, mem_coe, mem_iInf, mem_iff, toIdeal_iInf, vanishingIdeal
-/
theorem coe_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    (vanishingIdeal t : Set A) =
      { f | forall x : ProjectiveSpectrum 𝒜, x in t -> f in x.asHomogeneousIdeal } := by
  ext f
  rw [vanishingIdeal]; rw [SetLike.mem_coe]; rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]
  refine forall_congr' fun x => ?_
  rw [HomogeneousIdeal.toIdeal_iInf]; rw [Submodule.mem_iInf]; rw [HomogeneousIdeal.mem_iff]

/--
theorem `mem_vanishingIdeal` / 定理 `mem_vanishingIdeal`

English:
theorem mem_vanishingIdeal
  given: (t : Set (ProjectiveSpectrum 𝒜)) (f : A)
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]

中文:
定理 mem_vanishingIdeal
  条件: (t : 集合 (射影谱 𝒜)) (f : A)
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]

Depends on / 依赖: Set.mem_ofPred_eq, SetLike, SetLike.mem_coe, coe_vanishingIdeal, mem_coe, mem_ofPred_eq
-/
theorem mem_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (f : A) :
    f in vanishingIdeal t ↔ forall x : ProjectiveSpectrum 𝒜, x in t -> f in x.asHomogeneousIdeal := by
  rw [← SetLike.mem_coe]; rw [coe_vanishingIdeal]; rw [Set.mem_ofPred_eq]

@[simp]
/--
theorem `vanishingIdeal_singleton` / 定理 `vanishingIdeal_singleton`

English:
theorem vanishingIdeal_singleton
  given: (x : ProjectiveSpectrum 𝒜)
  proof: by
  simp [vanishingIdeal]

中文:
定理 vanishingIdeal_singleton
  条件: (x : 射影谱 𝒜)
  证明: by
  simp [vanishingIdeal]

Depends on / 依赖: vanishingIdeal
-/
theorem vanishingIdeal_singleton (x : ProjectiveSpectrum 𝒜) :
    vanishingIdeal ({x} : Set (ProjectiveSpectrum 𝒜)) = x.asHomogeneousIdeal := by
  simp [vanishingIdeal]

/--
theorem `subset_zeroLocus_iff_le_vanishingIdeal` / 定理 `subset_zeroLocus_iff_le_vanishingIdeal`

English:
theorem subset_zeroLocus_iff_le_vanishingIdeal
  given: (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A)
  proof: ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zeroLocus _ _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

中文:
定理 subset_zeroLocus_iff_le_vanishingIdeal
  条件: (t : 集合 (射影谱 𝒜)) (I : 理想 A)
  证明: ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zeroLocus _ _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

Depends on / 依赖: le_trans, mem_vanishingIdeal, mem_zeroLocus
-/
theorem subset_zeroLocus_iff_le_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (I : Ideal A) :
    t subseteq zeroLocus 𝒜 I ↔ I <= (vanishingIdeal t).toIdeal :=
  ⟨fun h _ k => (mem_vanishingIdeal _ _).mpr fun _ j => (mem_zeroLocus _ _ _).mpr (h j) k, fun h =>
    fun x j =>
    (mem_zeroLocus _ _ _).mpr (le_trans h fun _ h => ((mem_vanishingIdeal _ _).mp h) x j)⟩

variable (𝒜)

/--
theorem `gc_ideal` / 定理 `gc_ideal`

English:
theorem gc_ideal
  proof: fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

中文:
定理 gc_ideal
  证明: fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

Depends on / 依赖: subset_zeroLocus_iff_le_vanishingIdeal
-/
theorem gc_ideal :
    @GaloisConnection (Ideal A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => (vanishingIdeal t).toIdeal :=
  fun I t => subset_zeroLocus_iff_le_vanishingIdeal t I

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `gc_set` / 定理 `gc_set`

English:
theorem gc_set
  proof: by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi A _).gc
  simpa [zeroLocus_span, Function.comp_def] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)

中文:
定理 gc_set
  证明: by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi A _).gc
  simpa [zeroLocus_span, Function.comp_def] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)

Depends on / 依赖: Function, Function.comp_def, GaloisConnection, GaloisConnection.compose, Ideal.span, Submodule, Submodule.gi, comp_def, compose, gc_ideal, ideal_gc, zeroLocus_span
-/
theorem gc_set :
    @GaloisConnection (Set A) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun s => zeroLocus 𝒜 s) fun t => vanishingIdeal t := by
  have ideal_gc : GaloisConnection Ideal.span _ := (Submodule.gi A _).gc
  simpa [zeroLocus_span, Function.comp_def] using GaloisConnection.compose ideal_gc (gc_ideal 𝒜)

/--
theorem `gc_homogeneousIdeal` / 定理 `gc_homogeneousIdeal`

English:
theorem gc_homogeneousIdeal
  proof: fun I t => by
  simpa [show I.toIdeal <= (vanishingIdeal t).toIdeal ↔ I <= vanishingIdeal t from Iff.rfl] using!
    subset_zeroLocus_iff_le_vanishingIdeal t I.toIdeal

中文:
定理 gc_homogeneousIdeal
  证明: fun I t => by
  simpa [show I.toIdeal <= (vanishingIdeal t).toIdeal ↔ I <= vanishingIdeal t from Iff.rfl] using!
    subset_zeroLocus_iff_le_vanishingIdeal t I.toIdeal

Depends on / 依赖: I.toIdeal, Iff.rfl, subset_zeroLocus_iff_le_vanishingIdeal, toIdeal, vanishingIdeal
-/
theorem gc_homogeneousIdeal :
    @GaloisConnection (HomogeneousIdeal 𝒜) (Set (ProjectiveSpectrum 𝒜))ᵒᵈ _ _
      (fun I => zeroLocus 𝒜 I) fun t => vanishingIdeal t :=
  fun I t => by
  simpa [show I.toIdeal <= (vanishingIdeal t).toIdeal ↔ I <= vanishingIdeal t from Iff.rfl] using!
    subset_zeroLocus_iff_le_vanishingIdeal t I.toIdeal

/--
theorem `subset_zeroLocus_iff_subset_vanishingIdeal` / 定理 `subset_zeroLocus_iff_subset_vanishingIdeal`

English:
theorem subset_zeroLocus_iff_subset_vanishingIdeal
  given: (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A)
  proof: (gc_set _) s t

中文:
定理 subset_zeroLocus_iff_subset_vanishingIdeal
  条件: (t : 集合 (射影谱 𝒜)) (s : 集合 A)
  证明: (gc_set _) s t

Depends on / 依赖: gc_set
-/
theorem subset_zeroLocus_iff_subset_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) (s : Set A) :
    t subseteq zeroLocus 𝒜 s ↔ s subseteq vanishingIdeal t :=
  (gc_set _) s t

/--
theorem `subset_vanishingIdeal_zeroLocus` / 定理 `subset_vanishingIdeal_zeroLocus`

English:
theorem subset_vanishingIdeal_zeroLocus
  given: (s : Set A)
  statement: s subseteq vanishingIdeal (zeroLocus 𝒜 s)
  proof: (gc_set _).le_u_l s

中文:
定理 subset_vanishingIdeal_zeroLocus
  条件: (s : 集合 A)
  结论: s subseteq vanishingIdeal (zeroLocus 𝒜 s)
  证明: (gc_set _).le_u_l s

Depends on / 依赖: gc_set, le_u_l
-/
theorem subset_vanishingIdeal_zeroLocus (s : Set A) : s subseteq vanishingIdeal (zeroLocus 𝒜 s) :=
  (gc_set _).le_u_l s

/--
theorem `ideal_le_vanishingIdeal_zeroLocus` / 定理 `ideal_le_vanishingIdeal_zeroLocus`

English:
theorem ideal_le_vanishingIdeal_zeroLocus
  given: (I : Ideal A)
  proof: (gc_ideal _).le_u_l I

中文:
定理 ideal_le_vanishingIdeal_zeroLocus
  条件: (I : 理想 A)
  证明: (gc_ideal _).le_u_l I

Depends on / 依赖: AncestralRel, Finite, Finite.of_injective, N.ext_iff, N.le_iff_exists_mono, P.AncestralRel, P.II, S.mk, SSet.N.dim_lt_of_lt, SSet.S.ext_iff, Subtype, Subtype.ext_iff, X.map, dim_lt_of_lt, ext_iff, f.op, gc_ideal, le_iff_exists_mono, le_u_l, of_injective
-/
theorem ideal_le_vanishingIdeal_zeroLocus (I : Ideal A) :
    I <= (vanishingIdeal (zeroLocus 𝒜 I)).toIdeal :=
  (gc_ideal _).le_u_l I

/--
theorem `homogeneousIdeal_le_vanishingIdeal_zeroLocus` / 定理 `homogeneousIdeal_le_vanishingIdeal_zeroLocus`

English:
theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus
  given: (I : HomogeneousIdeal 𝒜)
  proof: (gc_homogeneousIdeal _).le_u_l I

中文:
定理 homogeneousIdeal_le_vanishingIdeal_zeroLocus
  条件: (I : HomogeneousIdeal 𝒜)
  证明: (gc_homogeneousIdeal _).le_u_l I

Depends on / 依赖: gc_homogeneousIdeal, le_u_l
-/
theorem homogeneousIdeal_le_vanishingIdeal_zeroLocus (I : HomogeneousIdeal 𝒜) :
    I <= vanishingIdeal (zeroLocus 𝒜 I) :=
  (gc_homogeneousIdeal _).le_u_l I

/--
theorem `subset_zeroLocus_vanishingIdeal` / 定理 `subset_zeroLocus_vanishingIdeal`

English:
theorem subset_zeroLocus_vanishingIdeal
  given: (t : Set (ProjectiveSpectrum 𝒜))
  proof: (gc_ideal _).l_u_le t

中文:
定理 subset_zeroLocus_vanishingIdeal
  条件: (t : 集合 (射影谱 𝒜))
  证明: (gc_ideal _).l_u_le t

Depends on / 依赖: Acc.intro, P.rank, gc_ideal, hy.inv, l_u_le
-/
theorem subset_zeroLocus_vanishingIdeal (t : Set (ProjectiveSpectrum 𝒜)) :
    t subseteq zeroLocus 𝒜 (vanishingIdeal t) :=
  (gc_ideal _).l_u_le t

/--
theorem `zeroLocus_anti_mono` / 定理 `zeroLocus_anti_mono`

English:
theorem zeroLocus_anti_mono
  given: {s t : Set A} (h : s subseteq t)
  statement: zeroLocus 𝒜 t subseteq zeroLocus 𝒜 s
  proof: (gc_set _).monotone_l h

中文:
定理 zeroLocus_anti_mono
  条件: {s t : 集合 A} (h : s subseteq t)
  结论: zeroLocus 𝒜 t subseteq zeroLocus 𝒜 s
  证明: (gc_set _).monotone_l h

Depends on / 依赖: Finite, Finite.bddAbove_range, Nat.add_one_le_iff, P.rank, add_one_le_iff, bddAbove_range, gc_set, le_csSup, monotone_l
-/
theorem zeroLocus_anti_mono {s t : Set A} (h : s subseteq t) : zeroLocus 𝒜 t subseteq zeroLocus 𝒜 s :=
  (gc_set _).monotone_l h

/--
theorem `zeroLocus_anti_mono_ideal` / 定理 `zeroLocus_anti_mono_ideal`

English:
theorem zeroLocus_anti_mono_ideal
  given: {s t : Ideal A} (h : s <= t)
  proof: (gc_ideal _).monotone_l h

中文:
定理 zeroLocus_anti_mono_ideal
  条件: {s t : 理想 A} (h : s <= t)
  证明: (gc_ideal _).monotone_l h

Depends on / 依赖: gc_ideal, monotone_l
-/
theorem zeroLocus_anti_mono_ideal {s t : Ideal A} (h : s <= t) :
    zeroLocus 𝒜 (t : Set A) subseteq zeroLocus 𝒜 (s : Set A) :=
  (gc_ideal _).monotone_l h

/--
theorem `zeroLocus_anti_mono_homogeneousIdeal` / 定理 `zeroLocus_anti_mono_homogeneousIdeal`

English:
theorem zeroLocus_anti_mono_homogeneousIdeal
  given: {s t : HomogeneousIdeal 𝒜} (h : s <= t)
  proof: (gc_homogeneousIdeal _).monotone_l h

中文:
定理 zeroLocus_anti_mono_homogeneousIdeal
  条件: {s t : HomogeneousIdeal 𝒜} (h : s <= t)
  证明: (gc_homogeneousIdeal _).monotone_l h

Depends on / 依赖: gc_homogeneousIdeal, monotone_l
-/
theorem zeroLocus_anti_mono_homogeneousIdeal {s t : HomogeneousIdeal 𝒜} (h : s <= t) :
    zeroLocus 𝒜 (t : Set A) subseteq zeroLocus 𝒜 (s : Set A) :=
  (gc_homogeneousIdeal _).monotone_l h

/--
theorem `vanishingIdeal_anti_mono` / 定理 `vanishingIdeal_anti_mono`

English:
theorem vanishingIdeal_anti_mono
  given: {s t : Set (ProjectiveSpectrum 𝒜)} (h : s subseteq t)
  proof: (gc_ideal _).monotone_u h

中文:
定理 vanishingIdeal_anti_mono
  条件: {s t : 集合 (射影谱 𝒜)} (h : s subseteq t)
  证明: (gc_ideal _).monotone_u h

Depends on / 依赖: gc_ideal, monotone_u
-/
theorem vanishingIdeal_anti_mono {s t : Set (ProjectiveSpectrum 𝒜)} (h : s subseteq t) :
    vanishingIdeal t <= vanishingIdeal s :=
  (gc_ideal _).monotone_u h

/--
theorem `zeroLocus_bot` / 定理 `zeroLocus_bot`

English:
theorem zeroLocus_bot
  statement: zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ
  proof: (gc_ideal 𝒜).l_bot

@[simp]

中文:
定理 zeroLocus_bot
  结论: zeroLocus 𝒜 ((⊥ : 理想 A) : 集合 A) = 集合.univ
  证明: (gc_ideal 𝒜).l_bot

@[simp]

Depends on / 依赖: gc_ideal, l_bot
-/
theorem zeroLocus_bot : zeroLocus 𝒜 ((⊥ : Ideal A) : Set A) = Set.univ :=
  (gc_ideal 𝒜).l_bot

@[simp]
/--
theorem `zeroLocus_singleton_zero` / 定理 `zeroLocus_singleton_zero`

English:
theorem zeroLocus_singleton_zero
  statement: zeroLocus 𝒜 ({0} : Set A) = Set.univ
  proof: zeroLocus_bot _

@[simp]

中文:
定理 zeroLocus_singleton_zero
  结论: zeroLocus 𝒜 ({0} : 集合 A) = 集合.univ
  证明: zeroLocus_bot _

@[simp]

Depends on / 依赖: zeroLocus_bot
-/
theorem zeroLocus_singleton_zero : zeroLocus 𝒜 ({0} : Set A) = Set.univ :=
  zeroLocus_bot _

@[simp]
/--
theorem `zeroLocus_empty` / 定理 `zeroLocus_empty`

English:
theorem zeroLocus_empty
  statement: zeroLocus 𝒜 (∅ : Set A) = Set.univ
  proof: (gc_set 𝒜).l_bot

@[simp]

中文:
定理 zeroLocus_empty
  结论: zeroLocus 𝒜 (∅ : 集合 A) = 集合.univ
  证明: (gc_set 𝒜).l_bot

@[simp]

Depends on / 依赖: gc_set, l_bot
-/
theorem zeroLocus_empty : zeroLocus 𝒜 (∅ : Set A) = Set.univ :=
  (gc_set 𝒜).l_bot

@[simp]
/--
theorem `vanishingIdeal_univ` / 定理 `vanishingIdeal_univ`

English:
theorem vanishingIdeal_univ
  statement: vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤
  proof: by
  simpa using! (gc_ideal _).u_top

中文:
定理 vanishingIdeal_univ
  结论: vanishingIdeal (∅ : 集合 (射影谱 𝒜)) = ⊤
  证明: by
  simpa using! (gc_ideal _).u_top

Depends on / 依赖: gc_ideal, u_top
-/
theorem vanishingIdeal_univ : vanishingIdeal (∅ : Set (ProjectiveSpectrum 𝒜)) = ⊤ := by
  simpa using! (gc_ideal _).u_top

/--
theorem `zeroLocus_empty_of_one_mem` / 定理 `zeroLocus_empty_of_one_mem`

English:
theorem zeroLocus_empty_of_one_mem
  given: {s : Set A} (h : (1 : A) in s)
  statement: zeroLocus 𝒜 s = ∅
  proof: Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
(inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top
x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr hx h

@[simp]

中文:
定理 zeroLocus_empty_of_one_mem
  条件: {s : 集合 A} (h : (1 : A) in s)
  结论: zeroLocus 𝒜 s = ∅
  证明: Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
(inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top
x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr hx h

@[simp]

Depends on / 依赖: IsPrime, Set.eq_empty_iff_forall_notMem.mpr, asHomogeneousIdeal, eq_empty_iff_forall_notMem, eq_top_iff_one, ne_top, toIdeal, x.asHomogeneousIdeal.toIdeal.IsPrime, x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr
-/
theorem zeroLocus_empty_of_one_mem {s : Set A} (h : (1 : A) in s) : zeroLocus 𝒜 s = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
(inferInstance : x.asHomogeneousIdeal.toIdeal.IsPrime).ne_top
x.asHomogeneousIdeal.toIdeal.eq_top_iff_one.mpr hx h

@[simp]
/--
theorem `zeroLocus_singleton_one` / 定理 `zeroLocus_singleton_one`

English:
theorem zeroLocus_singleton_one
  statement: zeroLocus 𝒜 ({1} : Set A) = ∅
  proof: zeroLocus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]

中文:
定理 zeroLocus_singleton_one
  结论: zeroLocus 𝒜 ({1} : 集合 A) = ∅
  证明: zeroLocus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]

Depends on / 依赖: Set.mem_singleton, mem_singleton, zeroLocus_empty_of_one_mem
-/
theorem zeroLocus_singleton_one : zeroLocus 𝒜 ({1} : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem 𝒜 (Set.mem_singleton (1 : A))

@[simp]
/--
theorem `zeroLocus_univ` / 定理 `zeroLocus_univ`

English:
theorem zeroLocus_univ
  statement: zeroLocus 𝒜 (Set.univ : Set A) = ∅
  proof: zeroLocus_empty_of_one_mem _ (Set.mem_univ 1)

中文:
定理 zeroLocus_univ
  结论: zeroLocus 𝒜 (集合.univ : 集合 A) = ∅
  证明: zeroLocus_empty_of_one_mem _ (Set.mem_univ 1)

Depends on / 依赖: Set.mem_univ, mem_univ, zeroLocus_empty_of_one_mem
-/
theorem zeroLocus_univ : zeroLocus 𝒜 (Set.univ : Set A) = ∅ :=
  zeroLocus_empty_of_one_mem _ (Set.mem_univ 1)

/--
theorem `zeroLocus_sup_ideal` / 定理 `zeroLocus_sup_ideal`

English:
theorem zeroLocus_sup_ideal
  given: (I J : Ideal A)
  proof: (gc_ideal 𝒜).l_sup

中文:
定理 zeroLocus_sup_ideal
  条件: (I J : 理想 A)
  证明: (gc_ideal 𝒜).l_sup

Depends on / 依赖: gc_ideal, l_sup
-/
theorem zeroLocus_sup_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊔ J : Ideal A) : Set A) = zeroLocus _ I inter zeroLocus _ J :=
  (gc_ideal 𝒜).l_sup

/--
theorem `zeroLocus_sup_homogeneousIdeal` / 定理 `zeroLocus_sup_homogeneousIdeal`

English:
theorem zeroLocus_sup_homogeneousIdeal
  given: (I J : HomogeneousIdeal 𝒜)
  proof: (gc_homogeneousIdeal 𝒜).l_sup

中文:
定理 zeroLocus_sup_homogeneousIdeal
  条件: (I J : HomogeneousIdeal 𝒜)
  证明: (gc_homogeneousIdeal 𝒜).l_sup

Depends on / 依赖: gc_homogeneousIdeal, l_sup
-/
theorem zeroLocus_sup_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I ⊔ J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus _ I inter zeroLocus _ J :=
  (gc_homogeneousIdeal 𝒜).l_sup

/--
theorem `zeroLocus_union` / 定理 `zeroLocus_union`

English:
theorem zeroLocus_union
  given: (s s' : Set A)
  statement: zeroLocus 𝒜 (s union s') = zeroLocus _ s inter zeroLocus _ s'
  proof: (gc_set 𝒜).l_sup

中文:
定理 zeroLocus_union
  条件: (s s' : 集合 A)
  结论: zeroLocus 𝒜 (s union s') = zeroLocus _ s inter zeroLocus _ s'
  证明: (gc_set 𝒜).l_sup

Depends on / 依赖: gc_set, l_sup
-/
theorem zeroLocus_union (s s' : Set A) : zeroLocus 𝒜 (s union s') = zeroLocus _ s inter zeroLocus _ s' :=
  (gc_set 𝒜).l_sup

/--
theorem `vanishingIdeal_union` / 定理 `vanishingIdeal_union`

English:
theorem vanishingIdeal_union
  given: (t t' : Set (ProjectiveSpectrum 𝒜))
  proof: by
  ext1; exact (gc_ideal 𝒜).u_inf

中文:
定理 vanishingIdeal_union
  条件: (t t' : 集合 (射影谱 𝒜))
  证明: by
  ext1; exact (gc_ideal 𝒜).u_inf

Depends on / 依赖: gc_ideal, u_inf
-/
theorem vanishingIdeal_union (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (t union t') = vanishingIdeal t ⊓ vanishingIdeal t' := by
  ext1; exact (gc_ideal 𝒜).u_inf

/--
theorem `zeroLocus_iSup_ideal` / 定理 `zeroLocus_iSup_ideal`

English:
theorem zeroLocus_iSup_ideal
  given: {γ : Sort*} (I : γ -> Ideal A)
  proof: (gc_ideal 𝒜).l_iSup

中文:
定理 zeroLocus_iSup_ideal
  条件: {γ : 类型层*} (I : γ -> 理想 A)
  证明: (gc_ideal 𝒜).l_iSup

Depends on / 依赖: gc_ideal, l_iSup
-/
theorem zeroLocus_iSup_ideal {γ : Sort*} (I : γ -> Ideal A) :
    zeroLocus _ ((⨆ i, I i : Ideal A) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_ideal 𝒜).l_iSup

/--
theorem `zeroLocus_iSup_homogeneousIdeal` / 定理 `zeroLocus_iSup_homogeneousIdeal`

English:
theorem zeroLocus_iSup_homogeneousIdeal
  given: {γ : Sort*} (I : γ -> HomogeneousIdeal 𝒜)
  proof: (gc_homogeneousIdeal 𝒜).l_iSup

中文:
定理 zeroLocus_iSup_homogeneousIdeal
  条件: {γ : 类型层*} (I : γ -> HomogeneousIdeal 𝒜)
  证明: (gc_homogeneousIdeal 𝒜).l_iSup

Depends on / 依赖: gc_homogeneousIdeal, l_iSup
-/
theorem zeroLocus_iSup_homogeneousIdeal {γ : Sort*} (I : γ -> HomogeneousIdeal 𝒜) :
    zeroLocus _ ((⨆ i, I i : HomogeneousIdeal 𝒜) : Set A) = ⋂ i, zeroLocus 𝒜 (I i) :=
  (gc_homogeneousIdeal 𝒜).l_iSup

/--
theorem `zeroLocus_iUnion` / 定理 `zeroLocus_iUnion`

English:
theorem zeroLocus_iUnion
  given: {γ : Sort*} (s : γ -> Set A)
  proof: (gc_set 𝒜).l_iSup

中文:
定理 zeroLocus_iUnion
  条件: {γ : 类型层*} (s : γ -> 集合 A)
  证明: (gc_set 𝒜).l_iSup

Depends on / 依赖: gc_set, l_iSup
-/
theorem zeroLocus_iUnion {γ : Sort*} (s : γ -> Set A) :
    zeroLocus 𝒜 (⋃ i, s i) = ⋂ i, zeroLocus 𝒜 (s i) :=
  (gc_set 𝒜).l_iSup

/--
theorem `zeroLocus_bUnion` / 定理 `zeroLocus_bUnion`

English:
theorem zeroLocus_bUnion
  given: (s : Set (Set A))
  proof: by
  simp only [zeroLocus_iUnion]

中文:
定理 zeroLocus_bUnion
  条件: (s : 集合 (集合 A))
  证明: by
  simp only [zeroLocus_iUnion]

Depends on / 依赖: zeroLocus_iUnion
-/
theorem zeroLocus_bUnion (s : Set (Set A)) :
    zeroLocus 𝒜 (⋃ s' in s, s' : Set A) = ⋂ s' in s, zeroLocus 𝒜 s' := by
  simp only [zeroLocus_iUnion]

/--
theorem `vanishingIdeal_iUnion` / 定理 `vanishingIdeal_iUnion`

English:
theorem vanishingIdeal_iUnion
  given: {γ : Sort*} (t : γ -> Set (ProjectiveSpectrum 𝒜))
  proof: HomogeneousIdeal.toIdeal_injective by
    convert! (gc_ideal 𝒜).u_iInf; exact HomogeneousIdeal.toIdeal_iInf _

中文:
定理 vanishingIdeal_iUnion
  条件: {γ : 类型层*} (t : γ -> 集合 (射影谱 𝒜))
  证明: HomogeneousIdeal.toIdeal_injective by
    convert! (gc_ideal 𝒜).u_iInf; exact HomogeneousIdeal.toIdeal_iInf _

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.toIdeal_iInf, HomogeneousIdeal.toIdeal_injective, convert, gc_ideal, toIdeal_iInf, toIdeal_injective, u_iInf
-/
theorem vanishingIdeal_iUnion {γ : Sort*} (t : γ -> Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (⋃ i, t i) = ⨅ i, vanishingIdeal (t i) :=
HomogeneousIdeal.toIdeal_injective by
    convert! (gc_ideal 𝒜).u_iInf; exact HomogeneousIdeal.toIdeal_iInf _

/--
theorem `zeroLocus_inf` / 定理 `zeroLocus_inf`

English:
theorem zeroLocus_inf
  given: (I J : Ideal A)
  proof: Set.ext fun x => x.isPrime.inf_le

中文:
定理 zeroLocus_inf
  条件: (I J : 理想 A)
  证明: Set.ext fun x => x.isPrime.inf_le

Depends on / 依赖: Set.ext, inf_le, isPrime, x.isPrime.inf_le
-/
theorem zeroLocus_inf (I J : Ideal A) :
    zeroLocus 𝒜 ((I ⊓ J : Ideal A) : Set A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.inf_le

/--
theorem `union_zeroLocus` / 定理 `union_zeroLocus`

English:
theorem union_zeroLocus
  given: (s s' : Set A)
  proof: by
  rw [zeroLocus_inf]
  simp

中文:
定理 union_zeroLocus
  条件: (s s' : 集合 A)
  证明: by
  rw [zeroLocus_inf]
  simp

Depends on / 依赖: zeroLocus_inf
-/
theorem union_zeroLocus (s s' : Set A) :
    zeroLocus 𝒜 s union zeroLocus 𝒜 s' = zeroLocus 𝒜 (Ideal.span s ⊓ Ideal.span s' : Ideal A) := by
  rw [zeroLocus_inf]
  simp

/--
theorem `zeroLocus_mul_ideal` / 定理 `zeroLocus_mul_ideal`

English:
theorem zeroLocus_mul_ideal
  given: (I J : Ideal A)
  proof: Set.ext fun x => x.isPrime.mul_le

中文:
定理 zeroLocus_mul_ideal
  条件: (I J : 理想 A)
  证明: Set.ext fun x => x.isPrime.mul_le

Depends on / 依赖: Set.ext, isPrime, mul_le, x.isPrime.mul_le
-/
theorem zeroLocus_mul_ideal (I J : Ideal A) :
    zeroLocus 𝒜 ((I * J : Ideal A) : Set A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le

/--
theorem `zeroLocus_mul_homogeneousIdeal` / 定理 `zeroLocus_mul_homogeneousIdeal`

English:
theorem zeroLocus_mul_homogeneousIdeal
  given: (I J : HomogeneousIdeal 𝒜)
  proof: Set.ext fun x => x.isPrime.mul_le

中文:
定理 zeroLocus_mul_homogeneousIdeal
  条件: (I J : HomogeneousIdeal 𝒜)
  证明: Set.ext fun x => x.isPrime.mul_le

Depends on / 依赖: Set.ext, isPrime, mul_le, x.isPrime.mul_le
-/
theorem zeroLocus_mul_homogeneousIdeal (I J : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 ((I * J : HomogeneousIdeal 𝒜) : Set A) = zeroLocus 𝒜 I union zeroLocus 𝒜 J :=
  Set.ext fun x => x.isPrime.mul_le

/--
theorem `zeroLocus_singleton_mul` / 定理 `zeroLocus_singleton_mul`

English:
theorem zeroLocus_singleton_mul
  given: (f g : A)
  proof: Set.ext fun x => by simpa using x.isPrime.mul_mem_iff_mem_or_mem

@[simp]

中文:
定理 zeroLocus_singleton_mul
  条件: (f g : A)
  证明: Set.ext fun x => by simpa using x.isPrime.mul_mem_iff_mem_or_mem

@[simp]

Depends on / 依赖: Set.ext, isPrime, mul_mem_iff_mem_or_mem, x.isPrime.mul_mem_iff_mem_or_mem
-/
theorem zeroLocus_singleton_mul (f g : A) :
    zeroLocus 𝒜 ({f * g} : Set A) = zeroLocus 𝒜 {f} union zeroLocus 𝒜 {g} :=
  Set.ext fun x => by simpa using x.isPrime.mul_mem_iff_mem_or_mem

@[simp]
/--
theorem `zeroLocus_singleton_pow` / 定理 `zeroLocus_singleton_pow`

English:
theorem zeroLocus_singleton_pow
  given: (f : A) (n : Nat) (hn : 0 < n)
  proof: Set.ext fun x => by simpa using x.isPrime.pow_mem_iff_mem n hn

中文:
定理 zeroLocus_singleton_pow
  条件: (f : A) (n : 自然数) (hn : 0 < n)
  证明: Set.ext fun x => by simpa using x.isPrime.pow_mem_iff_mem n hn

Depends on / 依赖: Set.ext, isPrime, pow_mem_iff_mem, x.isPrime.pow_mem_iff_mem
-/
theorem zeroLocus_singleton_pow (f : A) (n : Nat) (hn : 0 < n) :
    zeroLocus 𝒜 ({f ^ n} : Set A) = zeroLocus 𝒜 {f} :=
  Set.ext fun x => by simpa using x.isPrime.pow_mem_iff_mem n hn

/--
theorem `sup_vanishingIdeal_le` / 定理 `sup_vanishingIdeal_le`

English:
theorem sup_vanishingIdeal_le
  given: (t t' : Set (ProjectiveSpectrum 𝒜))
  proof: by
  intro r
  rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_sup]; rw [mem_vanishingIdeal]; rw [Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [HomogeneousIdeal.mem_iff]; rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

中文:
定理 sup_vanishingIdeal_le
  条件: (t t' : 集合 (射影谱 𝒜))
  证明: by
  intro r
  rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_sup]; rw [mem_vanishingIdeal]; rw [Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [HomogeneousIdeal.mem_iff]; rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

Depends on / 依赖: HomogeneousIdeal, HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_sup, Submodule, Submodule.add_mem, Submodule.mem_sup, add_mem, mem_iff, mem_sup, mem_vanishingIdeal, solve_by_elim, toIdeal_sup
-/
theorem sup_vanishingIdeal_le (t t' : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal t ⊔ vanishingIdeal t' <= vanishingIdeal (t inter t') := by
  intro r
  rw [← HomogeneousIdeal.mem_iff]; rw [HomogeneousIdeal.toIdeal_sup]; rw [mem_vanishingIdeal]; rw [Submodule.mem_sup]
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩
  rw [HomogeneousIdeal.mem_iff]; rw [mem_vanishingIdeal] at hf hg
  apply Submodule.add_mem <;> solve_by_elim

/--
theorem `mem_compl_zeroLocus_iff_notMem` / 定理 `mem_compl_zeroLocus_iff_notMem`

English:
theorem mem_compl_zeroLocus_iff_notMem
  given: {f : A} {I : ProjectiveSpectrum 𝒜}
  proof: by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

中文:
定理 mem_compl_zeroLocus_iff_notMem
  条件: {f : A} {I : 射影谱 𝒜}
  证明: by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

Depends on / 依赖: Set.mem_compl_iff, Set.singleton_subset_iff, mem_compl_iff, mem_zeroLocus, singleton_subset_iff
-/
theorem mem_compl_zeroLocus_iff_notMem {f : A} {I : ProjectiveSpectrum 𝒜} :
    I in (zeroLocus 𝒜 {f} : Set (ProjectiveSpectrum 𝒜))ᶜ ↔ f ∉ I.asHomogeneousIdeal := by
  rw [Set.mem_compl_iff]; rw [mem_zeroLocus]; rw [Set.singleton_subset_iff]; rfl

/--
Instance `zariskiTopology` / 实例 `zariskiTopology`

English:
instance zariskiTopology
  signature: : TopologicalSpace (ProjectiveSpectrum 𝒜)
  body: TopologicalSpace.ofClosed (Set.range (ProjectiveSpectrum.zeroLocus 𝒜)) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      let f : Zs -> Set _ := fun i => Classical.choose (h i.2)
      have H : (Set.iInter fun i => zeroLocus 𝒜 (f i)) in Set.range (zeroLocus 𝒜) :=
        ⟨_, zeroLocus_iUnion 𝒜 _⟩
      convert! H using 2
      funext i
      exact (Classical.choose_spec (h i.2)).symm)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus 𝒜 s t).symm⟩)

中文:
实例 zariskiTopology
  签名: : 拓扑空间 (射影谱 𝒜)
  定义体: TopologicalSpace.ofClosed (Set.range (ProjectiveSpectrum.zeroLocus 𝒜)) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      let f : Zs -> Set _ := fun i => Classical.choose (h i.2)
      have H : (Set.iInter fun i => zeroLocus 𝒜 (f i)) in Set.range (zeroLocus 𝒜) :=
        ⟨_, zeroLocus_iUnion 𝒜 _⟩
      convert! H using 2
      funext i
      exact (Classical.choose_spec (h i.2)).symm)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus 𝒜 s t).symm⟩)

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, ProjectiveSpectrum, ProjectiveSpectrum.zeroLocus, Set.iInter, Set.range, Set.sInter_eq_iInter, Set.univ, TopologicalSpace, TopologicalSpace.ofClosed, choose_spec, convert, iInter, ofClosed, sInter_eq_iInter, union_zeroLocus, zeroLocus, zeroLocus_iUnion
-/
instance zariskiTopology : TopologicalSpace (ProjectiveSpectrum 𝒜) :=
  TopologicalSpace.ofClosed (Set.range (ProjectiveSpectrum.zeroLocus 𝒜)) ⟨Set.univ, by simp⟩
    (by
      intro Zs h
      rw [Set.sInter_eq_iInter]
      let f : Zs -> Set _ := fun i => Classical.choose (h i.2)
      have H : (Set.iInter fun i => zeroLocus 𝒜 (f i)) in Set.range (zeroLocus 𝒜) :=
        ⟨_, zeroLocus_iUnion 𝒜 _⟩
      convert! H using 2
      funext i
      exact (Classical.choose_spec (h i.2)).symm)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      exact ⟨_, (union_zeroLocus 𝒜 s t).symm⟩)

/--
Definition of `top` / `top` 的定义

English:
definition top
  signature: : TopCat
  body: TopCat.of (ProjectiveSpectrum 𝒜)

中文:
定义 top
  签名: : 顶元素范畴
  定义体: TopCat.of (ProjectiveSpectrum 𝒜)

Depends on / 依赖: ProjectiveSpectrum, TopCat, TopCat.of
-/
def top : TopCat :=
  TopCat.of (ProjectiveSpectrum 𝒜)

/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (U : Set (ProjectiveSpectrum 𝒜))
  statement: IsOpen U ↔ exists s, Uᶜ = zeroLocus 𝒜 s
  proof: by
  simp only [@eq_comm _ Uᶜ]; rfl

中文:
定理 isOpen_iff
  条件: (U : 集合 (射影谱 𝒜))
  结论: 是开集 U ↔ 存在 s, Uᶜ = zeroLocus 𝒜 s
  证明: by
  simp only [@eq_comm _ Uᶜ]; rfl

Depends on / 依赖: eq_comm
-/
theorem isOpen_iff (U : Set (ProjectiveSpectrum 𝒜)) : IsOpen U ↔ exists s, Uᶜ = zeroLocus 𝒜 s := by
  simp only [@eq_comm _ Uᶜ]; rfl

/--
theorem `isClosed_iff_zeroLocus` / 定理 `isClosed_iff_zeroLocus`

English:
theorem isClosed_iff_zeroLocus
  given: (Z : Set (ProjectiveSpectrum 𝒜))
  proof: by rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

中文:
定理 isClosed_iff_zeroLocus
  条件: (Z : 集合 (射影谱 𝒜))
  证明: by rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

Depends on / 依赖: compl_compl, isOpen_compl_iff, isOpen_iff
-/
theorem isClosed_iff_zeroLocus (Z : Set (ProjectiveSpectrum 𝒜)) :
    IsClosed Z ↔ exists s, Z = zeroLocus 𝒜 s := by rw [← isOpen_compl_iff, isOpen_iff, compl_compl]

/--
theorem `isClosed_zeroLocus` / 定理 `isClosed_zeroLocus`

English:
theorem isClosed_zeroLocus
  given: (s : Set A)
  statement: IsClosed (zeroLocus 𝒜 s)
  proof: by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

中文:
定理 isClosed_zeroLocus
  条件: (s : 集合 A)
  结论: 是闭集 (zeroLocus 𝒜 s)
  证明: by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

Depends on / 依赖: isClosed_iff_zeroLocus
-/
theorem isClosed_zeroLocus (s : Set A) : IsClosed (zeroLocus 𝒜 s) := by
  rw [isClosed_iff_zeroLocus]
  exact ⟨s, rfl⟩

/--
theorem `zeroLocus_vanishingIdeal_eq_closure` / 定理 `zeroLocus_vanishingIdeal_eq_closure`

English:
theorem zeroLocus_vanishingIdeal_eq_closure
  given: (t : Set (ProjectiveSpectrum 𝒜))
  proof: by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : exists s, t' = zeroLocus 𝒜 s := by rwa [isClosed_iff_zeroLocus] at ht'
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    exact Set.Subset.trans ht hx
  · rw [(isClosed_zeroLocus _ _).closure_subset_iff]
    exact subset_zeroLocus_vanishingIdeal 𝒜 t

中文:
定理 zeroLocus_vanishingIdeal_eq_closure
  条件: (t : 集合 (射影谱 𝒜))
  证明: by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : exists s, t' = zeroLocus 𝒜 s := by rwa [isClosed_iff_zeroLocus] at ht'
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    exact Set.Subset.trans ht hx
  · rw [(isClosed_zeroLocus _ _).closure_subset_iff]
    exact subset_zeroLocus_vanishingIdeal 𝒜 t

Depends on / 依赖: Set.Subset.antisymm, Set.Subset.trans, Subset, antisymm, closure_subset_iff, isClosed_iff_zeroLocus, isClosed_zeroLocus, subset_zeroLocus_iff_subset_vanishingIdeal, subset_zeroLocus_vanishingIdeal, zeroLocus
-/
theorem zeroLocus_vanishingIdeal_eq_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    zeroLocus 𝒜 (vanishingIdeal t : Set A) = closure t := by
  apply Set.Subset.antisymm
  · rintro x hx t' ⟨ht', ht⟩
    obtain ⟨fs, rfl⟩ : exists s, t' = zeroLocus 𝒜 s := by rwa [isClosed_iff_zeroLocus] at ht'
    rw [subset_zeroLocus_iff_subset_vanishingIdeal] at ht
    exact Set.Subset.trans ht hx
  · rw [(isClosed_zeroLocus _ _).closure_subset_iff]
    exact subset_zeroLocus_vanishingIdeal 𝒜 t

/--
theorem `vanishingIdeal_closure` / 定理 `vanishingIdeal_closure`

English:
theorem vanishingIdeal_closure
  given: (t : Set (ProjectiveSpectrum 𝒜))
  proof: by
  have : (vanishingIdeal (zeroLocus 𝒜 (vanishingIdeal t))).toIdeal = _ := (gc_ideal 𝒜).u_l_u_eq_u t
  ext1
  rw [zeroLocus_vanishingIdeal_eq_closure 𝒜 t] at this
  exact this

中文:
定理 vanishingIdeal_closure
  条件: (t : 集合 (射影谱 𝒜))
  证明: by
  have : (vanishingIdeal (zeroLocus 𝒜 (vanishingIdeal t))).toIdeal = _ := (gc_ideal 𝒜).u_l_u_eq_u t
  ext1
  rw [zeroLocus_vanishingIdeal_eq_closure 𝒜 t] at this
  exact this

Depends on / 依赖: gc_ideal, toIdeal, u_l_u_eq_u, vanishingIdeal, zeroLocus, zeroLocus_vanishingIdeal_eq_closure
-/
theorem vanishingIdeal_closure (t : Set (ProjectiveSpectrum 𝒜)) :
    vanishingIdeal (closure t) = vanishingIdeal t := by
  have : (vanishingIdeal (zeroLocus 𝒜 (vanishingIdeal t))).toIdeal = _ := (gc_ideal 𝒜).u_l_u_eq_u t
  ext1
  rw [zeroLocus_vanishingIdeal_eq_closure 𝒜 t] at this
  exact this

section BasicOpen

/--
Definition of `basicOpen` / `basicOpen` 的定义

English:
definition basicOpen
  signature: (r : A)
  body: { x | r ∉ x.asHomogeneousIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]

中文:
定义 basicOpen
  签名: (r : A)
  定义体: { x | r ∉ x.asHomogeneousIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]

Depends on / 依赖: asHomogeneousIdeal, x.asHomogeneousIdeal
-/
def basicOpen (r : A) : TopologicalSpace.Opens (ProjectiveSpectrum 𝒜) where
  carrier := { x | r ∉ x.asHomogeneousIdeal }
is_open' := ⟨{r}, Set.ext fun _ => Set.singleton_subset_iff.trans Classical.not_not.symm⟩

@[simp]
/--
theorem `mem_basicOpen` / 定理 `mem_basicOpen`

English:
theorem mem_basicOpen
  given: (f : A) (x : ProjectiveSpectrum 𝒜)
  proof: Iff.rfl

中文:
定理 mem_basicOpen
  条件: (f : A) (x : 射影谱 𝒜)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x in basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

/--
theorem `mem_coe_basicOpen` / 定理 `mem_coe_basicOpen`

English:
theorem mem_coe_basicOpen
  given: (f : A) (x : ProjectiveSpectrum 𝒜)
  proof: Iff.rfl

中文:
定理 mem_coe_basicOpen
  条件: (f : A) (x : 射影谱 𝒜)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe_basicOpen (f : A) (x : ProjectiveSpectrum 𝒜) :
    x in (↑(basicOpen 𝒜 f) : Set (ProjectiveSpectrum 𝒜)) ↔ f ∉ x.asHomogeneousIdeal :=
  Iff.rfl

/--
theorem `isOpen_basicOpen` / 定理 `isOpen_basicOpen`

English:
theorem isOpen_basicOpen
  given: {a : A}
  statement: IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜))
  proof: (basicOpen 𝒜 a).isOpen

@[simp]

中文:
定理 isOpen_basicOpen
  条件: {a : A}
  结论: 是开集 (basicOpen 𝒜 a : 集合 (射影谱 𝒜))
  证明: (basicOpen 𝒜 a).isOpen

@[simp]

Depends on / 依赖: basicOpen, isOpen
-/
theorem isOpen_basicOpen {a : A} : IsOpen (basicOpen 𝒜 a : Set (ProjectiveSpectrum 𝒜)) :=
  (basicOpen 𝒜 a).isOpen

@[simp]
/--
theorem `basicOpen_eq_zeroLocus_compl` / 定理 `basicOpen_eq_zeroLocus_compl`

English:
theorem basicOpen_eq_zeroLocus_compl
  given: (r : A)
  proof: Set.ext fun x => by simp only [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]

中文:
定理 basicOpen_eq_zeroLocus_compl
  条件: (r : A)
  证明: Set.ext fun x => by simp only [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]

Depends on / 依赖: NatTrans, NatTrans.mono_iff_mono_app, Set.ext, Set.mem_compl_iff, Set.singleton_subset_iff, h.symm, mem_compl_iff, mem_zeroLocus, mono_iff_injective, mono_iff_mono_app, singleton_subset_iff
-/
theorem basicOpen_eq_zeroLocus_compl (r : A) :
    (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜)) = (zeroLocus 𝒜 {r})ᶜ :=
  Set.ext fun x => by simp only [Set.mem_compl_iff, mem_zeroLocus, Set.singleton_subset_iff]; rfl

@[simp]
/--
theorem `basicOpen_one` / 定理 `basicOpen_one`

English:
theorem basicOpen_one
  statement: basicOpen 𝒜 (1 : A) = ⊤
  proof: TopologicalSpace.Opens.ext by simp

@[simp]

中文:
定理 basicOpen_one
  结论: basicOpen 𝒜 (1 : A) = ⊤
  证明: TopologicalSpace.Opens.ext by simp

@[simp]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext
-/
theorem basicOpen_one : basicOpen 𝒜 (1 : A) = ⊤ :=
TopologicalSpace.Opens.ext by simp

@[simp]
/--
theorem `basicOpen_zero` / 定理 `basicOpen_zero`

English:
theorem basicOpen_zero
  statement: basicOpen 𝒜 (0 : A) = ⊥
  proof: TopologicalSpace.Opens.ext by simp

中文:
定理 basicOpen_zero
  结论: basicOpen 𝒜 (0 : A) = ⊥
  证明: TopologicalSpace.Opens.ext by simp

Depends on / 依赖: Limits, Limits.Sigma.map, TopologicalSpace, TopologicalSpace.Opens.ext
-/
theorem basicOpen_zero : basicOpen 𝒜 (0 : A) = ⊥ :=
TopologicalSpace.Opens.ext by simp

/--
theorem `basicOpen_mul` / 定理 `basicOpen_mul`

English:
theorem basicOpen_mul
  given: (f g : A)
  statement: basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
  proof: TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

中文:
定理 basicOpen_mul
  条件: (f g : A)
  结论: basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g
  证明: TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext, zeroLocus_singleton_mul
-/
theorem basicOpen_mul (f g : A) : basicOpen 𝒜 (f * g) = basicOpen 𝒜 f ⊓ basicOpen 𝒜 g :=
TopologicalSpace.Opens.ext by simp [zeroLocus_singleton_mul]

/--
theorem `basicOpen_mul_le_left` / 定理 `basicOpen_mul_le_left`

English:
theorem basicOpen_mul_le_left
  given: (f g : A)
  statement: basicOpen 𝒜 (f * g) <= basicOpen 𝒜 f
  proof: by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_left

中文:
定理 basicOpen_mul_le_left
  条件: (f g : A)
  结论: basicOpen 𝒜 (f * g) <= basicOpen 𝒜 f
  证明: by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_left

Depends on / 依赖: basicOpen_mul, inf_le_left
-/
theorem basicOpen_mul_le_left (f g : A) : basicOpen 𝒜 (f * g) <= basicOpen 𝒜 f := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_left

/--
theorem `basicOpen_mul_le_right` / 定理 `basicOpen_mul_le_right`

English:
theorem basicOpen_mul_le_right
  given: (f g : A)
  statement: basicOpen 𝒜 (f * g) <= basicOpen 𝒜 g
  proof: by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_right

@[simp]

中文:
定理 basicOpen_mul_le_right
  条件: (f g : A)
  结论: basicOpen 𝒜 (f * g) <= basicOpen 𝒜 g
  证明: by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_right

@[simp]

Depends on / 依赖: basicOpen_mul, inf_le_right
-/
theorem basicOpen_mul_le_right (f g : A) : basicOpen 𝒜 (f * g) <= basicOpen 𝒜 g := by
  rw [basicOpen_mul 𝒜 f g]
  exact inf_le_right

@[simp]
/--
theorem `basicOpen_pow` / 定理 `basicOpen_pow`

English:
theorem basicOpen_pow
  given: (f : A) (n : Nat) (hn : 0 < n)
  statement: basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
  proof: TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow 𝒜 f n hn

中文:
定理 basicOpen_pow
  条件: (f : A) (n : 自然数) (hn : 0 < n)
  结论: basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
  证明: TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow 𝒜 f n hn

Depends on / 依赖: TopologicalSpace, TopologicalSpace.Opens.ext, zeroLocus_singleton_pow
-/
theorem basicOpen_pow (f : A) (n : Nat) (hn : 0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f :=
TopologicalSpace.Opens.ext by simpa using zeroLocus_singleton_pow 𝒜 f n hn

/--
theorem `basicOpen_eq_union_of_projection` / 定理 `basicOpen_eq_union_of_projection`

English:
theorem basicOpen_eq_union_of_projection
  given: (f : A)
  proof: TopologicalSpace.Opens.ext
    Set.ext fun z => by
      rw [mem_coe_basicOpen]; rw [mem_coe]; rw [iSup]; rw [TopologicalSpace.Opens.mem_sSup]
      constructor <;> intro hz
      · rcases show exists i, GradedRing.proj 𝒜 i f ∉ z.asHomogeneousIdeal by
          contrapose! hz with H
          classical
          rw [← DirectSum.sum_support_decompose 𝒜 f]
          apply Ideal.sum_mem _ fun i _ => H i with ⟨i, hi⟩
        exact ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i f), ⟨i, rfl⟩, by rwa [mem_basicOpen]⟩
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)

中文:
定理 basicOpen_eq_union_of_projection
  条件: (f : A)
  证明: TopologicalSpace.Opens.ext
    Set.ext fun z => by
      rw [mem_coe_basicOpen]; rw [mem_coe]; rw [iSup]; rw [TopologicalSpace.Opens.mem_sSup]
      constructor <;> intro hz
      · rcases show exists i, GradedRing.proj 𝒜 i f ∉ z.asHomogeneousIdeal by
          contrapose! hz with H
          classical
          rw [← DirectSum.sum_support_decompose 𝒜 f]
          apply Ideal.sum_mem _ fun i _ => H i with ⟨i, hi⟩
        exact ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i f), ⟨i, rfl⟩, by rwa [mem_basicOpen]⟩
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)

Depends on / 依赖: DirectSum, DirectSum.sum_support_decompose, GradedRing, GradedRing.proj, Ideal.sum_mem, Set.ext, TopologicalSpace, TopologicalSpace.Opens.ext, TopologicalSpace.Opens.mem_sSup, asHomogeneousIdeal, basicOpen, classical, contrapose, mem_basicOpen, mem_coe, mem_coe_basicOpen, mem_sSup, sum_mem, sum_support_decompose, z.asHomogeneousIdeal
-/
theorem basicOpen_eq_union_of_projection (f : A) :
    basicOpen 𝒜 f = ⨆ i : Nat, basicOpen 𝒜 (GradedRing.proj 𝒜 i f) :=
TopologicalSpace.Opens.ext
    Set.ext fun z => by
      rw [mem_coe_basicOpen]; rw [mem_coe]; rw [iSup]; rw [TopologicalSpace.Opens.mem_sSup]
      constructor <;> intro hz
      · rcases show exists i, GradedRing.proj 𝒜 i f ∉ z.asHomogeneousIdeal by
          contrapose! hz with H
          classical
          rw [← DirectSum.sum_support_decompose 𝒜 f]
          apply Ideal.sum_mem _ fun i _ => H i with ⟨i, hi⟩
        exact ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i f), ⟨i, rfl⟩, by rwa [mem_basicOpen]⟩
      · obtain ⟨_, ⟨i, rfl⟩, hz⟩ := hz
        exact fun rid => hz (z.1.2 i rid)

/--
theorem `isTopologicalBasis_basic_opens` / 定理 `isTopologicalBasis_basic_opens`

English:
theorem isTopologicalBasis_basic_opens
  proof: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen 𝒜
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen 𝒜 f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono 𝒜 (Set.singleton_subset_iff.mpr hfs)

中文:
定理 isTopologicalBasis_basic_opens
  证明: by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen 𝒜
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen 𝒜 f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono 𝒜 (Set.singleton_subset_iff.mpr hfs)

Depends on / 依赖: Set.compl_subset_compl, Set.mem_compl_iff, Set.not_subset, Set.singleton_subset_iff.mpr, TopologicalSpace, TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds, basicOpen, basicOpen_eq_zeroLocus_compl, compl_compl, compl_subset_compl, isOpen_basicOpen, isTopologicalBasis_of_isOpen_of_nhds, mem_compl_iff, mem_zeroLocus, not_subset, singleton_subset_iff, zeroLocus_anti_mono
-/
theorem isTopologicalBasis_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun r : A => (basicOpen 𝒜 r : Set (ProjectiveSpectrum 𝒜))) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨r, rfl⟩
    exact isOpen_basicOpen 𝒜
  · rintro p U hp ⟨s, hs⟩
    rw [← compl_compl U]; rw [Set.mem_compl_iff]; rw [← hs]; rw [mem_zeroLocus]; rw [Set.not_subset] at hp
    obtain ⟨f, hfs, hfp⟩ := hp
    refine ⟨basicOpen 𝒜 f, ⟨f, rfl⟩, hfp, ?_⟩
    rw [← Set.compl_subset_compl]; rw [← hs]; rw [basicOpen_eq_zeroLocus_compl]; rw [compl_compl]
    exact zeroLocus_anti_mono 𝒜 (Set.singleton_subset_iff.mpr hfs)

end BasicOpen

section Order



/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ProjectiveSpectrum 𝒜)
  body: PartialOrder.lift asHomogeneousIdeal fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp only [mk.injEq, imp_self]

@[simp]

中文:
实例 :
  签名: 偏序 (射影谱 𝒜)
  定义体: PartialOrder.lift asHomogeneousIdeal fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp only [mk.injEq, imp_self]

@[simp]

Depends on / 依赖: PartialOrder, PartialOrder.lift, asHomogeneousIdeal, imp_self, mk.injEq
-/
instance : PartialOrder (ProjectiveSpectrum 𝒜) :=
  PartialOrder.lift asHomogeneousIdeal fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp only [mk.injEq, imp_self]

@[simp]
/--
theorem `as_ideal_le_as_ideal` / 定理 `as_ideal_le_as_ideal`

English:
theorem as_ideal_le_as_ideal
  given: (x y : ProjectiveSpectrum 𝒜)
  proof: Iff.rfl

@[simp]

中文:
定理 as_ideal_le_as_ideal
  条件: (x y : 射影谱 𝒜)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem as_ideal_le_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal <= y.asHomogeneousIdeal ↔ x <= y :=
  Iff.rfl

@[simp]
/--
theorem `as_ideal_lt_as_ideal` / 定理 `as_ideal_lt_as_ideal`

English:
theorem as_ideal_lt_as_ideal
  given: (x y : ProjectiveSpectrum 𝒜)
  proof: Iff.rfl

中文:
定理 as_ideal_lt_as_ideal
  条件: (x y : 射影谱 𝒜)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem as_ideal_lt_as_ideal (x y : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal < y.asHomogeneousIdeal ↔ x < y :=
  Iff.rfl

/--
theorem `le_iff_mem_closure` / 定理 `le_iff_mem_closure`

English:
theorem le_iff_mem_closure
  given: (x y : ProjectiveSpectrum 𝒜)
  proof: by
  rw [← as_ideal_le_as_ideal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]
  simp only [as_ideal_le_as_ideal, coe_subset_coe]

中文:
定理 le_iff_mem_closure
  条件: (x y : 射影谱 𝒜)
  证明: by
  rw [← as_ideal_le_as_ideal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]
  simp only [as_ideal_le_as_ideal, coe_subset_coe]

Depends on / 依赖: as_ideal_le_as_ideal, coe_subset_coe, mem_zeroLocus, vanishingIdeal_singleton, zeroLocus_vanishingIdeal_eq_closure
-/
theorem le_iff_mem_closure (x y : ProjectiveSpectrum 𝒜) :
    x <= y ↔ y in closure ({x} : Set (ProjectiveSpectrum 𝒜)) := by
  rw [← as_ideal_le_as_ideal]; rw [← zeroLocus_vanishingIdeal_eq_closure]; rw [mem_zeroLocus]; rw [vanishingIdeal_singleton]
  simp only [as_ideal_le_as_ideal, coe_subset_coe]

end Order

end ProjectiveSpectrum
