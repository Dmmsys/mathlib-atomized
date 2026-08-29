/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Factorization lemma

In this file, we show that if `f : K ⟶ L` is a morphism between bounded below
cochain complexes in an abelian category with enough injectives,
there exists a factorization `ι ≫ π = f` with `ι : K ⟶ K'` a monomorphism that is also
a quasimorphism and `π : K' ⟶ L` a morphism which degreewise is an epimorphism with
an injective kernel, while `K'` is also bounded below (with precise bounds depending
on the available bounds for `K` and `L`): this is
`CochainComplex.Plus.modelCategoryQuillen.cm5a`. Using the factorization
obtained in the file `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`,
we may assume `f : K ⇨ L` is a monomorphism (a case which appears as
the lemma `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof`).

In the proof, the key (private) lemma is be
`CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step` which shows that
if `f` is a monomorphism which is a quasi-isomorphism in degrees `≤ n₀` and
`n₀ + 1 = n₁`, then `f` has a factorisation `ι ≫ π = f`
where `ι` is a monomorphism that is a quasi-isomorphism in degrees `≤ n₁`,
and `π` is an isomorphism in degrees `≤ n₀` that is also a degreewise
epimorphism with an injective kernel. The proof of `step` decomposes
a two separate lemmas `step₁` and `step₂`: we first ensure that `ι`
induces a monomorphism in homology in degree `n₁`, and we proceed further
in `step₂`.

As we assume that both `K` and `L` are bounded below, we may find `n₀ : ℤ`
such that `K` and `L` are strictly `≥ n₀ + 1`: in particular, `f` induces
an isomorphism in degrees `≤ n₀`. Iterating the lemma `step`, we construct
a projective system `ℕᵒᵖ ⥤ CochainComplex C ℤ`
(see `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.cochainComplexFunctor`).
Degreewise, this projective system is essentially constant, which allows
to take its limit, which shall be the intermediate object in the
lemma `cm5a_cof`.

-/


open CategoryTheory Limits Opposite Abelian HomologicalComplex Pretriangulated

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex.Plus.modelCategoryQuillen

variable {K L : CochainComplex C Int} (f : K ⟶ L)

namespace cm5a_cof

/--
Definition of `cofFib` / `cofFib` 的定义

English:
definition cofFib
  signature: : ObjectProperty (Factorisation f)
  body: fun F => Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

中文:
定义 cofFib
  签名: : Object命题erty (Factorisation f)
  定义体: fun F => Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

Depends on / 依赖: degreewiseEpiWithInjectiveKernel
-/
def cofFib : ObjectProperty (Factorisation f) :=
  fun F => Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

instance (F : (cofFib f).FullSubcategory) : Mono F.obj.ι :=
  F.property.1

variable {f} in
/--
Definition of `quasiIsoLE` / `quasiIsoLE` 的定义

English:
definition quasiIsoLE
  signature: (n : Int)
  body: fun F => forall i <= n, QuasiIsoAt F.obj.ι i

中文:
定义 quasiIsoLE
  签名: (n : 整数)
  定义体: fun F => forall i <= n, QuasiIsoAt F.obj.ι i

Depends on / 依赖: F.obj, QuasiIsoAt
-/
def quasiIsoLE (n : Int) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F => forall i <= n, QuasiIsoAt F.obj.ι i

variable {f} in
/--
Definition of `isIsoLE` / `isIsoLE` 的定义

English:
definition isIsoLE
  signature: (n : Int)
  body: fun F => forall i <= n, IsIso (F.obj.π.f i)

中文:
定义 isIsoLE
  签名: (n : 整数)
  定义体: fun F => forall i <= n, IsIso (F.obj.π.f i)

Depends on / 依赖: F.obj
-/
def isIsoLE (n : Int) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F => forall i <= n, IsIso (F.obj.π.f i)

namespace step₁

variable [EnoughInjectives C]

/-!
This section provides the material in order to prove the lemma `step₁` below.
Given a monomorphism `f : K ⟶ L` in `CochainComplex C ℤ` which is
a quasi-isomorphism in degrees `≤ n₀` (with `n₀ + 1 = n₁`), we construct
a factorization `ι f n₁ ≫ π K L n₁ = f` where the intermediate object
`mid K L n₁` is `S K n₁ ⊞ L`, with `S K n₁` the single complex in degree `n₁`
given by an injective object containing `K.opcycles n₁` (which is a cokernel of
the differential `K.X n₀ ⟶ K.X n₁`).
We obtain that `ι f n₁` is a quasi-isomorphism in degrees `≤ n₀` and
induces a monomorphism in homology in degree `n₀`,
and that `π K L n₁` is an isomorphism in degrees `≤ n₀` that is
also a degreewise epimorphism with an injective kernel. -/

variable (n₀ n₁ : Int) (hn₁ : n₀ + 1 = n₁)

variable (K) in
/--
Definition of `S` / `S` 的定义

English:
abbreviation S
  signature: : CochainComplex C Int
  body: ((single C _ n₁).obj (Injective.under (K.opcycles n₁)))

中文:
缩写 S
  签名: : CochainComplex C 整数
  定义体: ((single C _ n₁).obj (Injective.under (K.opcycles n₁)))

Depends on / 依赖: Injective, Injective.under, K.opcycles, opcycles, single
-/
noncomputable abbrev S : CochainComplex C Int :=
    ((single C _ n₁).obj (Injective.under (K.opcycles n₁)))

variable (K L) in
/--
Definition of `mid` / `mid` 的定义

English:
abbreviation mid
  body: S K n₁ ⊞ L

中文:
缩写 mid
  定义体: S K n₁ ⊞ L
-/
noncomputable abbrev mid := S K n₁ ⊞ L

variable (K) in
/--
Definition of `i` / `i` 的定义

English:
definition i
  signature: : K ⟶ S K n₁
  body: mkHomToSingle (K.pOpcycles n₁ ≫ Injective.ι _) (by simp)

中文:
定义 i
  签名: : K ⟶ S K n₁
  定义体: mkHomToSingle (K.pOpcycles n₁ ≫ Injective.ι _) (by simp)

Depends on / 依赖: Injective, K.pOpcycles, mkHomToSingle, pOpcycles
-/
noncomputable def i : K ⟶ S K n₁ := mkHomToSingle (K.pOpcycles n₁ ≫ Injective.ι _) (by simp)

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : K ⟶ mid K L n₁
  body: biprod.lift (i K n₁) f

中文:
缩写 ι
  签名: : K ⟶ mid K L n₁
  定义体: biprod.lift (i K n₁) f

Depends on / 依赖: biprod, biprod.lift
-/
noncomputable abbrev ι : K ⟶ mid K L n₁ := biprod.lift (i K n₁) f

variable (K L) in
/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: : mid K L n₁ ⟶ L
  body: biprod.snd

中文:
缩写 π
  签名: : mid K L n₁ ⟶ L
  定义体: biprod.snd

Depends on / 依赖: biprod, biprod.snd
-/
noncomputable abbrev π : mid K L n₁ ⟶ L := biprod.snd

variable (K L) in
/--
Definition of `σ` / `σ` 的定义

English:
abbreviation σ
  signature: : L ⟶ mid K L n₁
  body: biprod.inr

@[reassoc]

中文:
缩写 σ
  签名: : L ⟶ mid K L n₁
  定义体: biprod.inr

@[reassoc]

Depends on / 依赖: biprod, biprod.inr
-/
noncomputable abbrev σ : L ⟶ mid K L n₁ := biprod.inr

@[reassoc]
/--
lemma `ι_π` / 引理 `ι_π`

English:
lemma ι_π
  statement: ι f n₁ ≫ π K L n₁ = f
  proof: by simp

中文:
引理 ι_π
  结论: ι f n₁ ≫ π K L n₁ = f
  证明: by simp
-/
lemma ι_π : ι f n₁ ≫ π K L n₁ = f := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Mono (ι f n₁)
  body: mono_of_mono_fac (ι_π f n₁)

中文:
实例 [Mono
  签名: f] : Mono (ι f n₁)
  定义体: mono_of_mono_fac (ι_π f n₁)

Depends on / 依赖: mono_of_mono_fac
-/
instance [Mono f] : Mono (ι f n₁) := mono_of_mono_fac (ι_π f n₁)

variable (K L) in
/--
lemma `degreewiseEpiWithInjectiveKernel_π` / 引理 `degreewiseEpiWithInjectiveKernel_π`

English:
lemma degreewiseEpiWithInjectiveKernel_π
  proof: by
  intro q
  rw [Abelian.epiWithInjectiveKernel_iff]
  exact ⟨(S K n₁).X q, inferInstance, (biprod.inl : _ ⟶ mid K L n₁).f q, by simp,
    ⟨{ r := (biprod.fst : mid K L n₁ ⟶ _).f q, s := (biprod.inr : _ ⟶ mid K L n₁).f q }⟩⟩

中文:
引理 degreewiseEpiWithInjectiveKernel_π
  证明: by
  intro q
  rw [Abelian.epiWithInjectiveKernel_iff]
  exact ⟨(S K n₁).X q, inferInstance, (biprod.inl : _ ⟶ mid K L n₁).f q, by simp,
    ⟨{ r := (biprod.fst : mid K L n₁ ⟶ _).f q, s := (biprod.inr : _ ⟶ mid K L n₁).f q }⟩⟩

Depends on / 依赖: Abelian, Abelian.epiWithInjectiveKernel_iff, biprod, biprod.fst, biprod.inl, biprod.inr, epiWithInjectiveKernel_iff
-/
lemma degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π K L n₁) := by
  intro q
  rw [Abelian.epiWithInjectiveKernel_iff]
  exact ⟨(S K n₁).X q, inferInstance, (biprod.inl : _ ⟶ mid K L n₁).f q, by simp,
    ⟨{ r := (biprod.fst : mid K L n₁ ⟶ _).f q, s := (biprod.inr : _ ⟶ mid K L n₁).f q }⟩⟩

variable (K L) in
/--
lemma `isIso_π_f` / 引理 `isIso_π_f`

English:
lemma isIso_π_f
  given: (i : Int) (hi : i != n₁ := by lia)
  proof: by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up Int) _ _ _ hi).eq_of_tgt
  · simp

include hn₁ in

中文:
引理 isIso_π_f
  条件: (i : 整数) (hi : i != n₁ := by lia)
  证明: by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up Int) _ _ _ hi).eq_of_tgt
  · simp

include hn₁ in

Depends on / 依赖: biprod, biprod.inr, biprodX_ext_to_iff, eq_of_tgt, isZero_single_obj_X
-/
lemma isIso_π_f (i : Int) (hi : i != n₁ := by lia) :
    IsIso ((π K L n₁).f i) := by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up Int) _ _ _ hi).eq_of_tgt
  · simp

include hn₁ in
variable (K L) in
/--
lemma `quasiIsoAt_π` / 引理 `quasiIsoAt_π`

English:
lemma quasiIsoAt_π
  given: (i : Int) (hi : i <= n₀ := by lia)
  proof: by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (i - 1) i (i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := isIso_π_f ..
    have : IsIso φ.τ₂ := isIso_π_f ..
    have : IsIso φ.τ₃ := isIso_π_f ..
    exact 

中文:
引理 quasiIsoAt_π
  条件: (i : 整数) (hi : i <= n₀ := by lia)
  证明: by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (i - 1) i (i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := isIso_π_f ..
    have : IsIso φ.τ₂ := isIso_π_f ..
    have : IsIso φ.τ₃ := isIso_π_f ..
    exact 

Depends on / 依赖: QuasiIsoAt, ShortComplex, ShortComplex.isZero_homology_of_isZero_X, ShortComplex.quasiIso_of_epi_of_isIso_of_mono, biprod, biprod.inl, hi.lt_or_eq, homologyMap, isZero_homology_of_isZero_X, lt_or_eq, quasiIsoAt_iff, quasiIsoAt_iff_isIso_homologyMap, quasiIso_of_epi_of_isIso_of_mono, shortComplexFunctor
-/
lemma quasiIsoAt_π (i : Int) (hi : i <= n₀ := by lia) :
    QuasiIsoAt (π K L n₁) i := by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (i - 1) i (i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := isIso_π_f ..
    have : IsIso φ.τ₂ := isIso_π_f ..
    have : IsIso φ.τ₃ := isIso_π_f ..
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have : homologyMap (biprod.inl : _ ⟶ mid K L n₁) i = 0 :=
      (ShortComplex.isZero_homology_of_isZero_X₂ _
        (isZero_single_obj_X (.up Int) _ _ _ (by lia))).eq_of_src _ _
    refine ⟨homologyMap (σ K L n₁) i, ?_, ?_⟩
    · simp [← homologyMap_id, ← biprod.total, homologyMap_comp, this]
    · simp [← homologyMap_comp, homologyMap_id]

variable (hf : forall i <= n₀, QuasiIsoAt f i)

include hn₁ hf in
/--
lemma `quasiIsoAt_ι` / 引理 `quasiIsoAt_ι`

English:
lemma quasiIsoAt_ι
  given: (i : Int) (hi : i <= n₀)
  proof: by
  have := quasiIsoAt_π K L n₀ n₁ hn₁ i hi
  rw [← quasiIsoAt_iff_comp_right _ (π K L n₁)]; rw [ι_π]
  exact hf i hi

中文:
引理 quasiIsoAt_ι
  条件: (i : 整数) (hi : i <= n₀)
  证明: by
  have := quasiIsoAt_π K L n₀ n₁ hn₁ i hi
  rw [← quasiIsoAt_iff_comp_right _ (π K L n₁)]; rw [ι_π]
  exact hf i hi

Depends on / 依赖: quasiIsoAt_iff_comp_right
-/
lemma quasiIsoAt_ι (i : Int) (hi : i <= n₀) :
    QuasiIsoAt (ι f n₁) i := by
  have := quasiIsoAt_π K L n₀ n₁ hn₁ i hi
  rw [← quasiIsoAt_iff_comp_right _ (π K L n₁)]; rw [ι_π]
  exact hf i hi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (homologyMap (ι f n₁) n₁)
  body: by
  let n₀ := n₁ - 1
  rw [mono_homologyMap_iff_up_to_refinements _ n₀ n₁ (n₁ + 1) (by simp; lia) (by simp)]
  intro A x₁ _ y₀ hy₀
  obtain ⟨y₀, rfl⟩ : exists (z₁ : A ⟶ L.X n₀), z₁ ≫ (σ K L n₁).f n₀ = y₀ := by
    refine ⟨y₀ ≫ (π K L n₁).f n₀, Eq.trans ?_ (Category.comp_id _)⟩
    have : (biprod.in

中文:
实例 :
  签名: Mono (homologyMap (ι f n₁) n₁)
  定义体: by
  let n₀ := n₁ - 1
  rw [mono_homologyMap_iff_up_to_refinements _ n₀ n₁ (n₁ + 1) (by simp; lia) (by simp)]
  intro A x₁ _ y₀ hy₀
  obtain ⟨y₀, rfl⟩ : exists (z₁ : A ⟶ L.X n₀), z₁ ≫ (σ K L n₁).f n₀ = y₀ := by
    refine ⟨y₀ ≫ (π K L n₁).f n₀, Eq.trans ?_ (Category.comp_id _)⟩
    have : (biprod.in

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Eq.trans, Hom.comm, biprod, biprod.inl, biprodX_ext_to_iff, biprod_inr_fst_f, biprod_lift_fst_f, biprod_total_f, comp_id, eq_of_src, isZero_single_obj_X, mono_homologyMap_iff_up_to_refinements
-/
instance : Mono (homologyMap (ι f n₁) n₁) := by
  let n₀ := n₁ - 1
  rw [mono_homologyMap_iff_up_to_refinements _ n₀ n₁ (n₁ + 1) (by simp; lia) (by simp)]
  intro A x₁ _ y₀ hy₀
  obtain ⟨y₀, rfl⟩ : exists (z₁ : A ⟶ L.X n₀), z₁ ≫ (σ K L n₁).f n₀ = y₀ := by
    refine ⟨y₀ ≫ (π K L n₁).f n₀, Eq.trans ?_ (Category.comp_id _)⟩
    have : (biprod.inl : _ ⟶ mid K L n₁).f n₀ = 0 :=
      (isZero_single_obj_X (.up Int) _ _ _ (by lia)).eq_of_src _ _
    simp [this, ← biprod_total_f]
  simp only [Category.assoc, Hom.comm, biprodX_ext_to_iff, biprod_lift_fst_f,
    biprod_inr_fst_f, comp_zero, biprod_lift_snd_f, biprod_inr_snd_f,
    Category.comp_id] at hy₀
  obtain ⟨h₁, h₂⟩ := hy₀
  replace h₁ : x₁ ≫ K.pOpcycles n₁ = 0 := by
    rw [← cancel_mono (Injective.ι _)]
    simpa [i, ← cancel_mono (singleObjXSelf (.up Int) n₁ _).hom] using h₁
  obtain ⟨A₁, π, _, x₀, hx₀⟩ :=
    (K.comp_pOpcycles_eq_zero_iff_up_to_refinements x₁ n₀ (by simp; lia)).1 h₁
  exact ⟨A₁, π, inferInstance, x₀, hx₀⟩

end step₁

open step₁ in
/--
lemma `step₁` / 引理 `step₁`

English:
lemma step₁
  statement: [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
  proof: ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun i hi => quasiIsoAt_ι f n₀ n₁ hn₁ hf i hi,
    fun i hi => isIso_π_f K L n₁ i (by lia),
    inferInstance⟩

中文:
引理 step₁
  结论: [EnoughInjectives C] [Mono f] (n₀ n₁ : 整数)
  证明: ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun i hi => quasiIsoAt_ι f n₀ n₁ hn₁ hf i hi,
    fun i hi => isIso_π_f K L n₁ i (by lia),
    inferInstance⟩

Depends on / 依赖: F.obj, FullSubcategory, cofFib, homologyMap, isIsoLE, quasiIsoLE
-/
lemma step₁ [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
    (hf : forall i <= n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    exists (F : (cofFib f).FullSubcategory), quasiIsoLE n₀ F ∧ isIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) :=
  ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun i hi => quasiIsoAt_ι f n₀ n₁ hn₁ hf i hi,
    fun i hi => isIso_π_f K L n₁ i (by lia),
    inferInstance⟩

namespace step₂

/-!
This section provides the material in order to prove the lemma `step₂` below.
Given a monomorphism `f : K ⟶ L` that is a quasi-isomorphism in degrees `< n`
and which induces a monomorphism in homology in degree `n`, we construct
a factorisation of `f` as `ι f n ≫ π f n = f` where
`ι f n : K ⟶ mid f n` is a monomorphism which is a quasi-isomorphism
in degrees `≤ n`, `π f n` is a degreewise epimorphism with an injective kernel
which also induces isomorphisms in degrees `≤ n`.
-/

open HomComplex

variable [EnoughInjectives C] (n : Int)

/--
Definition of `S` / `S` 的定义

English:
abbreviation S
  body: (single C (.up Int) n).obj (Injective.under (((cokernel f).truncGE n).X n))

中文:
缩写 S
  定义体: (single C (.up Int) n).obj (Injective.under (((cokernel f).truncGE n).X n))

Depends on / 依赖: Injective, Injective.under, cokernel, single, truncGE
-/
noncomputable abbrev S :=
  (single C (.up Int) n).obj (Injective.under (((cokernel f).truncGE n).X n))

/--
Definition of `p` / `p` 的定义

English:
definition p
  signature: : (cokernel f).truncGE n ⟶ S f n
  body: mkHomToSingle (Injective.ι _) (fun i hi => by
    simp only [ComplexShape.up_Rel] at hi
    exact (isZero_of_isStrictlyGE _ n _).eq_of_src _ _)

中文:
定义 p
  签名: : (cokernel f).truncGE n ⟶ S f n
  定义体: mkHomToSingle (Injective.ι _) (fun i hi => by
    simp only [ComplexShape.up_Rel] at hi
    exact (isZero_of_isStrictlyGE _ n _).eq_of_src _ _)

Depends on / 依赖: ComplexShape, ComplexShape.up_Rel, Injective, eq_of_src, isZero_of_isStrictlyGE, mkHomToSingle, up_Rel
-/
noncomputable def p : (cokernel f).truncGE n ⟶ S f n :=
  mkHomToSingle (Injective.ι _) (fun i hi => by
    simp only [ComplexShape.up_Rel] at hi
    exact (isZero_of_isStrictlyGE _ n _).eq_of_src _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono ((p f n).f n)
  body: by
  simp only [p, mkHomToSingle_f, mono_comp_iff_of_mono]
  infer_instance

中文:
实例 :
  签名: Mono ((p f n).f n)
  定义体: by
  simp only [p, mkHomToSingle_f, mono_comp_iff_of_mono]
  infer_instance

Depends on / 依赖: infer_instance, mkHomToSingle_f, mono_comp_iff_of_mono
-/
instance : Mono ((p f n).f n) := by
  simp only [p, mkHomToSingle_f, mono_comp_iff_of_mono]
  infer_instance

/--
Definition of `α` / `α` 的定义

English:
definition α
  signature: : L ⟶ S f n
  body: cokernel.π f ≫ (cokernel f).πTruncGE n ≫ p f n

@[reassoc (attr := simp)]

中文:
定义 α
  签名: : L ⟶ S f n
  定义体: cokernel.π f ≫ (cokernel f).πTruncGE n ≫ p f n

@[reassoc (attr := simp)]

Depends on / 依赖: cokernel
-/
noncomputable def α : L ⟶ S f n := cokernel.π f ≫ (cokernel f).πTruncGE n ≫ p f n

@[reassoc (attr := simp)]
/--
lemma `comp_α` / 引理 `comp_α`

English:
lemma comp_α
  statement: f ≫ α f n = 0
  proof: by simp [α]

@[reassoc (attr := simp)]

中文:
引理 comp_α
  结论: f ≫ α f n = 0
  证明: by simp [α]

@[reassoc (attr := simp)]
-/
lemma comp_α : f ≫ α f n = 0 := by simp [α]

@[reassoc (attr := simp)]
/--
lemma `comp_α_f` / 引理 `comp_α_f`

English:
lemma comp_α_f
  given: (i : Int)
  statement: f.f i ≫ (α f n).f i = 0
  proof: by simp [← comp_f]

中文:
引理 comp_α_f
  条件: (i : 整数)
  结论: f.f i ≫ (α f n).f i = 0
  证明: by simp [← comp_f]

Depends on / 依赖: comp_f
-/
lemma comp_α_f (i : Int) : f.f i ≫ (α f n).f i = 0 := by simp [← comp_f]

/--
Definition of `mid` / `mid` 的定义

English:
abbreviation mid
  body: mappingCocone (α f n)

中文:
缩写 mid
  定义体: mappingCocone (α f n)

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.IsHomological.mk, HomologicalComplex, HomologicalComplex.shortExact_of_degreewise_shortExact, IsHomological, S.mapNatIso, ShortComplex, ShortComplex.exact_iff_of_iso, distinguished_iff_iso_trianglehOfDegreewiseSplit, exact_iff_of_iso, hS.homology_exact, homologyFunctorFactors, mapNatIso, mappingCocone, shortExact, shortExact_of_degreewise_shortExact
-/
noncomputable abbrev mid := mappingCocone (α f n)

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : K ⟶ mid f n
  body: mappingCocone.lift (α f n) f 0 (by simp)

中文:
缩写 ι
  签名: : K ⟶ mid f n
  定义体: mappingCocone.lift (α f n) f 0 (by simp)

Depends on / 依赖: mappingCocone, mappingCocone.lift
-/
noncomputable abbrev ι : K ⟶ mid f n := mappingCocone.lift (α f n) f 0 (by simp)

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: : mid f n ⟶ L
  body: mappingCocone.fst (α f n)

@[reassoc]

中文:
缩写 π
  签名: : mid f n ⟶ L
  定义体: mappingCocone.fst (α f n)

@[reassoc]

Depends on / 依赖: mappingCocone, mappingCocone.fst
-/
noncomputable abbrev π : mid f n ⟶ L := mappingCocone.fst (α f n)

@[reassoc]
/--
lemma `ι_π` / 引理 `ι_π`

English:
lemma ι_π
  statement: ι f n ≫ π f n = f
  proof: by simp

中文:
引理 ι_π
  结论: ι f n ≫ π f n = f
  证明: by simp
-/
lemma ι_π : ι f n ≫ π f n = f := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : Mono (ι f n)
  body: mono_of_mono_fac (ι_π f n)

中文:
实例 [Mono
  签名: f] : Mono (ι f n)
  定义体: mono_of_mono_fac (ι_π f n)

Depends on / 依赖: mono_of_mono_fac
-/
instance [Mono f] : Mono (ι f n) := mono_of_mono_fac (ι_π f n)

/--
lemma `degreewiseEpiWithInjectiveKernel_π` / 引理 `degreewiseEpiWithInjectiveKernel_π`

English:
lemma degreewiseEpiWithInjectiveKernel_π
  proof: by
  intro i
  rw [epiWithInjectiveKernel_iff]
  exact ⟨_, inferInstance, (mappingCocone.inr (α f n)).1.v (i - 1) i (by lia), by simp,
    ⟨{r := (mappingCocone.snd (α f n)).v _ _ (by lia)
      s := (mappingCocone.inl (α f n)).v _ _ (by lia)
      id := (add_comm _ _).trans (by simp [mappingCocone.

中文:
引理 degreewiseEpiWithInjectiveKernel_π
  证明: by
  intro i
  rw [epiWithInjectiveKernel_iff]
  exact ⟨_, inferInstance, (mappingCocone.inr (α f n)).1.v (i - 1) i (by lia), by simp,
    ⟨{r := (mappingCocone.snd (α f n)).v _ _ (by lia)
      s := (mappingCocone.inl (α f n)).v _ _ (by lia)
      id := (add_comm _ _).trans (by simp [mappingCocone.

Depends on / 依赖: add_comm, epiWithInjectiveKernel_iff, id_X, mappingCocone, mappingCocone.id_X, mappingCocone.inl, mappingCocone.inr, mappingCocone.snd
-/
lemma degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π f n) := by
  intro i
  rw [epiWithInjectiveKernel_iff]
  exact ⟨_, inferInstance, (mappingCocone.inr (α f n)).1.v (i - 1) i (by lia), by simp,
    ⟨{r := (mappingCocone.snd (α f n)).v _ _ (by lia)
      s := (mappingCocone.inl (α f n)).v _ _ (by lia)
      id := (add_comm _ _).trans (by simp [mappingCocone.id_X]) }⟩⟩

/--
lemma `isIso_π_f` / 引理 `isIso_π_f`

English:
lemma isIso_π_f
  given: (i : Int) (hi : i <= n)
  statement: IsIso ((π f n).f i)
  proof: by
  refine ⟨(mappingCocone.inl (α f n)).v i i (add_zero i), ?_, by simp⟩
  simp [← mappingCocone.id_X (α f n) i (i - 1) (by lia),
    (isZero_single_obj_X _ _ _ _ (by lia)).eq_of_src
      ((mappingCocone.inr (α f n)).1.v (i - 1) i (by lia)) 0]

中文:
引理 isIso_π_f
  条件: (i : 整数) (hi : i <= n)
  结论: IsIso ((π f n).f i)
  证明: by
  refine ⟨(mappingCocone.inl (α f n)).v i i (add_zero i), ?_, by simp⟩
  simp [← mappingCocone.id_X (α f n) i (i - 1) (by lia),
    (isZero_single_obj_X _ _ _ _ (by lia)).eq_of_src
      ((mappingCocone.inr (α f n)).1.v (i - 1) i (by lia)) 0]

Depends on / 依赖: add_zero, eq_of_src, id_X, isZero_single_obj_X, mappingCocone, mappingCocone.id_X, mappingCocone.inl, mappingCocone.inr
-/
lemma isIso_π_f (i : Int) (hi : i <= n) : IsIso ((π f n).f i) := by
  refine ⟨(mappingCocone.inl (α f n)).v i i (add_zero i), ?_, by simp⟩
  simp [← mappingCocone.id_X (α f n) i (i - 1) (by lia),
    (isZero_single_obj_X _ _ _ _ (by lia)).eq_of_src
      ((mappingCocone.inr (α f n)).1.v (i - 1) i (by lia)) 0]

section

attribute [local instance] HasDerivedCategory.standard

/--
lemma `mono_homologyMap_π` / 引理 `mono_homologyMap_π`

English:
lemma mono_homologyMap_π
  given: (q : Int) (hq : q <= n)
  statement: Mono (homologyMap (π f n) q)
  proof: (CochainComplex.homologyMap_exact₁_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) (q - 1) q (by lia)).mono_g
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_src _ _)

中文:
引理 mono_homologyMap_π
  条件: (q : 整数) (hq : q <= n)
  结论: Mono (homologyMap (π f n) q)
  证明: (CochainComplex.homologyMap_exact₁_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) (q - 1) q (by lia)).mono_g
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_src _ _)

Depends on / 依赖: CochainComplex, CochainComplex.homologyMap_exact, DerivedCategory, DerivedCategory.mappingCocone_triangle_distinguished, ExactAt, ExactAt.isZero_homology, HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.subcategoryAcyclic, ObjectProperty, ObjectProperty.prop_of_iso, commShiftIso, eq_of_src, exactAt_single_obj, isKInjective_iff_rightOrthogonal, isZero_homology, le_shift, mappingCocone_triangle_distinguished, mono_g, prop_of_iso
-/
lemma mono_homologyMap_π (q : Int) (hq : q <= n) : Mono (homologyMap (π f n) q) :=
  (CochainComplex.homologyMap_exact₁_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) (q - 1) q (by lia)).mono_g
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_src _ _)

/--
lemma `epi_homologyMap_π` / 引理 `epi_homologyMap_π`

English:
lemma epi_homologyMap_π
  given: (q : Int) (hq : q < n)
  statement: Epi (homologyMap (π f n) q)
  proof: (CochainComplex.homologyMap_exact₂_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) q).epi_f
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_tgt _ _)

中文:
引理 epi_homologyMap_π
  条件: (q : 整数) (hq : q < n)
  结论: Epi (homologyMap (π f n) q)
  证明: (CochainComplex.homologyMap_exact₂_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) q).epi_f
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_tgt _ _)

Depends on / 依赖: CochainComplex, CochainComplex.homologyMap_exact, DerivedCategory, DerivedCategory.mappingCocone_triangle_distinguished, ExactAt, ExactAt.isZero_homology, epi_f, eq_of_tgt, exactAt_single_obj, isZero_homology, mappingCocone_triangle_distinguished
-/
lemma epi_homologyMap_π (q : Int) (hq : q < n) : Epi (homologyMap (π f n) q) :=
  (CochainComplex.homologyMap_exact₂_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) q).epi_f
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_tgt _ _)

end

/--
lemma `quasiIsoAt_π` / 引理 `quasiIsoAt_π`

English:
lemma quasiIsoAt_π
  given: (q : Int) (hq : q < n)
  statement: QuasiIsoAt (π f n) q
  proof: by
  have := mono_homologyMap_π f n q (by lia)
  have := epi_homologyMap_π f n q hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply Balanced.isIso_of_mono_of_epi

中文:
引理 quasiIsoAt_π
  条件: (q : 整数) (hq : q < n)
  结论: QuasiIsoAt (π f n) q
  证明: by
  have := mono_homologyMap_π f n q (by lia)
  have := epi_homologyMap_π f n q hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply Balanced.isIso_of_mono_of_epi

Depends on / 依赖: Balanced, Balanced.isIso_of_mono_of_epi, isIso_of_mono_of_epi, quasiIsoAt_iff_isIso_homologyMap
-/
lemma quasiIsoAt_π (q : Int) (hq : q < n) : QuasiIsoAt (π f n) q := by
  have := mono_homologyMap_π f n q (by lia)
  have := epi_homologyMap_π f n q hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply Balanced.isIso_of_mono_of_epi

/-- The (exact) short complex `K.homology n ⟶ L.homology n ⟶ (S f n).homology n`. -/
@[simps]
/--
Definition of `homologyShortComplex` / `homologyShortComplex` 的定义

English:
definition homologyShortComplex
  signature: : ShortComplex C
  body: ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp]; rw [comp_α]; rw [homologyMap_zero])

中文:
定义 homologyShortComplex
  签名: : ShortComplex C
  定义体: ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp]; rw [comp_α]; rw [homologyMap_zero])

Depends on / 依赖: ShortComplex, ShortComplex.mk, homologyMap, homologyMap_comp, homologyMap_zero
-/
noncomputable def homologyShortComplex : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp]; rw [comp_α]; rw [homologyMap_zero])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: (homologyMap f n)] :
  body: by
  assumption

中文:
实例 [Mono
  签名: (homologyMap f n)] :
  定义体: by
  assumption

Depends on / 依赖: isKInjective_of_injective
-/
instance [Mono (homologyMap f n)] :
    Mono (homologyShortComplex f n).f := by
  assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (homologyMap (p f n) n)
  body: by
  have := (S f n).isIso_homologyπ (n - 1) n (by simp) (by simp)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (p f n) n) := by
    rw [homologyπ_naturality (p f n) n]
    infer_instance
  have := (truncGE (cokernel f) n).isIso_homologyπ (n - 1) n (by simp)
    ((isZero_of_isSt

中文:
实例 :
  签名: Mono (homologyMap (p f n) n)
  定义体: by
  have := (S f n).isIso_homologyπ (n - 1) n (by simp) (by simp)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (p f n) n) := by
    rw [homologyπ_naturality (p f n) n]
    infer_instance
  have := (truncGE (cokernel f) n).isIso_homologyπ (n - 1) n (by simp)
    ((isZero_of_isSt

Depends on / 依赖: IsIso.inv_hom_id_assoc, cokernel, eq_of_src, homologyMap, infer_instance, inv_hom_id_assoc, isZero_of_isStrictlyGE, truncGE
-/
instance : Mono (homologyMap (p f n) n) := by
  have := (S f n).isIso_homologyπ (n - 1) n (by simp) (by simp)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (p f n) n) := by
    rw [homologyπ_naturality (p f n) n]
    infer_instance
  have := (truncGE (cokernel f) n).isIso_homologyπ (n - 1) n (by simp)
    ((isZero_of_isStrictlyGE _ n _ (by lia)).eq_of_src _ _)
  rw [← IsIso.inv_hom_id_assoc ((truncGE (cokernel f) n).homologyπ n) (homologyMap (p f n) n)]
  infer_instance

omit [EnoughInjectives C] in
/--
lemma `shortExact` / 引理 `shortExact`

English:
lemma shortExact
  given: [Mono f]
  statement: (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  proof: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

中文:
引理 shortExact
  条件: [Mono f]
  结论: (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  证明: ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_g_is_cokernel, cokernelIsCokernel, exact_of_g_is_cokernel
-/
lemma shortExact [Mono f] : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `exact_homologyShortComplex` / 引理 `exact_homologyShortComplex`

English:
lemma exact_homologyShortComplex
  given: [Mono f]
  proof: by
  let T := ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])
  let φ : T ⟶ homologyShortComplex f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ p f n) n
      comm₂₃ := 

中文:
引理 exact_homologyShortComplex
  条件: [Mono f]
  证明: by
  let T := ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])
  let φ : T ⟶ homologyShortComplex f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ p f n) n
      comm₂₃ := 

Depends on / 依赖: Category, Category.id_comp, ShortComplex, ShortComplex.ex, ShortComplex.mk, cokernel, cokernel.condition, condition, homologyMap, homologyMap_comp, homologyMap_zero, homologyShortComplex, id_comp
-/
lemma exact_homologyShortComplex [Mono f] :
    (homologyShortComplex f n).Exact := by
  let T := ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])
  let φ : T ⟶ homologyShortComplex f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ p f n) n
      comm₂₃ := by
        dsimp
        rw [Category.id_comp]; rw [← homologyMap_comp]; rw [α] }
  obtain ⟨_, _, _⟩ : Mono φ.τ₃ ∧ IsIso φ.τ₂ ∧ Epi φ.τ₁ := by
    dsimp [φ]
    rw [homologyMap_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact (shortExact f).homology_exact₂ n

variable (hf : forall i < n, QuasiIsoAt f i)

include hf

omit [EnoughInjectives C] in
/--
lemma `isGE_cokernel` / 引理 `isGE_cokernel`

English:
lemma isGE_cokernel
  given: [Mono f] [Mono (homologyMap f n)]
  statement: (cokernel f).IsGE n
  proof: by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  refine ((shortExact f).homology_exact₃ i (i + 1) (by simp)).isZero_X₂ ?_ ?_
  · have := hf i hi
    rw [← ((shortExact f).homology_exact₂ i).epi_f_iff]
    infer_instance
  · rw [← ((shortExact f).homology_exact₁ i (i + 1) (by simp

中文:
引理 isGE_cokernel
  条件: [Mono f] [Mono (homologyMap f n)]
  结论: (cokernel f).IsGE n
  证明: by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  refine ((shortExact f).homology_exact₃ i (i + 1) (by simp)).isZero_X₂ ?_ ?_
  · have := hf i hi
    rw [← ((shortExact f).homology_exact₂ i).epi_f_iff]
    infer_instance
  · rw [← ((shortExact f).homology_exact₁ i (i + 1) (by simp

Depends on / 依赖: epi_f_iff, exactAt_iff_isZero_homology, infer_instance, isGE_iff, mono_g_iff, shortExact
-/
lemma isGE_cokernel [Mono f] [Mono (homologyMap f n)] : (cokernel f).IsGE n := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  refine ((shortExact f).homology_exact₃ i (i + 1) (by simp)).isZero_X₂ ?_ ?_
  · have := hf i hi
    rw [← ((shortExact f).homology_exact₂ i).epi_f_iff]
    infer_instance
  · rw [← ((shortExact f).homology_exact₁ i (i + 1) (by simp)).mono_g_iff]
    by_cases hi' : i + 1 < n
    · have := hf (i + 1) (by lia)
      infer_instance
    · obtain rfl : n = i + 1 := by lia
      infer_instance

omit [EnoughInjectives C] in
/--
lemma `quasiIso_truncGEπ` / 引理 `quasiIso_truncGEπ`

English:
lemma quasiIso_truncGEπ
  given: [Mono f] [Mono (homologyMap f n)]
  proof: by
  rw [quasiIso_πTruncGE_iff]
  exact isGE_cokernel f n hf

中文:
引理 quasiIso_truncGEπ
  条件: [Mono f] [Mono (homologyMap f n)]
  证明: by
  rw [quasiIso_πTruncGE_iff]
  exact isGE_cokernel f n hf

Depends on / 依赖: isGE_cokernel
-/
lemma quasiIso_truncGEπ [Mono f] [Mono (homologyMap f n)] :
    QuasiIso ((cokernel f).πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  exact isGE_cokernel f n hf

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local instance] HasDerivedCategory.standard in
/--
lemma `quasiIsoAt_ι` / 引理 `quasiIsoAt_ι`

English:
lemma quasiIsoAt_ι
  given: [Mono f] [Mono (homologyMap f n)] (q : Int) (hq : q <= n)
  proof: by
  obtain hq | rfl := hq.lt_or_eq'
  · have := quasiIsoAt_π f n q hq
    rw [← quasiIsoAt_iff_comp_right _ (π f n)]; rw [mappingCocone.lift_fst]
    exact hf q hq
  · have := mono_homologyMap_π f n n (by lia)
    have : Mono (homologyMap (mappingCocone.triangle (α f n)).mor₁ n) := by
      dsimp; 

中文:
引理 quasiIsoAt_ι
  条件: [Mono f] [Mono (homologyMap f n)] (q : 整数) (hq : q <= n)
  证明: by
  obtain hq | rfl := hq.lt_or_eq'
  · have := quasiIsoAt_π f n q hq
    rw [← quasiIsoAt_iff_comp_right _ (π f n)]; rw [mappingCocone.lift_fst]
    exact hf q hq
  · have := mono_homologyMap_π f n n (by lia)
    have : Mono (homologyMap (mappingCocone.triangle (α f n)).mor₁ n) := by
      dsimp; 

Depends on / 依赖: CochainComplex, CochainComplex.homologyMap_exact, DerivedCategory, DerivedCategory.mappingCocone_triangle_distinguished, exact_homologyShortComplex, fIsKernel, homologyMa, homologyMap, hq.lt_or_eq, infer_instance, lift_fst, lt_or_eq, mappingCocone, mappingCocone.lift_fst, mappingCocone.triangle, mappingCocone_triangle_distinguished, quasiIsoAt_iff_comp_right, triangle
-/
lemma quasiIsoAt_ι [Mono f] [Mono (homologyMap f n)] (q : Int) (hq : q <= n) :
    QuasiIsoAt (ι f n) q := by
  obtain hq | rfl := hq.lt_or_eq'
  · have := quasiIsoAt_π f n q hq
    rw [← quasiIsoAt_iff_comp_right _ (π f n)]; rw [mappingCocone.lift_fst]
    exact hf q hq
  · have := mono_homologyMap_π f n n (by lia)
    have : Mono (homologyMap (mappingCocone.triangle (α f n)).mor₁ n) := by
      dsimp; infer_instance
    have h₁ := (exact_homologyShortComplex f n).fIsKernel
    have h₂ := (CochainComplex.homologyMap_exact₂_of_distTriang _
      (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) n).fIsKernel
    have : homologyMap (ι f n) n = (IsLimit.conePointUniqueUpToIso h₁ h₂).hom := by
      simp [← cancel_mono (homologyMap (π f n) n),
        dsimp% IsLimit.conePointUniqueUpToIso_hom_comp h₁ h₂ .zero,
        ← homologyMap_comp, mappingCocone.lift_fst]
    rw [quasiIsoAt_iff_isIso_homologyMap]; rw [this]
    infer_instance

end step₂

open step₂ in
/--
lemma `step₂` / 引理 `step₂`

English:
lemma step₂
  statement: [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
  proof: ⟨.mk { mid := mid f n₁, ι := ι f n₁, π := π f n₁}
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π f n₁⟩,
    fun i hi => quasiIsoAt_ι f n₁ (fun j hj => hf j (by lia)) _ hi,
    isIso_π_f f n₁⟩

中文:
引理 step₂
  结论: [EnoughInjectives C] [Mono f] (n₀ n₁ : 整数)
  证明: ⟨.mk { mid := mid f n₁, ι := ι f n₁, π := π f n₁}
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π f n₁⟩,
    fun i hi => quasiIsoAt_ι f n₁ (fun j hj => hf j (by lia)) _ hi,
    isIso_π_f f n₁⟩

Depends on / 依赖: FullSubcategory, cofFib, isIsoLE, quasiIsoLE
-/
lemma step₂ [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
    (hf : forall i <= n₀, QuasiIsoAt f i) [Mono (homologyMap f n₁)] (hn₁ : n₀ + 1 = n₁ := by lia) :
    exists (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₁ F :=
  ⟨.mk { mid := mid f n₁, ι := ι f n₁, π := π f n₁}
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π f n₁⟩,
    fun i hi => quasiIsoAt_ι f n₁ (fun j hj => hf j (by lia)) _ hi,
    isIso_π_f f n₁⟩

/--
lemma `step` / 引理 `step`

English:
lemma step
  statement: [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
  proof: by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ h₁
  refine ⟨.mk { mid := F₂.obj.mid, ι := F₂.obj.ι, π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun i hi => ?_⟩⟩
  have 

中文:
引理 step
  结论: [EnoughInjectives C] [Mono f] (n₀ n₁ : 整数)
  证明: by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ h₁
  refine ⟨.mk { mid := F₂.obj.mid, ι := F₂.obj.ι, π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun i hi => ?_⟩⟩
  have 

Depends on / 依赖: FullSubcategory, MorphismProperty, MorphismProperty.comp_mem, cofFib, comp_mem, infer_instance, isIsoLE, obj.mid, property, quasiIsoLE
-/
lemma step [EnoughInjectives C] [Mono f] (n₀ n₁ : Int)
    (hf : forall i <= n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    exists (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₀ F := by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ h₁
  refine ⟨.mk { mid := F₂.obj.mid, ι := F₂.obj.ι, π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun i hi => ?_⟩⟩
  have := h₂ i hi
  have := h₄ i (by lia)
  dsimp
  infer_instance

/--
Definition of `CofFibFactorizationQuasiIsoLE` / `CofFibFactorizationQuasiIsoLE` 的定义

English:
abbreviation CofFibFactorizationQuasiIsoLE
  signature: (n : Int)
  body: (quasiIsoLE (f := f) n).FullSubcategory

中文:
缩写 CofFibFactorizationQuasiIsoLE
  签名: (n : 整数)
  定义体: (quasiIsoLE (f := f) n).FullSubcategory

Depends on / 依赖: FullSubcategory, HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.subcategoryAcyclic, ObjectProperty, ObjectProperty.prop_of_iso, commShiftIso, isKProjective_iff_leftOrthogonal, le_shift, leftOrthogonal, leftOrthogonal.le_shift, prop_of_iso, quasiIsoLE, quotient, subcategoryAcyclic, symm.app
-/
abbrev CofFibFactorizationQuasiIsoLE (n : Int) := (quasiIsoLE (f := f) n).FullSubcategory

variable [EnoughInjectives C]

namespace CofFibFactorizationQuasiIsoLE

/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: [Mono f] (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE (n + 1)]
  body: .mk (.mk { mid := L, ι := f, π := 𝟙 L }
    ⟨by assumption, fun i => epiWithInjectiveKernel_of_iso (𝟙 (L.X i))⟩)
    (fun i hi => by
      dsimp
      rw [quasiIsoAt_iff_isIso_homologyMap]
      apply IsZero.isIso
      all_goals
      · rw [← exactAt_iff_isZero_homology]
        exact exactAt_of_is

中文:
定义 zero
  签名: [Mono f] (n : 整数) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE (n + 1)]
  定义体: .mk (.mk { mid := L, ι := f, π := 𝟙 L }
    ⟨by assumption, fun i => epiWithInjectiveKernel_of_iso (𝟙 (L.X i))⟩)
    (fun i hi => by
      dsimp
      rw [quasiIsoAt_iff_isIso_homologyMap]
      apply IsZero.isIso
      all_goals
      · rw [← exactAt_iff_isZero_homology]
        exact exactAt_of_is

Depends on / 依赖: IsZero, IsZero.isIso, all_goals, epiWithInjectiveKernel_of_iso, exactAt_iff_isZero_homology, exactAt_of_isGE, quasiIsoAt_iff_isIso_homologyMap
-/
def zero [Mono f] (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE (n + 1)] :
    CofFibFactorizationQuasiIsoLE f (n + (0 : Nat)) :=
  .mk (.mk { mid := L, ι := f, π := 𝟙 L }
    ⟨by assumption, fun i => epiWithInjectiveKernel_of_iso (𝟙 (L.X i))⟩)
    (fun i hi => by
      dsimp
      rw [quasiIsoAt_iff_isIso_homologyMap]
      apply IsZero.isIso
      all_goals
      · rw [← exactAt_iff_isZero_homology]
        exact exactAt_of_isGE _ (n + 1) i)

variable {f} in
/--
lemma `exists_next` / 引理 `exists_next`

English:
lemma exists_next
  statement: {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
  proof: by
  obtain ⟨F₁₂, h₁, h₂⟩ := step F.obj.obj.ι n₀ n₁ F.property
  exact ⟨.mk (.mk { mid := F₁₂.obj.mid, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₁,
      ObjectProperty.homMk { h := F₁₂.obj.π

中文:
引理 exists_next
  结论: {n₀ : 整数} (F : CofFibFactorizationQuasiIsoLE f n₀)
  证明: by
  obtain ⟨F₁₂, h₁, h₂⟩ := step F.obj.obj.ι n₀ n₁ F.property
  exact ⟨.mk (.mk { mid := F₁₂.obj.mid, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₁,
      ObjectProperty.homMk { h := F₁₂.obj.π

Depends on / 依赖: F.obj.obj, F.obj.property, F.property, MorphismProperty, MorphismProperty.comp_mem, ObjectProperty, ObjectProperty.homMk, comp_mem, infer_instance, obj.mid, property
-/
lemma exists_next {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : Int) (hn₁ : n₀ + 1 = n₁) :
    exists (F' : CofFibFactorizationQuasiIsoLE f n₁) (g : F'.1 ⟶ F.1),
      forall (i : Int) (_ : i <= n₀), IsIso (g.hom.h.f i) := by
  obtain ⟨F₁₂, h₁, h₂⟩ := step F.obj.obj.ι n₀ n₁ F.property
  exact ⟨.mk (.mk { mid := F₁₂.obj.mid, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₁,
      ObjectProperty.homMk { h := F₁₂.obj.π }, h₂⟩

variable {f} in
/--
Definition of `next` / `next` 的定义

English:
definition next
  signature: {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
  body: (F.exists_next n₁ hn₁).choose

中文:
定义 next
  签名: {n₀ : 整数} (F : CofFibFactorizationQuasiIsoLE f n₀)
  定义体: (F.exists_next n₁ hn₁).choose

Depends on / 依赖: F.exists_next, exists_next
-/
noncomputable def next {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : Int) (hn₁ : n₀ + 1 = n₁) :
    CofFibFactorizationQuasiIsoLE f n₁ :=
  (F.exists_next n₁ hn₁).choose

variable {f} in
/--
Definition of `fromNext` / `fromNext` 的定义

English:
definition fromNext
  signature: {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
  body: (F.exists_next n₁ hn₁).choose_spec.choose

中文:
定义 fromNext
  签名: {n₀ : 整数} (F : CofFibFactorizationQuasiIsoLE f n₀)
  定义体: (F.exists_next n₁ hn₁).choose_spec.choose

Depends on / 依赖: CochainComplex, CochainComplex.isKProjective_of_projective, F.exists_next, choose_spec, choose_spec.choose, exists_next, isKProjective_of_projective
-/
noncomputable def fromNext {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : Int) (hn₁ : n₀ + 1 = n₁) :
    (F.next n₁ hn₁).obj ⟶ F.obj :=
  (F.exists_next n₁ hn₁).choose_spec.choose

variable {f} in
/--
lemma `isIso_fromNext_hom_h_f` / 引理 `isIso_fromNext_hom_h_f`

English:
lemma isIso_fromNext_hom_h_f
  statement: {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
  proof: (F.exists_next n₁ hn₁).choose_spec.choose_spec i hi

中文:
引理 isIso_fromNext_hom_h_f
  结论: {n₀ : 整数} (F : CofFibFactorizationQuasiIsoLE f n₀)
  证明: (F.exists_next n₁ hn₁).choose_spec.choose_spec i hi

Depends on / 依赖: F.exists_next, choose_spec, choose_spec.choose_spec, exists_next
-/
lemma isIso_fromNext_hom_h_f {n₀ : Int} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : Int) (hn₁ : n₀ + 1 = n₁) (i : Int) (hi : i <= n₀) :
    IsIso ((F.fromNext n₁ hn₁).hom.h.f i) :=
  (F.exists_next n₁ hn₁).choose_spec.choose_spec i hi

/--
Definition of `sequence` / `sequence` 的定义

English:
definition sequence

中文:
定义 sequence
-/
noncomputable def sequence
    [Mono f] (n₀ : Int) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)] :
    forall (q : Nat), CofFibFactorizationQuasiIsoLE f (n₀ + q)
  | 0 => zero f n₀
  | q + 1 => (sequence n₀ q).next _ (by lia)

variable [Mono f] (n₀ : Int) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)]

/--
Definition of `toSequenceNext` / `toSequenceNext` 的定义

English:
definition toSequenceNext
  signature: (q : Nat)
  body: (sequence f n₀ q).fromNext _ (by lia)

中文:
定义 toSequenceNext
  签名: (q : 自然数)
  定义体: (sequence f n₀ q).fromNext _ (by lia)

Depends on / 依赖: fromNext, sequence
-/
noncomputable def toSequenceNext (q : Nat) :
    (sequence f n₀ (q + 1)).obj ⟶ (sequence f n₀ q).obj :=
  (sequence f n₀ q).fromNext _ (by lia)

end CofFibFactorizationQuasiIsoLE

variable [Mono f] (n₀ : Int) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)]

/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Natᵒᵖ ⥤ (cofFib f).FullSubcategory
  body: (Functor.ofSequence (fun q => (CofFibFactorizationQuasiIsoLE.toSequenceNext f n₀ q).op)).leftOp

中文:
定义 functor
  签名: : 自然数ᵒᵖ ⥤ (cofFib f).FullSubcategory
  定义体: (Functor.ofSequence (fun q => (CofFibFactorizationQuasiIsoLE.toSequenceNext f n₀ q).op)).leftOp

Depends on / 依赖: CofFibFactorizationQuasiIsoLE, CofFibFactorizationQuasiIsoLE.toSequenceNext, Functor, Functor.ofSequence, leftOp, ofSequence, toSequenceNext
-/
noncomputable def functor : Natᵒᵖ ⥤ (cofFib f).FullSubcategory :=
  (Functor.ofSequence (fun q => (CofFibFactorizationQuasiIsoLE.toSequenceNext f n₀ q).op)).leftOp

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_functor_map_hom_h_f` / 引理 `isIso_functor_map_hom_h_f`

English:
lemma isIso_functor_map_hom_h_f
  given: {q₁ q₂ : Nat} (hq : q₁ <= q₂) (i : Int) (hi : i <= n₀ + q₁)
  proof: by
  wlog hq' : q₁ + 1 = q₂ generalizing q₁ q₂
  · clear hq'
    obtain ⟨k, hk⟩ := Nat.le.dest hq
    induction k generalizing q₁ q₂ with
    | zero =>
      obtain rfl : q₁ = q₂ := by simpa using hk
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
        ObjectProperty.FullSubc

中文:
引理 isIso_functor_map_hom_h_f
  条件: {q₁ q₂ : 自然数} (hq : q₁ <= q₂) (i : 整数) (hi : i <= n₀ + q₁)
  证明: by
  wlog hq' : q₁ + 1 = q₂ generalizing q₁ q₂
  · clear hq'
    obtain ⟨k, hk⟩ := Nat.le.dest hq
    induction k generalizing q₁ q₂ with
    | zero =>
      obtain rfl : q₁ = q₂ := by simpa using hk
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
        ObjectProperty.FullSubc

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Factorisation, Factorisation.id_h, FullSubcategory, Functor, Functor.map_comp, IsIso.comp_isIso, Nat.le.dest, ObjectProperty, ObjectProperty.FullSubcategory.id_hom, comp_isIso, generalizing, homOfLE_comp, homOfLE_refl, id_f, id_h, id_hom, infer_instance, map_comp
-/
lemma isIso_functor_map_hom_h_f {q₁ q₂ : Nat} (hq : q₁ <= q₂) (i : Int) (hi : i <= n₀ + q₁) :
    IsIso (((functor f n₀).map (homOfLE hq).op).hom.h.f i) := by
  wlog hq' : q₁ + 1 = q₂ generalizing q₁ q₂
  · clear hq'
    obtain ⟨k, hk⟩ := Nat.le.dest hq
    induction k generalizing q₁ q₂ with
    | zero =>
      obtain rfl : q₁ = q₂ := by simpa using hk
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
        ObjectProperty.FullSubcategory.id_hom, Factorisation.id_h, id_f]
      infer_instance
    | succ k h =>
      rw [← homOfLE_comp (show q₁ <= q₁ + k by lia) (show q₁ + k <= q₂ by lia)]; rw [op_comp]; rw [Functor.map_comp]
      exact IsIso.comp_isIso' (this _ (by lia) (by lia)) (h _ (by lia) rfl)
  subst hq'
  dsimp [functor]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact CofFibFactorizationQuasiIsoLE.isIso_fromNext_hom_h_f _ _ _ _ hi

/--
Definition of `cochainComplexFunctor` / `cochainComplexFunctor` 的定义

English:
abbreviation cochainComplexFunctor
  signature: : Natᵒᵖ ⥤ CochainComplex C Int
  body: functor f n₀ ⋙ ObjectProperty.ι _ ⋙ Factorisation.forget

中文:
缩写 cochainComplexFunctor
  签名: : 自然数ᵒᵖ ⥤ CochainComplex C 整数
  定义体: functor f n₀ ⋙ ObjectProperty.ι _ ⋙ Factorisation.forget

Depends on / 依赖: Factorisation, Factorisation.forget, ObjectProperty, forget, functor
-/
noncomputable abbrev cochainComplexFunctor : Natᵒᵖ ⥤ CochainComplex C Int :=
  functor f n₀ ⋙ ObjectProperty.ι _ ⋙ Factorisation.forget

/--
lemma `isEventuallyConstantTo` / 引理 `isEventuallyConstantTo`

English:
lemma isEventuallyConstantTo
  given: (i : Int) (q : Nat) (h : i <= n₀ + q := by lia)
  proof: fun _ _ => isIso_functor_map_hom_h_f _ _ _ _ (by lia)

中文:
引理 isEventuallyConstantTo
  条件: (i : 整数) (q : 自然数) (h : i <= n₀ + q := by lia)
  证明: fun _ _ => isIso_functor_map_hom_h_f _ _ _ _ (by lia)

Depends on / 依赖: IsEventuallyConstantTo, cochainComplexFunctor, isIso_functor_map_hom_h_f
-/
lemma isEventuallyConstantTo (i : Int) (q : Nat) (h : i <= n₀ + q := by lia) :
    (cochainComplexFunctor f n₀ ⋙ eval _ _ i).IsEventuallyConstantTo (op q) :=
  fun _ _ => isIso_functor_map_hom_h_f _ _ _ _ (by lia)

instance (i : Int) : HasLimit (cochainComplexFunctor f n₀ ⋙ eval _ _ i) :=
  (isEventuallyConstantTo f n₀ i (n₀ - i).natAbs).hasLimit

/--
Definition of `mid` / `mid` 的定义

English:
abbreviation mid
  signature: : CochainComplex C Int
  body: limit (cochainComplexFunctor f n₀)

中文:
缩写 mid
  签名: : CochainComplex C 整数
  定义体: limit (cochainComplexFunctor f n₀)

Depends on / 依赖: cochainComplexFunctor
-/
noncomputable abbrev mid : CochainComplex C Int := limit (cochainComplexFunctor f n₀)

/--
Definition of `midπ` / `midπ` 的定义

English:
definition midπ
  signature: (q : Nat)
  body: limit.π _ (op q)

@[reassoc (attr := simp)]

中文:
定义 midπ
  签名: (q : 自然数)
  定义体: limit.π _ (op q)

@[reassoc (attr := simp)]
-/
noncomputable def midπ (q : Nat) : mid f n₀ ⟶ ((functor f n₀).obj (op q)).obj.mid :=
  limit.π _ (op q)

@[reassoc (attr := simp)]
/--
lemma `midπ_w` / 引理 `midπ_w`

English:
lemma midπ_w
  given: (q₁ q₂ : Nat) (hq : q₁ <= q₂)
  proof: limit.w _ _

@[reassoc (attr := simp)]

中文:
引理 midπ_w
  条件: (q₁ q₂ : 自然数) (hq : q₁ <= q₂)
  证明: limit.w _ _

@[reassoc (attr := simp)]

Depends on / 依赖: limit.w
-/
lemma midπ_w (q₁ q₂ : Nat) (hq : q₁ <= q₂) :
    midπ f n₀ q₂ ≫ ((functor f n₀).map (homOfLE hq).op).hom.h =
      midπ f n₀ q₁ :=
  limit.w _ _

@[reassoc (attr := simp)]
/--
lemma `midπ_w_f` / 引理 `midπ_w_f`

English:
lemma midπ_w_f
  given: (q₁ q₂ : Nat) (hq : q₁ <= q₂) (i : Int)
  proof: by
  rw [← midπ_w f n₀ q₁ q₂ hq]
  dsimp

中文:
引理 midπ_w_f
  条件: (q₁ q₂ : 自然数) (hq : q₁ <= q₂) (i : 整数)
  证明: by
  rw [← midπ_w f n₀ q₁ q₂ hq]
  dsimp
-/
lemma midπ_w_f (q₁ q₂ : Nat) (hq : q₁ <= q₂) (i : Int) :
    (midπ f n₀ q₂).f i ≫ ((functor f n₀).map (homOfLE hq).op).hom.h.f i =
      (midπ f n₀ q₁).f i := by
  rw [← midπ_w f n₀ q₁ q₂ hq]
  dsimp

/--
lemma `isIso_midπ_f` / 引理 `isIso_midπ_f`

English:
lemma isIso_midπ_f
  given: (q : Nat) (i : Int) (h : i <= n₀ + q := by lia)
  proof: isIso_π_f_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _) _ _
    (isEventuallyConstantTo f n₀ _ _)

中文:
引理 isIso_midπ_f
  条件: (q : 自然数) (i : 整数) (h : i <= n₀ + q := by lia)
  证明: isIso_π_f_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _) _ _
    (isEventuallyConstantTo f n₀ _ _)

Depends on / 依赖: isEventuallyConstantTo, isLimit, limit.isLimit
-/
lemma isIso_midπ_f (q : Nat) (i : Int) (h : i <= n₀ + q := by lia) :
    IsIso ((midπ f n₀ q).f i) :=
  isIso_π_f_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _) _ _
    (isEventuallyConstantTo f n₀ _ _)

/--
lemma `quasiIsoAt_midπ` / 引理 `quasiIsoAt_midπ`

English:
lemma quasiIsoAt_midπ
  given: (q : Nat) (i : Int) (h : i + 1 <= n₀ + q)
  proof: quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _)
    (i - 1) i (i + 1) (by simp) (by simp) _
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)

中文:
引理 quasiIsoAt_midπ
  条件: (q : 自然数) (i : 整数) (h : i + 1 <= n₀ + q)
  证明: quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _)
    (i - 1) i (i + 1) (by simp) (by simp) _
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)

Depends on / 依赖: isEventuallyConstantTo, isLimit, limit.isLimit
-/
lemma quasiIsoAt_midπ (q : Nat) (i : Int) (h : i + 1 <= n₀ + q) :
    QuasiIsoAt (midπ f n₀ q) i :=
  quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _)
    (i - 1) i (i + 1) (by simp) (by simp) _
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)
    (isEventuallyConstantTo f n₀ _ _)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : K ⟶ mid f n₀
  body: limit.lift _ (Cone.mk _ { app q := ((functor f n₀).obj q).obj.ι })

中文:
定义 ι
  签名: : K ⟶ mid f n₀
  定义体: limit.lift _ (Cone.mk _ { app q := ((functor f n₀).obj q).obj.ι })

Depends on / 依赖: Cone.mk, functor, limit.lift
-/
noncomputable def ι : K ⟶ mid f n₀ :=
  limit.lift _ (Cone.mk _ { app q := ((functor f n₀).obj q).obj.ι })

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_midπ` / 引理 `ι_midπ`

English:
lemma ι_midπ
  given: (q : Nat)
  statement: ι f n₀ ≫ midπ f n₀ q = ((functor f n₀).obj (op q)).obj.ι
  proof: by
  simp [ι, midπ]

@[reassoc (attr := simp)]

中文:
引理 ι_midπ
  条件: (q : 自然数)
  结论: ι f n₀ ≫ midπ f n₀ q = ((functor f n₀).obj (op q)).obj.ι
  证明: by
  simp [ι, midπ]

@[reassoc (attr := simp)]
-/
lemma ι_midπ (q : Nat) : ι f n₀ ≫ midπ f n₀ q = ((functor f n₀).obj (op q)).obj.ι := by
  simp [ι, midπ]

@[reassoc (attr := simp)]
/--
lemma `ι_midπ_f` / 引理 `ι_midπ_f`

English:
lemma ι_midπ_f
  given: (q : Nat) (i : Int)
  statement: (ι f n₀).f i ≫ (midπ f n₀ q).f i =
  proof: by
  rw [← ι_midπ]
  dsimp

中文:
引理 ι_midπ_f
  条件: (q : 自然数) (i : 整数)
  结论: (ι f n₀).f i ≫ (midπ f n₀ q).f i =
  证明: by
  rw [← ι_midπ]
  dsimp
-/
lemma ι_midπ_f (q : Nat) (i : Int) : (ι f n₀).f i ≫ (midπ f n₀ q).f i =
    ((functor f n₀).obj (op q)).obj.ι.f i := by
  rw [← ι_midπ]
  dsimp

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : mid f n₀ ⟶ L
  body: midπ f n₀ 0 ≫ ((functor f n₀).obj (op 0)).obj.π

@[reassoc (attr := simp)]

中文:
定义 π
  签名: : mid f n₀ ⟶ L
  定义体: midπ f n₀ 0 ≫ ((functor f n₀).obj (op 0)).obj.π

@[reassoc (attr := simp)]

Depends on / 依赖: functor
-/
noncomputable def π : mid f n₀ ⟶ L := midπ f n₀ 0 ≫ ((functor f n₀).obj (op 0)).obj.π

@[reassoc (attr := simp)]
/--
lemma `ι_π` / 引理 `ι_π`

English:
lemma ι_π
  statement: ι f n₀ ≫ π f n₀ = f
  proof: by
  simp [π]

@[reassoc (attr := simp)]

中文:
引理 ι_π
  结论: ι f n₀ ≫ π f n₀ = f
  证明: by
  simp [π]

@[reassoc (attr := simp)]
-/
lemma ι_π : ι f n₀ ≫ π f n₀ = f := by
  simp [π]

@[reassoc (attr := simp)]
/--
lemma `midπ_π` / 引理 `midπ_π`

English:
lemma midπ_π
  given: (q : Nat)
  statement: midπ f n₀ q ≫ ((functor f n₀).obj (op q)).obj.π = π f n₀
  proof: by
  simp [π, ← midπ_w_assoc f n₀ 0 q (by lia)]

@[reassoc (attr := simp)]

中文:
引理 midπ_π
  条件: (q : 自然数)
  结论: midπ f n₀ q ≫ ((functor f n₀).obj (op q)).obj.π = π f n₀
  证明: by
  simp [π, ← midπ_w_assoc f n₀ 0 q (by lia)]

@[reassoc (attr := simp)]
-/
lemma midπ_π (q : Nat) : midπ f n₀ q ≫ ((functor f n₀).obj (op q)).obj.π = π f n₀ := by
  simp [π, ← midπ_w_assoc f n₀ 0 q (by lia)]

@[reassoc (attr := simp)]
/--
lemma `midπ_π_f` / 引理 `midπ_π_f`

English:
lemma midπ_π_f
  given: (q : Nat) (i : Int)
  proof: by
  rw [← midπ_π f n₀ q]
  dsimp

中文:
引理 midπ_π_f
  条件: (q : 自然数) (i : 整数)
  证明: by
  rw [← midπ_π f n₀ q]
  dsimp
-/
lemma midπ_π_f (q : Nat) (i : Int) :
    (midπ f n₀ q).f i ≫ ((functor f n₀).obj (op q)).obj.π.f i = (π f n₀).f i := by
  rw [← midπ_π f n₀ q]
  dsimp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (mid f n₀).IsStrictlyGE (n₀ + 1)
  body: by
  rw [isStrictlyGE_iff]
  intro i hi
  have := isIso_midπ_f f n₀ 0 i
  exact (L.isZero_of_isStrictlyGE (n₀ + 1) i).of_iso (asIso ((midπ f n₀ 0).f i))

中文:
实例 :
  签名: (mid f n₀).IsStrictlyGE (n₀ + 1)
  定义体: by
  rw [isStrictlyGE_iff]
  intro i hi
  have := isIso_midπ_f f n₀ 0 i
  exact (L.isZero_of_isStrictlyGE (n₀ + 1) i).of_iso (asIso ((midπ f n₀ 0).f i))

Depends on / 依赖: L.isZero_of_isStrictlyGE, isStrictlyGE_iff, isZero_of_isStrictlyGE, of_iso
-/
instance : (mid f n₀).IsStrictlyGE (n₀ + 1) := by
  rw [isStrictlyGE_iff]
  intro i hi
  have := isIso_midπ_f f n₀ 0 i
  exact (L.isZero_of_isStrictlyGE (n₀ + 1) i).of_iso (asIso ((midπ f n₀ 0).f i))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (ι f n₀)
  body: HomologicalComplex.mono_of_mono_f _ (fun i => by
    obtain ⟨q, _⟩ : exists (q : Nat), IsIso ((midπ f n₀ q).f i) :=
      ⟨(i - n₀).natAbs, isIso_midπ_f f n₀ _ i⟩
    exact mono_of_mono_fac (ι_midπ_f f n₀ q i))

中文:
实例 :
  签名: Mono (ι f n₀)
  定义体: HomologicalComplex.mono_of_mono_f _ (fun i => by
    obtain ⟨q, _⟩ : exists (q : Nat), IsIso ((midπ f n₀ q).f i) :=
      ⟨(i - n₀).natAbs, isIso_midπ_f f n₀ _ i⟩
    exact mono_of_mono_fac (ι_midπ_f f n₀ q i))

Depends on / 依赖: HomologicalComplex, HomologicalComplex.mono_of_mono_f, mono_of_mono_f, mono_of_mono_fac, natAbs
-/
instance : Mono (ι f n₀) :=
  HomologicalComplex.mono_of_mono_f _ (fun i => by
    obtain ⟨q, _⟩ : exists (q : Nat), IsIso ((midπ f n₀ q).f i) :=
      ⟨(i - n₀).natAbs, isIso_midπ_f f n₀ _ i⟩
    exact mono_of_mono_fac (ι_midπ_f f n₀ q i))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (ι f n₀)
  body: by
    obtain ⟨q, hq⟩ : exists (q : Nat), i + 1 <= n₀ + q := ⟨(i + 1 - n₀).natAbs, by lia⟩
    have := quasiIsoAt_midπ f n₀ q i hq
    rw [← quasiIsoAt_iff_comp_right _ (midπ f n₀ q)]; rw [ι_midπ]
    exact (CofFibFactorizationQuasiIsoLE.sequence f n₀ q).property i (by lia)

中文:
实例 :
  签名: QuasiIso (ι f n₀)
  定义体: by
    obtain ⟨q, hq⟩ : exists (q : Nat), i + 1 <= n₀ + q := ⟨(i + 1 - n₀).natAbs, by lia⟩
    have := quasiIsoAt_midπ f n₀ q i hq
    rw [← quasiIsoAt_iff_comp_right _ (midπ f n₀ q)]; rw [ι_midπ]
    exact (CofFibFactorizationQuasiIsoLE.sequence f n₀ q).property i (by lia)

Depends on / 依赖: CofFibFactorizationQuasiIsoLE, CofFibFactorizationQuasiIsoLE.sequence, natAbs, property, quasiIsoAt_iff_comp_right, sequence
-/
instance : QuasiIso (ι f n₀) where
  quasiIsoAt i := by
    obtain ⟨q, hq⟩ : exists (q : Nat), i + 1 <= n₀ + q := ⟨(i + 1 - n₀).natAbs, by lia⟩
    have := quasiIsoAt_midπ f n₀ q i hq
    rw [← quasiIsoAt_iff_comp_right _ (midπ f n₀ q)]; rw [ι_midπ]
    exact (CofFibFactorizationQuasiIsoLE.sequence f n₀ q).property i (by lia)

/--
lemma `degreewiseEpiWithInjectiveKernel_π` / 引理 `degreewiseEpiWithInjectiveKernel_π`

English:
lemma degreewiseEpiWithInjectiveKernel_π
  statement: degreewiseEpiWithInjectiveKernel (π f n₀)
  proof: by
  intro i
  obtain ⟨q, hq⟩ : exists (q : Nat), i <= n₀ + q := ⟨(i - n₀).natAbs, by lia⟩
  rw [← midπ_π_f f n₀ q]
  have := isIso_midπ_f f n₀ q i
  exact MorphismProperty.comp_mem _ _ _
    (epiWithInjectiveKernel_of_iso _)
    ((CofFibFactorizationQuasiIsoLE.sequence f n₀ q).obj.property.2 i)

中文:
引理 degreewiseEpiWithInjectiveKernel_π
  结论: degreewiseEpiWithInjectiveKernel (π f n₀)
  证明: by
  intro i
  obtain ⟨q, hq⟩ : exists (q : Nat), i <= n₀ + q := ⟨(i - n₀).natAbs, by lia⟩
  rw [← midπ_π_f f n₀ q]
  have := isIso_midπ_f f n₀ q i
  exact MorphismProperty.comp_mem _ _ _
    (epiWithInjectiveKernel_of_iso _)
    ((CofFibFactorizationQuasiIsoLE.sequence f n₀ q).obj.property.2 i)

Depends on / 依赖: CofFibFactorizationQuasiIsoLE, CofFibFactorizationQuasiIsoLE.sequence, MorphismProperty, MorphismProperty.comp_mem, comp_mem, epiWithInjectiveKernel_of_iso, natAbs, obj.property, property, sequence
-/
lemma degreewiseEpiWithInjectiveKernel_π : degreewiseEpiWithInjectiveKernel (π f n₀) := by
  intro i
  obtain ⟨q, hq⟩ : exists (q : Nat), i <= n₀ + q := ⟨(i - n₀).natAbs, by lia⟩
  rw [← midπ_π_f f n₀ q]
  have := isIso_midπ_f f n₀ q i
  exact MorphismProperty.comp_mem _ _ _
    (epiWithInjectiveKernel_of_iso _)
    ((CofFibFactorizationQuasiIsoLE.sequence f n₀ q).obj.property.2 i)

end cm5a_cof

variable [EnoughInjectives C]

open cm5a_cof in
public lemma cm5a_cof (n : Int) [K.IsStrictlyGE n] [L.IsStrictlyGE n] [Mono f] :
    exists (K' : CochainComplex C Int) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  obtain ⟨n, rfl⟩ : exists (q : Int), n = q + 1 := ⟨n - 1, by simp⟩
  exact ⟨mid f n, inferInstance, ι f n, π f n, inferInstance,
    inferInstance, degreewiseEpiWithInjectiveKernel_π f n, ι_π f n⟩

public lemma cm5a (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    exists (K' : CochainComplex C Int) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  have : K.IsStrictlyGE n := K.isStrictlyGE_of_ge n (n + 1) (by lia)
  obtain ⟨L', _, i, p, _, hp, _, rfl⟩ := cm5b f n
  obtain ⟨K', _, ι, π, _, _, hπ, rfl⟩ := cm5a_cof i n
  exact ⟨K', inferInstance, ι, π ≫ p, inferInstance, inferInstance,
    MorphismProperty.comp_mem _ _ _ hπ hp, by simp⟩

open ZeroObject

variable (K)

public lemma exists_mono_quasiIso_injective (n₀ n₁ : Int) (h : n₀ + 1 = n₁ := by lia)
    [K.IsStrictlyGE n₁] :
    exists (L : CochainComplex C Int) (i : K ⟶ L) (_hi : Mono i) (_hi' : QuasiIso i)
      (_ : forall (n : Int), Injective (L.X n)), L.IsStrictlyGE n₀ := by
  have : K.IsStrictlyGE (n₀ + 1) := by rw [h]; infer_instance
  obtain ⟨L, hL, i, p, hi, hi', hp, _⟩ := cm5a (0 : K ⟶ 0) n₀
  exact ⟨L, i, hi, hi', (degreewiseEpiWithInjectiveKernel_iff_of_isZero p
    (Limits.isZero_zero _)).1 hp, hL⟩

public lemma exists_quasiIso_injective (n : Int) [K.IsStrictlyGE n] :
    exists (L : CochainComplex C Int) (i : K ⟶ L) (_hi' : QuasiIso i)
      (_hL : forall (n : Int), Injective (L.X n)), L.IsStrictlyGE n := by
  /- The proof proceeds by first applying `exists_mono_quasiIso_injective` in order to
  obtain a monomorphism `K ⟶ L` that is also a quasi-isomorphism
  with `L` consisting of injective objects and `L` lying in degrees `≥ n - 1`.
  Then, as it is quasi-isomorphic to `K`, the cochain complex `L` is cohomologically
  in degrees `≥ n`, so that the composition `K ⟶ L ⟶ L.truncGE n` is a quasi-isomorphism.
  In order to conclude, one needs to show that `(L.truncGE n).X n` is injective,
  i.e. that `L.opcycles n` is injective. -/
  have : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  obtain ⟨L, i, _, _, hL, _⟩ := exists_mono_quasiIso_injective K (n - 1) n (by simp)
  have : L.IsGE n := by
    have hK : K.IsGE n := inferInstance
    rw [← DerivedCategory.isGE_Q_obj_iff] at hK ⊢
    exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map i)) n
  have : QuasiIso (L.πTruncGE n) := (L.quasiIso_πTruncGE_iff n).mpr inferInstance
  have : Injective (L.opcycles n) :=
    L.injective_opcycles (n - 1) n (L.exactAt_of_isGE n (n - 1))
  -- note: this `i ≫ L.πTruncGE n` is a mono in degrees > n, but it may not be in degree n
  refine ⟨L.truncGE n, i ≫ L.πTruncGE n, inferInstance, fun q => ?_, inferInstance⟩
  obtain h | rfl | h := lt_trichotomy q n
  · exact (isZero_of_isStrictlyGE _ n _ h).injective
  · exact Injective.of_iso (L.truncGEXIsoOpcycles q).symm inferInstance
  · exact Injective.of_iso (L.truncGEXIso n q h).symm (hL q)

end CochainComplex.Plus.modelCategoryQuillen
