/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Factorizations.Basic

/-!
# Factorization lemma

Let `C` be an abelian category with enough injectives. We show that
any morphism `f : K ⟶ L` between bounded below cochain complexes in `C`
can be factored as `i ≫ p` where `i : K ⟶ L'` is a monomorphism (with
`L'` bounded below) and `p : L' ⟶ L` a quasi-isomorphism that is an epimorphism
with a degreewise injective kernel. (This is part of the factorization axiom CM5
for a model category structure on bounded below cochain complexes (TODO @joelriou).)

-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C Int} (f : K ⟶ L)

namespace cm5b

variable (K L) in
/-- Given a cochain complex `K`, this is a cochain complex `I K` with
zero differentials which in degree `n` consists of the injective
object `Injective.under (K.X n)`. -/
@[simps]
/--
Definition of `I` / `I` 的定义

English:
definition I
  signature: : CochainComplex C Int where
  body: Injective.under (K.X n)
  d _ _ := 0

中文:
定义 I
  签名: : CochainComplex C 整数 where
  定义体: Injective.under (K.X n)
  d _ _ := 0

Depends on / 依赖: Injective, Injective.under
-/
noncomputable def I : CochainComplex C Int where
  X n := Injective.under (K.X n)
  d _ _ := 0

set_option backward.defeqAttrib.useBackward true in
instance (n : Int) : Injective ((I K).X n) := by
  dsimp
  infer_instance

instance (n : Int) [K.IsStrictlyGE n] : (I K).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact Injective.isZero_under _ (K.isZero_of_isStrictlyGE n i hi)

instance (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    (mappingCone (𝟙 (I K)) ⊞ L).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up Int) i).mapBiprod _ _)
  simp only [HomologicalComplex.eval_obj, biprod_isZero_iff, mappingCone.isZero_X_iff, I_X]
  refine ⟨⟨?_, ?_⟩, L.isZero_of_isStrictlyGE n i hi⟩
  all_goals exact (I K).isZero_of_isStrictlyGE (n + 1) _

variable (K L) in
/--
Definition of `p` / `p` 的定义

English:
abbreviation p
  signature: : mappingCone (𝟙 (I K)) ⊞ L ⟶ L
  body: biprod.snd

中文:
缩写 p
  签名: : mappingCone (𝟙 (I K)) ⊞ L ⟶ L
  定义体: biprod.snd

Depends on / 依赖: biprod, biprod.snd
-/
noncomputable abbrev p : mappingCone (𝟙 (I K)) ⊞ L ⟶ L := biprod.snd

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `i` / `i` 的定义

English:
definition i
  signature: : K ⟶ mappingCone (𝟙 (I K)) ⊞ L
  body: biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq (p + 1) (p + 1) (by lia) rfl]))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι 

中文:
定义 i
  签名: : K ⟶ mappingCone (𝟙 (I K)) ⊞ L
  定义体: biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq (p + 1) (p + 1) (by lia) rfl]))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι 

Depends on / 依赖: Cochain, Cocycle, HomComplex, HomComplex.Cochain.mk, HomComplex.Cochain.ofHoms, HomComplex.Cocycle.mk, Injective, biprod, biprod.lift, cat_disch, mappingCone, mappingCone.lift, ofHoms
-/
noncomputable def i : K ⟶ mappingCone (𝟙 (I K)) ⊞ L :=
  biprod.lift (mappingCone.lift _
    (HomComplex.Cocycle.mk (HomComplex.Cochain.mk (fun p q _ => K.d p q ≫ Injective.ι _)) 2
      (by lia) (by
        ext p q hpq
        simp [HomComplex.δ_v 1 2 (by lia) _ p q hpq (p + 1) (p + 1) (by lia) rfl]))
    (HomComplex.Cochain.ofHoms (fun n => Injective.ι _)) (by cat_disch)) f

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `i_f_comp` / 引理 `i_f_comp`

English:
lemma i_f_comp
  given: (n : Int)
  statement: (i f).f n ≫
  proof: by
  simp [i]

中文:
引理 i_f_comp
  条件: (n : 整数)
  结论: (i f).f n ≫
  证明: by
  simp [i]
-/
lemma i_f_comp (n : Int) : (i f).f n ≫
    (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _).f n ≫
      (mappingCone.snd (𝟙 (I K))).v n n (add_zero n) = Injective.ι (K.X n) := by
  simp [i]

set_option backward.isDefEq.respectTransparency false in
instance (n : Int) : Mono ((i f).f n) := mono_of_mono_fac (i_f_comp f n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (i f)
  body: HomologicalComplex.mono_of_mono_f (i f) inferInstance

@[reassoc (attr := simp)]

中文:
实例 :
  签名: Mono (i f)
  定义体: HomologicalComplex.mono_of_mono_f (i f) inferInstance

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.mono_of_mono_f, mono_of_mono_f
-/
instance : Mono (i f) := HomologicalComplex.mono_of_mono_f (i f) inferInstance

@[reassoc (attr := simp)]
/--
lemma `fac` / 引理 `fac`

English:
lemma fac
  statement: i f ≫ p K L = f
  proof: by simp [i]

中文:
引理 fac
  结论: i f ≫ p K L = f
  证明: by simp [i]
-/
lemma fac : i f ≫ p K L = f := by simp [i]

instance (n : Int) : Injective ((mappingCone (𝟙 (I K))).X n) :=
  Injective.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 (I K)) n (n + 1) rfl).symm
    inferInstance

variable (K L) in
/--
lemma `degreewiseEpiWithInjectiveKernel_p` / 引理 `degreewiseEpiWithInjectiveKernel_p`

English:
lemma degreewiseEpiWithInjectiveKernel_p
  proof: by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp 

中文:
引理 degreewiseEpiWithInjectiveKernel_p
  证明: by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp 

Depends on / 依赖: HomologicalComplex, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, add_f_apply, all_goals, biprod, biprod.fst, biprod.inl, biprod.inr, comp_f, epiWithInjectiveKernel_iff, mappingCone
-/
lemma degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (p K L) := by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp [← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply]

variable (K L) in
/--
Definition of `homotopyEquiv` / `homotopyEquiv` 的定义

English:
definition homotopyEquiv
  signature: : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  body: p K L
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 (I K)))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mapping

中文:
定义 homotopyEquiv
  签名: : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  定义体: p K L
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 (I K)))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mapping
-/
noncomputable def homotopyEquiv : HomotopyEquiv (mappingCone (𝟙 (I K)) ⊞ L) L where
  hom := p K L
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 (I K)))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ mappingCone (𝟙 (I K)) ⊞ L)).compLeft
        (biprod.fst : mappingCone (𝟙 (I K)) ⊞ L ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    (Homotopy.ofEq (by simp [p])).trans (h₂.symm.trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (p K L)
  body: (homotopyEquiv K L).quasiIso_hom

中文:
实例 :
  签名: QuasiIso (p K L)
  定义体: (homotopyEquiv K L).quasiIso_hom

Depends on / 依赖: homotopyEquiv, quasiIso_hom
-/
instance : QuasiIso (p K L) := (homotopyEquiv K L).quasiIso_hom

end cm5b

/--
lemma `cm5b` / 引理 `cm5b`

English:
lemma cm5b
  given: (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n]
  proof: ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    cm5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

中文:
引理 cm5b
  条件: (n : 整数) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n]
  证明: ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    cm5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

Depends on / 依赖: cm5b.degreewiseEpiWithInjectiveKernel_p, cm5b.i, cm5b.p, degreewiseEpiWithInjectiveKernel_p, infer_instance
-/
lemma cm5b (n : Int) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    exists (L' : CochainComplex C Int) (_hL' : L'.IsStrictlyGE n)
      (i : K ⟶ L') (p : L' ⟶ L) (_hi : Mono i)
      (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p),
      i ≫ p = f :=
  ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    cm5b.degreewiseEpiWithInjectiveKernel_p K L, inferInstance, by simp⟩

end CochainComplex
