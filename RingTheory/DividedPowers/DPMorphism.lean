/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DividedPowers.Basic

/-! # Divided power morphisms

Let `A` and `B` be commutative (semi)rings, let `I` be an ideal of `A` and let `J` be an ideal of
`B`. Given divided power structures on `I` and `J`, a ring morphism `A →+* B` is a *divided
power morphism* if it is compatible with these divided power structures.

## Main definitions

* `DividedPowers.IsDPMorphism` : given divided power structures on the `A`-ideal `I` and the
  `B`-ideal `J`, a ring morphism `A →+* B` is a divided power morphism if it is compatible with
  these divided power structures.
* `DividedPowers.DPMorphism` : a bundled version of `IsDPMorphism`.
* `DividedPowers.ideal_from_ringHom` : given a ring homomorphism `A →+* B` and ideals `I ⊆ A` and
  `J ⊆ B` such that `I.map f ≤ J`, this is the `A`-ideal on which
  `f (hI.dpow n x) = hJ.dpow n (f x)`.
* `DividedPowers.DPMorphism.fromGens` : the `DPMorphism` induced by a ring morphism, given that
  divided powers are compatible on a generating set.

## Main results

* `DividedPowers.dpow_eq_from_gens` : if two divided power structures on an ideal `I` agree on a
  generating set, then they are equal.

## Implementation remarks

We provided both a bundled and an unbundled definition of divided power morphisms. For developing
the basic theory, the unbundled version `IsDPMorphism` is more convenient. However, we anticipate
that the bundled version `DPMorphism` will be better for the development of crystalline
cohomology.

## References

* [P. Berthelot, *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus, *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby, *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby, *Les algèbres à puissances dividées*][Roby-1965]
-/

@[expose] public section

open Ideal Set SetLike

namespace DividedPowers

/--
Definition of `IsDPMorphism` / `IsDPMorphism` 的定义

English:
structure IsDPMorphism
  parameters: {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  axioms and operations (2):
    - ideal_comp : I.map f <= J
    - dpow_comp : forall {n : Nat}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a)

中文:
结构 是DP态射
  参数: {A B : 类型} [交换半环 A] [交换半环 B] {I : 理想 A} {J : 理想 B}
  公理与运算 (2 个):
    - ideal_comp : I.map f <= J
    - dpow_comp : 对任意 {n : 自然数}, 对任意 a in I, hJ.dpow n (f a) = f (hI.dpow n a)
-/
structure IsDPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A ->+* B) : Prop where
  ideal_comp : I.map f <= J
  dpow_comp : forall {n : Nat}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a)

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

/--
lemma `isDPMorphism_def` / 引理 `isDPMorphism_def`

English:
lemma isDPMorphism_def
  given: (f : A ->+* B)
  proof: ⟨fun h => ⟨h.ideal_comp, h.dpow_comp⟩, fun ⟨h1, h2⟩ => IsDPMorphism.mk h1 h2⟩

中文:
引理 isDPMorphism_def
  条件: (f : A ->+* B)
  证明: ⟨fun h => ⟨h.ideal_comp, h.dpow_comp⟩, fun ⟨h1, h2⟩ => IsDPMorphism.mk h1 h2⟩

Depends on / 依赖: IsDPMorphism, IsDPMorphism.mk, dpow_comp, h.dpow_comp, h.ideal_comp, ideal_comp
-/
lemma isDPMorphism_def (f : A ->+* B) :
    IsDPMorphism hI hJ f ↔ I.map f <= J ∧ forall {n}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  ⟨fun h => ⟨h.ideal_comp, h.dpow_comp⟩, fun ⟨h1, h2⟩ => IsDPMorphism.mk h1 h2⟩

/--
lemma `isDPMorphism_iff` / 引理 `isDPMorphism_iff`

English:
lemma isDPMorphism_iff
  given: (f : A ->+* B)
  proof: by
  rw [isDPMorphism_def]; rw [and_congr_right_iff]
  refine fun hIJ => ⟨fun H n _ => H, fun H n => ?_⟩
  by_cases hn : n = 0
  · intro _ ha
    rw [hn]; rw [hI.dpow_zero ha]; rw [hJ.dpow_zero (hIJ (mem_map_of_mem f ha))]; rw [map_one]
  · exact H n hn

中文:
引理 isDPMorphism_iff
  条件: (f : A ->+* B)
  证明: by
  rw [isDPMorphism_def]; rw [and_congr_right_iff]
  refine fun hIJ => ⟨fun H n _ => H, fun H n => ?_⟩
  by_cases hn : n = 0
  · intro _ ha
    rw [hn]; rw [hI.dpow_zero ha]; rw [hJ.dpow_zero (hIJ (mem_map_of_mem f ha))]; rw [map_one]
  · exact H n hn

Depends on / 依赖: and_congr_right_iff, dpow_zero, hI.dpow_zero, hJ.dpow_zero, isDPMorphism_def, map_one, mem_map_of_mem
-/
lemma isDPMorphism_iff (f : A ->+* B) :
    IsDPMorphism hI hJ f ↔ I.map f <= J ∧ forall n != 0, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a) := by
  rw [isDPMorphism_def]; rw [and_congr_right_iff]
  refine fun hIJ => ⟨fun H n _ => H, fun H n => ?_⟩
  by_cases hn : n = 0
  · intro _ ha
    rw [hn]; rw [hI.dpow_zero ha]; rw [hJ.dpow_zero (hIJ (mem_map_of_mem f ha))]; rw [map_one]
  · exact H n hn

namespace IsDPMorphism

variable {hI hJ} {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K)

/--
theorem `map_dpow` / 定理 `map_dpow`

English:
theorem map_dpow
  given: {f : A ->+* B} (hf : IsDPMorphism hI hJ f) {n : Nat} {a : A} (ha : a in I)
  proof: (hf.2 a ha).symm

中文:
定理 map_dpow
  条件: {f : A ->+* B} (hf : 是DP态射 hI hJ f) {n : 自然数} {a : A} (ha : a in I)
  证明: (hf.2 a ha).symm
-/
theorem map_dpow {f : A ->+* B} (hf : IsDPMorphism hI hJ f) {n : Nat} {a : A} (ha : a in I) :
    f (hI.dpow n a) = hJ.dpow n (f a) := (hf.2 a ha).symm

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f : A ->+* B} {g : B ->+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f)
  proof: by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha]; rw [hg.2]
  exact hf.1 (mem_map_of_mem f ha)

中文:
定理 comp
  条件: {f : A ->+* B} {g : B ->+* C} (hg : 是DP态射 hJ hK g) (hf : 是DP态射 hI hJ f)
  证明: by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha]; rw [hg.2]
  exact hf.1 (mem_map_of_mem f ha)

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_comp, coe_comp, comp_apply, le_trans, map_map, map_mono, mem_map_of_mem
-/
theorem comp {f : A ->+* B} {g : B ->+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
    IsDPMorphism hI hK (g.comp f) := by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha => ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha]; rw [hg.2]
  exact hf.1 (mem_map_of_mem f ha)

end IsDPMorphism

/-- A bundled divided power morphism between rings endowed with divided power structures. -/
@[ext]
/--
Definition of `DPMorphism` / `DPMorphism` 的定义

English:
structure DPMorphism
  parameters: {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  extends: RingHom A B
  axioms and operations (2):
    - ideal_comp : I.map toRingHom <= J
    - dpow_comp : forall {n : Nat}, forall a in I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)

中文:
结构 DP态射
  参数: {A B : 类型} [交换半环 A] [交换半环 B] {I : 理想 A} {J : 理想 B}
  继承: 环态射 A B
  公理与运算 (2 个):
    - ideal_comp : I.map toRingHom <= J
    - dpow_comp : 对任意 {n : 自然数}, 对任意 a in I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)
-/
structure DPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) extends RingHom A B where
  ideal_comp : I.map toRingHom <= J
  dpow_comp : forall {n : Nat}, forall a in I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)

namespace DPMorphism

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (DPMorphism hI hJ) A B where
  body: h.toRingHom
  coe_injective h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh'; ext; rw [hh']

中文:
实例 instFunLike
  签名: : 函数状 (DP态射 hI hJ) A B where
  定义体: h.toRingHom
  coe_injective h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh'; ext; rw [hh']

Depends on / 依赖: h.toRingHom, toRingHom
-/
instance instFunLike : FunLike (DPMorphism hI hJ) A B where
  coe h := h.toRingHom
  coe_injective h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh'; ext; rw [hh']

/--
Instance `coe_ringHom` / 实例 `coe_ringHom`

English:
instance coe_ringHom
  signature: : CoeOut (DPMorphism hI hJ) (A ->+* B)
  body: ⟨DPMorphism.toRingHom⟩

中文:
实例 coe_ringHom
  签名: : CoeOut (DP态射 hI hJ) (A ->+* B)
  定义体: ⟨DPMorphism.toRingHom⟩

Depends on / 依赖: DPMorphism, DPMorphism.toRingHom, toRingHom
-/
instance coe_ringHom : CoeOut (DPMorphism hI hJ) (A ->+* B) := ⟨DPMorphism.toRingHom⟩

/--
theorem `coe_toRingHom` / 定理 `coe_toRingHom`

English:
theorem coe_toRingHom
  given: {f : DPMorphism hI hJ}
  statement: ⇑(f : A ->+* B) = f
  proof: rfl

中文:
定理 coe_toRingHom
  条件: {f : DP态射 hI hJ}
  结论: ⇑(f : A ->+* B) = f
  证明: rfl
-/
@[simp] theorem coe_toRingHom {f : DPMorphism hI hJ} : ⇑(f : A ->+* B) = f := rfl

/--
lemma `toRingHom_apply` / 引理 `toRingHom_apply`

English:
lemma toRingHom_apply
  given: {f : DPMorphism hI hJ} {a : A}
  statement: f.toRingHom a = f a
  proof: rfl

中文:
引理 toRingHom_apply
  条件: {f : DP态射 hI hJ} {a : A}
  结论: f.toRingHom a = f a
  证明: rfl
-/
@[simp] lemma toRingHom_apply {f : DPMorphism hI hJ} {a : A} : f.toRingHom a = f a := rfl

variable {hI hJ}

/--
lemma `isDPMorphism` / 引理 `isDPMorphism`

English:
lemma isDPMorphism
  given: (f : DPMorphism hI hJ)
  statement: IsDPMorphism hI hJ f.toRingHom
  proof: ⟨f.ideal_comp, f.dpow_comp⟩

中文:
引理 isDPMorphism
  条件: (f : DP态射 hI hJ)
  结论: 是DP态射 hI hJ f.toRingHom
  证明: ⟨f.ideal_comp, f.dpow_comp⟩

Depends on / 依赖: dpow_comp, f.dpow_comp, f.ideal_comp, ideal_comp
-/
lemma isDPMorphism (f : DPMorphism hI hJ) : IsDPMorphism hI hJ f.toRingHom :=
  ⟨f.ideal_comp, f.dpow_comp⟩

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {f : A ->+* B} (hf : IsDPMorphism hI hJ f)
  body: ⟨f, hf.1, hf.2⟩

中文:
定义 mk'
  签名: {f : A ->+* B} (hf : 是DP态射 hI hJ f)
  定义体: ⟨f, hf.1, hf.2⟩
-/
def mk' {f : A ->+* B} (hf : IsDPMorphism hI hJ f) : DPMorphism hI hJ :=
  ⟨f, hf.1, hf.2⟩

variable (hI hJ)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `_root_.DividedPowers.ideal_from_ringHom` / `_root_.DividedPowers.ideal_from_ringHom` 的定义

English:
definition _root_.DividedPowers.ideal_from_ringHom
  signature: {f : A ->+* B} (hf : I.map f <= J)
  body: {x in I | forall n : Nat, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := fun hx hy => by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    refine ⟨I.add_mem hx.1 hy.1, fun n => ?_⟩
    rw [hI.dpow_add hx.1 hy.1]; rw [map_sum]; rw [hJ.dpow_add (hf (mem_map_of_mem f hx.1)) (hf (mem_m

中文:
定义 _root_.DividedPowers.ideal_from_ringHom
  签名: {f : A ->+* B} (hf : I.map f <= J)
  定义体: {x in I | forall n : Nat, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := fun hx hy => by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    refine ⟨I.add_mem hx.1 hy.1, fun n => ?_⟩
    rw [hI.dpow_add hx.1 hy.1]; rw [map_sum]; rw [hJ.dpow_add (hf (mem_map_of_mem f hx.1)) (hf (mem_m

Depends on / 依赖: hI.dpow, hJ.dpow
-/
def _root_.DividedPowers.ideal_from_ringHom {f : A ->+* B} (hf : I.map f <= J) : Ideal A where
  carrier := {x in I | forall n : Nat, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := fun hx hy => by
    simp only [mem_ofPred_eq, map_add] at hx hy ⊢
    refine ⟨I.add_mem hx.1 hy.1, fun n => ?_⟩
    rw [hI.dpow_add hx.1 hy.1]; rw [map_sum]; rw [hJ.dpow_add (hf (mem_map_of_mem f hx.1)) (hf (mem_map_of_mem f hy.1))]
    apply congr_arg
    ext k
    rw [map_mul]; rw [hx.2]; rw [hy.2]
  zero_mem' := by
    simp only [mem_ofPred_eq, Submodule.zero_mem, map_zero, true_and]
    intro n
    induction n with
    | zero => rw [hI.dpow_zero I.zero_mem, hJ.dpow_zero J.zero_mem, map_one]
    | succ n => rw [hI.dpow_eval_zero n.succ_ne_zero, hJ.dpow_eval_zero n.succ_ne_zero, map_zero]
  smul_mem' := fun r x hx => by
    refine ⟨I.smul_mem r hx.1, (fun n => ?_)⟩
    rw [smul_eq_mul]; rw [hI.dpow_mul hx.1]; rw [map_mul]; rw [map_mul]; rw [map_pow]; rw [hJ.dpow_mul (hf (mem_map_of_mem f hx.1))]; rw [hx.2 n]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `fromGens` / `fromGens` 的定义

English:
definition fromGens
  signature: {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <= J)
  body: f
  ideal_comp := hf
  dpow_comp {n} x hx := by
    have hS' : S subseteq ideal_from_ringHom hI hJ hf := fun y hy => by
      simp only [mem_coe, ideal_from_ringHom, Submodule.mem_mk]
      exact ⟨hS ▸ subset_span hy, fun n => h y hy⟩
    rw [← span_le]; rw [← hS] at hS'
    exact ((hS' hx).2 n).sym

中文:
定义 fromGens
  签名: {f : A ->+* B} {S : 集合 A} (hS : I = span S) (hf : I.map f <= J)
  定义体: f
  ideal_comp := hf
  dpow_comp {n} x hx := by
    have hS' : S subseteq ideal_from_ringHom hI hJ hf := fun y hy => by
      simp only [mem_coe, ideal_from_ringHom, Submodule.mem_mk]
      exact ⟨hS ▸ subset_span hy, fun n => h y hy⟩
    rw [← span_le]; rw [← hS] at hS'
    exact ((hS' hx).2 n).sym
-/
def fromGens {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <= J)
    (h : forall {n : Nat}, forall x in S, f (hI.dpow n x) = hJ.dpow n (f x)) : DPMorphism hI hJ where
  toRingHom := f
  ideal_comp := hf
  dpow_comp {n} x hx := by
    have hS' : S subseteq ideal_from_ringHom hI hJ hf := fun y hy => by
      simp only [mem_coe, ideal_from_ringHom, Submodule.mem_mk]
      exact ⟨hS ▸ subset_span hy, fun n => h y hy⟩
    rw [← span_le]; rw [← hS] at hS'
    exact ((hS' hx).2 n).symm

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : DPMorphism hI hI where
  body: RingHom.id A
  ideal_comp := by simp only [map_id, le_refl]
  dpow_comp _ _ := by simp only [RingHom.id_apply]

中文:
定义 id
  签名: : DP态射 hI hI where
  定义体: RingHom.id A
  ideal_comp := by simp only [map_id, le_refl]
  dpow_comp _ _ := by simp only [RingHom.id_apply]

Depends on / 依赖: RingHom, RingHom.id
-/
def id : DPMorphism hI hI where
  toRingHom := RingHom.id A
  ideal_comp := by simp only [map_id, le_refl]
  dpow_comp _ _ := by simp only [RingHom.id_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (DPMorphism hI hI)
  body: ⟨DPMorphism.id hI⟩

中文:
实例 :
  签名: 可居 (DP态射 hI hI)
  定义体: ⟨DPMorphism.id hI⟩

Depends on / 依赖: DPMorphism, DPMorphism.id
-/
instance : Inhabited (DPMorphism hI hI) := ⟨DPMorphism.id hI⟩

/--
theorem `fromGens_coe` / 定理 `fromGens_coe`

English:
theorem fromGens_coe
  statement: {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <= J)
  proof: rfl

中文:
定理 fromGens_coe
  结论: {f : A ->+* B} {S : 集合 A} (hS : I = span S) (hf : I.map f <= J)
  证明: rfl
-/
theorem fromGens_coe {f : A ->+* B} {S : Set A} (hS : I = span S) (hf : I.map f <= J)
    (h : forall {n : Nat}, forall x in S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    (fromGens hI hJ hS hf h).toRingHom = f := rfl

end DPMorphism

namespace IsDPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)

open DPMorphism

/--
theorem `on_span` / 定理 `on_span`

English:
theorem on_span
  statement: {f : A ->+* B} {S : Set A} (hS : I = span S) (hS' : forall s in S, f s in J)
  proof: by
  suffices h : I.map f <= J by
    exact ⟨h, fun a ha => by
      rw [← fromGens_coe hI hJ hS h hdp]; rw [(fromGens hI hJ hS h hdp).dpow_comp a ha]⟩
  rw [hS]; rw [map_span]; rw [span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has

中文:
定理 on_span
  结论: {f : A ->+* B} {S : 集合 A} (hS : I = span S) (hS' : 对任意 s in S, f s in J)
  证明: by
  suffices h : I.map f <= J by
    exact ⟨h, fun a ha => by
      rw [← fromGens_coe hI hJ hS h hdp]; rw [(fromGens hI hJ hS h hdp).dpow_comp a ha]⟩
  rw [hS]; rw [map_span]; rw [span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has

Depends on / 依赖: I.map, dpow_comp, fromGens, fromGens_coe, map_span, span_le
-/
theorem on_span {f : A ->+* B} {S : Set A} (hS : I = span S) (hS' : forall s in S, f s in J)
    (hdp : forall {n : Nat}, forall a in S, f (hI.dpow n a) = hJ.dpow n (f a)) : IsDPMorphism hI hJ f := by
  suffices h : I.map f <= J by
    exact ⟨h, fun a ha => by
      rw [← fromGens_coe hI hJ hS h hdp]; rw [(fromGens hI hJ hS h hdp).dpow_comp a ha]⟩
  rw [hS]; rw [map_span]; rw [span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has

/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: (f : A ->+* B) (g : B ->+* C) (heq : J = I.map f) (hf : IsDPMorphism hI hJ f)
  proof: by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]; rw [hh.2 a ha]; rw [RingHom.comp_apply]; rw [hf.2 a ha]

中文:
定理 of_comp
  结论: (f : A ->+* B) (g : B ->+* C) (heq : J = I.map f) (hf : 是DP态射 hI hJ f)
  证明: by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]; rw [hh.2 a ha]; rw [RingHom.comp_apply]; rw [hf.2 a ha]

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply, mem_map_of_mem, on_span
-/
theorem of_comp (f : A ->+* B) (g : B ->+* C) (heq : J = I.map f) (hf : IsDPMorphism hI hJ f)
    (hh : IsDPMorphism hI hK (g.comp f)) : IsDPMorphism hJ hK g := by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]; rw [hh.2 a ha]; rw [RingHom.comp_apply]; rw [hf.2 a ha]

end IsDPMorphism

namespace DPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} {hI : DividedPowers I} {hJ : DividedPowers J} {hK : DividedPowers K}

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : DPMorphism hJ hK) (f : DPMorphism hI hJ)
  body: mk' (IsDPMorphism.comp hK g.isDPMorphism f.isDPMorphism)

中文:
定义 comp
  签名: (g : DP态射 hJ hK) (f : DP态射 hI hJ)
  定义体: mk' (IsDPMorphism.comp hK g.isDPMorphism f.isDPMorphism)
-/
protected def comp (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
    DPMorphism hI hK :=
  mk' (IsDPMorphism.comp hK g.isDPMorphism f.isDPMorphism)

/--
lemma `comp_toRingHom` / 引理 `comp_toRingHom`

English:
lemma comp_toRingHom
  given: (g : DPMorphism hJ hK) (f : DPMorphism hI hJ)
  proof: rfl

中文:
引理 comp_toRingHom
  条件: (g : DP态射 hJ hK) (f : DP态射 hI hJ)
  证明: rfl
-/
@[simp] lemma comp_toRingHom (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
    (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom := rfl

end DPMorphism

section Uniqueness

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI hI' : DividedPowers I) (hJ : DividedPowers J) {f : A ->+* B}

/--
theorem `dpow_comp_from_gens` / 定理 `dpow_comp_from_gens`

English:
theorem dpow_comp_from_gens
  statement: {S : Set A} (hS : I = span S) (hS' : forall s in S, f s in J)
  proof: (IsDPMorphism.on_span hI hJ hS hS' hdp).2

中文:
定理 dpow_comp_from_gens
  结论: {S : 集合 A} (hS : I = span S) (hS' : 对任意 s in S, f s in J)
  证明: (IsDPMorphism.on_span hI hJ hS hS' hdp).2

Depends on / 依赖: IsDPMorphism, IsDPMorphism.on_span, on_span
-/
theorem dpow_comp_from_gens {S : Set A} (hS : I = span S) (hS' : forall s in S, f s in J)
    (hdp : forall {n : Nat}, forall a in S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    forall {n}, forall a in I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  (IsDPMorphism.on_span hI hJ hS hS' hdp).2

/--
theorem `dpow_eq_from_gens` / 定理 `dpow_eq_from_gens`

English:
theorem dpow_eq_from_gens
  statement: {S : Set A} (hS : I = span S)
  proof: by
  ext n a
  by_cases ha : a in I
  · refine hI.dpow_comp_from_gens hI' (f := RingHom.id A) hS ?_ ?_ a ha
    · intro s hs
      simp only [RingHom.id_apply, hS]
      exact subset_span hs
    · intro m b hb
      simpa only [RingHom.id_apply] using (hdp b hb)
  · rw [hI.dpow_null ha, hI'.dpow_nul

中文:
定理 dpow_eq_from_gens
  结论: {S : 集合 A} (hS : I = span S)
  证明: by
  ext n a
  by_cases ha : a in I
  · refine hI.dpow_comp_from_gens hI' (f := RingHom.id A) hS ?_ ?_ a ha
    · intro s hs
      simp only [RingHom.id_apply, hS]
      exact subset_span hs
    · intro m b hb
      simpa only [RingHom.id_apply] using (hdp b hb)
  · rw [hI.dpow_null ha, hI'.dpow_nul

Depends on / 依赖: RingHom, RingHom.id, RingHom.id_apply, dpow_comp_from_gens, dpow_null, hI.dpow_comp_from_gens, hI.dpow_null, id_apply, subset_span
-/
theorem dpow_eq_from_gens {S : Set A} (hS : I = span S)
    (hdp : forall {n : Nat}, forall a in S, hI.dpow n a = hI'.dpow n a) : hI' = hI := by
  ext n a
  by_cases ha : a in I
  · refine hI.dpow_comp_from_gens hI' (f := RingHom.id A) hS ?_ ?_ a ha
    · intro s hs
      simp only [RingHom.id_apply, hS]
      exact subset_span hs
    · intro m b hb
      simpa only [RingHom.id_apply] using (hdp b hb)
  · rw [hI.dpow_null ha, hI'.dpow_null ha]

end Uniqueness

end DividedPowers
