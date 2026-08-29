/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homology of the extension of a homological complex

Given an embedding `e : c.Embedding c'` and `K : HomologicalComplex C c`, we shall
compute the homology of `K.extend e`. In degrees that are not in the image of `e.f`,
the homology is obviously zero. When `e.f j = j`, we construct an isomorphism
`(K.extend e).homology j' ≅ K.homology j`.

-/

@[expose] public section

open CategoryTheory Limits Category

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

namespace extend

section HomologyData

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

include hk hk' in
/--
lemma `comp_d_eq_zero_iff` / 引理 `comp_d_eq_zero_iff`

English:
lemma comp_d_eq_zero_iff
  given: ⦃W
  statement: C⦄ (φ : W ⟶ K.X j) :
  proof: by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk']; rw [Iso.inv_hom_id_assoc]; rw [← cancel_mono (K.extendXIso e hk').inv]; rw [zero_comp]; rw [assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K

中文:
引理 comp_d_eq_zero_iff
  条件: ⦃W
  结论: C⦄ (φ : W ⟶ K.X j) :
  证明: by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk']; rw [Iso.inv_hom_id_assoc]; rw [← cancel_mono (K.extendXIso e hk').inv]; rw [zero_comp]; rw [assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K

Depends on / 依赖: Iso.inv_hom_id_assoc, K.extendXIso, K.extend_d_eq, K.extend_d_from_eq_zero, K.shape, c.Rel, cancel_mono, comp_zero, e.rel, extendXIso, extend_d_eq, extend_d_from_eq_zero, inv_hom_id_assoc, next_eq, true_iff, zero_comp
-/
lemma comp_d_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ K.X j) :
    φ ≫ K.d j k = 0 ↔ φ ≫ (K.extendXIso e hj').inv ≫ (K.extend e).d j' k' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    rw [K.extend_d_eq e hj' hk']; rw [Iso.inv_hom_id_assoc]; rw [← cancel_mono (K.extendXIso e hk').inv]; rw [zero_comp]; rw [assoc]
  · simp only [K.shape _ _ hjk, comp_zero, true_iff]
    rw [K.extend_d_from_eq_zero e j' k' j hj']; rw [comp_zero]; rw [comp_zero]
    rw [hk]
    exact hjk

include hi hi' in
/--
lemma `d_comp_eq_zero_iff` / 引理 `d_comp_eq_zero_iff`

English:
lemma d_comp_eq_zero_iff
  given: ⦃W
  statement: C⦄ (φ : K.X j ⟶ W) :
  proof: by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (K.extendXIso e hi').hom]; rw [comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff

中文:
引理 d_comp_eq_zero_iff
  条件: ⦃W
  结论: C⦄ (φ : K.X j ⟶ W) :
  证明: by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (K.extendXIso e hi').hom]; rw [comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff

Depends on / 依赖: Iso.inv_hom_id_assoc, K.extendXIso, K.extend_d_eq, K.extend_d_to_eq_zero, K.shape, c.Rel, cancel_epi, comp_zero, e.rel, extendXIso, extend_d_eq, extend_d_to_eq_zero, inv_hom_id_assoc, prev_eq, true_iff, zero_comp
-/
lemma d_comp_eq_zero_iff ⦃W : C⦄ (φ : K.X j ⟶ W) :
    K.d i j ≫ φ = 0 ↔ (K.extend e).d i' j' ≫ (K.extendXIso e hj').hom ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    rw [K.extend_d_eq e hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [← cancel_epi (K.extendXIso e hi').hom]; rw [comp_zero]
  · simp only [K.shape _ _ hij, zero_comp, true_iff]
    rw [K.extend_d_to_eq_zero e i' j' j hj']; rw [zero_comp]
    rw [hi]
    exact hij

namespace leftHomologyData

variable (cone : KernelFork (K.d j k)) (hcone : IsLimit cone)

/-- The kernel fork of `(K.extend e).d j' k'` that is deduced from a kernel
fork of `K.d j k `. -/
@[simp]
/--
Definition of `kernelFork` / `kernelFork` 的定义

English:
definition kernelFork
  signature: : KernelFork ((K.extend e).d j' k')
  body: KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

中文:
定义 kernelFork
  签名: : KernelFork ((K.extend e).d j' k')
  定义体: KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

Depends on / 依赖: KernelFork, KernelFork.of, comp_d_eq_zero_iff, condition, cone.condition, extendXIso
-/
noncomputable def kernelFork : KernelFork ((K.extend e).d j' k') :=
  KernelFork.ofι (cone.ι ≫ (extendXIso K e hj').inv)
    (by rw [assoc, ← comp_d_eq_zero_iff K e hj' hk hk' cone.ι, cone.condition])

/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: : IsLimit (kernelFork K e hj' hk hk' cone)
  body: KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

中文:
定义 isLimitKernelFork
  签名: : IsLimit (kernelFork K e hj' hk hk' cone)
  定义体: KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

Depends on / 依赖: K.extend, KernelFork, KernelFork.isLimitOfIsLimitOfIff, comp_d_eq_zero_iff, extend, extendXIso, isLimitOfIsLimitOfIff
-/
noncomputable def isLimitKernelFork : IsLimit (kernelFork K e hj' hk hk' cone) :=
  KernelFork.isLimitOfIsLimitOfIff hcone ((K.extend e).d j' k')
    (extendXIso K e hj').symm (comp_d_eq_zero_iff K e hj' hk hk')

variable (cocone : CokernelCofork (hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k))))
  (hcocone : IsColimit cocone)

include hi hi' hcone in
/--
lemma `lift_d_comp_eq_zero_iff'` / 引理 `lift_d_comp_eq_zero_iff'`

English:
lemma lift_d_comp_eq_zero_iff'
  given: ⦃W
  statement: C⦄ (f' : K.X i ⟶ cone.pt)
  proof: by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc]; rw [hf']; rw [← cancel_mono (extendXIso K e hj').inv]; rw [assoc]; rw [assoc]; rw [

中文:
引理 lift_d_comp_eq_zero_iff'
  条件: ⦃W
  结论: C⦄ (f' : K.X i ⟶ cone.pt)
  证明: by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc]; rw [hf']; rw [← cancel_mono (extendXIso K e hj').inv]; rw [assoc]; rw [assoc]; rw [

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, K.extendXIso, K.extend_d_eq, K.shape, c.Rel, cancel_epi, cancel_mono, comp_zero, e.rel, extendXIso, extend_d_eq, hom_ext, prev_eq, zero_comp
-/
lemma lift_d_comp_eq_zero_iff' ⦃W : C⦄ (f' : K.X i ⟶ cone.pt)
    (hf' : f' ≫ cone.ι = K.d i j)
    (f'' : (K.extend e).X i' ⟶ cone.pt)
    (hf'' : f'' ≫ cone.ι ≫ (extendXIso K e hj').inv = (K.extend e).d i' j')
    (φ : cone.pt ⟶ W) :
    f' ≫ φ = 0 ↔ f'' ≫ φ = 0 := by
  by_cases hij : c.Rel i j
  · have hi'' : e.f i = i' := by rw [← hi', ← hj', c'.prev_eq' (e.rel hij)]
    have : (K.extendXIso e hi'').hom ≫ f' = f'' := by
      apply Fork.IsLimit.hom_ext hcone
      rw [assoc]; rw [hf']; rw [← cancel_mono (extendXIso K e hj').inv]; rw [assoc]; rw [assoc]; rw [hf'']; rw [K.extend_d_eq e hi'' hj']
    rw [← cancel_epi (K.extendXIso e hi'').hom]; rw [comp_zero]; rw [← this]; rw [assoc]
  · have h₁ : f' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      simp only [zero_comp, hf', K.shape _ _ hij]
    have h₂ : f'' = 0 := by
      apply Fork.IsLimit.hom_ext hcone
      rw [← cancel_mono (extendXIso K e hj').inv]; rw [assoc]; rw [hf'']; rw [zero_comp]; rw [zero_comp]; rw [K.extend_d_to_eq_zero e i' j' j hj']
      rw [hi]
      exact hij
    simp [h₁, h₂]

include hi hi' in
/--
lemma `lift_d_comp_eq_zero_iff` / 引理 `lift_d_comp_eq_zero_iff`

English:
lemma lift_d_comp_eq_zero_iff
  given: ⦃W
  statement: C⦄ (φ : cone.pt ⟶ W) :
  proof: lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

中文:
引理 lift_d_comp_eq_zero_iff
  条件: ⦃W
  结论: C⦄ (φ : cone.pt ⟶ W) :
  证明: lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

Depends on / 依赖: IsLimit, IsLimit.fac, WalkingParallelPair, WalkingParallelPair.zero, hcone.fac, lift_d_comp_eq_zero_iff
-/
lemma lift_d_comp_eq_zero_iff ⦃W : C⦄ (φ : cone.pt ⟶ W) :
    hcone.lift (KernelFork.ofι (K.d i j) (K.d_comp_d i j k)) ≫ φ = 0 ↔
      ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) ≫ φ = 0 :=
  lift_d_comp_eq_zero_iff' K e hj' hi hi' cone hcone _ (hcone.fac _ _) _
    (IsLimit.fac _ _ WalkingParallelPair.zero) _

/--
Definition of `cokernelCofork` / `cokernelCofork` 的定义

English:
definition cokernelCofork
  signature: :
  body: CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

中文:
定义 cokernelCofork
  签名: :
  定义体: CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

Depends on / 依赖: CokernelCofork, CokernelCofork.of, cocone, cocone.condition, condition, lift_d_comp_eq_zero_iff
-/
noncomputable def cokernelCofork :
    CokernelCofork ((isLimitKernelFork K e hj' hk hk' cone hcone).lift
      (KernelFork.ofι ((K.extend e).d i' j') (d_comp_d _ _ _ _))) :=
  CokernelCofork.ofπ cocone.π (by
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone]
    exact cocone.condition)

/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: :
  body: CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

中文:
定义 isColimitCokernelCofork
  签名: :
  定义体: CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

Depends on / 依赖: CokernelCofork, CokernelCofork.isColimitOfIsColimitOfIff, hcocone, isColimitOfIsColimitOfIff, lift_d_comp_eq_zero_iff
-/
noncomputable def isColimitCokernelCofork :
    IsColimit (cokernelCofork K e hj' hi hi' hk hk' cone hcone cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff' hcocone _
    (lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' cone hcone)

end leftHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open leftHomologyData in
/-- The left homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a left homology data of `K.sc' i j k`. -/
@[simps]
/--
Definition of `leftHomologyData` / `leftHomologyData` 的定义

English:
definition leftHomologyData
  signature: (h : (K.sc' i j k).LeftHomologyData)
  body: h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc]; rw [← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact 

中文:
定义 leftHomologyData
  签名: (h : (K.sc' i j k).LeftHomologyData)
  定义体: h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc]; rw [← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact 
-/
noncomputable def leftHomologyData (h : (K.sc' i j k).LeftHomologyData) :
    ((K.extend e).sc' i' j' k').LeftHomologyData where
  K := h.K
  H := h.H
  i := h.i ≫ (extendXIso K e hj').inv
  π := h.π
  wi := by
    dsimp
    rw [assoc]; rw [← comp_d_eq_zero_iff K e hj' hk hk']
    exact h.wi
  hi := isLimitKernelFork K e hj' hk hk' _ h.hi
  wπ := by
    dsimp
    rw [← lift_d_comp_eq_zero_iff K e hj' hi hi' hk hk' _ h.hi]
    exact h.wπ
  hπ := isColimitCokernelCofork K e hj' hi hi' hk hk' _ h.hi _ h.hπ

namespace rightHomologyData

variable (cocone : CokernelCofork (K.d i j)) (hcocone : IsColimit cocone)

/-- The cokernel cofork of `(K.extend e).d i' j'` that is deduced from a cokernel
cofork of `K.d i j`. -/
@[simp]
/--
Definition of `cokernelCofork` / `cokernelCofork` 的定义

English:
definition cokernelCofork
  signature: : CokernelCofork ((K.extend e).d i' j')
  body: CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π) (by
    rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π]; rw [cocone.condition])

中文:
定义 cokernelCofork
  签名: : CokernelCofork ((K.extend e).d i' j')
  定义体: CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π) (by
    rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π]; rw [cocone.condition])

Depends on / 依赖: CokernelCofork, CokernelCofork.of, cocone, cocone.condition, condition, d_comp_eq_zero_iff, extendXIso
-/
noncomputable def cokernelCofork : CokernelCofork ((K.extend e).d i' j') :=
  CokernelCofork.ofπ ((extendXIso K e hj').hom ≫ cocone.π) (by
    rw [← d_comp_eq_zero_iff K e hj' hi hi' cocone.π]; rw [cocone.condition])

/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: : IsColimit (cokernelCofork K e hj' hi hi' cocone)
  body: CokernelCofork.isColimitOfIsColimitOfIff hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

中文:
定义 isColimitCokernelCofork
  签名: : IsColimit (cokernelCofork K e hj' hi hi' cocone)
  定义体: CokernelCofork.isColimitOfIsColimitOfIff hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

Depends on / 依赖: CokernelCofork, CokernelCofork.isColimitOfIsColimitOfIff, K.extend, d_comp_eq_zero_iff, extend, extendXIso, hcocone, isColimitOfIsColimitOfIff
-/
noncomputable def isColimitCokernelCofork : IsColimit (cokernelCofork K e hj' hi hi' cocone) :=
  CokernelCofork.isColimitOfIsColimitOfIff hcocone ((K.extend e).d i' j')
    (extendXIso K e hj') (d_comp_eq_zero_iff K e hj' hi hi')

variable (cone : KernelFork (hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k))))
  (hcone : IsLimit cone)

include hk hk' hcocone in
/--
lemma `d_comp_desc_eq_zero_iff'` / 引理 `d_comp_desc_eq_zero_iff'`

English:
lemma d_comp_desc_eq_zero_iff'
  given: ⦃W
  statement: C⦄ (f' : cocone.pt ⟶ K.X k)
  proof: by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf']; rw [← cancel_epi (extendXIso K e hj').hom]; rw [hf'']; rw [K.extend

中文:
引理 d_comp_desc_eq_zero_iff'
  条件: ⦃W
  结论: C⦄ (f' : cocone.pt ⟶ K.X k)
  证明: by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf']; rw [← cancel_epi (extendXIso K e hj').hom]; rw [hf'']; rw [K.extend

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, K.extendXIso, K.extend_d_eq, K.shape, c.Rel, cancel_epi, cancel_mono, comp_zero, e.rel, extendXIso, extend_d_eq, hcocone, hom_ext, next_eq, reassoc_of, zero_comp
-/
lemma d_comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k)
    (hf' : cocone.π ≫ f' = K.d j k)
    (f'' : cocone.pt ⟶ (K.extend e).X k')
    (hf'' : (extendXIso K e hj').hom ≫ cocone.π ≫ f'' = (K.extend e).d j' k')
    (φ : W ⟶ cocone.pt) :
    φ ≫ f' = 0 ↔ φ ≫ f'' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf']; rw [← cancel_epi (extendXIso K e hj').hom]; rw [hf'']; rw [K.extend_d_eq e hj' hk'']
    rw [← cancel_mono (K.extendXIso e hk'').inv]; rw [zero_comp]; rw [assoc]; rw [this]
  · have h₁ : f' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      simp only [hf', comp_zero, K.shape _ _ hjk]
    have h₂ : f'' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [← cancel_epi (extendXIso K e hj').hom]; rw [hf'']; rw [comp_zero]; rw [comp_zero]; rw [K.extend_d_from_eq_zero e j' k' j hj']
      rw [hk]
      exact hjk
    simp [h₁, h₂]

set_option backward.defeqAttrib.useBackward true in
include hk hk' in
/--
lemma `d_comp_desc_eq_zero_iff` / 引理 `d_comp_desc_eq_zero_iff`

English:
lemma d_comp_desc_eq_zero_iff
  given: ⦃W
  statement: C⦄ (φ : W ⟶ cocone.pt) :
  proof: d_comp_desc_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (hcocone.fac _ _) _ (by
    simpa using! (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
      WalkingParallelPair.one) _

中文:
引理 d_comp_desc_eq_zero_iff
  条件: ⦃W
  结论: C⦄ (φ : W ⟶ cocone.pt) :
  证明: d_comp_desc_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (hcocone.fac _ _) _ (by
    simpa using! (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
      WalkingParallelPair.one) _

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one, cocone, d_comp_desc_eq_zero_iff, hcocone, hcocone.fac, isColimitCokernelCofork
-/
lemma d_comp_desc_eq_zero_iff ⦃W : C⦄ (φ : W ⟶ cocone.pt) :
    φ ≫ hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k)) = 0 ↔
      φ ≫ ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) = 0 :=
  d_comp_desc_eq_zero_iff' K e hj' hk hk' cocone hcocone _ (hcocone.fac _ _) _ (by
    simpa using! (isColimitCokernelCofork K e hj' hi hi' cocone hcocone).fac _
      WalkingParallelPair.one) _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `kernelFork` / `kernelFork` 的定义

English:
definition kernelFork
  signature: :
  body: KernelFork.ofι cone.ι (by
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

中文:
定义 kernelFork
  签名: :
  定义体: KernelFork.ofι cone.ι (by
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

Depends on / 依赖: KernelFork, KernelFork.of, cocone, condition, cone.condition, d_comp_desc_eq_zero_iff, hcocone
-/
noncomputable def kernelFork :
    KernelFork ((isColimitCokernelCofork K e hj' hi hi' cocone hcocone).desc
      (CokernelCofork.ofπ ((K.extend e).d j' k') (d_comp_d _ _ _ _))) :=
  KernelFork.ofι cone.ι (by
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone]
    exact cone.condition)

/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: :
  body: KernelFork.isLimitOfIsLimitOfIff' hcone _
    (d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

中文:
定义 isLimitKernelFork
  签名: :
  定义体: KernelFork.isLimitOfIsLimitOfIff' hcone _
    (d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

Depends on / 依赖: KernelFork, KernelFork.isLimitOfIsLimitOfIff, cocone, d_comp_desc_eq_zero_iff, hcocone, isLimitOfIsLimitOfIff
-/
noncomputable def isLimitKernelFork :
    IsLimit (kernelFork K e hj' hi hi' hk hk' cocone hcocone cone) :=
  KernelFork.isLimitOfIsLimitOfIff' hcone _
    (d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' cocone hcocone)

end rightHomologyData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open rightHomologyData in
/-- The right homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a right homology data of `K.sc' i j k`. -/
@[simps]
/--
Definition of `rightHomologyData` / `rightHomologyData` 的定义

English:
definition rightHomologyData
  signature: (h : (K.sc' i j k).RightHomologyData)
  body: h.Q
  H := h.H
  p := (extendXIso K e hj').hom ≫ h.p
  ι := h.ι
  wp := by
    dsimp
    rw [← d_comp_eq_zero_iff K e hj' hi hi']
    exact h.wp
  hp := isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    dsimp
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
 

中文:
定义 rightHomologyData
  签名: (h : (K.sc' i j k).RightHomologyData)
  定义体: h.Q
  H := h.H
  p := (extendXIso K e hj').hom ≫ h.p
  ι := h.ι
  wp := by
    dsimp
    rw [← d_comp_eq_zero_iff K e hj' hi hi']
    exact h.wp
  hp := isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    dsimp
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
 
-/
noncomputable def rightHomologyData (h : (K.sc' i j k).RightHomologyData) :
    ((K.extend e).sc' i' j' k').RightHomologyData where
  Q := h.Q
  H := h.H
  p := (extendXIso K e hj').hom ≫ h.p
  ι := h.ι
  wp := by
    dsimp
    rw [← d_comp_eq_zero_iff K e hj' hi hi']
    exact h.wp
  hp := isColimitCokernelCofork K e hj' hi hi' _ h.hp
  wι := by
    dsimp
    rw [← d_comp_desc_eq_zero_iff K e hj' hi hi' hk hk' _ h.hp]
    exact h.wι
  hι := isLimitKernelFork K e hj' hi hi' hk hk' _ h.hp _ h.hι

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightHomologyData_g'` / 引理 `rightHomologyData_g'`

English:
lemma rightHomologyData_g'
  given: (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k')
  proof: by
  rw [← cancel_epi h.p]; rw [← cancel_epi (extendXIso K e hj').hom]
  have := (rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this]; rw [K.extend_d_eq e hj' hk'']; rw [h.p_g'_assoc]; rw [shortComplexFunctor'_obj_g]

中文:
引理 rightHomologyData_g'
  条件: (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k')
  证明: by
  rw [← cancel_epi h.p]; rw [← cancel_epi (extendXIso K e hj').hom]
  have := (rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this]; rw [K.extend_d_eq e hj' hk'']; rw [h.p_g'_assoc]; rw [shortComplexFunctor'_obj_g]

Depends on / 依赖: K.extend_d_eq, _assoc, _obj_g, cancel_epi, extendXIso, extend_d_eq, h.p_g, rightHomologyData, shortComplexFunctor
-/
lemma rightHomologyData_g' (h : (K.sc' i j k).RightHomologyData) (hk'' : e.f k = k') :
    (rightHomologyData K e hj' hi hi' hk hk' h).g' = h.g' ≫ (K.extendXIso e hk'').inv := by
  rw [← cancel_epi h.p]; rw [← cancel_epi (extendXIso K e hj').hom]
  have := (rightHomologyData K e hj' hi hi' hk hk' h).p_g'
  dsimp at this
  rw [assoc] at this
  rw [this]; rw [K.extend_d_eq e hj' hk'']; rw [h.p_g'_assoc]; rw [shortComplexFunctor'_obj_g]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The homology data of `(K.extend e).sc' i' j' k'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps]
/--
Definition of `homologyData` / `homologyData` 的定义

English:
definition homologyData
  signature: (h : (K.sc' i j k).HomologyData)
  body: leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

中文:
定义 homologyData
  签名: (h : (K.sc' i j k).HomologyData)
  定义体: leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

Depends on / 依赖: h.left, leftHomologyData
-/
noncomputable def homologyData (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc' i' j' k').HomologyData where
  left := leftHomologyData K e hj' hi hi' hk hk' h.left
  right := rightHomologyData K e hj' hi hi' hk hk' h.right
  iso := h.iso

set_option backward.isDefEq.respectTransparency.types false in
/-- The homology data of `(K.extend e).sc j'` that is deduced
from a homology data of `K.sc' i j k`. -/
@[simps!]
/--
Definition of `homologyData'` / `homologyData'` 的定义

English:
definition homologyData'
  signature: (h : (K.sc' i j k).HomologyData)
  body: homologyData K e hj' hi rfl hk rfl h

中文:
定义 homologyData'
  签名: (h : (K.sc' i j k).HomologyData)
  定义体: homologyData K e hj' hi rfl hk rfl h

Depends on / 依赖: homologyData
-/
noncomputable def homologyData' (h : (K.sc' i j k).HomologyData) :
    ((K.extend e).sc j').HomologyData :=
  homologyData K e hj' hi rfl hk rfl h

end HomologyData

/--
lemma `hasHomology` / 引理 `hasHomology`

English:
lemma hasHomology
  given: {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j]
  proof: ShortComplex.HasHomology.mk'
    (homologyData' K e hj' rfl rfl ((K.sc j).homologyData))

中文:
引理 hasHomology
  条件: {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j]
  证明: ShortComplex.HasHomology.mk'
    (homologyData' K e hj' rfl rfl ((K.sc j).homologyData))

Depends on / 依赖: HasHomology, K.sc, ShortComplex, ShortComplex.HasHomology.mk, homologyData
-/
lemma hasHomology {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] :
    (K.extend e).HasHomology j' :=
  ShortComplex.HasHomology.mk'
    (homologyData' K e hj' rfl rfl ((K.sc j).homologyData))

instance (j : ι) [K.HasHomology j] : (K.extend e).HasHomology (e.f j) :=
  hasHomology K e rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: j, K.HasHomology j] (j'
  body: by
  by_cases h : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := h
    infer_instance
  · have hj := isZero_extend_X K e j' (by tauto)
    exact ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofZeros _ (hj.eq_of_tgt _ _) (hj.eq_of_src _ _))

中文:
实例 [forall
  签名: j, K.HasHomology j] (j'
  定义体: by
  by_cases h : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := h
    infer_instance
  · have hj := isZero_extend_X K e j' (by tauto)
    exact ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofZeros _ (hj.eq_of_tgt _ _) (hj.eq_of_src _ _))

Depends on / 依赖: HasHomology, HomologyData, ShortComplex, ShortComplex.HasHomology.mk, ShortComplex.HomologyData.ofZeros, eq_of_src, eq_of_tgt, hj.eq_of_src, hj.eq_of_tgt, infer_instance, isZero_extend_X, ofZeros
-/
instance [forall j, K.HasHomology j] (j' : ι') : (K.extend e).HasHomology j' := by
  by_cases h : exists j, e.f j = j'
  · obtain ⟨j, rfl⟩ := h
    infer_instance
  · have hj := isZero_extend_X K e j' (by tauto)
    exact ShortComplex.HasHomology.mk'
      (ShortComplex.HomologyData.ofZeros _ (hj.eq_of_tgt _ _) (hj.eq_of_src _ _))

end extend

/--
lemma `extend_exactAt` / 引理 `extend_exactAt`

English:
lemma extend_exactAt
  given: (j' : ι') (hj' : forall j, e.f j != j')
  proof: exactAt_of_isSupported _ e j' hj'

中文:
引理 extend_exactAt
  条件: (j' : ι') (hj' : 对任意 j, e.f j != j')
  证明: exactAt_of_isSupported _ e j' hj'

Depends on / 依赖: exactAt_of_isSupported
-/
lemma extend_exactAt (j' : ι') (hj' : forall j, e.f j != j') :
    (K.extend e).ExactAt j' :=
  exactAt_of_isSupported _ e j' hj'

section

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

/--
Definition of `extendCyclesIso` / `extendCyclesIso` 的定义

English:
definition extendCyclesIso
  signature: :
  body: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

中文:
定义 extendCyclesIso
  签名: :
  定义体: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

Depends on / 依赖: K.sc, cyclesIso, extend, extend.homologyData, homologyData, homologyData.left.cyclesIso.symm, left.cyclesIso
-/
noncomputable def extendCyclesIso :
    (K.extend e).cycles j' ≅ K.cycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.cyclesIso ≪≫
    (K.sc j).homologyData.left.cyclesIso.symm

/--
Definition of `extendOpcyclesIso` / `extendOpcyclesIso` 的定义

English:
definition extendOpcyclesIso
  signature: :
  body: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

中文:
定义 extendOpcyclesIso
  签名: :
  定义体: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

Depends on / 依赖: K.sc, extend, extend.homologyData, homologyData, homologyData.right.opcyclesIso.symm, opcyclesIso, right.opcyclesIso
-/
noncomputable def extendOpcyclesIso :
    (K.extend e).opcycles j' ≅ K.opcycles j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).right.opcyclesIso ≪≫
    (K.sc j).homologyData.right.opcyclesIso.symm

/--
Definition of `extendHomologyIso` / `extendHomologyIso` 的定义

English:
definition extendHomologyIso
  signature: :
  body: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

include hj' in

中文:
定义 extendHomologyIso
  签名: :
  定义体: (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

include hj' in

Depends on / 依赖: K.sc, extend, extend.homologyData, homologyData, homologyData.left.homologyIso.symm, homologyIso, left.homologyIso
-/
noncomputable def extendHomologyIso :
    (K.extend e).homology j' ≅ K.homology j :=
  (extend.homologyData' K e hj' rfl rfl (K.sc j).homologyData).left.homologyIso ≪≫
    (K.sc j).homologyData.left.homologyIso.symm

include hj' in
/--
lemma `extend_exactAt_iff` / 引理 `extend_exactAt_iff`

English:
lemma extend_exactAt_iff
  proof: by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

中文:
引理 extend_exactAt_iff
  证明: by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

Depends on / 依赖: HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, K.extendHomologyIso, exactAt_iff_isZero_homology, extendHomologyIso, isZero_iff
-/
lemma extend_exactAt_iff :
    (K.extend e).ExactAt j' ↔ K.ExactAt j := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `extendCyclesIso_hom_iCycles` / 引理 `extendCyclesIso_hom_iCycles`

English:
lemma extendCyclesIso_hom_iCycles
  proof: by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv]; rw [Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso, iCycles]
  rw [assoc]; rw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.cyclesIso_ho

中文:
引理 extendCyclesIso_hom_iCycles
  证明: by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv]; rw [Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso, iCycles]
  rw [assoc]; rw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.cyclesIso_ho

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.extendCyclesIso, LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i, ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc, cancel_epi, comp_id, cyclesIso_hom_comp_i, cyclesIso_inv_comp_iCycles_assoc, extendCyclesIso, iCycles, inv_hom_id, inv_hom_id_assoc
-/
lemma extendCyclesIso_hom_iCycles :
    (K.extendCyclesIso e hj').hom ≫ K.iCycles j =
      (K.extend e).iCycles j' ≫ (K.extendXIso e hj').hom := by
  rw [← cancel_epi (K.extendCyclesIso e hj').inv]; rw [Iso.inv_hom_id_assoc]
  dsimp [extendCyclesIso, iCycles]
  rw [assoc]; rw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]

@[reassoc (attr := simp)]
/--
lemma `extendCyclesIso_inv_iCycles` / 引理 `extendCyclesIso_inv_iCycles`

English:
lemma extendCyclesIso_inv_iCycles
  proof: by
  simp only [← cancel_epi (K.extendCyclesIso e hj').hom, Iso.hom_inv_id_assoc,
    extendCyclesIso_hom_iCycles_assoc, Iso.hom_inv_id, comp_id]

中文:
引理 extendCyclesIso_inv_iCycles
  证明: by
  simp only [← cancel_epi (K.extendCyclesIso e hj').hom, Iso.hom_inv_id_assoc,
    extendCyclesIso_hom_iCycles_assoc, Iso.hom_inv_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, K.extendCyclesIso, cancel_epi, comp_id, extendCyclesIso, extendCyclesIso_hom_iCycles_assoc, hom_inv_id, hom_inv_id_assoc
-/
lemma extendCyclesIso_inv_iCycles :
    (K.extendCyclesIso e hj').inv ≫ (K.extend e).iCycles j' =
      K.iCycles j ≫ (K.extendXIso e hj').inv := by
  simp only [← cancel_epi (K.extendCyclesIso e hj').hom, Iso.hom_inv_id_assoc,
    extendCyclesIso_hom_iCycles_assoc, Iso.hom_inv_id, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `homologyπ_extendHomologyIso_hom` / 引理 `homologyπ_extendHomologyIso_hom`

English:
lemma homologyπ_extendHomologyIso_hom
  proof: by
  dsimp [extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]; rw [← cancel_mono (K.sc j).homologyData.left.homologyIso.hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.homologyπ_comp_

中文:
引理 homologyπ_extendHomologyIso_hom
  证明: by
  dsimp [extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]; rw [← cancel_mono (K.sc j).homologyData.left.homologyIso.hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.homologyπ_comp_

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.sc, LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.homology, cancel_mono, comp_id, extendCyclesIso, extendHomologyIso, homologyData, homologyData.left.homologyIso.hom, homologyIso, inv_hom_id, inv_hom_id_assoc
-/
lemma homologyπ_extendHomologyIso_hom :
    (K.extend e).homologyπ j' ≫ (K.extendHomologyIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ K.homologyπ j := by
  dsimp [extendHomologyIso, homologyπ]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]; rw [← cancel_mono (K.sc j).homologyData.left.homologyIso.hom]; rw [assoc]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  dsimp [extendCyclesIso]
  simp only [assoc, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `homologyπ_extendHomologyIso_inv` / 引理 `homologyπ_extendHomologyIso_inv`

English:
lemma homologyπ_extendHomologyIso_inv
  proof: by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

中文:
引理 homologyπ_extendHomologyIso_inv
  证明: by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.extendHomologyIso, cancel_mono, comp_id, extendHomologyIso, inv_hom_id, inv_hom_id_assoc
-/
lemma homologyπ_extendHomologyIso_inv :
    K.homologyπ j ≫ (K.extendHomologyIso e hj').inv =
      (K.extendCyclesIso e hj').inv ≫ (K.extend e).homologyπ j' := by
  simp only [← cancel_mono (K.extendHomologyIso e hj').hom,
    assoc, Iso.inv_hom_id, comp_id, homologyπ_extendHomologyIso_hom, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `pOpcycles_extendOpcyclesIso_inv` / 引理 `pOpcycles_extendOpcyclesIso_inv`

English:
lemma pOpcycles_extendOpcyclesIso_inv
  proof: by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [ShortComplex.Right

中文:
引理 pOpcycles_extendOpcyclesIso_inv
  证明: by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [ShortComplex.Right

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.extendOpcyclesIso, RightHomologyData, ShortComplex, ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc, ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv, cancel_mono, comp_id, extendOpcyclesIso, inv_hom_id, inv_hom_id_assoc, pOpcycles, pOpcycles_comp_opcyclesIso_hom_assoc, p_comp_opcyclesIso_inv
-/
lemma pOpcycles_extendOpcyclesIso_inv :
    K.pOpcycles j ≫ (K.extendOpcyclesIso e hj').inv =
      (K.extendXIso e hj').inv ≫ (K.extend e).pOpcycles j' := by
  rw [← cancel_mono (K.extendOpcyclesIso e hj').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [extendOpcyclesIso, pOpcycles]
  rw [ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]
  dsimp
  rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv]
  rfl

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_extendOpcyclesIso_hom` / 引理 `pOpcycles_extendOpcyclesIso_hom`

English:
lemma pOpcycles_extendOpcyclesIso_hom
  proof: by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

中文:
引理 pOpcycles_extendOpcyclesIso_hom
  证明: by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, K.extendOpcyclesIso, cancel_mono, comp_id, extendOpcyclesIso, hom_inv_id, hom_inv_id_assoc, pOpcycles_extendOpcyclesIso_inv
-/
lemma pOpcycles_extendOpcyclesIso_hom :
    (K.extend e).pOpcycles j' ≫ (K.extendOpcyclesIso e hj').hom =
      (K.extendXIso e hj').hom ≫ K.pOpcycles j := by
  simp only [← cancel_mono (K.extendOpcyclesIso e hj').inv,
    assoc, Iso.hom_inv_id, comp_id, pOpcycles_extendOpcyclesIso_inv, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
/--
lemma `extendHomologyIso_hom_homologyι` / 引理 `extendHomologyIso_hom_homologyι`

English:
lemma extendHomologyIso_hom_homologyι
  proof: by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, pOpcycles_extendOpcyclesIso_hom]

@[reassoc (attr := simp)]

中文:
引理 extendHomologyIso_hom_homologyι
  证明: by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, pOpcycles_extendOpcyclesIso_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: K.extend, cancel_epi, extend, extendCyclesIso_hom_iCycles_assoc, pOpcycles_extendOpcyclesIso_hom
-/
lemma extendHomologyIso_hom_homologyι :
    (K.extendHomologyIso e hj').hom ≫ K.homologyι j =
      (K.extend e).homologyι j' ≫ (K.extendOpcyclesIso e hj').hom := by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, pOpcycles_extendOpcyclesIso_hom]

@[reassoc (attr := simp)]
/--
lemma `extendHomologyIso_inv_homologyι` / 引理 `extendHomologyIso_inv_homologyι`

English:
lemma extendHomologyIso_inv_homologyι
  proof: by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

中文:
引理 extendHomologyIso_inv_homologyι
  证明: by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, K.extendHomologyIso, cancel_epi, comp_id, extendHomologyIso, hom_inv_id, hom_inv_id_assoc
-/
lemma extendHomologyIso_inv_homologyι :
    (K.extendHomologyIso e hj').inv ≫ (K.extend e).homologyι j' =
      K.homologyι j ≫ (K.extendOpcyclesIso e hj').inv := by
  simp only [← cancel_epi (K.extendHomologyIso e hj').hom,
    Iso.hom_inv_id_assoc, extendHomologyIso_hom_homologyι_assoc, Iso.hom_inv_id, comp_id]

variable {K L}

@[reassoc (attr := simp)]
/--
lemma `extendCyclesIso_hom_naturality` / 引理 `extendCyclesIso_hom_naturality`

English:
lemma extendCyclesIso_hom_naturality
  proof: by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

@[reassoc (attr := simp)]

中文:
引理 extendCyclesIso_hom_naturality
  证明: by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

@[reassoc (attr := simp)]

Depends on / 依赖: L.iCycles, cancel_mono, extendMap_f, iCycles
-/
lemma extendCyclesIso_hom_naturality :
    cyclesMap (extendMap φ e) j' ≫ (L.extendCyclesIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j := by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

@[reassoc (attr := simp)]
/--
lemma `extendHomologyIso_hom_naturality` / 引理 `extendHomologyIso_hom_naturality`

English:
lemma extendHomologyIso_hom_naturality
  proof: by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

中文:
引理 extendHomologyIso_hom_naturality
  证明: by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

Depends on / 依赖: K.extend, cancel_epi, extend
-/
lemma extendHomologyIso_hom_naturality :
    homologyMap (extendMap φ e) j' ≫ (L.extendHomologyIso e hj').hom =
      (K.extendHomologyIso e hj').hom ≫ homologyMap φ j := by
  simp [← cancel_epi ((K.extend e).homologyπ _)]

set_option backward.defeqAttrib.useBackward true in
include hj' in
/--
lemma `quasiIsoAt_extendMap_iff` / 引理 `quasiIsoAt_extendMap_iff`

English:
lemma quasiIsoAt_extendMap_iff
  proof: by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

中文:
引理 quasiIsoAt_extendMap_iff
  证明: by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

Depends on / 依赖: Arrow.isoMk, K.extendHomologyIso, L.extendHomologyIso, MorphismProperty, MorphismProperty.isomorphisms, arrow_mk_iso_iff, extendHomologyIso, hasLimit, isEventuallyConstantTo, isomorphisms, natAbs, quasiIsoAt_iff_isIso_homologyMap
-/
lemma quasiIsoAt_extendMap_iff :
    QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

end

variable {K L} in
/--
lemma `quasiIso_extendMap_iff` / 引理 `quasiIso_extendMap_iff`

English:
lemma quasiIso_extendMap_iff
  given: [forall j, K.HasHomology j] [forall j, L.HasHomology j]
  proof: by
  simp only [quasiIso_iff, ← fun j => quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact extend_exactAt _ _ 

中文:
引理 quasiIso_extendMap_iff
  条件: [对任意 j, K.HasHomology j] [对任意 j, L.HasHomology j]
  证明: by
  simp only [quasiIso_iff, ← fun j => quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact extend_exactAt _ _ 

Depends on / 依赖: all_goals, extend_exactAt, quasiIsoAt_extendMap_iff, quasiIsoAt_iff_exactAt, quasiIso_iff
-/
lemma quasiIso_extendMap_iff [forall j, K.HasHomology j] [forall j, L.HasHomology j] :
    QuasiIso (extendMap φ e) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, ← fun j => quasiIsoAt_extendMap_iff φ e (j := j) (hj' := rfl)]
  constructor
  · tauto
  · intro h j'
    by_cases hj' : exists j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      exact h j
    · rw [quasiIsoAt_iff_exactAt]
      all_goals
        exact extend_exactAt _ _ _ (by simpa using hj')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: j, K.HasHomology j] [forall j, L.HasHomology j] [QuasiIso φ] :
  body: by
  rwa [quasiIso_extendMap_iff]

中文:
实例 [forall
  签名: j, K.HasHomology j] [对任意 j, L.HasHomology j] [QuasiIso φ] :
  定义体: by
  rwa [quasiIso_extendMap_iff]

Depends on / 依赖: quasiIso_extendMap_iff
-/
instance [forall j, K.HasHomology j] [forall j, L.HasHomology j] [QuasiIso φ] :
    QuasiIso (extendMap φ e) := by
  rwa [quasiIso_extendMap_iff]

end HomologicalComplex
