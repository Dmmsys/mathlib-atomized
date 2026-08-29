/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The homology of a restriction

Under favourable circumstances, we may relate the
homology of `K : HomologicalComplex C c'` in degree `j'` and
that of `K.restriction e` in degree `j` when `e : Embedding c c'`
is an embedding of complex shapes. See `restriction.sc'Iso`
and `restriction.hasHomology`.

-/

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

namespace restriction

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism `(K.restriction e).sc' i j k ≅ K.sc' i' j' k'` when
`e` is an embedding of complex shapes, `i'`, `j`, `k`' are the respective
images of `i`, `j`, `k` by `e.f`, `j` is the previous index of `i`, etc. -/
@[simps!]
/--
Definition of `sc'Iso` / `sc'Iso` 的定义

English:
definition sc'Iso
  signature: : (K.restriction e).sc' i j k ≅ K.sc' i' j' k'
  body: ShortComplex.isoMk (K.restrictionXIso e hi') (K.restrictionXIso e hj') (K.restrictionXIso e hk')
    (by subst hi' hj'; simp [restrictionXIso])
    (by subst hj' hk'; simp [restrictionXIso])

include hi hk hi' hj' hk' hi'' hk'' in

中文:
定义 sc'Iso
  签名: : (K.restriction e).sc' i j k ≅ K.sc' i' j' k'
  定义体: ShortComplex.isoMk (K.restrictionXIso e hi') (K.restrictionXIso e hj') (K.restrictionXIso e hk')
    (by subst hi' hj'; simp [restrictionXIso])
    (by subst hj' hk'; simp [restrictionXIso])

include hi hk hi' hj' hk' hi'' hk'' in

Depends on / 依赖: K.restrictionXIso, ShortComplex, ShortComplex.isoMk, restrictionXIso
-/
def sc'Iso : (K.restriction e).sc' i j k ≅ K.sc' i' j' k' :=
  ShortComplex.isoMk (K.restrictionXIso e hi') (K.restrictionXIso e hj') (K.restrictionXIso e hk')
    (by subst hi' hj'; simp [restrictionXIso])
    (by subst hj' hk'; simp [restrictionXIso])

include hi hk hi' hj' hk' hi'' hk'' in
/--
lemma `hasHomology` / 引理 `hasHomology`

English:
lemma hasHomology
  given: [K.HasHomology j']
  statement: (K.restriction e).HasHomology j
  proof: ShortComplex.hasHomology_of_iso (K.isoSc' i' j' k' hi'' hk'' ≪≫
    (sc'Iso K e i j k hi' hj' hk' hi'' hk'').symm ≪≫
    ((K.restriction e).isoSc' i j k hi hk).symm)

中文:
引理 hasHomology
  条件: [K.HasHomology j']
  结论: (K.restriction e).HasHomology j
  证明: ShortComplex.hasHomology_of_iso (K.isoSc' i' j' k' hi'' hk'' ≪≫
    (sc'Iso K e i j k hi' hj' hk' hi'' hk'').symm ≪≫
    ((K.restriction e).isoSc' i j k hi hk).symm)

Depends on / 依赖: K.isoSc, K.restriction, ShortComplex, ShortComplex.hasHomology_of_iso, hasHomology_of_iso, restriction
-/
lemma hasHomology [K.HasHomology j'] : (K.restriction e).HasHomology j :=
  ShortComplex.hasHomology_of_iso (K.isoSc' i' j' k' hi'' hk'' ≪≫
    (sc'Iso K e i j k hi' hj' hk' hi'' hk'').symm ≪≫
    ((K.restriction e).isoSc' i j k hi hk).symm)

end restriction

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

/--
Definition of `restrictionCyclesIso` / `restrictionCyclesIso` 的定义

English:
definition restrictionCyclesIso
  signature: :
  body: K.liftCycles ((K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom) _ hk'' (by
      rw [assoc]; rw [← cancel_mono (K.restrictionXIso e hk').inv]; rw [assoc]; rw [assoc]; rw [← restriction_d_eq]; rw [iCycles_d]; rw [zero_comp])
  inv :=
    (K.restriction e).liftCycles (K.iCycles j' ≫ (K.rest

中文:
定义 restrictionCyclesIso
  签名: :
  定义体: K.liftCycles ((K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom) _ hk'' (by
      rw [assoc]; rw [← cancel_mono (K.restrictionXIso e hk').inv]; rw [assoc]; rw [assoc]; rw [← restriction_d_eq]; rw [iCycles_d]; rw [zero_comp])
  inv :=
    (K.restriction e).liftCycles (K.iCycles j' ≫ (K.rest

Depends on / 依赖: Iso.inv_hom_id_assoc, K.iCycles, K.liftCycles, K.restriction, K.restrictionXIso, cancel_mono, hom_inv_id, iCycles, iCycles_d, iCycles_d_assoc, inv_hom_id_assoc, liftCycles, restriction, restrictionXIso, restriction_d_eq, zero_comp
-/
noncomputable def restrictionCyclesIso :
    (K.restriction e).cycles j ≅ K.cycles j' where
  hom :=
    K.liftCycles ((K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom) _ hk'' (by
      rw [assoc]; rw [← cancel_mono (K.restrictionXIso e hk').inv]; rw [assoc]; rw [assoc]; rw [← restriction_d_eq]; rw [iCycles_d]; rw [zero_comp])
  inv :=
    (K.restriction e).liftCycles (K.iCycles j' ≫ (K.restrictionXIso e hj').inv) _ hk (by
      rw [assoc]; rw [restriction_d_eq _ _ hj' hk']; rw [Iso.inv_hom_id_assoc]; rw [iCycles_d_assoc]; rw [zero_comp])
  hom_inv_id := by simp [← cancel_mono ((K.restriction e).iCycles j)]
  inv_hom_id := by simp [← cancel_mono (K.iCycles j')]

@[reassoc (attr := simp)]
/--
lemma `restrictionCyclesIso_hom_iCycles` / 引理 `restrictionCyclesIso_hom_iCycles`

English:
lemma restrictionCyclesIso_hom_iCycles
  proof: by
  simp [restrictionCyclesIso]

@[reassoc (attr := simp)]

中文:
引理 restrictionCyclesIso_hom_iCycles
  证明: by
  simp [restrictionCyclesIso]

@[reassoc (attr := simp)]

Depends on / 依赖: restrictionCyclesIso
-/
lemma restrictionCyclesIso_hom_iCycles :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.iCycles j' =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom := by
  simp [restrictionCyclesIso]

@[reassoc (attr := simp)]
/--
lemma `restrictionCyclesIso_inv_iCycles` / 引理 `restrictionCyclesIso_inv_iCycles`

English:
lemma restrictionCyclesIso_inv_iCycles
  proof: by
  simp [restrictionCyclesIso]

中文:
引理 restrictionCyclesIso_inv_iCycles
  证明: by
  simp [restrictionCyclesIso]

Depends on / 依赖: restrictionCyclesIso
-/
lemma restrictionCyclesIso_inv_iCycles :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫ (K.restriction e).iCycles j =
      K.iCycles j' ≫ (K.restrictionXIso e hj').inv := by
  simp [restrictionCyclesIso]

/--
Definition of `restrictionOpcyclesIso` / `restrictionOpcyclesIso` 的定义

English:
definition restrictionOpcyclesIso
  signature: :
  body: (K.restriction e).descOpcycles ((K.restrictionXIso e hj').hom ≫ K.pOpcycles j') _ hi (by
      rw [restriction_d_eq _ _ hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [d_pOpcycles]; rw [comp_zero])
  inv :=
    K.descOpcycles ((K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcyc

中文:
定义 restrictionOpcyclesIso
  签名: :
  定义体: (K.restriction e).descOpcycles ((K.restrictionXIso e hj').hom ≫ K.pOpcycles j') _ hi (by
      rw [restriction_d_eq _ _ hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [d_pOpcycles]; rw [comp_zero])
  inv :=
    K.descOpcycles ((K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcyc

Depends on / 依赖: Iso.inv_hom_id_assoc, K.descOpcycles, K.pOpcycles, K.restriction, K.restrictionXIso, cancel_epi, comp_zero, d_pOpcycles, descOpcycles, hom_inv_id, inv_hom_id, inv_hom_id_assoc, pOpcycles, restriction, restrictionXIso, restriction_d_eq, restriction_d_eq_assoc
-/
noncomputable def restrictionOpcyclesIso :
    (K.restriction e).opcycles j ≅ K.opcycles j' where
  hom :=
    (K.restriction e).descOpcycles ((K.restrictionXIso e hj').hom ≫ K.pOpcycles j') _ hi (by
      rw [restriction_d_eq _ _ hi' hj']; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [d_pOpcycles]; rw [comp_zero])
  inv :=
    K.descOpcycles ((K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcycles j) _ hi'' (by
      rw [← cancel_epi (K.restrictionXIso e hi').hom]; rw [← restriction_d_eq_assoc]; rw [comp_zero]; rw [d_pOpcycles])
  hom_inv_id := by simp [← cancel_epi ((K.restriction e).pOpcycles j)]
  inv_hom_id := by simp [← cancel_epi (K.pOpcycles j')]

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_restrictionOpcyclesIso_hom` / 引理 `pOpcycles_restrictionOpcyclesIso_hom`

English:
lemma pOpcycles_restrictionOpcyclesIso_hom
  proof: by
  simp [restrictionOpcyclesIso]

@[reassoc (attr := simp)]

中文:
引理 pOpcycles_restrictionOpcyclesIso_hom
  证明: by
  simp [restrictionOpcyclesIso]

@[reassoc (attr := simp)]

Depends on / 依赖: restrictionOpcyclesIso
-/
lemma pOpcycles_restrictionOpcyclesIso_hom :
    (K.restriction e).pOpcycles j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom =
      (K.restrictionXIso e hj').hom ≫ K.pOpcycles j' := by
  simp [restrictionOpcyclesIso]

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_restrictionOpcyclesIso_inv` / 引理 `pOpcycles_restrictionOpcyclesIso_inv`

English:
lemma pOpcycles_restrictionOpcyclesIso_inv
  proof: by
  simp [restrictionOpcyclesIso]

中文:
引理 pOpcycles_restrictionOpcyclesIso_inv
  证明: by
  simp [restrictionOpcyclesIso]

Depends on / 依赖: restrictionOpcyclesIso
-/
lemma pOpcycles_restrictionOpcyclesIso_inv :
    K.pOpcycles j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv =
      (K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcycles j := by
  simp [restrictionOpcyclesIso]

/--
Definition of `restrictionHomologyIso` / `restrictionHomologyIso` 的定义

English:
definition restrictionHomologyIso
  signature: :
  body: have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  (K.restriction e).homologyIsoSc' i j k hi hk ≪≫
    ShortComplex.homologyMapIso (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'') ≪≫
    (K.homo

中文:
定义 restrictionHomologyIso
  签名: :
  定义体: have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  (K.restriction e).homologyIsoSc' i j k hi hk ≪≫
    ShortComplex.homologyMapIso (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'') ≪≫
    (K.homo

Depends on / 依赖: HasHomology, K.homologyIsoSc, K.restriction, K.sc, ShortComplex, ShortComplex.homologyMapIso, homologyIsoSc, homologyMapIso, restriction, restriction.sc
-/
noncomputable def restrictionHomologyIso :
    (K.restriction e).homology j ≅ K.homology j' :=
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  (K.restriction e).homologyIsoSc' i j k hi hk ≪≫
    ShortComplex.homologyMapIso (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'') ≪≫
    (K.homologyIsoSc' i' j' k' hi'' hk'').symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/--
lemma `homologyπ_restrictionHomologyIso_hom` / 引理 `homologyπ_restrictionHomologyIso_hom`

English:
lemma homologyπ_restrictionHomologyIso_hom
  proof: by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [← cancel_mono

中文:
引理 homologyπ_restrictionHomologyIso_hom
  证明: by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [← cancel_mono

Depends on / 依赖: HasHomology, K.restriction, K.restrictionCyclesIso_hom_iCycles_assoc, K.sc, ShortComplex, ShortComplex.homologyMap_comp, cancel_mono, comp_id, homologyIsoSc, homologyMap_comp, id_comp, restriction, restrictionCyclesIso_hom_iCycles_assoc, restrictionHomologyIso, symm.trans
-/
lemma homologyπ_restrictionHomologyIso_hom :
    (K.restriction e).homologyπ j ≫
      (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom =
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.homologyπ j' := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [← cancel_mono (K.sc j').homologyι]; rw [assoc]; rw [assoc]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id]; rw [id_comp]
  apply (K.restrictionCyclesIso_hom_iCycles_assoc e j k hk hj' hk' hk'' _).symm.trans
  congr 1
  symm
  apply ShortComplex.homology_π_ι

@[reassoc]
/--
lemma `homologyπ_restrictionHomologyIso_inv` / 引理 `homologyπ_restrictionHomologyIso_inv`

English:
lemma homologyπ_restrictionHomologyIso_inv
  proof: by
  rw [← cancel_mono (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [homologyπ_restrictionHomologyIso_hom]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

中文:
引理 homologyπ_restrictionHomologyIso_inv
  证明: by
  rw [← cancel_mono (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [homologyπ_restrictionHomologyIso_hom]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.restrictionHomologyIso, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, restrictionHomologyIso
-/
lemma homologyπ_restrictionHomologyIso_inv :
    K.homologyπ j' ≫ (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫ (K.restriction e).homologyπ j := by
  rw [← cancel_mono (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [homologyπ_restrictionHomologyIso_hom]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp, nolint unusedHavesSuffices)]
/--
lemma `restrictionHomologyIso_inv_homologyι` / 引理 `restrictionHomologyIso_inv_homologyι`

English:
lemma restrictionHomologyIso_inv_homologyι
  proof: by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [assoc]; rw [←

中文:
引理 restrictionHomologyIso_inv_homologyι
  证明: by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [assoc]; rw [←

Depends on / 依赖: HasHomology, K.restriction, K.sc, ShortComplex, ShortComplex.homologyMap_comp, ShortComplex.homology_, cancel_epi, comp_id, homologyIsoSc, homologyMap_comp, id_comp, pOpcycles_restrictionO, restriction, restrictionHomologyIso
-/
lemma restrictionHomologyIso_inv_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv ≫
      (K.restriction e).homologyι j =
    K.homologyι j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp]; rw [← ShortComplex.homologyMap_comp]; rw [assoc]; rw [← cancel_epi (K.sc j').homologyπ]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id]; rw [id_comp]
  refine ((ShortComplex.homology_π_ι_assoc _ _).trans ?_).symm
  congr 1
  apply pOpcycles_restrictionOpcyclesIso_inv

@[reassoc (attr := simp)]
/--
lemma `restrictionHomologyIso_hom_homologyι` / 引理 `restrictionHomologyIso_hom_homologyι`

English:
lemma restrictionHomologyIso_hom_homologyι
  proof: by
  rw [← cancel_epi (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv]; rw [Iso.inv_hom_id_assoc]; rw [restrictionHomologyIso_inv_homologyι_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 restrictionHomologyIso_hom_homologyι
  证明: by
  rw [← cancel_epi (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv]; rw [Iso.inv_hom_id_assoc]; rw [restrictionHomologyIso_inv_homologyι_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, K.restrictionHomologyIso, cancel_epi, comp_id, inv_hom_id, inv_hom_id_assoc, restrictionHomologyIso
-/
lemma restrictionHomologyIso_hom_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫ K.homologyι j' =
      (K.restriction e).homologyι j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom := by
  rw [← cancel_epi (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv]; rw [Iso.inv_hom_id_assoc]; rw [restrictionHomologyIso_inv_homologyι_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

end HomologicalComplex
