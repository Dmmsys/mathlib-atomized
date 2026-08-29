/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncLE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncLE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

In order to achieve this, we dualize the constructions from the file
`Embedding.TruncGE`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [forall i', K.HasHomology i'] [forall i', L.HasHomology i'] [forall i', M.HasHomology i']

/--
Definition of `truncLE'` / `truncLE'` 的定义

English:
definition truncLE'
  signature: : HomologicalComplex C c
  body: (K.op.truncGE' e.op).unop

中文:
定义 truncLE'
  签名: : HomologicalComplex C c
  定义体: (K.op.truncGE' e.op).unop

Depends on / 依赖: K.op.truncGE, e.op, truncGE
-/
noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

/--
Definition of `truncLE'XIso` / `truncLE'XIso` 的定义

English:
definition truncLE'XIso
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i)
  body: (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop

中文:
定义 truncLE'XIso
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i)
  定义体: (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop
-/
noncomputable def truncLE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.X i' :=
  (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop

/--
Definition of `truncLE'XIsoCycles` / `truncLE'XIsoCycles` 的定义

English:
definition truncLE'XIsoCycles
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i)
  body: (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

中文:
定义 truncLE'XIsoCycles
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i)
  定义体: (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm
-/
noncomputable def truncLE'XIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.cycles i' :=
  (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

/--
lemma `truncLE'_d_eq` / 引理 `truncLE'_d_eq`

English:
lemma truncLE'_d_eq
  statement: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  proof: Quiver.Hom.op_inj (by simpa using! K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

中文:
引理 truncLE'_d_eq
  结论: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  证明: Quiver.Hom.op_inj (by simpa using! K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))
-/
lemma truncLE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : ¬ e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫ K.d i' j' ≫
        (K.truncLE'XIso e hj' hj).inv :=
  Quiver.Hom.op_inj (by simpa using! K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `truncLE'_d_eq_toCycles` / 引理 `truncLE'_d_eq_toCycles`

English:
lemma truncLE'_d_eq_toCycles
  statement: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  proof: Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using! K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))

中文:
引理 truncLE'_d_eq_toCycles
  结论: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  证明: Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using! K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))
-/
lemma truncLE'_d_eq_toCycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫
      K.toCycles i' j' ≫ (K.truncLE'XIsoCycles e hj' hj).inv :=
  Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using! K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))

section

variable [HasZeroObject C]

/--
Definition of `truncLE` / `truncLE` 的定义

English:
definition truncLE
  signature: : HomologicalComplex C c'
  body: (K.op.truncGE e.op).unop

中文:
定义 truncLE
  签名: : HomologicalComplex C c'
  定义体: (K.op.truncGE e.op).unop

Depends on / 依赖: K.op.truncGE, e.op, truncGE
-/
noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

/--
Definition of `truncLEIso` / `truncLEIso` 的定义

English:
definition truncLEIso
  signature: : K.truncLE e ≅ (K.truncLE' e).extend e
  body: (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

中文:
定义 truncLEIso
  签名: : K.truncLE e ≅ (K.truncLE' e).extend e
  定义体: (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

Depends on / 依赖: K.truncLE, extendOpIso, mapIso, symm.op, truncLE, unopFunctor
-/
noncomputable def truncLEIso : K.truncLE e ≅ (K.truncLE' e).extend e :=
  (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

/--
Definition of `truncLEXIso` / `truncLEXIso` 的定义

English:
definition truncLEXIso
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i)
  body: (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

中文:
定义 truncLEXIso
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i)
  定义体: (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

Depends on / 依赖: K.op.truncGEXIso, e.op, truncGEXIso, unop.symm
-/
noncomputable def truncLEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.X i' :=
  (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

/--
Definition of `truncLEXIsoCycles` / `truncLEXIsoCycles` 的定义

English:
definition truncLEXIsoCycles
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i)
  body: (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

中文:
定义 truncLEXIsoCycles
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i)
  定义体: (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

Depends on / 依赖: K.op.truncGEXIsoOpcycles, K.opcyclesOpIso, e.op, opcyclesOpIso, truncGEXIsoOpcycles, unop.symm
-/
noncomputable def truncLEXIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.cycles i' :=
  (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

end

section

variable {K L M}

/--
Definition of `truncLE'Map` / `truncLE'Map` 的定义

English:
definition truncLE'Map
  signature: : K.truncLE' e ⟶ L.truncLE' e
  body: (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

中文:
定义 truncLE'Map
  签名: : K.truncLE' e ⟶ L.truncLE' e
  定义体: (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op
-/
noncomputable def truncLE'Map : K.truncLE' e ⟶ L.truncLE' e :=
  (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `truncLE'Map_f_eq_cyclesMap` / 引理 `truncLE'Map_f_eq_cyclesMap`

English:
lemma truncLE'Map_f_eq_cyclesMap
  given: {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i')
  proof: by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc]; rw [assoc]; rw [truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h]; rw [opcyclesOpIso_inv_naturality_assoc]; rw [Iso.hom_inv_id_assoc]

中文:
引理 truncLE'Map_f_eq_cyclesMap
  条件: {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i')
  证明: by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc]; rw [assoc]; rw [truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h]; rw [opcyclesOpIso_inv_naturality_assoc]; rw [Iso.hom_inv_id_assoc]
-/
lemma truncLE'Map_f_eq_cyclesMap {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIsoCycles e h hi).hom ≫ cyclesMap φ i' ≫
        (L.truncLE'XIsoCycles e h hi).inv := by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc]; rw [assoc]; rw [truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h]; rw [opcyclesOpIso_inv_naturality_assoc]; rw [Iso.hom_inv_id_assoc]

/--
lemma `truncLE'Map_f_eq` / 引理 `truncLE'Map_f_eq`

English:
lemma truncLE'Map_f_eq
  given: {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i')
  proof: Quiver.Hom.op_inj
    (by simpa using! truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

中文:
引理 truncLE'Map_f_eq
  条件: {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i')
  证明: Quiver.Hom.op_inj
    (by simpa using! truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)
-/
lemma truncLE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncLE'XIso e h hi).inv :=
  Quiver.Hom.op_inj
    (by simpa using! truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

variable (K) in
@[simp]
/--
lemma `truncLE'Map_id` / 引理 `truncLE'Map_id`

English:
lemma truncLE'Map_id
  statement: truncLE'Map (𝟙 K) e = 𝟙 _
  proof: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

@[reassoc, simp]

中文:
引理 truncLE'Map_id
  结论: truncLE'Map (𝟙 K) e = 𝟙 _
  证明: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

@[reassoc, simp]
-/
lemma truncLE'Map_id : truncLE'Map (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

@[reassoc, simp]
/--
lemma `truncLE'Map_comp` / 引理 `truncLE'Map_comp`

English:
lemma truncLE'Map_comp
  statement: truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e
  proof: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

中文:
引理 truncLE'Map_comp
  结论: truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e
  证明: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))
-/
lemma truncLE'Map_comp : truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

variable [HasZeroObject C]

/--
Definition of `truncLEMap` / `truncLEMap` 的定义

English:
definition truncLEMap
  signature: : K.truncLE e ⟶ L.truncLE e
  body: (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

中文:
定义 truncLEMap
  签名: : K.truncLE e ⟶ L.truncLE e
  定义体: (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

Depends on / 依赖: e.op, opFunctor, truncGEMap, unopFunctor
-/
noncomputable def truncLEMap : K.truncLE e ⟶ L.truncLE e :=
  (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

variable (K) in
@[simp]
/--
lemma `truncLEMap_id` / 引理 `truncLEMap_id`

English:
lemma truncLEMap_id
  statement: truncLEMap (𝟙 K) e = 𝟙 _
  proof: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGEMap_id e.op))

@[reassoc, simp]

中文:
引理 truncLEMap_id
  结论: truncLEMap (𝟙 K) e = 𝟙 _
  证明: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGEMap_id e.op))

@[reassoc, simp]

Depends on / 依赖: K.op.truncGEMap_id, Quiver, Quiver.Hom.op, congr_arg, congr_map, e.op, truncGEMap_id, unopFunctor
-/
lemma truncLEMap_id : truncLEMap (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGEMap_id e.op))

@[reassoc, simp]
/--
lemma `truncLEMap_comp` / 引理 `truncLEMap_comp`

English:
lemma truncLEMap_comp
  statement: truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e
  proof: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGEMap_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

中文:
引理 truncLEMap_comp
  结论: truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e
  证明: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGEMap_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

Depends on / 依赖: Quiver, Quiver.Hom.op, congr_arg, congr_map, e.op, opFunctor, truncGEMap_comp, unopFunctor
-/
lemma truncLEMap_comp : truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGEMap_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

end

/--
Definition of `truncLE'ToRestriction` / `truncLE'ToRestriction` 的定义

English:
definition truncLE'ToRestriction
  signature: : K.truncLE' e ⟶ K.restriction e
  body: (unopFunctor C c.symm).map (K.op.restrictionToTruncGE' e.op).op

中文:
定义 truncLE'ToRestriction
  签名: : K.truncLE' e ⟶ K.restriction e
  定义体: (unopFunctor C c.symm).map (K.op.restrictionToTruncGE' e.op).op
-/
noncomputable def truncLE'ToRestriction : K.truncLE' e ⟶ K.restriction e :=
  (unopFunctor C c.symm).map (K.op.restrictionToTruncGE' e.op).op

/--
lemma `isIso_truncLE'ToRestriction` / 引理 `isIso_truncLE'ToRestriction`

English:
lemma isIso_truncLE'ToRestriction
  given: (i : ι) (hi : ¬ e.BoundaryLE i)
  proof: by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

中文:
引理 isIso_truncLE'ToRestriction
  条件: (i : ι) (hi : ¬ e.BoundaryLE i)
  证明: by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

Depends on / 依赖: K.op.isIso_restrictionToTruncGE, K.op.restrictionToTruncGE, e.op, infer_instance, isIso_restrictionToTruncGE, restrictionToTruncGE
-/
lemma isIso_truncLE'ToRestriction (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.truncLE'ToRestriction e).f i) := by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

variable {K L} in
@[reassoc (attr := simp)]
/--
lemma `truncLE'ToRestriction_naturality` / 引理 `truncLE'ToRestriction_naturality`

English:
lemma truncLE'ToRestriction_naturality
  proof: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))

中文:
引理 truncLE'ToRestriction_naturality
  证明: (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))
-/
lemma truncLE'ToRestriction_naturality :
    truncLE'Map φ e ≫ L.truncLE'ToRestriction e =
      K.truncLE'ToRestriction e ≫ restrictionMap φ e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))

instance (i : ι) : Mono ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs (Mono ((K.op.restrictionToTruncGE' e.op).f i).unop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] (i
  body: inferInstanceAs (IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop)

中文:
实例 [K.IsStrictlySupported
  签名: e] (i
  定义体: inferInstanceAs (IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop)

Depends on / 依赖: K.op.restrictionToTruncGE, e.op, restrictionToTruncGE
-/
instance [K.IsStrictlySupported e] (i : ι) :
    IsIso ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs (IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop)

section

variable [HasZeroObject C]

/--
Definition of `ιTruncLE` / `ιTruncLE` 的定义

English:
definition ιTruncLE
  signature: : K.truncLE e ⟶ K
  body: (unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op

中文:
定义 ιTruncLE
  签名: : K.truncLE e ⟶ K
  定义体: (unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op

Depends on / 依赖: K.op, e.op, unopFunctor
-/
noncomputable def ιTruncLE : K.truncLE e ⟶ K :=
  (unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op

instance (i' : ι') : Mono ((K.ιTruncLE e).f i') :=
  inferInstanceAs (Mono ((K.op.πTruncGE e.op).f i').unop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (K.ιTruncLE e)
  body: mono_of_mono_f _ (fun _ => inferInstance)

中文:
实例 :
  签名: Mono (K.ιTruncLE e)
  定义体: mono_of_mono_f _ (fun _ => inferInstance)

Depends on / 依赖: mono_of_mono_f
-/
instance : Mono (K.ιTruncLE e) := mono_of_mono_f _ (fun _ => inferInstance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (K.truncLE e).IsStrictlySupported e
  body: by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e.op)

中文:
实例 :
  签名: (K.truncLE e).IsStrictlySupported e
  定义体: by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e.op)

Depends on / 依赖: IsStrictlySupported, K.op.truncGE, e.op, isStrictlySupported_op_iff, truncGE
-/
instance : (K.truncLE e).IsStrictlySupported e := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e.op)

variable {K L} in
@[reassoc (attr := simp)]
/--
lemma `ιTruncLE_naturality` / 引理 `ιTruncLE_naturality`

English:
lemma ιTruncLE_naturality
  proof: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (πTruncGE_naturality ((opFunctor C c').map φ.op) e.op))

中文:
引理 ιTruncLE_naturality
  证明: (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (πTruncGE_naturality ((opFunctor C c').map φ.op) e.op))

Depends on / 依赖: Quiver, Quiver.Hom.op, congr_arg, congr_map, e.op, opFunctor, unopFunctor
-/
lemma ιTruncLE_naturality :
    truncLEMap φ e ≫ L.ιTruncLE e = K.ιTruncLE e ≫ φ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (πTruncGE_naturality ((opFunctor C c').map φ.op) e.op))

instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncLE e).IsStrictlySupported e' := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs ((K.op.truncGE e.op).IsStrictlySupported e'.op)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] : IsIso (K.ιTruncLE e)
  body: inferInstanceAs (IsIso ((unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op))

中文:
实例 [K.IsStrictlySupported
  签名: e] : IsIso (K.ιTruncLE e)
  定义体: inferInstanceAs (IsIso ((unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op))

Depends on / 依赖: K.op, e.op, unopFunctor
-/
instance [K.IsStrictlySupported e] : IsIso (K.ιTruncLE e) :=
  inferInstanceAs (IsIso ((unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op))

/--
lemma `isIso_ιTruncLE_iff` / 引理 `isIso_ιTruncLE_iff`

English:
lemma isIso_ιTruncLE_iff
  statement: IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e
  proof: ⟨fun _ => isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ => inferInstance⟩

中文:
引理 isIso_ιTruncLE_iff
  结论: IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e
  证明: ⟨fun _ => isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ => inferInstance⟩

Depends on / 依赖: isStrictlySupported_of_iso
-/
lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e :=
  ⟨fun _ => isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ => inferInstance⟩

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncLE]
    (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
/--
Definition of `truncLE'Functor` / `truncLE'Functor` 的定义

English:
definition truncLE'Functor
  signature: :
  body: K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

中文:
定义 truncLE'Functor
  签名: :
  定义体: K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

Depends on / 依赖: K.truncLE, truncLE
-/
noncomputable def truncLE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.truncGE' e ⟶ K.restriction e` for all `K`. -/
@[simps]
/--
Definition of `truncLE'ToRestrictionNatTrans` / `truncLE'ToRestrictionNatTrans` 的定义

English:
definition truncLE'ToRestrictionNatTrans
  signature: :
  body: K.truncLE'ToRestriction e

中文:
定义 truncLE'ToRestrictionNatTrans
  签名: :
  定义体: K.truncLE'ToRestriction e
-/
noncomputable def truncLE'ToRestrictionNatTrans :
    e.truncLE'Functor C ⟶ e.restrictionFunctor C where
  app K := K.truncLE'ToRestriction e

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`. -/
@[simps]
/--
Definition of `truncLEFunctor` / `truncLEFunctor` 的定义

English:
definition truncLEFunctor
  signature: :
  body: K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

中文:
定义 truncLEFunctor
  签名: :
  定义体: K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

Depends on / 依赖: K.truncLE, truncLE
-/
noncomputable def truncLEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.ιTruncLE e : K.truncLE e ⟶ K` for all `K`. -/
@[simps]
/--
Definition of `ιTruncLENatTrans` / `ιTruncLENatTrans` 的定义

English:
definition ιTruncLENatTrans
  signature: : e.truncLEFunctor C ⟶ 𝟭 _ where
  body: K.ιTruncLE e

中文:
定义 ιTruncLENatTrans
  签名: : e.truncLEFunctor C ⟶ 𝟭 _ where
  定义体: K.ιTruncLE e
-/
noncomputable def ιTruncLENatTrans : e.truncLEFunctor C ⟶ 𝟭 _ where
  app K := K.ιTruncLE e

end ComplexShape.Embedding
