/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncGE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncGE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

For example, if `e` is the embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ`
in `ComplexShape.up ℤ` which sends `n : ℕ` to `p + n` and `K : CochainComplex C ℤ`,
then `K.truncGE' e : CochainComplex C ℕ` is the following complex:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). Then, the
cochain complex `K.truncGE e` is indexed by `ℤ`, and has the
following shape:

`... ⟶ 0 ⟶ 0 ⟶ 0 ⟶ Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where `Q` is in degree `p`.

We also construct the canonical epimorphism `K.πTruncGE e : K ⟶ K.truncGE e`.

## TODO
* show that `K.πTruncGE e : K ⟶ K.truncGE e` induces an isomorphism
  in homology in degrees in the image of `e.f`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [forall i', K.HasHomology i'] [forall i', L.HasHomology i'] [forall i', M.HasHomology i']

namespace truncGE'

open scoped Classical in
/--
Definition of `X` / `X` 的定义

English:
definition X
  signature: (i : ι)
  body: if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

中文:
定义 X
  签名: (i : ι)
  定义体: if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

Depends on / 依赖: BoundaryGE, K.opcycles, e.BoundaryGE, opcycles
-/
noncomputable def X (i : ι) : C :=
  if e.BoundaryGE i
  then K.opcycles (e.f i)
  else K.X (e.f i)

/--
Definition of `XIsoOpcycles` / `XIsoOpcycles` 的定义

English:
definition XIsoOpcycles
  signature: {i : ι} (hi : e.BoundaryGE i)
  body: eqToIso (if_pos hi)

中文:
定义 XIsoOpcycles
  签名: {i : ι} (hi : e.BoundaryGE i)
  定义体: eqToIso (if_pos hi)

Depends on / 依赖: eqToIso, if_pos
-/
noncomputable def XIsoOpcycles {i : ι} (hi : e.BoundaryGE i) :
    X K e i ≅ K.opcycles (e.f i) :=
  eqToIso (if_pos hi)

/--
Definition of `XIso` / `XIso` 的定义

English:
definition XIso
  signature: {i : ι} (hi : ¬ e.BoundaryGE i)
  body: eqToIso (if_neg hi)

中文:
定义 XIso
  签名: {i : ι} (hi : ¬ e.BoundaryGE i)
  定义体: eqToIso (if_neg hi)

Depends on / 依赖: eqToIso, if_neg
-/
noncomputable def XIso {i : ι} (hi : ¬ e.BoundaryGE i) :
    X K e i ≅ K.X (e.f i) :=
  eqToIso (if_neg hi)

open scoped Classical in
/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (i j : ι)
  body: if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0

@[reassoc

中文:
定义 d
  签名: (i j : ι)
  定义体: if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0

@[reassoc

Depends on / 依赖: BoundaryGE, K.fromOpcycles, XIsoOpcycles, c.Rel, e.BoundaryGE, e.not_boundaryGE_next, fromOpcycles, not_boundaryGE_next, truncGE
-/
noncomputable def d (i j : ι) : X K e i ⟶ X K e j :=
  if hij : c.Rel i j
  then
    if hi : e.BoundaryGE i
    then (truncGE'.XIsoOpcycles K e hi).hom ≫ K.fromOpcycles (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
    else (XIso K e hi).hom ≫ K.d (e.f i) (e.f j) ≫
      (XIso K e (e.not_boundaryGE_next hij)).inv
  else 0

@[reassoc (attr := simp)]
/--
lemma `d_comp_d` / 引理 `d_comp_d`

English:
lemma d_comp_d
  given: (i j k : ι)
  statement: d K e i j ≫ d K e j k = 0
  proof: by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

中文:
引理 d_comp_d
  条件: (i j k : ι)
  结论: d K e i j ≫ d K e j k = 0
  证明: by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

Depends on / 依赖: c.Rel, comp_zero, dif_neg, dif_pos, e.not_boundaryGE_next, not_boundaryGE_next, split_ifs, zero_comp
-/
lemma d_comp_d (i j k : ι) : d K e i j ≫ d K e j k = 0 := by
  dsimp [d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

end truncGE'

/--
Definition of `truncGE'` / `truncGE'` 的定义

English:
definition truncGE'
  signature: : HomologicalComplex C c where
  body: truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

中文:
定义 truncGE'
  签名: : 同调复形 C c where
  定义体: truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

Depends on / 依赖: truncGE
-/
noncomputable def truncGE' : HomologicalComplex C c where
  X := truncGE'.X K e
  d := truncGE'.d K e
  shape _ _ h := dif_neg h

/--
Definition of `truncGE'XIso` / `truncGE'XIso` 的定义

English:
definition truncGE'XIso
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  body: (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

中文:
定义 truncGE'XIso
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  定义体: (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)
-/
noncomputable def truncGE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.X i' :=
  (truncGE'.XIso K e hi) ≪≫ eqToIso (by subst hi'; rfl)

/--
Definition of `truncGE'XIsoOpcycles` / `truncGE'XIsoOpcycles` 的定义

English:
definition truncGE'XIsoOpcycles
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  body: (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

中文:
定义 truncGE'XIsoOpcycles
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  定义体: (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)
-/
noncomputable def truncGE'XIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE' e).X i ≅ K.opcycles i' :=
  (truncGE'.XIsoOpcycles K e hi) ≪≫ eqToIso (by subst hi'; rfl)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `truncGE'_d_eq` / 引理 `truncGE'_d_eq`

English:
lemma truncGE'_d_eq
  statement: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  proof: by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

中文:
引理 truncGE'_d_eq
  结论: {i j : ι} (hij : c.关系 i j) {i' j' : ι'}
  证明: by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]
-/
lemma truncGE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIso e hi' hi).hom ≫ K.d i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_neg hi]
  subst hi' hj'
  simp [truncGE'XIso]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `truncGE'_d_eq_fromOpcycles` / 引理 `truncGE'_d_eq_fromOpcycles`

English:
lemma truncGE'_d_eq_fromOpcycles
  statement: {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
  proof: by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

中文:
引理 truncGE'_d_eq_fromOpcycles
  结论: {i j : ι} (hij : c.关系 i j) {i' j' : ι'}
  证明: by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]
-/
lemma truncGE'_d_eq_fromOpcycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hi : e.BoundaryGE i) :
    (K.truncGE' e).d i j = (K.truncGE'XIsoOpcycles e hi' hi).hom ≫ K.fromOpcycles i' j' ≫
      (K.truncGE'XIso e hj' (e.not_boundaryGE_next hij)).inv := by
  dsimp [truncGE', truncGE'.d]
  rw [dif_pos hij]; rw [dif_pos hi]
  subst hi' hj'
  simp [truncGE'XIso, truncGE'XIsoOpcycles]

section

variable [HasZeroObject C]

/--
Definition of `truncGE` / `truncGE` 的定义

English:
definition truncGE
  signature: : HomologicalComplex C c'
  body: (K.truncGE' e).extend e

中文:
定义 truncGE
  签名: : 同调复形 C c'
  定义体: (K.truncGE' e).extend e

Depends on / 依赖: K.truncGE, extend, truncGE
-/
noncomputable def truncGE : HomologicalComplex C c' := (K.truncGE' e).extend e

/--
Definition of `truncGEXIso` / `truncGEXIso` 的定义

English:
definition truncGEXIso
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  body: (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

中文:
定义 truncGEXIso
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  定义体: (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

Depends on / 依赖: K.truncGE, extendXIso, truncGE
-/
noncomputable def truncGEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.X i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIso e hi' hi

/--
Definition of `truncGEXIsoOpcycles` / `truncGEXIsoOpcycles` 的定义

English:
definition truncGEXIsoOpcycles
  signature: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  body: (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

中文:
定义 truncGEXIsoOpcycles
  签名: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  定义体: (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

Depends on / 依赖: K.truncGE, XIsoOpcycles, extendXIso, truncGE
-/
noncomputable def truncGEXIsoOpcycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.truncGE e).X i' ≅ K.opcycles i' :=
  (K.truncGE' e).extendXIso e hi' ≪≫ K.truncGE'XIsoOpcycles e hi' hi

end

section

variable {K L M}

open scoped Classical in
/--
Definition of `truncGE'Map` / `truncGE'Map` 的定义

English:
definition truncGE'Map
  signature: : K.truncGE' e ⟶ L.truncGE' e where
  body: if hi : e.BoundaryGE i
    then
      (K.truncGE'XIsoOpcycles e rfl hi).hom ≫ opcyclesMap φ (e.f i) ≫
        (L.truncGE'XIsoOpcycles e rfl hi).inv
    else
      (K.truncGE'XIso e rfl hi).hom ≫ φ.f (e.f i) ≫ (L.truncGE'XIso e rfl hi).inv
  comm' i j hij := by
    rw [dif_neg (e.not_boundaryGE_next 

中文:
定义 truncGE'Map
  签名: : K.truncGE' e ⟶ L.truncGE' e where
  定义体: if hi : e.BoundaryGE i
    then
      (K.truncGE'XIsoOpcycles e rfl hi).hom ≫ opcyclesMap φ (e.f i) ≫
        (L.truncGE'XIsoOpcycles e rfl hi).inv
    else
      (K.truncGE'XIso e rfl hi).hom ≫ φ.f (e.f i) ≫ (L.truncGE'XIso e rfl hi).inv
  comm' i j hij := by
    rw [dif_neg (e.not_boundaryGE_next 
-/
noncomputable def truncGE'Map : K.truncGE' e ⟶ L.truncGE' e where
  f i :=
    if hi : e.BoundaryGE i
    then
      (K.truncGE'XIsoOpcycles e rfl hi).hom ≫ opcyclesMap φ (e.f i) ≫
        (L.truncGE'XIsoOpcycles e rfl hi).inv
    else
      (K.truncGE'XIso e rfl hi).hom ≫ φ.f (e.f i) ≫ (L.truncGE'XIso e rfl hi).inv
  comm' i j hij := by
    rw [dif_neg (e.not_boundaryGE_next hij)]
    by_cases hi : e.BoundaryGE i
    · rw [dif_pos hi]
      simp [truncGE'_d_eq_fromOpcycles _ e hij rfl rfl hi,
        ← cancel_epi (K.pOpcycles (e.f i))]
    · rw [dif_neg hi]
      simp [truncGE'_d_eq _ e hij rfl rfl hi]

/--
lemma `truncGE'Map_f_eq_opcyclesMap` / 引理 `truncGE'Map_f_eq_opcyclesMap`

English:
lemma truncGE'Map_f_eq_opcyclesMap
  given: {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i')
  proof: by
  subst h
  exact dif_pos hi

中文:
引理 truncGE'Map_f_eq_opcyclesMap
  条件: {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i')
  证明: by
  subst h
  exact dif_pos hi
-/
lemma truncGE'Map_f_eq_opcyclesMap {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIsoOpcycles e h hi).hom ≫ opcyclesMap φ i' ≫
        (L.truncGE'XIsoOpcycles e h hi).inv := by
  subst h
  exact dif_pos hi

/--
lemma `truncGE'Map_f_eq` / 引理 `truncGE'Map_f_eq`

English:
lemma truncGE'Map_f_eq
  given: {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'} (h : e.f i = i')
  proof: by
  subst h
  exact dif_neg hi

中文:
引理 truncGE'Map_f_eq
  条件: {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'} (h : e.f i = i')
  证明: by
  subst h
  exact dif_neg hi
-/
lemma truncGE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (truncGE'Map φ e).f i =
      (K.truncGE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncGE'XIso e h hi).inv := by
  subst h
  exact dif_neg hi

variable (K) in
@[simp]
/--
lemma `truncGE'Map_id` / 引理 `truncGE'Map_id`

English:
lemma truncGE'Map_id
  statement: truncGE'Map (𝟙 K) e = 𝟙 _
  proof: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

@[reassoc, simp]

中文:
引理 truncGE'Map_id
  结论: truncGE'Map (𝟙 K) e = 𝟙 _
  证明: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

@[reassoc, simp]
-/
lemma truncGE'Map_id : truncGE'Map (𝟙 K) e = 𝟙 _ := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

@[reassoc, simp]
/--
lemma `truncGE'Map_comp` / 引理 `truncGE'Map_comp`

English:
lemma truncGE'Map_comp
  statement: truncGE'Map (φ ≫ φ') e = truncGE'Map φ e ≫ truncGE'Map φ' e
  proof: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

中文:
引理 truncGE'Map_comp
  结论: truncGE'Map (φ ≫ φ') e = truncGE'Map φ e ≫ truncGE'Map φ' e
  证明: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [truncGE'Map_f_eq _ _ hi rfl]
-/
lemma truncGE'Map_comp : truncGE'Map (φ ≫ φ') e = truncGE'Map φ e ≫ truncGE'Map φ' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [truncGE'Map_f_eq_opcyclesMap _ _ hi rfl, opcyclesMap_comp]
  · simp [truncGE'Map_f_eq _ _ hi rfl]

variable [HasZeroObject C]

/--
Definition of `truncGEMap` / `truncGEMap` 的定义

English:
definition truncGEMap
  signature: : K.truncGE e ⟶ L.truncGE e
  body: (e.extendFunctor C).map (truncGE'Map φ e)

中文:
定义 truncGEMap
  签名: : K.truncGE e ⟶ L.truncGE e
  定义体: (e.extendFunctor C).map (truncGE'Map φ e)

Depends on / 依赖: e.extendFunctor, extendFunctor, truncGE
-/
noncomputable def truncGEMap : K.truncGE e ⟶ L.truncGE e :=
  (e.extendFunctor C).map (truncGE'Map φ e)

variable (K) in
@[simp]
/--
lemma `truncGEMap_id` / 引理 `truncGEMap_id`

English:
lemma truncGEMap_id
  statement: truncGEMap (𝟙 K) e = 𝟙 _
  proof: by
  simp [truncGEMap, truncGE]

@[reassoc, simp]

中文:
引理 truncGEMap_id
  结论: truncGEMap (𝟙 K) e = 𝟙 _
  证明: by
  simp [truncGEMap, truncGE]

@[reassoc, simp]

Depends on / 依赖: truncGE, truncGEMap
-/
lemma truncGEMap_id : truncGEMap (𝟙 K) e = 𝟙 _ := by
  simp [truncGEMap, truncGE]

@[reassoc, simp]
/--
lemma `truncGEMap_comp` / 引理 `truncGEMap_comp`

English:
lemma truncGEMap_comp
  statement: truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e
  proof: by
  simp [truncGEMap, truncGE]

中文:
引理 truncGEMap_comp
  结论: truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e
  证明: by
  simp [truncGEMap, truncGE]

Depends on / 依赖: truncGE, truncGEMap
-/
lemma truncGEMap_comp : truncGEMap (φ ≫ φ') e = truncGEMap φ e ≫ truncGEMap φ' e := by
  simp [truncGEMap, truncGE]

end

namespace restrictionToTruncGE'

open scoped Classical in
/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: (i : ι)
  body: if hi : e.BoundaryGE i then
    K.pOpcycles _ ≫ (K.truncGE'XIsoOpcycles e rfl hi).inv
  else
    (K.truncGE'XIso e rfl hi).inv

中文:
定义 f
  签名: (i : ι)
  定义体: if hi : e.BoundaryGE i then
    K.pOpcycles _ ≫ (K.truncGE'XIsoOpcycles e rfl hi).inv
  else
    (K.truncGE'XIso e rfl hi).inv

Depends on / 依赖: BoundaryGE, K.pOpcycles, K.truncGE, XIsoOpcycles, e.BoundaryGE, pOpcycles, truncGE
-/
noncomputable def f (i : ι) : (K.restriction e).X i ⟶ (K.truncGE' e).X i :=
  if hi : e.BoundaryGE i then
    K.pOpcycles _ ≫ (K.truncGE'XIsoOpcycles e rfl hi).inv
  else
    (K.truncGE'XIso e rfl hi).inv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `f_eq_iso_hom_pOpcycles_iso_inv` / 引理 `f_eq_iso_hom_pOpcycles_iso_inv`

English:
lemma f_eq_iso_hom_pOpcycles_iso_inv
  given: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  proof: by
  dsimp [f]
  rw [dif_pos hi]
  subst hi'
  simp [restrictionXIso]

中文:
引理 f_eq_iso_hom_pOpcycles_iso_inv
  条件: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i)
  证明: by
  dsimp [f]
  rw [dif_pos hi]
  subst hi'
  simp [restrictionXIso]

Depends on / 依赖: dif_pos, restrictionXIso
-/
lemma f_eq_iso_hom_pOpcycles_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  dsimp [f]
  rw [dif_pos hi]
  subst hi'
  simp [restrictionXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `f_eq_iso_hom_iso_inv` / 引理 `f_eq_iso_hom_iso_inv`

English:
lemma f_eq_iso_hom_iso_inv
  given: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  proof: by
  dsimp [f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

中文:
引理 f_eq_iso_hom_iso_inv
  条件: {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i)
  证明: by
  dsimp [f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

Depends on / 依赖: dif_neg, restrictionXIso
-/
lemma f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryGE i) :
    f K e i = (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  dsimp [f]
  rw [dif_neg hi]
  subst hi'
  simp [restrictionXIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  given: (i j : ι)
  proof: by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [f_eq_iso_hom_pOpcycles_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [f_eq_iso_hom_iso_inv K e

中文:
引理 comm
  条件: (i j : ι)
  证明: by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [f_eq_iso_hom_pOpcycles_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [f_eq_iso_hom_iso_inv K e

Depends on / 依赖: BoundaryGE, HomologicalComplex, HomologicalComplex.shape, K.truncGE, _d_eq, _d_eq_fromOpcycles, c.Rel, e.BoundaryGE, e.not_boundaryGE_next, f_eq_iso_hom_iso_inv, f_eq_iso_hom_pOpcycles_iso_inv, not_boundaryGE_next, restrictionXIso, truncGE
-/
lemma comm (i j : ι) :
    f K e i ≫ (K.truncGE' e).d i j = (K.restriction e).d i j ≫ f K e j := by
  by_cases hij : c.Rel i j
  · by_cases hi : e.BoundaryGE i
    · rw [f_eq_iso_hom_pOpcycles_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq_fromOpcycles e hij rfl rfl hi]
      simp [restrictionXIso]
    · rw [f_eq_iso_hom_iso_inv K e rfl hi,
        f_eq_iso_hom_iso_inv K e rfl (e.not_boundaryGE_next hij),
        K.truncGE'_d_eq e hij rfl rfl hi]
      simp [restrictionXIso]
  · simp [HomologicalComplex.shape _ _ _ hij]

end restrictionToTruncGE'

/--
Definition of `restrictionToTruncGE'` / `restrictionToTruncGE'` 的定义

English:
definition restrictionToTruncGE'
  signature: : K.restriction e ⟶ K.truncGE' e where
  body: restrictionToTruncGE'.f K e

中文:
定义 restrictionToTruncGE'
  签名: : K.restriction e ⟶ K.truncGE' e where
  定义体: restrictionToTruncGE'.f K e

Depends on / 依赖: restrictionToTruncGE
-/
noncomputable def restrictionToTruncGE' : K.restriction e ⟶ K.truncGE' e where
  f := restrictionToTruncGE'.f K e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `restrictionToTruncGE'_hasLift` / 引理 `restrictionToTruncGE'_hasLift`

English:
lemma restrictionToTruncGE'_hasLift
  statement: e.HasLift (K.restrictionToTruncGE' e)
  proof: by
  intro j hj i' _
  dsimp [restrictionToTruncGE']
  rw [restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv K e rfl hj]
  simp [restrictionXIso]

中文:
引理 restrictionToTruncGE'_hasLift
  结论: e.有Lift (K.restrictionToTruncGE' e)
  证明: by
  intro j hj i' _
  dsimp [restrictionToTruncGE']
  rw [restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv K e rfl hj]
  simp [restrictionXIso]
-/
lemma restrictionToTruncGE'_hasLift : e.HasLift (K.restrictionToTruncGE' e) := by
  intro j hj i' _
  dsimp [restrictionToTruncGE']
  rw [restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv K e rfl hj]
  simp [restrictionXIso]

/--
lemma `restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv` / 引理 `restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv`

English:
lemma restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
  proof: by
  apply restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv

中文:
引理 restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
  证明: by
  apply restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv
-/
lemma restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i = (K.restrictionXIso e hi').hom ≫ K.pOpcycles i' ≫
      (K.truncGE'XIsoOpcycles e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_iso_hom_pOpcycles_iso_inv

/--
lemma `restrictionToTruncGE'_f_eq_iso_hom_iso_inv` / 引理 `restrictionToTruncGE'_f_eq_iso_hom_iso_inv`

English:
lemma restrictionToTruncGE'_f_eq_iso_hom_iso_inv
  statement: {i : ι} {i' : ι'} (hi' : e.f i = i')
  proof: by
  apply restrictionToTruncGE'.f_eq_iso_hom_iso_inv

中文:
引理 restrictionToTruncGE'_f_eq_iso_hom_iso_inv
  结论: {i : ι} {i' : ι'} (hi' : e.f i = i')
  证明: by
  apply restrictionToTruncGE'.f_eq_iso_hom_iso_inv
-/
lemma restrictionToTruncGE'_f_eq_iso_hom_iso_inv {i : ι} {i' : ι'} (hi' : e.f i = i')
    (hi : ¬ e.BoundaryGE i) :
    (K.restrictionToTruncGE' e).f i =
      (K.restrictionXIso e hi').hom ≫ (K.truncGE'XIso e hi' hi).inv := by
  apply restrictionToTruncGE'.f_eq_iso_hom_iso_inv

/--
lemma `isIso_restrictionToTruncGE'` / 引理 `isIso_restrictionToTruncGE'`

English:
lemma isIso_restrictionToTruncGE'
  given: (i : ι) (hi : ¬ e.BoundaryGE i)
  proof: by
  rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
  infer_instance

中文:
引理 isIso_restrictionToTruncGE'
  条件: (i : ι) (hi : ¬ e.BoundaryGE i)
  证明: by
  rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
  infer_instance

Depends on / 依赖: K.restrictionToTruncGE, _f_eq_iso_hom_iso_inv, infer_instance, restrictionToTruncGE
-/
lemma isIso_restrictionToTruncGE' (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {K L} in
@[reassoc (attr := simp)]
/--
lemma `restrictionToTruncGE'_naturality` / 引理 `restrictionToTruncGE'_naturality`

English:
lemma restrictionToTruncGE'_naturality
  proof: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ e rfl hi,
      truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ e rfl hi,
      truncGE'Map_f_eq φ e hi rfl, restrictionXIso]

中文:
引理 restrictionToTruncGE'_naturality
  证明: by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ e rfl hi,
      truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ e rfl hi,
      truncGE'Map_f_eq φ e hi rfl, restrictionXIso]
-/
lemma restrictionToTruncGE'_naturality :
    K.restrictionToTruncGE' e ≫ truncGE'Map φ e =
      restrictionMap φ e ≫ L.restrictionToTruncGE' e := by
  ext i
  by_cases hi : e.BoundaryGE i
  · simp [restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv _ e rfl hi,
      truncGE'Map_f_eq_opcyclesMap φ e hi rfl, restrictionXIso]
  · simp [restrictionToTruncGE'_f_eq_iso_hom_iso_inv _ e rfl hi,
      truncGE'Map_f_eq φ e hi rfl, restrictionXIso]

attribute [local instance] epi_comp in
instance (i : ι) : Epi ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    infer_instance
  · have := K.isIso_restrictionToTruncGE' e i hi
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] (i
  body: by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    have : IsIso (K.pOpcycles (e.f i)) := K.isIso_pOpcycles _ _ rfl (by
      obtain ⟨hi₁, hi₂⟩ := hi
      apply IsZero.eq_of_src (K.isZero_X_of_isStrictlySupported e _
        (fun j hj => hi

中文:
实例 [K.是StrictlySupported
  签名: e] (i
  定义体: by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    have : IsIso (K.pOpcycles (e.f i)) := K.isIso_pOpcycles _ _ rfl (by
      obtain ⟨hi₁, hi₂⟩ := hi
      apply IsZero.eq_of_src (K.isZero_X_of_isStrictlySupported e _
        (fun j hj => hi

Depends on / 依赖: BoundaryGE, IsZero, IsZero.eq_of_src, K.isIso_pOpcycles, K.isZero_X_of_isStrictlySupported, K.pOpcycles, K.restrictionToTruncGE, _f_eq_iso_hom_iso_inv, _f_eq_iso_hom_pOpcycles_iso_inv, e.BoundaryGE, eq_of_src, infer_instance, isIso_pOpcycles, isZero_X_of_isStrictlySupported, pOpcycles, restrictionToTruncGE
-/
instance [K.IsStrictlySupported e] (i : ι) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  by_cases hi : e.BoundaryGE i
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e rfl hi]
    have : IsIso (K.pOpcycles (e.f i)) := K.isIso_pOpcycles _ _ rfl (by
      obtain ⟨hi₁, hi₂⟩ := hi
      apply IsZero.eq_of_src (K.isZero_X_of_isStrictlySupported e _
        (fun j hj => hi₂ j (by simpa only [hj] using hi₁))))
    infer_instance
  · rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
    infer_instance

section

variable [HasZeroObject C]

/--
Definition of `πTruncGE` / `πTruncGE` 的定义

English:
definition πTruncGE
  signature: : K ⟶ K.truncGE e
  body: e.liftExtend (K.restrictionToTruncGE' e) (K.restrictionToTruncGE'_hasLift e)

中文:
定义 πTruncGE
  签名: : K ⟶ K.truncGE e
  定义体: e.liftExtend (K.restrictionToTruncGE' e) (K.restrictionToTruncGE'_hasLift e)

Depends on / 依赖: K.restrictionToTruncGE, _hasLift, e.liftExtend, liftExtend, restrictionToTruncGE
-/
noncomputable def πTruncGE : K ⟶ K.truncGE e :=
  e.liftExtend (K.restrictionToTruncGE' e) (K.restrictionToTruncGE'_hasLift e)

set_option backward.isDefEq.respectTransparency false in
instance (i' : ι') : Epi ((K.πTruncGE e).f i') := by
  by_cases hi' : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    dsimp [πTruncGE]
    rw [e.epi_liftExtend_f_iff _ _ hi]
    infer_instance
  · apply (isZero_extend_X _ _ _ (by simpa using hi')).epi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (K.πTruncGE e)
  body: epi_of_epi_f _ (fun _ => inferInstance)

中文:
实例 :
  签名: 满态射 (K.πTruncGE e)
  定义体: epi_of_epi_f _ (fun _ => inferInstance)

Depends on / 依赖: epi_of_epi_f
-/
instance : Epi (K.πTruncGE e) := epi_of_epi_f _ (fun _ => inferInstance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (K.truncGE e).IsStrictlySupported e
  body: by
  dsimp [truncGE]
  infer_instance

中文:
实例 :
  签名: (K.truncGE e).是StrictlySupported e
  定义体: by
  dsimp [truncGE]
  infer_instance

Depends on / 依赖: infer_instance, truncGE
-/
instance : (K.truncGE e).IsStrictlySupported e := by
  dsimp [truncGE]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {K L} in
@[reassoc (attr := simp)]
/--
lemma `πTruncGE_naturality` / 引理 `πTruncGE_naturality`

English:
lemma πTruncGE_naturality
  proof: by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [truncGEMap, πTruncGE]
  rw [e.homRestrict_comp_extendMap]; rw [e.homRestrict_liftExtend]; rw [e.homRestrict_precomp]; rw [e.homRestrict_liftExtend]; rw [restrictionToTruncGE'_naturality]

中文:
引理 πTruncGE_naturality
  证明: by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [truncGEMap, πTruncGE]
  rw [e.homRestrict_comp_extendMap]; rw [e.homRestrict_liftExtend]; rw [e.homRestrict_precomp]; rw [e.homRestrict_liftExtend]; rw [restrictionToTruncGE'_naturality]

Depends on / 依赖: _naturality, e.homEquiv, e.homRestrict_comp_extendMap, e.homRestrict_liftExtend, e.homRestrict_precomp, homEquiv, homRestrict_comp_extendMap, homRestrict_liftExtend, homRestrict_precomp, injective, restrictionToTruncGE, truncGEMap
-/
lemma πTruncGE_naturality :
    K.πTruncGE e ≫ truncGEMap φ e = φ ≫ L.πTruncGE e := by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [truncGEMap, πTruncGE]
  rw [e.homRestrict_comp_extendMap]; rw [e.homRestrict_liftExtend]; rw [e.homRestrict_precomp]; rw [e.homRestrict_liftExtend]; rw [restrictionToTruncGE'_naturality]

set_option backward.isDefEq.respectTransparency false in
instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncGE e).IsStrictlySupported e' where
  isZero := by
    intro i' hi'
    by_cases hi'' : exists i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi''
      by_cases hi''' : e.BoundaryGE i
      · rw [IsZero.iff_id_eq_zero, ← cancel_epi
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIsoOpcycles e hi hi''').inv,
          ← cancel_epi (HomologicalComplex.pOpcycles _ _)]
        apply (K.isZero_X_of_isStrictlySupported e' i' hi').eq_of_src
      · exact (K.isZero_X_of_isStrictlySupported e' i' hi').of_iso
          ((K.truncGE' e).extendXIso e hi ≪≫ K.truncGE'XIso e hi hi''')
    · exact (K.truncGE e).isZero_X_of_isStrictlySupported e _ (by simpa using hi'')

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] : IsIso (K.πTruncGE e)
  body: by
  suffices forall (i' : ι'), IsIso ((K.πTruncGE e).f i') by
    apply Hom.isIso_of_components
  intro i'
  by_cases! hn : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hn
    dsimp [πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi]
    infer_instance
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply

中文:
实例 [K.是StrictlySupported
  签名: e] : 是同构 (K.πTruncGE e)
  定义体: by
  suffices forall (i' : ι'), IsIso ((K.πTruncGE e).f i') by
    apply Hom.isIso_of_components
  intro i'
  by_cases! hn : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hn
    dsimp [πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi]
    infer_instance
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply

Depends on / 依赖: Hom.isIso_of_components, all_goals, e.isIso_liftExtend_f_iff, eq_of_src, infer_instance, isIso_liftExtend_f_iff, isIso_of_components, isZero_X_of_isStrictlySupported
-/
instance [K.IsStrictlySupported e] : IsIso (K.πTruncGE e) := by
  suffices forall (i' : ι'), IsIso ((K.πTruncGE e).f i') by
    apply Hom.isIso_of_components
  intro i'
  by_cases! hn : exists i, e.f i = i'
  · obtain ⟨i, hi⟩ := hn
    dsimp [πTruncGE]
    rw [e.isIso_liftExtend_f_iff _ _ hi]
    infer_instance
  · refine ⟨0, ?_, ?_⟩
    all_goals
      apply (isZero_X_of_isStrictlySupported _ e i' hn).eq_of_src

/--
lemma `isIso_πTruncGE_iff` / 引理 `isIso_πTruncGE_iff`

English:
lemma isIso_πTruncGE_iff
  statement: IsIso (K.πTruncGE e) ↔ K.IsStrictlySupported e
  proof: ⟨fun _ => isStrictlySupported_of_iso (asIso (K.πTruncGE e)).symm e,
    fun _ => inferInstance⟩

中文:
引理 isIso_πTruncGE_iff
  结论: 是同构 (K.πTruncGE e) ↔ K.是StrictlySupported e
  证明: ⟨fun _ => isStrictlySupported_of_iso (asIso (K.πTruncGE e)).symm e,
    fun _ => inferInstance⟩

Depends on / 依赖: isStrictlySupported_of_iso
-/
lemma isIso_πTruncGE_iff : IsIso (K.πTruncGE e) ↔ K.IsStrictlySupported e :=
  ⟨fun _ => isStrictlySupported_of_iso (asIso (K.πTruncGE e)).symm e,
    fun _ => inferInstance⟩

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncGE]
    (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
/--
Definition of `truncGE'Functor` / `truncGE'Functor` 的定义

English:
definition truncGE'Functor
  signature: :
  body: K.truncGE' e
  map φ := HomologicalComplex.truncGE'Map φ e

中文:
定义 truncGE'函子
  签名: :
  定义体: K.truncGE' e
  map φ := HomologicalComplex.truncGE'Map φ e

Depends on / 依赖: K.truncGE, truncGE
-/
noncomputable def truncGE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncGE' e
  map φ := HomologicalComplex.truncGE'Map φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.restriction e ⟶ K.truncGE' e` for all `K`. -/
@[simps]
/--
Definition of `restrictionToTruncGE'NatTrans` / `restrictionToTruncGE'NatTrans` 的定义

English:
definition restrictionToTruncGE'NatTrans
  signature: :
  body: K.restrictionToTruncGE' e

中文:
定义 restrictionToTruncGE'自然变换
  签名: :
  定义体: K.restrictionToTruncGE' e

Depends on / 依赖: K.restrictionToTruncGE, restrictionToTruncGE
-/
noncomputable def restrictionToTruncGE'NatTrans :
    e.restrictionFunctor C ⟶ e.truncGE'Functor C where
  app K := K.restrictionToTruncGE' e

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncGE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`. -/
@[simps]
/--
Definition of `truncGEFunctor` / `truncGEFunctor` 的定义

English:
definition truncGEFunctor
  signature: :
  body: K.truncGE e
  map φ := HomologicalComplex.truncGEMap φ e

中文:
定义 truncGEFunctor
  签名: :
  定义体: K.truncGE e
  map φ := HomologicalComplex.truncGEMap φ e

Depends on / 依赖: K.truncGE, truncGE
-/
noncomputable def truncGEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncGE e
  map φ := HomologicalComplex.truncGEMap φ e

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.πTruncGE e : K ⟶ K.truncGE e` for all `K`. -/
@[simps]
/--
Definition of `πTruncGENatTrans` / `πTruncGENatTrans` 的定义

English:
definition πTruncGENatTrans
  signature: : 𝟭 _ ⟶ e.truncGEFunctor C where
  body: K.πTruncGE e

中文:
定义 πTruncGE自然数Trans
  签名: : 𝟭 _ ⟶ e.truncGEFunctor C where
  定义体: K.πTruncGE e
-/
noncomputable def πTruncGENatTrans : 𝟭 _ ⟶ e.truncGEFunctor C where
  app K := K.πTruncGE e

end ComplexShape.Embedding
