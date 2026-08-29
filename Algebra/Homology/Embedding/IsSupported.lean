/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Support of homological complexes

Given an embedding `e : c.Embedding c'` of complex shapes, we say
that `K : HomologicalComplex C c'` is supported (resp. strictly supported) on `e`
if `K` is exact in degree `i'` (resp. `K.X i'` is zero) whenever `i'` is
not of the form `e.f i`. This defines two typeclasses `K.IsSupported e`
and `K.IsStrictlySupported e`.

We also define predicates `K.IsSupportedOutside e` and `K.IsStrictlySupportedOutside e`
when the conditions above are satisfied for those `i'` that are of the form `e.f i`.
(These two predicates are not made typeclasses because in most practical applications,
they are equivalent to `K.IsSupported e'` or `K.IsStrictlySupported e'` for a
complementary embedding `e'`.)

-/

public section

open CategoryTheory Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

/--
Definition of `IsStrictlySupported` / `IsStrictlySupported` 的定义

English:
class IsStrictlySupported
  parameters: : Prop where
  axioms and operations (1):
    - isZero((i' : ι') (hi' : forall i, e.f i != i')) : IsZero (K.X i')

中文:
类 是StrictlySupported
  参数: : 命题 where
  公理与运算 (1 个):
    - isZero((i' : ι') (hi' : 对任意 i, e.f i != i')) : 是零 (K.X i')
-/
class IsStrictlySupported : Prop where
  isZero (i' : ι') (hi' : forall i, e.f i != i') : IsZero (K.X i')

/--
lemma `isZero_X_of_isStrictlySupported` / 引理 `isZero_X_of_isStrictlySupported`

English:
lemma isZero_X_of_isStrictlySupported
  statement: [K.IsStrictlySupported e]
  proof: IsStrictlySupported.isZero i' hi'

include e' in

中文:
引理 isZero_X_of_isStrictlySupported
  结论: [K.是StrictlySupported e]
  证明: IsStrictlySupported.isZero i' hi'

include e' in

Depends on / 依赖: IsStrictlySupported, IsStrictlySupported.isZero, isZero
-/
lemma isZero_X_of_isStrictlySupported [K.IsStrictlySupported e]
    (i' : ι') (hi' : forall i, e.f i != i') :
    IsZero (K.X i') :=
  IsStrictlySupported.isZero i' hi'

include e' in
variable {K L} in
/--
lemma `isStrictlySupported_of_iso` / 引理 `isStrictlySupported_of_iso`

English:
lemma isStrictlySupported_of_iso
  given: [K.IsStrictlySupported e]
  statement: L.IsStrictlySupported e where
  proof: (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

@[simp]

中文:
引理 isStrictlySupported_of_iso
  条件: [K.是StrictlySupported e]
  结论: L.是StrictlySupported e where
  证明: (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

@[simp]

Depends on / 依赖: K.isZero_X_of_isStrictlySupported, isZero_X_of_isStrictlySupported, of_iso
-/
lemma isStrictlySupported_of_iso [K.IsStrictlySupported e] : L.IsStrictlySupported e where
  isZero i' hi' := (K.isZero_X_of_isStrictlySupported e i' hi').of_iso
    ((eval _ _ i').mapIso e'.symm)

@[simp]
/--
lemma `isStrictlySupported_op_iff` / 引理 `isStrictlySupported_op_iff`

English:
lemma isStrictlySupported_op_iff
  proof: ⟨(fun _ => ⟨fun i' hi' => (K.op.isZero_X_of_isStrictlySupported e.op i' hi').unop⟩),
    (fun _ => ⟨fun i' hi' => (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩

中文:
引理 isStrictlySupported_op_iff
  证明: ⟨(fun _ => ⟨fun i' hi' => (K.op.isZero_X_of_isStrictlySupported e.op i' hi').unop⟩),
    (fun _ => ⟨fun i' hi' => (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩

Depends on / 依赖: K.isZero_X_of_isStrictlySupported, K.op.isZero_X_of_isStrictlySupported, e.op, isZero_X_of_isStrictlySupported
-/
lemma isStrictlySupported_op_iff :
    K.op.IsStrictlySupported e.op ↔ K.IsStrictlySupported e :=
  ⟨(fun _ => ⟨fun i' hi' => (K.op.isZero_X_of_isStrictlySupported e.op i' hi').unop⟩),
    (fun _ => ⟨fun i' hi' => (K.isZero_X_of_isStrictlySupported e i' hi').op⟩)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] : K.op.IsStrictlySupported e.op
  body: by
  rw [isStrictlySupported_op_iff]
  infer_instance

中文:
实例 [K.是StrictlySupported
  签名: e] : K.op.是StrictlySupported e.op
  定义体: by
  rw [isStrictlySupported_op_iff]
  infer_instance

Depends on / 依赖: infer_instance, isStrictlySupported_op_iff
-/
instance [K.IsStrictlySupported e] : K.op.IsStrictlySupported e.op := by
  rw [isStrictlySupported_op_iff]
  infer_instance

/-- If `K : HomologicalComplex C c'`, then `K.IsStrictlySupported e` holds for
an embedding `e : c.Embedding c'` of complex shapes if `K` is exact at `i'`
whenever `i'` is not of the form `e.f i` for some `i`. -/
@[mk_iff]
/--
Definition of `IsSupported` / `IsSupported` 的定义

English:
class IsSupported
  parameters: : Prop where
  axioms and operations (1):
    - exactAt((i' : ι') (hi' : forall i, e.f i != i')) : K.ExactAt i'

中文:
类 是Supported
  参数: : 命题 where
  公理与运算 (1 个):
    - exactAt((i' : ι') (hi' : 对任意 i, e.f i != i')) : K.ExactAt i'
-/
class IsSupported : Prop where
  exactAt (i' : ι') (hi' : forall i, e.f i != i') : K.ExactAt i'

/--
lemma `exactAt_of_isSupported` / 引理 `exactAt_of_isSupported`

English:
lemma exactAt_of_isSupported
  given: [K.IsSupported e] (i' : ι') (hi' : forall i, e.f i != i')
  proof: IsSupported.exactAt i' hi'

include e' in

中文:
引理 exactAt_of_isSupported
  条件: [K.是Supported e] (i' : ι') (hi' : 对任意 i, e.f i != i')
  证明: IsSupported.exactAt i' hi'

include e' in

Depends on / 依赖: IsSupported, IsSupported.exactAt, exactAt
-/
lemma exactAt_of_isSupported [K.IsSupported e] (i' : ι') (hi' : forall i, e.f i != i') :
    K.ExactAt i' :=
  IsSupported.exactAt i' hi'

include e' in
variable {K L} in
/--
lemma `isSupported_of_iso` / 引理 `isSupported_of_iso`

English:
lemma isSupported_of_iso
  given: [K.IsSupported e]
  statement: L.IsSupported e where
  proof: (K.exactAt_of_isSupported e i' hi').of_iso e'

中文:
引理 isSupported_of_iso
  条件: [K.是Supported e]
  结论: L.是Supported e where
  证明: (K.exactAt_of_isSupported e i' hi').of_iso e'

Depends on / 依赖: K.exactAt_of_isSupported, exactAt_of_isSupported, of_iso
-/
lemma isSupported_of_iso [K.IsSupported e] : L.IsSupported e where
  exactAt i' hi' :=
    (K.exactAt_of_isSupported e i' hi').of_iso e'

variable {K L} in
/--
lemma `isSupported_iff_of_quasiIso` / 引理 `isSupported_iff_of_quasiIso`

English:
lemma isSupported_iff_of_quasiIso
  statement: [forall i, K.HasHomology i] [forall i, L.HasHomology i]
  proof: by
  simp [isSupported_iff, exactAt_iff_of_quasiIsoAt φ]

中文:
引理 isSupported_iff_of_quasiIso
  结论: [对任意 i, K.有同调 i] [对任意 i, L.有同调 i]
  证明: by
  simp [isSupported_iff, exactAt_iff_of_quasiIsoAt φ]

Depends on / 依赖: exactAt_iff_of_quasiIsoAt, isSupported_iff
-/
lemma isSupported_iff_of_quasiIso [forall i, K.HasHomology i] [forall i, L.HasHomology i]
    [QuasiIso φ] :
    K.IsSupported e ↔ L.IsSupported e := by
  simp [isSupported_iff, exactAt_iff_of_quasiIsoAt φ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.IsStrictlySupported
  signature: e] : K.IsSupported e where
  body: by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

@[simp]

中文:
实例 [K.是StrictlySupported
  签名: e] : K.是Supported e where
  定义体: by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

@[simp]

Depends on / 依赖: K.isZero_X_of_isStrictlySupported, ShortComplex, ShortComplex.exact_of_isZero_X, exactAt_iff, isZero_X_of_isStrictlySupported
-/
instance [K.IsStrictlySupported e] : K.IsSupported e where
  exactAt i' hi' := by
    rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_X_of_isStrictlySupported e i' hi')

@[simp]
/--
lemma `isSupported_op_iff` / 引理 `isSupported_op_iff`

English:
lemma isSupported_op_iff
  proof: ⟨fun _ => ⟨fun i' hi' => (K.op.exactAt_of_isSupported e.op i' hi').unop⟩,
    fun _ => ⟨fun i' hi' => (K.exactAt_of_isSupported e i' hi').op⟩⟩

中文:
引理 isSupported_op_iff
  证明: ⟨fun _ => ⟨fun i' hi' => (K.op.exactAt_of_isSupported e.op i' hi').unop⟩,
    fun _ => ⟨fun i' hi' => (K.exactAt_of_isSupported e i' hi').op⟩⟩

Depends on / 依赖: K.exactAt_of_isSupported, K.op.exactAt_of_isSupported, e.op, exactAt_of_isSupported
-/
lemma isSupported_op_iff :
    K.op.IsSupported e.op ↔ K.IsSupported e :=
  ⟨fun _ => ⟨fun i' hi' => (K.op.exactAt_of_isSupported e.op i' hi').unop⟩,
    fun _ => ⟨fun i' hi' => (K.exactAt_of_isSupported e i' hi').op⟩⟩

/--
Definition of `IsStrictlySupportedOutside` / `IsStrictlySupportedOutside` 的定义

English:
structure IsStrictlySupportedOutside
  parameters: : Prop where
  axioms and operations (1):
    - isZero((i : ι)) : IsZero (K.X (e.f i))

中文:
结构 是StrictlySupportedOutside
  参数: : 命题 where
  公理与运算 (1 个):
    - isZero((i : ι)) : 是零 (K.X (e.f i))
-/
structure IsStrictlySupportedOutside : Prop where
  isZero (i : ι) : IsZero (K.X (e.f i))

@[simp]
/--
lemma `isStrictlySupportedOutside_op_iff` / 引理 `isStrictlySupportedOutside_op_iff`

English:
lemma isStrictlySupportedOutside_op_iff
  proof: ⟨fun h => ⟨fun i => (h.isZero i).unop⟩, fun h => ⟨fun i => (h.isZero i).op⟩⟩

中文:
引理 isStrictlySupportedOutside_op_iff
  证明: ⟨fun h => ⟨fun i => (h.isZero i).unop⟩, fun h => ⟨fun i => (h.isZero i).op⟩⟩

Depends on / 依赖: h.isZero, isZero
-/
lemma isStrictlySupportedOutside_op_iff :
    K.op.IsStrictlySupportedOutside e.op ↔ K.IsStrictlySupportedOutside e :=
  ⟨fun h => ⟨fun i => (h.isZero i).unop⟩, fun h => ⟨fun i => (h.isZero i).op⟩⟩

/--
Definition of `IsSupportedOutside` / `IsSupportedOutside` 的定义

English:
structure IsSupportedOutside
  parameters: : Prop where
  axioms and operations (1):
    - exactAt((i : ι)) : K.ExactAt (e.f i)

中文:
结构 是SupportedOutside
  参数: : 命题 where
  公理与运算 (1 个):
    - exactAt((i : ι)) : K.ExactAt (e.f i)
-/
structure IsSupportedOutside : Prop where
  exactAt (i : ι) : K.ExactAt (e.f i)

@[simp]
/--
lemma `isSupportedOutside_op_iff` / 引理 `isSupportedOutside_op_iff`

English:
lemma isSupportedOutside_op_iff
  proof: ⟨fun h => ⟨fun i => (h.exactAt i).unop⟩, fun h => ⟨fun i => (h.exactAt i).op⟩⟩

中文:
引理 isSupportedOutside_op_iff
  证明: ⟨fun h => ⟨fun i => (h.exactAt i).unop⟩, fun h => ⟨fun i => (h.exactAt i).op⟩⟩

Depends on / 依赖: exactAt, h.exactAt
-/
lemma isSupportedOutside_op_iff :
    K.op.IsSupportedOutside e.op ↔ K.IsSupportedOutside e :=
  ⟨fun h => ⟨fun i => (h.exactAt i).unop⟩, fun h => ⟨fun i => (h.exactAt i).op⟩⟩

variable {K e} in
/--
lemma `IsStrictlySupportedOutside.isSupportedOutside` / 引理 `IsStrictlySupportedOutside.isSupportedOutside`

English:
lemma IsStrictlySupportedOutside.isSupportedOutside
  given: (h : K.IsStrictlySupportedOutside e)
  proof: ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)

中文:
引理 是StrictlySupportedOutside.isSupportedOutside
  条件: (h : K.是StrictlySupportedOutside e)
  证明: ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)

Depends on / 依赖: ShortComplex, ShortComplex.exact_of_isZero_X, h.isZero, isZero
-/
lemma IsStrictlySupportedOutside.isSupportedOutside (h : K.IsStrictlySupportedOutside e) :
    K.IsSupportedOutside e where
  exactAt i := ShortComplex.exact_of_isZero_X₂ _ (h.isZero i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : (0
  body: (eval _ _ i).map_isZero (Limits.isZero_zero _)

中文:
实例 [有ZeroObject
  签名: C] : (0
  定义体: (eval _ _ i).map_isZero (Limits.isZero_zero _)

Depends on / 依赖: Limits, Limits.isZero_zero, isZero_zero, map_isZero
-/
instance [HasZeroObject C] : (0 : HomologicalComplex C c').IsStrictlySupported e where
  isZero i _ := (eval _ _ i).map_isZero (Limits.isZero_zero _)

/--
lemma `isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside` / 引理 `isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside`

English:
lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside
  proof: by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : exists i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.i

中文:
引理 isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside
  证明: by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : exists i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.i

Depends on / 依赖: IsZero, IsZero.eq_of_src, IsZero.iff_id_eq_zero, K.isZero_X_of_isStrictlySupported, all_goals, eq_of_src, iff_id_eq_zero, intros, isZero, isZero_X_of_isStrictlySupported, map_isZero
-/
lemma isZero_iff_isStrictlySupported_and_isStrictlySupportedOutside :
    IsZero K ↔ K.IsStrictlySupported e ∧ K.IsStrictlySupportedOutside e := by
  constructor
  · intro hK
    constructor
    all_goals
      constructor
      intros
      exact (eval _ _ _).map_isZero hK
  · rintro ⟨h₁, h₂⟩
    rw [IsZero.iff_id_eq_zero]
    ext n
    apply IsZero.eq_of_src
    by_cases hn : exists i, e.f i = n
    · obtain ⟨i, rfl⟩ := hn
      exact h₂.isZero i
    · exact K.isZero_X_of_isStrictlySupported e _ (by simpa using hn)

end

section

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (K : HomologicalComplex C c') (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `map_isStrictlySupported` / 实例 `map_isStrictlySupported`

English:
instance map_isStrictlySupported
  signature: [K.IsStrictlySupported e]
  body: by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id]; rw [(K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0]; rw [F.map_zero]

中文:
实例 map_isStrictlySupported
  签名: [K.是StrictlySupported e]
  定义体: by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id]; rw [(K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0]; rw [F.map_zero]

Depends on / 依赖: F.map_id, F.map_zero, IsZero, IsZero.iff_id_eq_zero, K.isZero_X_of_isStrictlySupported, eq_of_src, iff_id_eq_zero, isZero_X_of_isStrictlySupported, map_id, map_zero
-/
instance map_isStrictlySupported [K.IsStrictlySupported e] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e where
  isZero i' hi' := by
    rw [IsZero.iff_id_eq_zero]
    dsimp
    rw [← F.map_id]; rw [(K.isZero_X_of_isStrictlySupported e i' hi').eq_of_src (𝟙 _) 0]; rw [F.map_zero]

/--
lemma `isStrictlySupported_mapHomologicalComplex_obj_iff` / 引理 `isStrictlySupported_mapHomologicalComplex_obj_iff`

English:
lemma isStrictlySupported_mapHomologicalComplex_obj_iff
  given: [F.Faithful]
  proof: by
  refine ⟨fun _ => ⟨fun i' hi' => ?_⟩, fun _ => inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact F.map_injective ((isZero_X_of_isStrictlySupported
    ((F.mapHomologicalComplex c').obj K) e i' hi').eq_of_src _ _)

中文:
引理 isStrictlySupported_mapHomologicalComplex_obj_iff
  条件: [F.忠实]
  证明: by
  refine ⟨fun _ => ⟨fun i' hi' => ?_⟩, fun _ => inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact F.map_injective ((isZero_X_of_isStrictlySupported
    ((F.mapHomologicalComplex c').obj K) e i' hi').eq_of_src _ _)

Depends on / 依赖: F.mapHomologicalComplex, F.map_injective, IsZero, IsZero.iff_id_eq_zero, eq_of_src, iff_id_eq_zero, isZero_X_of_isStrictlySupported, mapHomologicalComplex, map_injective
-/
lemma isStrictlySupported_mapHomologicalComplex_obj_iff [F.Faithful] :
    ((F.mapHomologicalComplex c').obj K).IsStrictlySupported e ↔ K.IsStrictlySupported e := by
  refine ⟨fun _ => ⟨fun i' hi' => ?_⟩, fun _ => inferInstance⟩
  rw [IsZero.iff_id_eq_zero]
  exact F.map_injective ((isZero_X_of_isStrictlySupported
    ((F.mapHomologicalComplex c').obj K) e i' hi').eq_of_src _ _)

end

end HomologicalComplex
