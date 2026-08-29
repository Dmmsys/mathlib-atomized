/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Subgroup
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `‖x‖ = 0 → x = 0` we start setting up the
theory of `SeminormedAddGroupHom` and we specialize to `NormedAddGroupHom` when needed.
-/

@[expose] public section


noncomputable section

open NNReal

-- TODO: migrate to the new morphism / morphism_class style
/--
Definition of `NormedAddGroupHom` / `NormedAddGroupHom` 的定义

English:
structure NormedAddGroupHom
  parameters: (V W : Type*) [SeminormedAddCommGroup V]
  axioms and operations (3):
    - toFun : V -> W
    - map_add' : forall v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
    - bound' : exists C, forall v, ‖toFun v‖ <= C * ‖v‖

中文:
结构 NormedAddGroupHom
  参数: (V W : 类型) [SeminormedAddCommGroup V]
  公理与运算 (3 个):
    - toFun : V -> W
    - map_add' : 对任意 v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
    - bound' : 存在 C, 对任意 v, ‖toFun v‖ <= C * ‖v‖
-/
structure NormedAddGroupHom (V W : Type*) [SeminormedAddCommGroup V]
  [SeminormedAddCommGroup W] where
  /-- The function underlying a `NormedAddGroupHom` -/
  toFun : V -> W
  /-- A `NormedAddGroupHom` is additive. -/
  map_add' : forall v₁ v₂, toFun (v₁ + v₂) = toFun v₁ + toFun v₂
  /-- A `NormedAddGroupHom` is bounded. -/
  bound' : exists C, forall v, ‖toFun v‖ <= C * ‖v‖

namespace AddMonoidHom

variable {V W : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  {f g : NormedAddGroupHom V W}

/--
Definition of `mkNormedAddGroupHom` / `mkNormedAddGroupHom` 的定义

English:
definition mkNormedAddGroupHom
  signature: (f : V ->+ W) (C : Real) (h : forall v, ‖f v‖ <= C * ‖v‖)
  body: { f with bound' := ⟨C, h⟩ }

中文:
定义 mkNormedAddGroupHom
  签名: (f : V ->+ W) (C : 实数) (h : 对任意 v, ‖f v‖ <= C * ‖v‖)
  定义体: { f with bound' := ⟨C, h⟩ }
-/
def mkNormedAddGroupHom (f : V ->+ W) (C : Real) (h : forall v, ‖f v‖ <= C * ‖v‖) : NormedAddGroupHom V W :=
  { f with bound' := ⟨C, h⟩ }

/--
Definition of `mkNormedAddGroupHom'` / `mkNormedAddGroupHom'` 的定义

English:
definition mkNormedAddGroupHom'
  signature: (f : V ->+ W) (C : Real>=0) (hC : forall x, ‖f x‖₊ <= C * ‖x‖₊)
  body: { f with bound' := ⟨C, hC⟩ }

中文:
定义 mkNormedAddGroupHom'
  签名: (f : V ->+ W) (C : 实数>=0) (hC : 对任意 x, ‖f x‖₊ <= C * ‖x‖₊)
  定义体: { f with bound' := ⟨C, hC⟩ }
-/
def mkNormedAddGroupHom' (f : V ->+ W) (C : Real>=0) (hC : forall x, ‖f x‖₊ <= C * ‖x‖₊) :
    NormedAddGroupHom V W :=
  { f with bound' := ⟨C, hC⟩ }

end AddMonoidHom

/--
theorem `exists_pos_bound_of_bound` / 定理 `exists_pos_bound_of_bound`

English:
theorem exists_pos_bound_of_bound
  statement: {V W : Type*} [SeminormedAddCommGroup V]
  proof: ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
    calc
      ‖f x‖ <= M * ‖x‖ := h x
      _ <= max M 1 * ‖x‖ := by gcongr; apply le_max_left
      ⟩

中文:
定理 exists_pos_bound_of_bound
  结论: {V W : 类型} [SeminormedAddCommGroup V]
  证明: ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
    calc
      ‖f x‖ <= M * ‖x‖ := h x
      _ <= max M 1 * ‖x‖ := by gcongr; apply le_max_left
      ⟩

Depends on / 依赖: le_max_left, le_max_right, lt_of_lt_of_le, zero_lt_one
-/
theorem exists_pos_bound_of_bound {V W : Type*} [SeminormedAddCommGroup V]
    [SeminormedAddCommGroup W] {f : V -> W} (M : Real) (h : forall x, ‖f x‖ <= M * ‖x‖) :
    exists N, 0 < N ∧ forall x, ‖f x‖ <= N * ‖x‖ :=
  ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun x =>
    calc
      ‖f x‖ <= M * ‖x‖ := h x
      _ <= max M 1 * ‖x‖ := by gcongr; apply le_max_left
      ⟩

namespace NormedAddGroupHom

variable {V V₁ V₂ V₃ : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

variable {f g : NormedAddGroupHom V₁ V₂}

/--
Definition of `ofLipschitz` / `ofLipschitz` 的定义

English:
definition ofLipschitz
  signature: (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f)
  body: f.mkNormedAddGroupHom K fun x => by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0

中文:
定义 ofLipschitz
  签名: (f : V₁ ->+ V₂) {K : 实数>=0} (h : LipschitzWith K f)
  定义体: f.mkNormedAddGroupHom K fun x => by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0

Depends on / 依赖: dist_le_mul, dist_zero_right, f.mkNormedAddGroupHom, h.dist_le_mul, map_zero, mkNormedAddGroupHom
-/
def ofLipschitz (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f) : NormedAddGroupHom V₁ V₂ :=
  f.mkNormedAddGroupHom K fun x => by simpa only [map_zero, dist_zero_right] using h.dist_le_mul x 0

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  body: toFun
  coe_injective f g h := by cases f; cases g; congr

中文:
实例 funLike
  签名: : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  定义体: toFun
  coe_injective f g h := by cases f; cases g; congr
-/
instance funLike : FunLike (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Instance `toAddMonoidHomClass` / 实例 `toAddMonoidHomClass`

English:
instance toAddMonoidHomClass
  signature: : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  body: f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

initialize_simps_projections NormedAddGroupHom (toFun -> apply)

中文:
实例 toAddMonoidHomClass
  签名: : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  定义体: f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

initialize_simps_projections NormedAddGroupHom (toFun -> apply)

Depends on / 依赖: f.map_add, map_add
-/
instance toAddMonoidHomClass : AddMonoidHomClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  map_add f := f.map_add'
  map_zero f := (AddMonoidHom.mk' f.toFun f.map_add').map_zero

initialize_simps_projections NormedAddGroupHom (toFun -> apply)

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: (H : (f : V₁ -> V₂) = g)
  statement: f = g
  proof: by
  cases f; cases g; congr

中文:
定理 coe_inj
  条件: (H : (f : V₁ -> V₂) = g)
  结论: f = g
  证明: by
  cases f; cases g; congr
-/
theorem coe_inj (H : (f : V₁ -> V₂) = g) : f = g := by
  cases f; cases g; congr

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun
  proof: by
  apply coe_inj

中文:
定理 coe_injective
  结论: @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun
  证明: by
  apply coe_inj

Depends on / 依赖: coe_inj
-/
theorem coe_injective : @Function.Injective (NormedAddGroupHom V₁ V₂) (V₁ -> V₂) toFun := by
  apply coe_inj

/--
theorem `coe_inj_iff` / 定理 `coe_inj_iff`

English:
theorem coe_inj_iff
  statement: f = g ↔ (f : V₁ -> V₂) = g
  proof: ⟨congr_arg _, coe_inj⟩

@[ext]

中文:
定理 coe_inj_iff
  结论: f = g ↔ (f : V₁ -> V₂) = g
  证明: ⟨congr_arg _, coe_inj⟩

@[ext]

Depends on / 依赖: coe_inj, congr_arg
-/
theorem coe_inj_iff : f = g ↔ (f : V₁ -> V₂) = g :=
  ⟨congr_arg _, coe_inj⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (H : forall x, f x = g x)
  statement: f = g
  proof: coe_inj funext H

中文:
定理 ext
  条件: (H : 对任意 x, f x = g x)
  结论: f = g
  证明: coe_inj funext H

Depends on / 依赖: coe_inj
-/
theorem ext (H : forall x, f x = g x) : f = g :=
coe_inj funext H

variable (f g)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: f.toFun = f
  proof: rfl

中文:
定理 toFun_eq_coe
  结论: f.toFun = f
  证明: rfl
-/
theorem toFun_eq_coe : f.toFun = f :=
  rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f) (h₁) (h₂) (h₃)
  statement: ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f) (h₁) (h₂) (h₃)
  结论: ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : NormedAddGroupHom V₁ V₂) = f :=
  rfl

@[simp]
/--
theorem `coe_mkNormedAddGroupHom` / 定理 `coe_mkNormedAddGroupHom`

English:
theorem coe_mkNormedAddGroupHom
  given: (f : V₁ ->+ V₂) (C) (hC)
  statement: ⇑(f.mkNormedAddGroupHom C hC) = f
  proof: rfl

@[simp]

中文:
定理 coe_mkNormedAddGroupHom
  条件: (f : V₁ ->+ V₂) (C) (hC)
  结论: ⇑(f.mkNormedAddGroupHom C hC) = f
  证明: rfl

@[simp]
-/
theorem coe_mkNormedAddGroupHom (f : V₁ ->+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom C hC) = f :=
  rfl

@[simp]
/--
theorem `coe_mkNormedAddGroupHom'` / 定理 `coe_mkNormedAddGroupHom'`

English:
theorem coe_mkNormedAddGroupHom'
  given: (f : V₁ ->+ V₂) (C) (hC)
  statement: ⇑(f.mkNormedAddGroupHom' C hC) = f
  proof: rfl

中文:
定理 coe_mkNormedAddGroupHom'
  条件: (f : V₁ ->+ V₂) (C) (hC)
  结论: ⇑(f.mkNormedAddGroupHom' C hC) = f
  证明: rfl
-/
theorem coe_mkNormedAddGroupHom' (f : V₁ ->+ V₂) (C) (hC) : ⇑(f.mkNormedAddGroupHom' C hC) = f :=
  rfl

/--
Definition of `toAddMonoidHom` / `toAddMonoidHom` 的定义

English:
definition toAddMonoidHom
  signature: (f : NormedAddGroupHom V₁ V₂)
  body: AddMonoidHom.mk' f f.map_add'

@[simp]

中文:
定义 toAddMonoidHom
  签名: (f : NormedAddGroupHom V₁ V₂)
  定义体: AddMonoidHom.mk' f f.map_add'

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, f.map_add, map_add
-/
def toAddMonoidHom (f : NormedAddGroupHom V₁ V₂) : V₁ ->+ V₂ :=
  AddMonoidHom.mk' f f.map_add'

@[simp]
/--
theorem `coe_toAddMonoidHom` / 定理 `coe_toAddMonoidHom`

English:
theorem coe_toAddMonoidHom
  statement: ⇑f.toAddMonoidHom = f
  proof: rfl

中文:
定理 coe_toAddMonoidHom
  结论: ⇑f.toAddMonoidHom = f
  证明: rfl
-/
theorem coe_toAddMonoidHom : ⇑f.toAddMonoidHom = f :=
  rfl

/--
theorem `toAddMonoidHom_injective` / 定理 `toAddMonoidHom_injective`

English:
theorem toAddMonoidHom_injective
  proof: fun f g h =>
coe_inj by rw [← coe_toAddMonoidHom f, ← coe_toAddMonoidHom g, h]

@[simp]

中文:
定理 toAddMonoidHom_injective
  证明: fun f g h =>
coe_inj by rw [← coe_toAddMonoidHom f, ← coe_toAddMonoidHom g, h]

@[simp]
-/
theorem toAddMonoidHom_injective :
    Function.Injective (@NormedAddGroupHom.toAddMonoidHom V₁ V₂ _ _) := fun f g h =>
coe_inj by rw [← coe_toAddMonoidHom f, ← coe_toAddMonoidHom g, h]

@[simp]
/--
theorem `mk_toAddMonoidHom` / 定理 `mk_toAddMonoidHom`

English:
theorem mk_toAddMonoidHom
  given: (f) (h₁) (h₂)
  proof: rfl

中文:
定理 mk_toAddMonoidHom
  条件: (f) (h₁) (h₂)
  证明: rfl
-/
theorem mk_toAddMonoidHom (f) (h₁) (h₂) :
    (⟨f, h₁, h₂⟩ : NormedAddGroupHom V₁ V₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  statement: exists C, 0 < C ∧ forall x, ‖f x‖ <= C * ‖x‖
  proof: let ⟨_C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC

中文:
定理 bound
  结论: 存在 C, 0 < C ∧ 对任意 x, ‖f x‖ <= C * ‖x‖
  证明: let ⟨_C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC

Depends on / 依赖: exists_pos_bound_of_bound, f.bound
-/
theorem bound : exists C, 0 < C ∧ forall x, ‖f x‖ <= C * ‖x‖ :=
  let ⟨_C, hC⟩ := f.bound'
  exists_pos_bound_of_bound _ hC

/--
theorem `antilipschitz_of_norm_ge` / 定理 `antilipschitz_of_norm_ge`

English:
theorem antilipschitz_of_norm_ge
  given: {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖)
  statement: AntilipschitzWith K f
  proof: AntilipschitzWith.of_le_mul_dist fun x y => by simpa only [dist_eq_norm, map_sub] using h (x - y)

中文:
定理 antilipschitz_of_norm_ge
  条件: {K : 实数>=0} (h : 对任意 x, ‖x‖ <= K * ‖f x‖)
  结论: AntilipschitzWith K f
  证明: AntilipschitzWith.of_le_mul_dist fun x y => by simpa only [dist_eq_norm, map_sub] using h (x - y)

Depends on / 依赖: AntilipschitzWith, AntilipschitzWith.of_le_mul_dist, dist_eq_norm, map_sub, of_le_mul_dist
-/
theorem antilipschitz_of_norm_ge {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by simpa only [dist_eq_norm, map_sub] using h (x - y)

/--
Definition of `SurjectiveOnWith` / `SurjectiveOnWith` 的定义

English:
definition SurjectiveOnWith
  signature: (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : Real)
  body: forall h in K, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖

中文:
定义 SurjectiveOnWith
  签名: (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : 实数)
  定义体: forall h in K, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖
-/
def SurjectiveOnWith (f : NormedAddGroupHom V₁ V₂) (K : AddSubgroup V₂) (C : Real) : Prop :=
  forall h in K, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖

/--
theorem `SurjectiveOnWith.mono` / 定理 `SurjectiveOnWith.mono`

English:
theorem SurjectiveOnWith.mono
  statement: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : Real}
  proof: by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases Hg : ‖f g‖ = 0
  · simpa [Hg] using hg
  · exact hg.trans (by gcongr)

中文:
定理 SurjectiveOnWith.mono
  结论: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : 实数}
  证明: by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases Hg : ‖f g‖ = 0
  · simpa [Hg] using hg
  · exact hg.trans (by gcongr)

Depends on / 依赖: hg.trans, k_in
-/
theorem SurjectiveOnWith.mono {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C C' : Real}
    (h : f.SurjectiveOnWith K C) (H : C <= C') : f.SurjectiveOnWith K C' := by
  intro k k_in
  rcases h k k_in with ⟨g, rfl, hg⟩
  use g, rfl
  by_cases Hg : ‖f g‖ = 0
  · simpa [Hg] using hg
  · exact hg.trans (by gcongr)

/--
theorem `SurjectiveOnWith.exists_pos` / 定理 `SurjectiveOnWith.exists_pos`

English:
theorem SurjectiveOnWith.exists_pos
  statement: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : Real}
  proof: by
  refine ⟨|C| + 1, ?_, ?_⟩
  · linarith [abs_nonneg C]
  · apply h.mono
    linarith [le_abs_self C]

中文:
定理 SurjectiveOnWith.exists_pos
  结论: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : 实数}
  证明: by
  refine ⟨|C| + 1, ?_, ?_⟩
  · linarith [abs_nonneg C]
  · apply h.mono
    linarith [le_abs_self C]

Depends on / 依赖: abs_nonneg, h.mono, le_abs_self
-/
theorem SurjectiveOnWith.exists_pos {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : Real}
    (h : f.SurjectiveOnWith K C) : exists C' > 0, f.SurjectiveOnWith K C' := by
  refine ⟨|C| + 1, ?_, ?_⟩
  · linarith [abs_nonneg C]
  · apply h.mono
    linarith [le_abs_self C]

/--
theorem `SurjectiveOnWith.surjOn` / 定理 `SurjectiveOnWith.surjOn`

English:
theorem SurjectiveOnWith.surjOn
  statement: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : Real}
  proof: fun x hx =>
  (h x hx).imp fun _a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩

中文:
定理 SurjectiveOnWith.surjOn
  结论: {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : 实数}
  证明: fun x hx =>
  (h x hx).imp fun _a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩
-/
theorem SurjectiveOnWith.surjOn {f : NormedAddGroupHom V₁ V₂} {K : AddSubgroup V₂} {C : Real}
    (h : f.SurjectiveOnWith K C) : Set.SurjOn f Set.univ K := fun x hx =>
  (h x hx).imp fun _a ⟨ha, _⟩ => ⟨Set.mem_univ _, ha⟩

/-! ### The operator norm -/


/--
Definition of `opNorm` / `opNorm` 的定义

English:
definition opNorm
  signature: (f : NormedAddGroupHom V₁ V₂)
  body: sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

中文:
定义 opNorm
  签名: (f : NormedAddGroupHom V₁ V₂)
  定义体: sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
-/
def opNorm (f : NormedAddGroupHom V₁ V₂) :=
  sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }

/--
Instance `hasOpNorm` / 实例 `hasOpNorm`

English:
instance hasOpNorm
  signature: : Norm (NormedAddGroupHom V₁ V₂)
  body: ⟨opNorm⟩

中文:
实例 hasOpNorm
  签名: : Norm (NormedAddGroupHom V₁ V₂)
  定义体: ⟨opNorm⟩

Depends on / 依赖: opNorm
-/
instance hasOpNorm : Norm (NormedAddGroupHom V₁ V₂) :=
  ⟨opNorm⟩

/--
theorem `norm_def` / 定理 `norm_def`

English:
theorem norm_def
  statement: ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ }
  proof: rfl

中文:
定理 norm_def
  结论: ‖f‖ = sInf { c | 0 <= c ∧ 对任意 x, ‖f x‖ <= c * ‖x‖ }
  证明: rfl
-/
theorem norm_def : ‖f‖ = sInf { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
/--
theorem `bounds_nonempty` / 定理 `bounds_nonempty`

English:
theorem bounds_nonempty
  given: {f : NormedAddGroupHom V₁ V₂}
  proof: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

中文:
定理 bounds_nonempty
  条件: {f : NormedAddGroupHom V₁ V₂}
  证明: let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

Depends on / 依赖: f.bound, le_of_lt
-/
theorem bounds_nonempty {f : NormedAddGroupHom V₁ V₂} :
    exists c, c in { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

/--
theorem `bounds_bddBelow` / 定理 `bounds_bddBelow`

English:
theorem bounds_bddBelow
  given: {f : NormedAddGroupHom V₁ V₂}
  proof: ⟨0, fun _ ⟨hn, _⟩ => hn⟩

中文:
定理 bounds_bddBelow
  条件: {f : NormedAddGroupHom V₁ V₂}
  证明: ⟨0, fun _ ⟨hn, _⟩ => hn⟩
-/
theorem bounds_bddBelow {f : NormedAddGroupHom V₁ V₂} :
    BddBelow { c | 0 <= c ∧ forall x, ‖f x‖ <= c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

/--
theorem `opNorm_nonneg` / 定理 `opNorm_nonneg`

English:
theorem opNorm_nonneg
  statement: 0 <= ‖f‖
  proof: le_csInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

中文:
定理 opNorm_nonneg
  结论: 0 <= ‖f‖
  证明: le_csInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

Depends on / 依赖: bounds_nonempty, le_csInf
-/
theorem opNorm_nonneg : 0 <= ‖f‖ :=
  le_csInf bounds_nonempty fun _ ⟨hx, _⟩ => hx

/--
theorem `le_opNorm` / 定理 `le_opNorm`

English:
theorem le_opNorm
  given: (x : V₁)
  statement: ‖f x‖ <= ‖f‖ * ‖x‖
  proof: by
  obtain ⟨C, _Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, mul_zero] at hC ⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff₀ hlt).mp
      (le_csInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff₀ hlt).mpr <| by apply hc)

中文:
定理 le_opNorm
  条件: (x : V₁)
  结论: ‖f x‖ <= ‖f‖ * ‖x‖
  证明: by
  obtain ⟨C, _Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, mul_zero] at hC ⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff₀ hlt).mp
      (le_csInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff₀ hlt).mpr <| by apply hc)

Depends on / 依赖: Ne.symm, _Cpos, bounds_nonempty, f.bound, le_csInf, lt_of_le_of_ne, mul_zero, norm_nonneg, replace
-/
theorem le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖ := by
  obtain ⟨C, _Cpos, hC⟩ := f.bound
  replace hC := hC x
  by_cases h : ‖x‖ = 0
  · rwa [h, mul_zero] at hC ⊢
  have hlt : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  exact
    (div_le_iff₀ hlt).mp
      (le_csInf bounds_nonempty fun c ⟨_, hc⟩ => (div_le_iff₀ hlt).mpr <| by apply hc)

/--
theorem `le_opNorm_of_le` / 定理 `le_opNorm_of_le`

English:
theorem le_opNorm_of_le
  given: {c : Real} {x} (h : ‖x‖ <= c)
  statement: ‖f x‖ <= ‖f‖ * c
  proof: le_trans (f.le_opNorm x) (by gcongr; exact f.opNorm_nonneg)

中文:
定理 le_opNorm_of_le
  条件: {c : 实数} {x} (h : ‖x‖ <= c)
  结论: ‖f x‖ <= ‖f‖ * c
  证明: le_trans (f.le_opNorm x) (by gcongr; exact f.opNorm_nonneg)

Depends on / 依赖: f.le_opNorm, f.opNorm_nonneg, le_opNorm, le_trans, opNorm_nonneg
-/
theorem le_opNorm_of_le {c : Real} {x} (h : ‖x‖ <= c) : ‖f x‖ <= ‖f‖ * c :=
  le_trans (f.le_opNorm x) (by gcongr; exact f.opNorm_nonneg)

/--
theorem `le_of_opNorm_le` / 定理 `le_of_opNorm_le`

English:
theorem le_of_opNorm_le
  given: {c : Real} (h : ‖f‖ <= c) (x : V₁)
  statement: ‖f x‖ <= c * ‖x‖
  proof: (f.le_opNorm x).trans (by gcongr)

中文:
定理 le_of_opNorm_le
  条件: {c : 实数} (h : ‖f‖ <= c) (x : V₁)
  结论: ‖f x‖ <= c * ‖x‖
  证明: (f.le_opNorm x).trans (by gcongr)

Depends on / 依赖: f.le_opNorm, le_opNorm
-/
theorem le_of_opNorm_le {c : Real} (h : ‖f‖ <= c) (x : V₁) : ‖f x‖ <= c * ‖x‖ :=
  (f.le_opNorm x).trans (by gcongr)

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  statement: LipschitzWith ⟨‖f‖, opNorm_nonneg f⟩ f
  proof: LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]
    apply le_opNorm

中文:
定理 lipschitz
  结论: LipschitzWith ⟨‖f‖, opNorm_nonneg f⟩ f
  证明: LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]
    apply le_opNorm

Depends on / 依赖: LipschitzWith, LipschitzWith.of_dist_le_mul, dist_eq_norm, le_opNorm, map_sub, of_dist_le_mul
-/
theorem lipschitz : LipschitzWith ⟨‖f‖, opNorm_nonneg f⟩ f :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]
    apply le_opNorm

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (f : NormedAddGroupHom V₁ V₂)
  statement: UniformContinuous f
  proof: f.lipschitz.uniformContinuous

@[continuity]

中文:
定理 uniformContinuous
  条件: (f : NormedAddGroupHom V₁ V₂)
  结论: UniformContinuous f
  证明: f.lipschitz.uniformContinuous

@[continuity]
-/
protected theorem uniformContinuous (f : NormedAddGroupHom V₁ V₂) : UniformContinuous f :=
  f.lipschitz.uniformContinuous

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : NormedAddGroupHom V₁ V₂)
  statement: Continuous f
  proof: f.uniformContinuous.continuous

中文:
定理 continuous
  条件: (f : NormedAddGroupHom V₁ V₂)
  结论: Continuous f
  证明: f.uniformContinuous.continuous
-/
protected theorem continuous (f : NormedAddGroupHom V₁ V₂) : Continuous f :=
  f.uniformContinuous.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass (NormedAddGroupHom V₁ V₂) V₁ V₂
  body: fun f => f.continuous

中文:
实例 :
  签名: ContinuousMapClass (NormedAddGroupHom V₁ V₂) V₁ V₂
  定义体: fun f => f.continuous

Depends on / 依赖: continuous, f.continuous
-/
instance : ContinuousMapClass (NormedAddGroupHom V₁ V₂) V₁ V₂ where
  map_continuous := fun f => f.continuous

/--
theorem `ratio_le_opNorm` / 定理 `ratio_le_opNorm`

English:
theorem ratio_le_opNorm
  given: (x : V₁)
  statement: ‖f x‖ / ‖x‖ <= ‖f‖
  proof: div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

中文:
定理 ratio_le_opNorm
  条件: (x : V₁)
  结论: ‖f x‖ / ‖x‖ <= ‖f‖
  证明: div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

Depends on / 依赖: f.opNorm_nonneg, le_opNorm, norm_nonneg, opNorm_nonneg
-/
theorem ratio_le_opNorm (x : V₁) : ‖f x‖ / ‖x‖ <= ‖f‖ :=
  div_le_of_le_mul₀ (norm_nonneg _) f.opNorm_nonneg (le_opNorm _ _)

/--
theorem `opNorm_le_bound` / 定理 `opNorm_le_bound`

English:
theorem opNorm_le_bound
  given: {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖)
  statement: ‖f‖ <= M
  proof: csInf_le bounds_bddBelow ⟨hMp, hM⟩

中文:
定理 opNorm_le_bound
  条件: {M : 实数} (hMp : 0 <= M) (hM : 对任意 x, ‖f x‖ <= M * ‖x‖)
  结论: ‖f‖ <= M
  证明: csInf_le bounds_bddBelow ⟨hMp, hM⟩

Depends on / 依赖: bounds_bddBelow, csInf_le
-/
theorem opNorm_le_bound {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

/--
theorem `opNorm_eq_of_bounds` / 定理 `opNorm_eq_of_bounds`

English:
theorem opNorm_eq_of_bounds
  statement: {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖f x‖ <= M * ‖x‖)
  proof: le_antisymm (f.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff NormedAddGroupHom.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

中文:
定理 opNorm_eq_of_bounds
  结论: {M : 实数} (M_nonneg : 0 <= M) (h_above : 对任意 x, ‖f x‖ <= M * ‖x‖)
  证明: le_antisymm (f.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff NormedAddGroupHom.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

Depends on / 依赖: M_nonneg, N_nonneg, NormedAddGroupHom, NormedAddGroupHom.bounds_bddBelow, bounds_bddBelow, f.opNorm_le_bound, h_above, h_below, le_antisymm, le_csInf_iff, opNorm_le_bound
-/
theorem opNorm_eq_of_bounds {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖f x‖ <= M * ‖x‖)
    (h_below : forall N >= 0, (forall x, ‖f x‖ <= N * ‖x‖) -> M <= N) : ‖f‖ = M :=
  le_antisymm (f.opNorm_le_bound M_nonneg h_above)
    ((le_csInf_iff NormedAddGroupHom.bounds_bddBelow ⟨M, M_nonneg, h_above⟩).mpr
      fun N ⟨N_nonneg, hN⟩ => h_below N N_nonneg hN)

/--
theorem `opNorm_le_of_lipschitz` / 定理 `opNorm_le_of_lipschitz`

English:
theorem opNorm_le_of_lipschitz
  given: {f : NormedAddGroupHom V₁ V₂} {K : Real>=0} (hf : LipschitzWith K f)
  proof: f.opNorm_le_bound K.2 fun x => by simpa only [dist_zero_right, map_zero] using hf.dist_le_mul x 0

中文:
定理 opNorm_le_of_lipschitz
  条件: {f : NormedAddGroupHom V₁ V₂} {K : 实数>=0} (hf : LipschitzWith K f)
  证明: f.opNorm_le_bound K.2 fun x => by simpa only [dist_zero_right, map_zero] using hf.dist_le_mul x 0

Depends on / 依赖: dist_le_mul, dist_zero_right, f.opNorm_le_bound, hf.dist_le_mul, map_zero, opNorm_le_bound
-/
theorem opNorm_le_of_lipschitz {f : NormedAddGroupHom V₁ V₂} {K : Real>=0} (hf : LipschitzWith K f) :
    ‖f‖ <= K :=
  f.opNorm_le_bound K.2 fun x => by simpa only [dist_zero_right, map_zero] using hf.dist_le_mul x 0

/--
theorem `mkNormedAddGroupHom_norm_le` / 定理 `mkNormedAddGroupHom_norm_le`

English:
theorem mkNormedAddGroupHom_norm_le
  given: (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖)
  proof: opNorm_le_bound _ hC h

中文:
定理 mkNormedAddGroupHom_norm_le
  条件: (f : V₁ ->+ V₂) {C : 实数} (hC : 0 <= C) (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: opNorm_le_bound _ hC h

Depends on / 依赖: opNorm_le_bound
-/
theorem mkNormedAddGroupHom_norm_le (f : V₁ ->+ V₂) {C : Real} (hC : 0 <= C) (h : forall x, ‖f x‖ <= C * ‖x‖) :
    ‖f.mkNormedAddGroupHom C h‖ <= C :=
  opNorm_le_bound _ hC h

/--
theorem `ofLipschitz_norm_le` / 定理 `ofLipschitz_norm_le`

English:
theorem ofLipschitz_norm_le
  given: (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f)
  proof: mkNormedAddGroupHom_norm_le f K.coe_nonneg _

中文:
定理 ofLipschitz_norm_le
  条件: (f : V₁ ->+ V₂) {K : 实数>=0} (h : LipschitzWith K f)
  证明: mkNormedAddGroupHom_norm_le f K.coe_nonneg _

Depends on / 依赖: K.coe_nonneg, coe_nonneg, mkNormedAddGroupHom_norm_le
-/
theorem ofLipschitz_norm_le (f : V₁ ->+ V₂) {K : Real>=0} (h : LipschitzWith K f) :
    ‖ofLipschitz f h‖ <= K :=
  mkNormedAddGroupHom_norm_le f K.coe_nonneg _

/--
theorem `mkNormedAddGroupHom_norm_le'` / 定理 `mkNormedAddGroupHom_norm_le'`

English:
theorem mkNormedAddGroupHom_norm_le'
  given: (f : V₁ ->+ V₂) {C : Real} (h : forall x, ‖f x‖ <= C * ‖x‖)
  proof: opNorm_le_bound _ (le_max_right _ _) fun x =>
(h x).trans by gcongr; apply le_max_left

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le := mkNormedAddGroupHom_norm_le

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le' := mkNormedAddGroupHom_norm_le'

中文:
定理 mkNormedAddGroupHom_norm_le'
  条件: (f : V₁ ->+ V₂) {C : 实数} (h : 对任意 x, ‖f x‖ <= C * ‖x‖)
  证明: opNorm_le_bound _ (le_max_right _ _) fun x =>
(h x).trans by gcongr; apply le_max_left

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le := mkNormedAddGroupHom_norm_le

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le' := mkNormedAddGroupHom_norm_le'

Depends on / 依赖: le_max_left, le_max_right, opNorm_le_bound
-/
theorem mkNormedAddGroupHom_norm_le' (f : V₁ ->+ V₂) {C : Real} (h : forall x, ‖f x‖ <= C * ‖x‖) :
    ‖f.mkNormedAddGroupHom C h‖ <= max C 0 :=
  opNorm_le_bound _ (le_max_right _ _) fun x =>
(h x).trans by gcongr; apply le_max_left

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le := mkNormedAddGroupHom_norm_le

alias _root_.AddMonoidHom.mkNormedAddGroupHom_norm_le' := mkNormedAddGroupHom_norm_le'

/-! ### Addition of normed group homs -/


/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (NormedAddGroupHom V₁ V₂)
  body: ⟨fun f g =>
    (f.toAddMonoidHom + g.toAddMonoidHom).mkNormedAddGroupHom (‖f‖ + ‖g‖) fun v =>
      calc
        ‖f v + g v‖ <= ‖f v‖ + ‖g v‖ := norm_add_le _ _
        _ <= ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by gcongr <;> apply le_opNorm
        _ = (‖f‖ + ‖g‖) * ‖v‖ := by rw [add_mul]
        ⟩

中文:
实例 add
  签名: : Add (NormedAddGroupHom V₁ V₂)
  定义体: ⟨fun f g =>
    (f.toAddMonoidHom + g.toAddMonoidHom).mkNormedAddGroupHom (‖f‖ + ‖g‖) fun v =>
      calc
        ‖f v + g v‖ <= ‖f v‖ + ‖g v‖ := norm_add_le _ _
        _ <= ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by gcongr <;> apply le_opNorm
        _ = (‖f‖ + ‖g‖) * ‖v‖ := by rw [add_mul]
        ⟩

Depends on / 依赖: add_mul, f.toAddMonoidHom, g.toAddMonoidHom, le_opNorm, mkNormedAddGroupHom, norm_add_le, toAddMonoidHom
-/
instance add : Add (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    (f.toAddMonoidHom + g.toAddMonoidHom).mkNormedAddGroupHom (‖f‖ + ‖g‖) fun v =>
      calc
        ‖f v + g v‖ <= ‖f v‖ + ‖g v‖ := norm_add_le _ _
        _ <= ‖f‖ * ‖v‖ + ‖g‖ * ‖v‖ := by gcongr <;> apply le_opNorm
        _ = (‖f‖ + ‖g‖) * ‖v‖ := by rw [add_mul]
        ⟩

/--
theorem `opNorm_add_le` / 定理 `opNorm_add_le`

English:
theorem opNorm_add_le
  statement: ‖f + g‖ <= ‖f‖ + ‖g‖
  proof: mkNormedAddGroupHom_norm_le _ (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) _

@[simp]

中文:
定理 opNorm_add_le
  结论: ‖f + g‖ <= ‖f‖ + ‖g‖
  证明: mkNormedAddGroupHom_norm_le _ (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) _

@[simp]

Depends on / 依赖: add_nonneg, mkNormedAddGroupHom_norm_le, opNorm_nonneg
-/
theorem opNorm_add_le : ‖f + g‖ <= ‖f‖ + ‖g‖ :=
  mkNormedAddGroupHom_norm_le _ (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) _

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : NormedAddGroupHom V₁ V₂)
  statement: ⇑(f + g) = f + g
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (f g : NormedAddGroupHom V₁ V₂)
  结论: ⇑(f + g) = f + g
  证明: rfl

@[simp]
-/
theorem coe_add (f g : NormedAddGroupHom V₁ V₂) : ⇑(f + g) = f + g :=
  rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : NormedAddGroupHom V₁ V₂) (v : V₁)
  proof: rfl

中文:
定理 add_apply
  条件: (f g : NormedAddGroupHom V₁ V₂) (v : V₁)
  证明: rfl
-/
theorem add_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (f + g) v = f v + g v :=
  rfl



/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : Zero (NormedAddGroupHom V₁ V₂)
  body: ⟨(0 : V₁ ->+ V₂).mkNormedAddGroupHom 0 (by simp)⟩

中文:
实例 zero
  签名: : Zero (NormedAddGroupHom V₁ V₂)
  定义体: ⟨(0 : V₁ ->+ V₂).mkNormedAddGroupHom 0 (by simp)⟩

Depends on / 依赖: mkNormedAddGroupHom
-/
instance zero : Zero (NormedAddGroupHom V₁ V₂) :=
  ⟨(0 : V₁ ->+ V₂).mkNormedAddGroupHom 0 (by simp)⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (NormedAddGroupHom V₁ V₂)
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : Inhabited (NormedAddGroupHom V₁ V₂)
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited (NormedAddGroupHom V₁ V₂) :=
  ⟨0⟩

/--
theorem `opNorm_zero` / 定理 `opNorm_zero`

English:
theorem opNorm_zero
  statement: ‖(0 : NormedAddGroupHom V₁ V₂)‖ = 0
  proof: le_antisymm
    (csInf_le bounds_bddBelow
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eq
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (opNorm_nonneg _)

中文:
定理 opNorm_zero
  结论: ‖(0 : NormedAddGroupHom V₁ V₂)‖ = 0
  证明: le_antisymm
    (csInf_le bounds_bddBelow
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eq
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (opNorm_nonneg _)

Depends on / 依赖: bounds_bddBelow, csInf_le, ge_of_eq, le_antisymm, le_of_eq, norm_zero, opNorm_nonneg, zero_mul
-/
theorem opNorm_zero : ‖(0 : NormedAddGroupHom V₁ V₂)‖ = 0 :=
  le_antisymm
    (csInf_le bounds_bddBelow
      ⟨ge_of_eq rfl, fun _ =>
        le_of_eq
          (by
            rw [zero_mul]
            exact norm_zero)⟩)
    (opNorm_nonneg _)

/--
theorem `opNorm_zero_iff` / 定理 `opNorm_zero_iff`

English:
theorem opNorm_zero_iff
  statement: {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  proof: Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
            _ = _ := by rw [hn, zero_mul]))
    fun hf => by rw [hf, opNorm_zero]

@[simp]

中文:
定理 opNorm_zero_iff
  结论: {V₁ V₂ : 类型} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  证明: Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
            _ = _ := by rw [hn, zero_mul]))
    fun hf => by rw [hf, opNorm_zero]

@[simp]

Depends on / 依赖: Iff.intro, le_opNorm, norm_le_zero_iff, opNorm_zero, zero_mul
-/
theorem opNorm_zero_iff {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
    {f : NormedAddGroupHom V₁ V₂} : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn =>
      ext fun x =>
        norm_le_zero_iff.1
          (calc
            _ <= ‖f‖ * ‖x‖ := le_opNorm _ _
            _ = _ := by rw [hn, zero_mul]))
    fun hf => by rw [hf, opNorm_zero]

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : NormedAddGroupHom V₁ V₂) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : NormedAddGroupHom V₁ V₂) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : NormedAddGroupHom V₁ V₂) = 0 :=
  rfl

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (v : V₁)
  statement: (0 : NormedAddGroupHom V₁ V₂) v = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (v : V₁)
  结论: (0 : NormedAddGroupHom V₁ V₂) v = 0
  证明: rfl
-/
theorem zero_apply (v : V₁) : (0 : NormedAddGroupHom V₁ V₂) v = 0 :=
  rfl

variable {f g}

/-! ### The identity normed group hom -/


variable (V)

/-- The identity as a continuous normed group hom. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : NormedAddGroupHom V V
  body: (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp)

中文:
定义 id
  签名: : NormedAddGroupHom V V
  定义体: (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, mkNormedAddGroupHom
-/
def id : NormedAddGroupHom V V :=
  (AddMonoidHom.id V).mkNormedAddGroupHom 1 (by simp)

/--
theorem `norm_id_le` / 定理 `norm_id_le`

English:
theorem norm_id_le
  statement: ‖(id V : NormedAddGroupHom V V)‖ <= 1
  proof: opNorm_le_bound _ zero_le_one fun x => by simp

中文:
定理 norm_id_le
  结论: ‖(id V : NormedAddGroupHom V V)‖ <= 1
  证明: opNorm_le_bound _ zero_le_one fun x => by simp

Depends on / 依赖: opNorm_le_bound, zero_le_one
-/
theorem norm_id_le : ‖(id V : NormedAddGroupHom V V)‖ <= 1 :=
  opNorm_le_bound _ zero_le_one fun x => by simp

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
@[simp]
/--
theorem `norm_id` / 定理 `norm_id`

English:
theorem norm_id
  given: [NontrivialTopology V]
  statement: ‖id V‖ = 1
  proof: le_antisymm (norm_id_le V) by
    let ⟨x, hx⟩ := exists_norm_ne_zero V
    have := (id V).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

中文:
定理 norm_id
  条件: [NontrivialTopology V]
  结论: ‖id V‖ = 1
  证明: le_antisymm (norm_id_le V) by
    let ⟨x, hx⟩ := exists_norm_ne_zero V
    have := (id V).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

Depends on / 依赖: div_self, exists_norm_ne_zero, id_apply, le_antisymm, norm_id_le, ratio_le_opNorm
-/
theorem norm_id [NontrivialTopology V] : ‖id V‖ = 1 :=
le_antisymm (norm_id_le V) by
    let ⟨x, hx⟩ := exists_norm_ne_zero V
    have := (id V).ratio_le_opNorm x
    rwa [id_apply, div_self hx] at this

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: (NormedAddGroupHom.id V : V -> V) = _root_.id
  proof: rfl

中文:
定理 coe_id
  结论: (NormedAddGroupHom.id V : V -> V) = _root_.id
  证明: rfl
-/
theorem coe_id : (NormedAddGroupHom.id V : V -> V) = _root_.id :=
  rfl

/-! ### The negation of a normed group hom -/


/--
Instance `neg` / 实例 `neg`

English:
instance neg
  signature: : Neg (NormedAddGroupHom V₁ V₂)
  body: ⟨fun f => (-f.toAddMonoidHom).mkNormedAddGroupHom ‖f‖ fun v => by simp [le_opNorm f v]⟩

@[simp]

中文:
实例 neg
  签名: : Neg (NormedAddGroupHom V₁ V₂)
  定义体: ⟨fun f => (-f.toAddMonoidHom).mkNormedAddGroupHom ‖f‖ fun v => by simp [le_opNorm f v]⟩

@[simp]

Depends on / 依赖: f.toAddMonoidHom, le_opNorm, mkNormedAddGroupHom, toAddMonoidHom
-/
instance neg : Neg (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f => (-f.toAddMonoidHom).mkNormedAddGroupHom ‖f‖ fun v => by simp [le_opNorm f v]⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : NormedAddGroupHom V₁ V₂)
  statement: ⇑(-f) = -f
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (f : NormedAddGroupHom V₁ V₂)
  结论: ⇑(-f) = -f
  证明: rfl

@[simp]
-/
theorem coe_neg (f : NormedAddGroupHom V₁ V₂) : ⇑(-f) = -f :=
  rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  proof: rfl

中文:
定理 neg_apply
  条件: (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  证明: rfl
-/
theorem neg_apply (f : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (-f : NormedAddGroupHom V₁ V₂) v = -f v :=
  rfl

/--
theorem `opNorm_neg` / 定理 `opNorm_neg`

English:
theorem opNorm_neg
  given: (f : NormedAddGroupHom V₁ V₂)
  statement: ‖-f‖ = ‖f‖
  proof: by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

中文:
定理 opNorm_neg
  条件: (f : NormedAddGroupHom V₁ V₂)
  结论: ‖-f‖ = ‖f‖
  证明: by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

Depends on / 依赖: Pi.neg_apply, coe_neg, neg_apply, norm_def, norm_neg
-/
theorem opNorm_neg (f : NormedAddGroupHom V₁ V₂) : ‖-f‖ = ‖f‖ := by
  simp only [norm_def, coe_neg, norm_neg, Pi.neg_apply]

/-! ### Subtraction of normed group homs -/


/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: : Sub (NormedAddGroupHom V₁ V₂)
  body: ⟨fun f g =>
    { f.toAddMonoidHom - g.toAddMonoidHom with
      bound' := by
        simp only [AddMonoidHom.toFun_eq_coe, sub_eq_add_neg]
        exact (f + -g).bound' }⟩

@[simp]

中文:
实例 sub
  签名: : Sub (NormedAddGroupHom V₁ V₂)
  定义体: ⟨fun f g =>
    { f.toAddMonoidHom - g.toAddMonoidHom with
      bound' := by
        simp only [AddMonoidHom.toFun_eq_coe, sub_eq_add_neg]
        exact (f + -g).bound' }⟩

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toFun_eq_coe, f.toAddMonoidHom, g.toAddMonoidHom, sub_eq_add_neg, toAddMonoidHom, toFun_eq_coe
-/
instance sub : Sub (NormedAddGroupHom V₁ V₂) :=
  ⟨fun f g =>
    { f.toAddMonoidHom - g.toAddMonoidHom with
      bound' := by
        simp only [AddMonoidHom.toFun_eq_coe, sub_eq_add_neg]
        exact (f + -g).bound' }⟩

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : NormedAddGroupHom V₁ V₂)
  statement: ⇑(f - g) = f - g
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (f g : NormedAddGroupHom V₁ V₂)
  结论: ⇑(f - g) = f - g
  证明: rfl

@[simp]
-/
theorem coe_sub (f g : NormedAddGroupHom V₁ V₂) : ⇑(f - g) = f - g :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : NormedAddGroupHom V₁ V₂) (v : V₁)
  proof: rfl

中文:
定理 sub_apply
  条件: (f g : NormedAddGroupHom V₁ V₂) (v : V₁)
  证明: rfl
-/
theorem sub_apply (f g : NormedAddGroupHom V₁ V₂) (v : V₁) :
    (f - g : NormedAddGroupHom V₁ V₂) v = f v - g v :=
  rfl

/-! ### Scalar actions on normed group homs -/


section SMul

variable {R R' : Type*} [MonoidWithZero R] [DistribMulAction R V₂] [PseudoMetricSpace R]
  [IsBoundedSMul R V₂] [MonoidWithZero R'] [DistribMulAction R' V₂] [PseudoMetricSpace R']
  [IsBoundedSMul R' V₂]

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: : SMul R (NormedAddGroupHom V₁ V₂) where
  body: { toFun := r • ⇑f
      map_add' := (r • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨dist r 0 * b, fun x => by
          have := dist_smul_pair r (f x) (f 0)
          rw [map_zero]; rw [smul_zero]; rw [dist_zero_right]; rw [dist_zero_right] at this
          

中文:
实例 smul
  签名: : SMul R (NormedAddGroupHom V₁ V₂) where
  定义体: { toFun := r • ⇑f
      map_add' := (r • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨dist r 0 * b, fun x => by
          have := dist_smul_pair r (f x) (f 0)
          rw [map_zero]; rw [smul_zero]; rw [dist_zero_right]; rw [dist_zero_right] at this
          

Depends on / 依赖: dist_smul_pair, dist_zero_right, f.bound, f.toAddMonoidHom, map_add, map_zero, mul_assoc, smul_zero, this.trans, toAddMonoidHom
-/
instance smul : SMul R (NormedAddGroupHom V₁ V₂) where
  smul r f :=
    { toFun := r • ⇑f
      map_add' := (r • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨dist r 0 * b, fun x => by
          have := dist_smul_pair r (f x) (f 0)
          rw [map_zero]; rw [smul_zero]; rw [dist_zero_right]; rw [dist_zero_right] at this
          rw [mul_assoc]
          refine this.trans ?_
          gcongr
          exact hb x⟩ }

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : R) (f : NormedAddGroupHom V₁ V₂)
  statement: ⇑(r • f) = r • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: (r : R) (f : NormedAddGroupHom V₁ V₂)
  结论: ⇑(r • f) = r • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_smul (r : R) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  statement: (r • f) v = r • f v
  proof: rfl

中文:
定理 smul_apply
  条件: (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  结论: (r • f) v = r • f v
  证明: rfl
-/
theorem smul_apply (r : R) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMulCommClass R R' V₂]
  body: ext fun _ => smul_comm _ _ _

中文:
实例 smulCommClass
  签名: [SMulCommClass R R' V₂]
  定义体: ext fun _ => smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance smulCommClass [SMulCommClass R R' V₂] :
    SMulCommClass R R' (NormedAddGroupHom V₁ V₂) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R R'] [IsScalarTower R R' V₂]
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 isScalarTower
  签名: [SMul R R'] [IsScalarTower R R' V₂]
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance isScalarTower [SMul R R'] [IsScalarTower R R' V₂] :
    IsScalarTower R R' (NormedAddGroupHom V₁ V₂) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂]
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 isCentralScalar
  签名: [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂]
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance isCentralScalar [DistribMulAction Rᵐᵒᵖ V₂] [IsCentralScalar R V₂] :
    IsCentralScalar R (NormedAddGroupHom V₁ V₂) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end SMul

/--
Instance `nsmul` / 实例 `nsmul`

English:
instance nsmul
  signature: : SMul Nat (NormedAddGroupHom V₁ V₂) where
  body: { toFun := n • ⇑f
      map_add' := (n • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨n • b, fun v => by
          rw [Pi.smul_apply]; rw [nsmul_eq_mul]; rw [mul_assoc]
          exact norm_nsmul_le.trans (by gcongr; apply hb)⟩ }

@[simp]

中文:
实例 nsmul
  签名: : SMul 自然数 (NormedAddGroupHom V₁ V₂) where
  定义体: { toFun := n • ⇑f
      map_add' := (n • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨n • b, fun v => by
          rw [Pi.smul_apply]; rw [nsmul_eq_mul]; rw [mul_assoc]
          exact norm_nsmul_le.trans (by gcongr; apply hb)⟩ }

@[simp]

Depends on / 依赖: Pi.smul_apply, f.bound, f.toAddMonoidHom, map_add, mul_assoc, norm_nsmul_le, norm_nsmul_le.trans, nsmul_eq_mul, smul_apply, toAddMonoidHom
-/
instance nsmul : SMul Nat (NormedAddGroupHom V₁ V₂) where
  smul n f :=
    { toFun := n • ⇑f
      map_add' := (n • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨n • b, fun v => by
          rw [Pi.smul_apply]; rw [nsmul_eq_mul]; rw [mul_assoc]
          exact norm_nsmul_le.trans (by gcongr; apply hb)⟩ }

@[simp]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (r : Nat) (f : NormedAddGroupHom V₁ V₂)
  statement: ⇑(r • f) = r • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_nsmul
  条件: (r : 自然数) (f : NormedAddGroupHom V₁ V₂)
  结论: ⇑(r • f) = r • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_nsmul (r : Nat) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/--
theorem `nsmul_apply` / 定理 `nsmul_apply`

English:
theorem nsmul_apply
  given: (r : Nat) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  statement: (r • f) v = r • f v
  proof: rfl

中文:
定理 nsmul_apply
  条件: (r : 自然数) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  结论: (r • f) v = r • f v
  证明: rfl
-/
theorem nsmul_apply (r : Nat) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl

/--
Instance `zsmul` / 实例 `zsmul`

English:
instance zsmul
  signature: : SMul Int (NormedAddGroupHom V₁ V₂) where
  body: { toFun := z • ⇑f
      map_add' := (z • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨‖z‖ • b, fun v => by
          rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [mul_assoc]
          exact (norm_zsmul_le _ _).trans (by gcongr; apply hb)⟩ }

@[simp]

中文:
实例 zsmul
  签名: : SMul 整数 (NormedAddGroupHom V₁ V₂) where
  定义体: { toFun := z • ⇑f
      map_add' := (z • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨‖z‖ • b, fun v => by
          rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [mul_assoc]
          exact (norm_zsmul_le _ _).trans (by gcongr; apply hb)⟩ }

@[simp]

Depends on / 依赖: Pi.smul_apply, f.bound, f.toAddMonoidHom, map_add, mul_assoc, norm_zsmul_le, smul_apply, smul_eq_mul, toAddMonoidHom
-/
instance zsmul : SMul Int (NormedAddGroupHom V₁ V₂) where
  smul z f :=
    { toFun := z • ⇑f
      map_add' := (z • f.toAddMonoidHom).map_add'
      bound' :=
        let ⟨b, hb⟩ := f.bound'
        ⟨‖z‖ • b, fun v => by
          rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [mul_assoc]
          exact (norm_zsmul_le _ _).trans (by gcongr; apply hb)⟩ }

@[simp]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (r : Int) (f : NormedAddGroupHom V₁ V₂)
  statement: ⇑(r • f) = r • ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_zsmul
  条件: (r : 整数) (f : NormedAddGroupHom V₁ V₂)
  结论: ⇑(r • f) = r • ⇑f
  证明: rfl

@[simp]
-/
theorem coe_zsmul (r : Int) (f : NormedAddGroupHom V₁ V₂) : ⇑(r • f) = r • ⇑f :=
  rfl

@[simp]
/--
theorem `zsmul_apply` / 定理 `zsmul_apply`

English:
theorem zsmul_apply
  given: (r : Int) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  statement: (r • f) v = r • f v
  proof: rfl

中文:
定理 zsmul_apply
  条件: (r : 整数) (f : NormedAddGroupHom V₁ V₂) (v : V₁)
  结论: (r • f) v = r • f v
  证明: rfl
-/
theorem zsmul_apply (r : Int) (f : NormedAddGroupHom V₁ V₂) (v : V₁) : (r • f) v = r • f v :=
  rfl

/-! ### Normed group structure on normed group homs -/


/--
Instance `toAddCommGroup` / 实例 `toAddCommGroup`

English:
instance toAddCommGroup
  signature: : AddCommGroup (NormedAddGroupHom V₁ V₂)
  body: coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

中文:
实例 toAddCommGroup
  签名: : AddCommGroup (NormedAddGroupHom V₁ V₂)
  定义体: coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

Depends on / 依赖: addCommGroup, coe_injective, coe_injective.addCommGroup
-/
instance toAddCommGroup : AddCommGroup (NormedAddGroupHom V₁ V₂) :=
  coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/--
Instance `toSeminormedAddCommGroup` / 实例 `toSeminormedAddCommGroup`

English:
instance toSeminormedAddCommGroup
  signature: : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂)
  body: AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le }

中文:
实例 toSeminormedAddCommGroup
  签名: : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂)
  定义体: AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le }

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toSeminormedAddCommGroup, add_le, map_zero, opNorm, opNorm_add_le, opNorm_neg, opNorm_zero, toSeminormedAddCommGroup
-/
instance toSeminormedAddCommGroup : SeminormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupSeminorm.toSeminormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le }

/--
Instance `toNormedAddCommGroup` / 实例 `toNormedAddCommGroup`

English:
instance toNormedAddCommGroup
  signature: {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  body: AddGroupNorm.toNormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le
      eq_zero_of_map_eq_zero' := fun _f => opNorm_zero_iff.1 }

中文:
实例 toNormedAddCommGroup
  签名: {V₁ V₂ : 类型} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  定义体: AddGroupNorm.toNormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le
      eq_zero_of_map_eq_zero' := fun _f => opNorm_zero_iff.1 }

Depends on / 依赖: AddGroupNorm, AddGroupNorm.toNormedAddCommGroup, add_le, eq_zero_of_map_eq_zero, map_zero, opNorm, opNorm_add_le, opNorm_neg, opNorm_zero, opNorm_zero_iff, toNormedAddCommGroup
-/
instance toNormedAddCommGroup {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] :
    NormedAddCommGroup (NormedAddGroupHom V₁ V₂) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := opNorm
      map_zero' := opNorm_zero
      neg' := opNorm_neg
      add_le' := opNorm_add_le
      eq_zero_of_map_eq_zero' := fun _f => opNorm_zero_iff.1 }

/-- Coercion of a `NormedAddGroupHom` is an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/
@[simps]
/--
Definition of `coeAddHom` / `coeAddHom` 的定义

English:
definition coeAddHom
  signature: : NormedAddGroupHom V₁ V₂ ->+ V₁ -> V₂ where
  body: DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeAddHom
  签名: : NormedAddGroupHom V₁ V₂ ->+ V₁ -> V₂ where
  定义体: DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def coeAddHom : NormedAddGroupHom V₁ V₂ ->+ V₁ -> V₂ where
  toFun := DFunLike.coe
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
theorem `coe_sum` / 定理 `coe_sum`

English:
theorem coe_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂)
  proof: map_sum coeAddHom f s

中文:
定理 coe_sum
  条件: {ι : 类型} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂)
  证明: map_sum coeAddHom f s

Depends on / 依赖: coeAddHom, map_sum
-/
theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) :
    ⇑(∑ i in s, f i) = ∑ i in s, (f i : V₁ -> V₂) :=
  map_sum coeAddHom f s

/--
theorem `sum_apply` / 定理 `sum_apply`

English:
theorem sum_apply
  given: {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) (v : V₁)
  proof: by simp only [coe_sum, Finset.sum_apply]

中文:
定理 sum_apply
  条件: {ι : 类型} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) (v : V₁)
  证明: by simp only [coe_sum, Finset.sum_apply]

Depends on / 依赖: Finset, Finset.sum_apply, coe_sum, sum_apply
-/
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι -> NormedAddGroupHom V₁ V₂) (v : V₁) :
    (∑ i in s, f i) v = ∑ i in s, f i v := by simp only [coe_sum, Finset.sum_apply]



/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: {R : Type*} [MonoidWithZero R] [DistribMulAction R V₂]
  body: Function.Injective.distribMulAction coeAddHom coe_injective coe_smul

中文:
实例 distribMulAction
  签名: {R : 类型} [MonoidWithZero R] [DistribMulAction R V₂]
  定义体: Function.Injective.distribMulAction coeAddHom coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, coeAddHom, coe_injective, coe_smul, distribMulAction
-/
instance distribMulAction {R : Type*} [MonoidWithZero R] [DistribMulAction R V₂]
    [PseudoMetricSpace R] [IsBoundedSMul R V₂] : DistribMulAction R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.distribMulAction coeAddHom coe_injective coe_smul

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: {R : Type*} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [IsBoundedSMul R V₂]
  body: Function.Injective.module _ coeAddHom coe_injective coe_smul

中文:
实例 module
  签名: {R : 类型} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [IsBoundedSMul R V₂]
  定义体: Function.Injective.module _ coeAddHom coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, coeAddHom, coe_injective, coe_smul, module
-/
instance module {R : Type*} [Semiring R] [Module R V₂] [PseudoMetricSpace R] [IsBoundedSMul R V₂] :
    Module R (NormedAddGroupHom V₁ V₂) :=
  Function.Injective.module _ coeAddHom coe_injective coe_smul

/-! ### Composition of normed group homs -/


/-- The composition of continuous normed group homs. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂)
  body: (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (‖g‖ * ‖f‖) fun v =>
    calc
      ‖g (f v)‖ <= ‖g‖ * ‖f v‖ := le_opNorm _ _
      _ <= ‖g‖ * (‖f‖ * ‖v‖) := by gcongr; apply le_opNorm
      _ = ‖g‖ * ‖f‖ * ‖v‖ := by rw [mul_assoc]

中文:
定义 comp
  签名: (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂)
  定义体: (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (‖g‖ * ‖f‖) fun v =>
    calc
      ‖g (f v)‖ <= ‖g‖ * ‖f v‖ := le_opNorm _ _
      _ <= ‖g‖ * (‖f‖ * ‖v‖) := by gcongr; apply le_opNorm
      _ = ‖g‖ * ‖f‖ * ‖v‖ := by rw [mul_assoc]
-/
protected def comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    NormedAddGroupHom V₁ V₃ :=
  (g.toAddMonoidHom.comp f.toAddMonoidHom).mkNormedAddGroupHom (‖g‖ * ‖f‖) fun v =>
    calc
      ‖g (f v)‖ <= ‖g‖ * ‖f v‖ := le_opNorm _ _
      _ <= ‖g‖ * (‖f‖ * ‖v‖) := by gcongr; apply le_opNorm
      _ = ‖g‖ * ‖f‖ * ‖v‖ := by rw [mul_assoc]

/--
theorem `norm_comp_le` / 定理 `norm_comp_le`

English:
theorem norm_comp_le
  given: (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂)
  proof: mkNormedAddGroupHom_norm_le _ (by positivity) _

中文:
定理 norm_comp_le
  条件: (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂)
  证明: mkNormedAddGroupHom_norm_le _ (by positivity) _

Depends on / 依赖: mkNormedAddGroupHom_norm_le
-/
theorem norm_comp_le (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    ‖g.comp f‖ <= ‖g‖ * ‖f‖ :=
  mkNormedAddGroupHom_norm_le _ (by positivity) _

/--
theorem `norm_comp_le_of_le` / 定理 `norm_comp_le_of_le`

English:
theorem norm_comp_le_of_le
  statement: {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : Real} (hg : ‖g‖ <= C₂)
  proof: le_trans (norm_comp_le g f) by gcongr; exact le_trans (norm_nonneg _) hg

中文:
定理 norm_comp_le_of_le
  结论: {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : 实数} (hg : ‖g‖ <= C₂)
  证明: le_trans (norm_comp_le g f) by gcongr; exact le_trans (norm_nonneg _) hg

Depends on / 依赖: le_trans, norm_comp_le, norm_nonneg
-/
theorem norm_comp_le_of_le {g : NormedAddGroupHom V₂ V₃} {C₁ C₂ : Real} (hg : ‖g‖ <= C₂)
    (hf : ‖f‖ <= C₁) : ‖g.comp f‖ <= C₂ * C₁ :=
le_trans (norm_comp_le g f) by gcongr; exact le_trans (norm_nonneg _) hg

/--
theorem `norm_comp_le_of_le'` / 定理 `norm_comp_le_of_le'`

English:
theorem norm_comp_le_of_le'
  statement: {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : Real) (h : C₃ = C₂ * C₁)
  proof: by
  rw [h]
  exact norm_comp_le_of_le hg hf

中文:
定理 norm_comp_le_of_le'
  结论: {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : 实数) (h : C₃ = C₂ * C₁)
  证明: by
  rw [h]
  exact norm_comp_le_of_le hg hf

Depends on / 依赖: norm_comp_le_of_le
-/
theorem norm_comp_le_of_le' {g : NormedAddGroupHom V₂ V₃} (C₁ C₂ C₃ : Real) (h : C₃ = C₂ * C₁)
    (hg : ‖g‖ <= C₂) (hf : ‖f‖ <= C₁) : ‖g.comp f‖ <= C₃ := by
  rw [h]
  exact norm_comp_le_of_le hg hf

/--
Definition of `compHom` / `compHom` 的定义

English:
definition compHom
  signature: : NormedAddGroupHom V₂ V₃ ->+ NormedAddGroupHom V₁ V₂ ->+ NormedAddGroupHom V₁ V₃
  body: AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, AddMonoidHom.add_apply,
        AddMonoidHom.mk'_apply, coe_add])

@[simp]

中文:
定义 compHom
  签名: : NormedAddGroupHom V₂ V₃ ->+ NormedAddGroupHom V₁ V₂ ->+ NormedAddGroupHom V₁ V₃
  定义体: AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, AddMonoidHom.add_apply,
        AddMonoidHom.mk'_apply, coe_add])

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.add_apply, AddMonoidHom.mk, Pi.add_apply, _apply, add_apply, coe_add, comp_apply, g.comp, intros, map_add
-/
def compHom : NormedAddGroupHom V₂ V₃ ->+ NormedAddGroupHom V₁ V₂ ->+ NormedAddGroupHom V₁ V₃ :=
  AddMonoidHom.mk'
    (fun g =>
      AddMonoidHom.mk' (fun f => g.comp f)
        (by
          intros
          ext
          exact map_add g _ _))
    (by
      intros
      ext
      simp only [comp_apply, Pi.add_apply, AddMonoidHom.add_apply,
        AddMonoidHom.mk'_apply, coe_add])

@[simp]
/--
theorem `comp_zero` / 定理 `comp_zero`

English:
theorem comp_zero
  given: (f : NormedAddGroupHom V₂ V₃)
  statement: f.comp (0 : NormedAddGroupHom V₁ V₂) = 0
  proof: by
  ext
  exact map_zero f

@[simp]

中文:
定理 comp_zero
  条件: (f : NormedAddGroupHom V₂ V₃)
  结论: f.comp (0 : NormedAddGroupHom V₁ V₂) = 0
  证明: by
  ext
  exact map_zero f

@[simp]

Depends on / 依赖: map_zero
-/
theorem comp_zero (f : NormedAddGroupHom V₂ V₃) : f.comp (0 : NormedAddGroupHom V₁ V₂) = 0 := by
  ext
  exact map_zero f

@[simp]
/--
theorem `zero_comp` / 定理 `zero_comp`

English:
theorem zero_comp
  given: (f : NormedAddGroupHom V₁ V₂)
  statement: (0 : NormedAddGroupHom V₂ V₃).comp f = 0
  proof: by
  ext
  rfl

中文:
定理 zero_comp
  条件: (f : NormedAddGroupHom V₁ V₂)
  结论: (0 : NormedAddGroupHom V₂ V₃).comp f = 0
  证明: by
  ext
  rfl
-/
theorem zero_comp (f : NormedAddGroupHom V₁ V₂) : (0 : NormedAddGroupHom V₂ V₃).comp f = 0 := by
  ext
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {V₄ : Type*} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom V₃ V₄)
  proof: by
  ext
  rfl

中文:
定理 comp_assoc
  结论: {V₄ : 类型} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom V₃ V₄)
  证明: by
  ext
  rfl
-/
theorem comp_assoc {V₄ : Type*} [SeminormedAddCommGroup V₄] (h : NormedAddGroupHom V₃ V₄)
    (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext
  rfl

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)
  proof: rfl

中文:
定理 coe_comp
  条件: (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)
  证明: rfl
-/
theorem coe_comp (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃) :
    (g.comp f : V₁ -> V₃) = (g : V₂ -> V₃) ∘ (f : V₁ -> V₂) :=
  rfl

end NormedAddGroupHom

namespace NormedAddGroupHom

variable {V W V₁ V₂ V₃ : Type*} [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
  [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂] [SeminormedAddCommGroup V₃]

/-- The inclusion of an `AddSubgroup`, as bounded group homomorphism. -/
@[simps!]
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: (s : AddSubgroup V)
  body: (Subtype.val : s -> V)
  map_add' _ _ := AddSubgroup.coe_add _ _ _
  bound' := ⟨1, fun v => by rw [one_mul, AddSubgroup.coe_norm]⟩

中文:
定义 incl
  签名: (s : AddSubgroup V)
  定义体: (Subtype.val : s -> V)
  map_add' _ _ := AddSubgroup.coe_add _ _ _
  bound' := ⟨1, fun v => by rw [one_mul, AddSubgroup.coe_norm]⟩

Depends on / 依赖: Subtype, Subtype.val
-/
def incl (s : AddSubgroup V) : NormedAddGroupHom s V where
  toFun := (Subtype.val : s -> V)
  map_add' _ _ := AddSubgroup.coe_add _ _ _
  bound' := ⟨1, fun v => by rw [one_mul, AddSubgroup.coe_norm]⟩

/--
theorem `norm_incl` / 定理 `norm_incl`

English:
theorem norm_incl
  given: {V' : AddSubgroup V} (x : V')
  statement: ‖incl _ x‖ = ‖x‖
  proof: rfl

中文:
定理 norm_incl
  条件: {V' : AddSubgroup V} (x : V')
  结论: ‖incl _ x‖ = ‖x‖
  证明: rfl
-/
theorem norm_incl {V' : AddSubgroup V} (x : V') : ‖incl _ x‖ = ‖x‖ :=
  rfl

/-!### Kernel -/


section Kernels

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : AddSubgroup V₁
  body: f.toAddMonoidHom.ker

中文:
定义 ker
  签名: : AddSubgroup V₁
  定义体: f.toAddMonoidHom.ker

Depends on / 依赖: f.toAddMonoidHom.ker, toAddMonoidHom
-/
def ker : AddSubgroup V₁ :=
  f.toAddMonoidHom.ker

/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: (v : V₁)
  statement: v in f.ker ↔ f v = 0
  proof: by
  rw [ker]; rw [f.toAddMonoidHom.mem_ker]; rw [coe_toAddMonoidHom]

中文:
定理 mem_ker
  条件: (v : V₁)
  结论: v in f.ker ↔ f v = 0
  证明: by
  rw [ker]; rw [f.toAddMonoidHom.mem_ker]; rw [coe_toAddMonoidHom]

Depends on / 依赖: coe_toAddMonoidHom, f.toAddMonoidHom.mem_ker, mem_ker, toAddMonoidHom
-/
theorem mem_ker (v : V₁) : v in f.ker ↔ f v = 0 := by
  rw [ker]; rw [f.toAddMonoidHom.mem_ker]; rw [coe_toAddMonoidHom]

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
the corestriction of `f` to the kernel of `g`. -/
@[simps]
/--
Definition of `ker.lift` / `ker.lift` 的定义

English:
definition ker.lift
  signature: (h : g.comp f = 0)
  body: ⟨f v, by rw [g.mem_ker, ← comp_apply g f, h, zero_apply]⟩
  map_add' v w := by simp only [map_add, AddMemClass.mk_add_mk]
  bound' := f.bound'

@[simp]

中文:
定义 ker.lift
  签名: (h : g.comp f = 0)
  定义体: ⟨f v, by rw [g.mem_ker, ← comp_apply g f, h, zero_apply]⟩
  map_add' v w := by simp only [map_add, AddMemClass.mk_add_mk]
  bound' := f.bound'

@[simp]

Depends on / 依赖: comp_apply, g.mem_ker, mem_ker, zero_apply
-/
def ker.lift (h : g.comp f = 0) : NormedAddGroupHom V₁ g.ker where
  toFun v := ⟨f v, by rw [g.mem_ker, ← comp_apply g f, h, zero_apply]⟩
  map_add' v w := by simp only [map_add, AddMemClass.mk_add_mk]
  bound' := f.bound'

@[simp]
/--
theorem `ker.incl_comp_lift` / 定理 `ker.incl_comp_lift`

English:
theorem ker.incl_comp_lift
  given: (h : g.comp f = 0)
  statement: (incl g.ker).comp (ker.lift f g h) = f
  proof: by
  ext
  rfl

@[simp]

中文:
定理 ker.incl_comp_lift
  条件: (h : g.comp f = 0)
  结论: (incl g.ker).comp (ker.lift f g h) = f
  证明: by
  ext
  rfl

@[simp]
-/
theorem ker.incl_comp_lift (h : g.comp f = 0) : (incl g.ker).comp (ker.lift f g h) = f := by
  ext
  rfl

@[simp]
/--
theorem `ker_zero` / 定理 `ker_zero`

English:
theorem ker_zero
  statement: (0 : NormedAddGroupHom V₁ V₂).ker = ⊤
  proof: by
  ext
  simp [mem_ker]

中文:
定理 ker_zero
  结论: (0 : NormedAddGroupHom V₁ V₂).ker = ⊤
  证明: by
  ext
  simp [mem_ker]

Depends on / 依赖: mem_ker
-/
theorem ker_zero : (0 : NormedAddGroupHom V₁ V₂).ker = ⊤ := by
  ext
  simp [mem_ker]

/--
theorem `coe_ker` / 定理 `coe_ker`

English:
theorem coe_ker
  statement: (f.ker : Set V₁) = (f : V₁ -> V₂) ⁻¹' {0}
  proof: rfl

中文:
定理 coe_ker
  结论: (f.ker : Set V₁) = (f : V₁ -> V₂) ⁻¹' {0}
  证明: rfl
-/
theorem coe_ker : (f.ker : Set V₁) = (f : V₁ -> V₂) ⁻¹' {0} :=
  rfl

/--
theorem `isClosed_ker` / 定理 `isClosed_ker`

English:
theorem isClosed_ker
  given: {V₂ : Type*} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂)
  proof: f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

中文:
定理 isClosed_ker
  条件: {V₂ : 类型} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂)
  证明: f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

Depends on / 依赖: IsClosed, IsClosed.preimage, T1Space, T1Space.t1, coe_ker, continuous, f.coe_ker, f.continuous, preimage
-/
theorem isClosed_ker {V₂ : Type*} [NormedAddCommGroup V₂] (f : NormedAddGroupHom V₁ V₂) :
    IsClosed (f.ker : Set V₁) :=
  f.coe_ker ▸ IsClosed.preimage f.continuous (T1Space.t1 0)

end Kernels

/-! ### Range -/


section Range

variable (f : NormedAddGroupHom V₁ V₂) (g : NormedAddGroupHom V₂ V₃)

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: : AddSubgroup V₂
  body: f.toAddMonoidHom.range

中文:
定义 range
  签名: : AddSubgroup V₂
  定义体: f.toAddMonoidHom.range

Depends on / 依赖: f.toAddMonoidHom.range, toAddMonoidHom
-/
def range : AddSubgroup V₂ :=
  f.toAddMonoidHom.range

/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: (v : V₂)
  statement: v in f.range ↔ exists w, f w = v
  proof: Iff.rfl

@[simp]

中文:
定理 mem_range
  条件: (v : V₂)
  结论: v in f.range ↔ 存在 w, f w = v
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_range (v : V₂) : v in f.range ↔ exists w, f w = v := Iff.rfl

@[simp]
/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (v : V₁)
  statement: f v in f.range
  proof: ⟨v, rfl⟩

中文:
定理 mem_range_self
  条件: (v : V₁)
  结论: f v in f.range
  证明: ⟨v, rfl⟩
-/
theorem mem_range_self (v : V₁) : f v in f.range :=
  ⟨v, rfl⟩

/--
theorem `comp_range` / 定理 `comp_range`

English:
theorem comp_range
  statement: (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range
  proof: by
  unfold range
  rw [AddMonoidHom.map_range]
  rfl

中文:
定理 comp_range
  结论: (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range
  证明: by
  unfold range
  rw [AddMonoidHom.map_range]
  rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_range, map_range
-/
theorem comp_range : (g.comp f).range = AddSubgroup.map g.toAddMonoidHom f.range := by
  unfold range
  rw [AddMonoidHom.map_range]
  rfl

/--
theorem `incl_range` / 定理 `incl_range`

English:
theorem incl_range
  given: (s : AddSubgroup V₁)
  statement: (incl s).range = s
  proof: by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; simp, fun hx => ⟨⟨x, hx⟩, by simp⟩⟩

@[simp]

中文:
定理 incl_range
  条件: (s : AddSubgroup V₁)
  结论: (incl s).range = s
  证明: by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; simp, fun hx => ⟨⟨x, hx⟩, by simp⟩⟩

@[simp]
-/
theorem incl_range (s : AddSubgroup V₁) : (incl s).range = s := by
  ext x
  exact ⟨fun ⟨y, hy⟩ => by rw [← hy]; simp, fun hx => ⟨⟨x, hx⟩, by simp⟩⟩

@[simp]
/--
theorem `range_comp_incl_top` / 定理 `range_comp_incl_top`

English:
theorem range_comp_incl_top
  statement: (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range
  proof: by
  simp [comp_range, incl_range, ← AddMonoidHom.range_eq_map]; rfl

中文:
定理 range_comp_incl_top
  结论: (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range
  证明: by
  simp [comp_range, incl_range, ← AddMonoidHom.range_eq_map]; rfl

Depends on / 依赖: AddMonoidHom, AddMonoidHom.range_eq_map, comp_range, incl_range, range_eq_map
-/
theorem range_comp_incl_top : (f.comp (incl (⊤ : AddSubgroup V₁))).range = f.range := by
  simp [comp_range, incl_range, ← AddMonoidHom.range_eq_map]; rfl

end Range

variable {f : NormedAddGroupHom V W}

/--
Definition of `NormNoninc` / `NormNoninc` 的定义

English:
definition NormNoninc
  signature: (f : NormedAddGroupHom V W)
  body: forall v, ‖f v‖ <= ‖v‖

中文:
定义 NormNoninc
  签名: (f : NormedAddGroupHom V W)
  定义体: forall v, ‖f v‖ <= ‖v‖
-/
def NormNoninc (f : NormedAddGroupHom V W) : Prop :=
  forall v, ‖f v‖ <= ‖v‖

namespace NormNoninc

/--
theorem `normNoninc_iff_norm_le_one` / 定理 `normNoninc_iff_norm_le_one`

English:
theorem normNoninc_iff_norm_le_one
  statement: f.NormNoninc ↔ ‖f‖ <= 1
  proof: by
  refine ⟨fun h => ?_, fun h v => ?_⟩
  · refine opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using h v
  · simpa using le_of_opNorm_le f h v

中文:
定理 normNoninc_iff_norm_le_one
  结论: f.NormNoninc ↔ ‖f‖ <= 1
  证明: by
  refine ⟨fun h => ?_, fun h v => ?_⟩
  · refine opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using h v
  · simpa using le_of_opNorm_le f h v

Depends on / 依赖: le_of_opNorm_le, one_mul, opNorm_le_bound, zero_le_one
-/
theorem normNoninc_iff_norm_le_one : f.NormNoninc ↔ ‖f‖ <= 1 := by
  refine ⟨fun h => ?_, fun h v => ?_⟩
  · refine opNorm_le_bound _ zero_le_one fun v => ?_
    simpa [one_mul] using h v
  · simpa using le_of_opNorm_le f h v

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: (0 : NormedAddGroupHom V₁ V₂).NormNoninc
  proof: fun v => by simp

中文:
定理 zero
  结论: (0 : NormedAddGroupHom V₁ V₂).NormNoninc
  证明: fun v => by simp
-/
theorem zero : (0 : NormedAddGroupHom V₁ V₂).NormNoninc := fun v => by simp

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: (id V).NormNoninc
  proof: fun _v => le_rfl

中文:
定理 id
  结论: (id V).NormNoninc
  证明: fun _v => le_rfl

Depends on / 依赖: le_rfl
-/
theorem id : (id V).NormNoninc := fun _v => le_rfl

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
  proof: fun v => (hg (f v)).trans (hf v)

@[simp]

中文:
定理 comp
  结论: {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
  证明: fun v => (hg (f v)).trans (hf v)

@[simp]
-/
theorem comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : g.NormNoninc)
    (hf : f.NormNoninc) : (g.comp f).NormNoninc := fun v => (hg (f v)).trans (hf v)

@[simp]
/--
theorem `neg_iff` / 定理 `neg_iff`

English:
theorem neg_iff
  given: {f : NormedAddGroupHom V₁ V₂}
  statement: (-f).NormNoninc ↔ f.NormNoninc
  proof: ⟨fun h x => by simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩

中文:
定理 neg_iff
  条件: {f : NormedAddGroupHom V₁ V₂}
  结论: (-f).NormNoninc ↔ f.NormNoninc
  证明: ⟨fun h x => by simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩

Depends on / 依赖: le.trans, norm_neg
-/
theorem neg_iff {f : NormedAddGroupHom V₁ V₂} : (-f).NormNoninc ↔ f.NormNoninc :=
  ⟨fun h x => by simpa using h x, fun h x => (norm_neg (f x)).le.trans (h x)⟩

end NormNoninc

section Isometry

/--
theorem `norm_eq_of_isometry` / 定理 `norm_eq_of_isometry`

English:
theorem norm_eq_of_isometry
  given: {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V)
  statement: ‖f v‖ = ‖v‖
  proof: (AddMonoidHomClass.isometry_iff_norm f).mp hf v

中文:
定理 norm_eq_of_isometry
  条件: {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V)
  结论: ‖f v‖ = ‖v‖
  证明: (AddMonoidHomClass.isometry_iff_norm f).mp hf v

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_iff_norm, isometry_iff_norm
-/
theorem norm_eq_of_isometry {f : NormedAddGroupHom V W} (hf : Isometry f) (v : V) : ‖f v‖ = ‖v‖ :=
  (AddMonoidHomClass.isometry_iff_norm f).mp hf v

/--
theorem `isometry_id` / 定理 `isometry_id`

English:
theorem isometry_id
  statement: @Isometry V V _ _ (id V)
  proof: _root_.isometry_id

中文:
定理 isometry_id
  结论: @Isometry V V _ _ (id V)
  证明: _root_.isometry_id

Depends on / 依赖: _root_, _root_.isometry_id, isometry_id
-/
theorem isometry_id : @Isometry V V _ _ (id V) :=
  _root_.isometry_id

/--
theorem `isometry_comp` / 定理 `isometry_comp`

English:
theorem isometry_comp
  statement: {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : Isometry g)
  proof: hg.comp hf

中文:
定理 isometry_comp
  结论: {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : Isometry g)
  证明: hg.comp hf

Depends on / 依赖: hg.comp
-/
theorem isometry_comp {g : NormedAddGroupHom V₂ V₃} {f : NormedAddGroupHom V₁ V₂} (hg : Isometry g)
    (hf : Isometry f) : Isometry (g.comp f) :=
  hg.comp hf

/--
theorem `normNoninc_of_isometry` / 定理 `normNoninc_of_isometry`

English:
theorem normNoninc_of_isometry
  given: (hf : Isometry f)
  statement: f.NormNoninc
  proof: fun v =>
le_of_eq norm_eq_of_isometry hf v

中文:
定理 normNoninc_of_isometry
  条件: (hf : Isometry f)
  结论: f.NormNoninc
  证明: fun v =>
le_of_eq norm_eq_of_isometry hf v
-/
theorem normNoninc_of_isometry (hf : Isometry f) : f.NormNoninc := fun v =>
le_of_eq norm_eq_of_isometry hf v

end Isometry

variable {W₁ W₂ W₃ : Type*} [SeminormedAddCommGroup W₁] [SeminormedAddCommGroup W₂]
  [SeminormedAddCommGroup W₃]

variable (f) (g : NormedAddGroupHom V W)
variable {f₁ g₁ : NormedAddGroupHom V₁ W₁}
variable {f₂ g₂ : NormedAddGroupHom V₂ W₂}
variable {f₃ g₃ : NormedAddGroupHom V₃ W₃}

/--
Definition of `equalizer` / `equalizer` 的定义

English:
definition equalizer
  body: (f - g).ker

中文:
定义 equalizer
  定义体: (f - g).ker
-/
def equalizer :=
  (f - g).ker

namespace Equalizer

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : NormedAddGroupHom (f.equalizer g) V
  body: incl _

中文:
定义 ι
  签名: : NormedAddGroupHom (f.equalizer g) V
  定义体: incl _
-/
def ι : NormedAddGroupHom (f.equalizer g) V :=
  incl _

/--
theorem `comp_ι_eq` / 定理 `comp_ι_eq`

English:
theorem comp_ι_eq
  statement: f.comp (ι f g) = g.comp (ι f g)
  proof: by
  ext x
  rw [comp_apply]; rw [comp_apply]; rw [← sub_eq_zero]; rw [← NormedAddGroupHom.sub_apply]
  exact x.2

中文:
定理 comp_ι_eq
  结论: f.comp (ι f g) = g.comp (ι f g)
  证明: by
  ext x
  rw [comp_apply]; rw [comp_apply]; rw [← sub_eq_zero]; rw [← NormedAddGroupHom.sub_apply]
  exact x.2

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.sub_apply, comp_apply, sub_apply, sub_eq_zero
-/
theorem comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) := by
  ext x
  rw [comp_apply]; rw [comp_apply]; rw [← sub_eq_zero]; rw [← NormedAddGroupHom.sub_apply]
  exact x.2

variable {f g}

/-- If `φ : NormedAddGroupHom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`NormedAddGroupHom V₁ (f.equalizer g)`. -/
@[simps]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ)
  body: ⟨φ v,
      show (f - g) (φ v) = 0 by
        rw [NormedAddGroupHom.sub_apply]; rw [sub_eq_zero]; rw [← comp_apply]; rw [h]; rw [comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add]
  bound' := by
    obtain ⟨C, _C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩

@[simp]

中文:
定义 lift
  签名: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ)
  定义体: ⟨φ v,
      show (f - g) (φ v) = 0 by
        rw [NormedAddGroupHom.sub_apply]; rw [sub_eq_zero]; rw [← comp_apply]; rw [h]; rw [comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add]
  bound' := by
    obtain ⟨C, _C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_add, NormedAddGroupHom, NormedAddGroupHom.sub_apply, _C_pos, coe_add, comp_apply, map_add, sub_apply, sub_eq_zero
-/
def lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) :
    NormedAddGroupHom V₁ (f.equalizer g) where
  toFun v :=
    ⟨φ v,
      show (f - g) (φ v) = 0 by
        rw [NormedAddGroupHom.sub_apply]; rw [sub_eq_zero]; rw [← comp_apply]; rw [h]; rw [comp_apply]⟩
  map_add' v₁ v₂ := by
    ext
    simp only [map_add, AddSubgroup.coe_add]
  bound' := by
    obtain ⟨C, _C_pos, hC⟩ := φ.bound
    exact ⟨C, hC⟩

@[simp]
/--
theorem `ι_comp_lift` / 定理 `ι_comp_lift`

English:
theorem ι_comp_lift
  given: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ)
  proof: by
  ext
  rfl

中文:
定理 ι_comp_lift
  条件: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ)
  证明: by
  ext
  rfl
-/
theorem ι_comp_lift (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) :
    (ι _ _).comp (lift φ h) = φ := by
  ext
  rfl

/-- The lifting property of the equalizer as an equivalence. -/
@[simps]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: :
  body: lift φ φ.prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp

中文:
定义 liftEquiv
  签名: :
  定义体: lift φ φ.prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp
-/
def liftEquiv :
    { φ : NormedAddGroupHom V₁ V // f.comp φ = g.comp φ } ≃
      NormedAddGroupHom V₁ (f.equalizer g) where
  toFun φ := lift φ φ.prop
  invFun ψ := ⟨(ι f g).comp ψ, by rw [← comp_assoc, ← comp_assoc, comp_ι_eq]⟩
  left_inv φ := by simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
  body: lift (φ.comp <| ι _ _) by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq f₁ g₁]

中文:
定义 map
  签名: (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
  定义体: lift (φ.comp <| ι _ _) by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq f₁ g₁]

Depends on / 依赖: comp_assoc
-/
def map (φ : NormedAddGroupHom V₁ V₂) (ψ : NormedAddGroupHom W₁ W₂) (hf : ψ.comp f₁ = f₂.comp φ)
    (hg : ψ.comp g₁ = g₂.comp φ) : NormedAddGroupHom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
lift (φ.comp <| ι _ _) by
    simp only [← comp_assoc, ← hf, ← hg]
    simp only [comp_assoc, comp_ι_eq f₁ g₁]

variable {φ : NormedAddGroupHom V₁ V₂} {ψ : NormedAddGroupHom W₁ W₂}
variable {φ' : NormedAddGroupHom V₂ V₃} {ψ' : NormedAddGroupHom W₂ W₃}

@[simp]
/--
theorem `ι_comp_map` / 定理 `ι_comp_map`

English:
theorem ι_comp_map
  given: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  proof: ι_comp_lift _ _

@[simp]

中文:
定理 ι_comp_map
  条件: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  证明: ι_comp_lift _ _

@[simp]
-/
theorem ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
    (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι f₁ g₁) :=
  ι_comp_lift _ _

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (f₂ := f₁) (g₂ := g₁) (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁)
  proof: by
  ext
  rfl

中文:
定理 map_id
  结论: map (f₂ := f₁) (g₂ := g₁) (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁)
  证明: by
  ext
  rfl

Depends on / 依赖: equalizer
-/
theorem map_id : map (f₂ := f₁) (g₂ := g₁) (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) := by
  ext
  rfl

/--
theorem `comm_sq₂` / 定理 `comm_sq₂`

English:
theorem comm_sq₂
  given: (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ')
  proof: by
  rw [comp_assoc]; rw [hf]; rw [← comp_assoc]; rw [hf']; rw [comp_assoc]

中文:
定理 comm_sq₂
  条件: (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ')
  证明: by
  rw [comp_assoc]; rw [hf]; rw [← comp_assoc]; rw [hf']; rw [comp_assoc]

Depends on / 依赖: comp_assoc
-/
theorem comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
    (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) := by
  rw [comp_assoc]; rw [hf]; rw [← comp_assoc]; rw [hf']; rw [comp_assoc]

/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  statement: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  proof: by
  ext
  rfl

中文:
定理 map_comp_map
  结论: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  证明: by
  ext
  rfl
-/
theorem map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
    (hf' : ψ'.comp f₂ = f₃.comp φ') (hg' : ψ'.comp g₂ = g₃.comp φ') :
    (map φ' ψ' hf' hg').comp (map φ ψ hf hg) =
      map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') := by
  ext
  rfl

/--
theorem `ι_normNoninc` / 定理 `ι_normNoninc`

English:
theorem ι_normNoninc
  statement: (ι f g).NormNoninc
  proof: fun _v => le_rfl

中文:
定理 ι_normNoninc
  结论: (ι f g).NormNoninc
  证明: fun _v => le_rfl

Depends on / 依赖: le_rfl
-/
theorem ι_normNoninc : (ι f g).NormNoninc := fun _v => le_rfl

/--
theorem `lift_normNoninc` / 定理 `lift_normNoninc`

English:
theorem lift_normNoninc
  given: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc)
  proof: hφ

中文:
定理 lift_normNoninc
  条件: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc)
  证明: hφ
-/
theorem lift_normNoninc (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.NormNoninc) :
    (lift φ h).NormNoninc :=
  hφ

/--
theorem `norm_lift_le` / 定理 `norm_lift_le`

English:
theorem norm_lift_le
  given: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : Real) (hφ : ‖φ‖ <= C)
  proof: hφ

中文:
定理 norm_lift_le
  条件: (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : 实数) (hφ : ‖φ‖ <= C)
  证明: hφ
-/
theorem norm_lift_le (φ : NormedAddGroupHom V₁ V) (h : f.comp φ = g.comp φ) (C : Real) (hφ : ‖φ‖ <= C) :
    ‖lift φ h‖ <= C :=
  hφ

/--
theorem `map_normNoninc` / 定理 `map_normNoninc`

English:
theorem map_normNoninc
  statement: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  proof: lift_normNoninc _ _ hφ.comp ι_normNoninc

中文:
定理 map_normNoninc
  结论: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  证明: lift_normNoninc _ _ hφ.comp ι_normNoninc

Depends on / 依赖: lift_normNoninc
-/
theorem map_normNoninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
    (hφ : φ.NormNoninc) : (map φ ψ hf hg).NormNoninc :=
lift_normNoninc _ _ hφ.comp ι_normNoninc

/--
theorem `norm_map_le` / 定理 `norm_map_le`

English:
theorem norm_map_le
  statement: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : Real)
  proof: norm_lift_le _ _ _ hφ

中文:
定理 norm_map_le
  结论: (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : 实数)
  证明: norm_lift_le _ _ _ hφ

Depends on / 依赖: norm_lift_le
-/
theorem norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) (C : Real)
    (hφ : ‖φ.comp (ι f₁ g₁)‖ <= C) : ‖map φ ψ hf hg‖ <= C :=
  norm_lift_le _ _ _ hφ

end Equalizer

end NormedAddGroupHom
