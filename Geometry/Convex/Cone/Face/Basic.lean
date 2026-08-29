/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Faces of pointed cones

This file defines what it means for a pointed cone to be a face of another pointed cone and
establishes basic properties of this relation.
A subcone `F` of a cone `C` is a face if any two points in `C` that have a positive combination
in `F` are also in `F`.

## Main declarations

* `IsFaceOf F C`: States that the pointed cone `F` is a face of the pointed cone `C`.

## Implementation notes

* We do not use `IsExtreme` as a definition because this is an affine notion and does not allow the
  flexibility necessary to deal with cones over general rings. E.g. the cone of positive integers
  has no proper subset that are extreme. We prove that every face is an extreme set of its cone.
* Most results proven over a division ring hold more generally over an Archimedean ring. In
  particular, `iff_mem_of_add_mem_left` holds whenever for every `x ∈ R` there is a `y ∈ R` with
  `1 ≤ x * y`.

-/

open Submodule

public section

namespace PointedCone

variable {R M N : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

/-- A sub-cone `F` of a pointed cone `C` is a face of `C` if any two points of `C` with a strictly
positive combination in `F` are also in `F`. -/
@[mk_iff]
/--
Definition of `IsFaceOf` / `IsFaceOf` 的定义

English:
structure IsFaceOf
  parameters: (F C : PointedCone R M)
  axioms and operations (2):
    - le : F <= C
    - mem_of_smul_add_mem({x y : M} {a : R}) : x in C -> y in C -> 0 < a -> a • x + y in F -> x in F

中文:
结构 是FaceOf
  参数: (F C : PointedCone R M)
  公理与运算 (2 个):
    - le : F <= C
    - mem_of_smul_add_mem({x y : M} {a : R}) : x in C -> y in C -> 0 < a -> a • x + y in F -> x in F
-/
structure IsFaceOf (F C : PointedCone R M) : Prop where
  le : F <= C
  mem_of_smul_add_mem {x y : M} {a : R} :
    x in C -> y in C -> 0 < a -> a • x + y in F -> x in F

variable {C C₁ C₂ F F₁ F₂ : PointedCone R M}

namespace IsFaceOf

/--
theorem `mem_of_smul_add_smul_mem_left` / 定理 `mem_of_smul_add_smul_mem_left`

English:
theorem mem_of_smul_add_smul_mem_left
  statement: {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x in C)
  proof: hF.2 hx (smul_mem _ hb.le hy) ha h

中文:
定理 mem_of_smul_add_smul_mem_left
  结论: {x y : M} {a b : R} (hF : F.是FaceOf C) (hx : x in C)
  证明: hF.2 hx (smul_mem _ hb.le hy) ha h

Depends on / 依赖: hb.le, smul_mem
-/
theorem mem_of_smul_add_smul_mem_left {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x in C)
    (hy : y in C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y in F) : x in F :=
  hF.2 hx (smul_mem _ hb.le hy) ha h

/--
theorem `mem_of_smul_add_smul_mem_right` / 定理 `mem_of_smul_add_smul_mem_right`

English:
theorem mem_of_smul_add_smul_mem_right
  statement: {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x in C)
  proof: by
  apply hF.2 hy (smul_mem _ ha.le hx) hb; rwa [add_comm]

中文:
定理 mem_of_smul_add_smul_mem_right
  结论: {x y : M} {a b : R} (hF : F.是FaceOf C) (hx : x in C)
  证明: by
  apply hF.2 hy (smul_mem _ ha.le hx) hb; rwa [add_comm]

Depends on / 依赖: add_comm, ha.le, smul_mem
-/
theorem mem_of_smul_add_smul_mem_right {x y : M} {a b : R} (hF : F.IsFaceOf C) (hx : x in C)
    (hy : y in C) (ha : 0 < a) (hb : 0 < b) (h : a • x + b • y in F) : y in F := by
  apply hF.2 hy (smul_mem _ ha.le hx) hb; rwa [add_comm]

/-- A pointed cone `C` is a face of itself. -/
@[refl, simp]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (C : PointedCone R M)
  statement: C.IsFaceOf C
  proof: ⟨fun _ a => a, fun hx _ _ _ => hx⟩

中文:
定理 refl
  条件: (C : PointedCone R M)
  结论: C.是FaceOf C
  证明: ⟨fun _ a => a, fun hx _ _ _ => hx⟩
-/
protected theorem refl (C : PointedCone R M) : C.IsFaceOf C := ⟨fun _ a => a, fun hx _ _ _ => hx⟩

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  given: {C : PointedCone R M}
  statement: C.IsFaceOf C
  proof: .refl _

中文:
定理 rfl
  条件: {C : PointedCone R M}
  结论: C.是FaceOf C
  证明: .refl _
-/
protected theorem rfl {C : PointedCone R M} : C.IsFaceOf C := .refl _

/--
theorem `isFaceOf_iff_le` / 定理 `isFaceOf_iff_le`

English:
theorem isFaceOf_iff_le
  given: (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C)
  proof: ⟨IsFaceOf.le, fun h => ⟨h, fun hx hy ha hxy => h₁.2 (h₂.le hx) (h₂.le hy) ha hxy⟩⟩

中文:
定理 isFaceOf_iff_le
  条件: (h₁ : F₁.是FaceOf C) (h₂ : F₂.是FaceOf C)
  证明: ⟨IsFaceOf.le, fun h => ⟨h, fun hx hy ha hxy => h₁.2 (h₂.le hx) (h₂.le hy) ha hxy⟩⟩

Depends on / 依赖: IsFaceOf, IsFaceOf.le
-/
theorem isFaceOf_iff_le (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) :
    F₁.IsFaceOf F₂ ↔ F₁ <= F₂ :=
  ⟨IsFaceOf.le, fun h => ⟨h, fun hx hy ha hxy => h₁.2 (h₂.le hx) (h₂.le hy) ha hxy⟩⟩

/--
theorem `isExtreme` / 定理 `isExtreme`

English:
theorem isExtreme
  given: (h : F.IsFaceOf C)
  statement: IsExtreme R (C : Set M) F
  proof: by
  refine ⟨h.1, ?_⟩
  rintro _ xc _ yc _ zf ⟨_, _, a0, b0, -, rfl⟩
  exact h.mem_of_smul_add_smul_mem_left xc yc a0 b0 zf

中文:
定理 isExtreme
  条件: (h : F.是FaceOf C)
  结论: 是Extreme R (C : 集合 M) F
  证明: by
  refine ⟨h.1, ?_⟩
  rintro _ xc _ yc _ zf ⟨_, _, a0, b0, -, rfl⟩
  exact h.mem_of_smul_add_smul_mem_left xc yc a0 b0 zf

Depends on / 依赖: h.mem_of_smul_add_smul_mem_left, mem_of_smul_add_smul_mem_left
-/
theorem isExtreme (h : F.IsFaceOf C) : IsExtreme R (C : Set M) F := by
  refine ⟨h.1, ?_⟩
  rintro _ xc _ yc _ zf ⟨_, _, a0, b0, -, rfl⟩
  exact h.mem_of_smul_add_smul_mem_left xc yc a0 b0 zf

/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  given: (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂)
  proof: by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

中文:
定理 下确界
  条件: (h₁ : F₁.是FaceOf C₁) (h₂ : F₂.是FaceOf C₂)
  证明: by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂
-/
protected theorem inf (h₁ : F₁.IsFaceOf C₁) (h₂ : F₂.IsFaceOf C₂) :
    (F₁ ⊓ F₂).IsFaceOf (C₁ ⊓ C₂) := by
  use le_inf_iff.mpr ⟨Set.inter_subset_left.trans h₁.le, Set.inter_subset_right.trans h₂.le⟩
  simp only [mem_inf, and_imp]
  refine fun xc₁ xc₂ yc₁ yc₂ a0 hz₁ hz₂ => ⟨?_, ?_⟩
  · exact h₁.mem_of_smul_add_mem xc₁ yc₁ a0 hz₁
  · exact h₂.mem_of_smul_add_mem xc₂ yc₂ a0 hz₂

/--
theorem `inf_left` / 定理 `inf_left`

English:
theorem inf_left
  given: (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C)
  statement: (F₁ ⊓ F₂).IsFaceOf C
  proof: inf_idem C ▸ IsFaceOf.inf h₁ h₂

中文:
定理 inf_left
  条件: (h₁ : F₁.是FaceOf C) (h₂ : F₂.是FaceOf C)
  结论: (F₁ ⊓ F₂).是FaceOf C
  证明: inf_idem C ▸ IsFaceOf.inf h₁ h₂

Depends on / 依赖: IsFaceOf, IsFaceOf.inf, inf_idem
-/
theorem inf_left (h₁ : F₁.IsFaceOf C) (h₂ : F₂.IsFaceOf C) : (F₁ ⊓ F₂).IsFaceOf C :=
  inf_idem C ▸ IsFaceOf.inf h₁ h₂

/--
theorem `inf_right` / 定理 `inf_right`

English:
theorem inf_right
  given: (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂)
  statement: F.IsFaceOf (C₁ ⊓ C₂)
  proof: inf_idem F ▸ IsFaceOf.inf h₁ h₂

中文:
定理 inf_right
  条件: (h₁ : F.是FaceOf C₁) (h₂ : F.是FaceOf C₂)
  结论: F.是FaceOf (C₁ ⊓ C₂)
  证明: inf_idem F ▸ IsFaceOf.inf h₁ h₂

Depends on / 依赖: IsFaceOf, IsFaceOf.inf, inf_idem
-/
theorem inf_right (h₁ : F.IsFaceOf C₁) (h₂ : F.IsFaceOf C₂) : F.IsFaceOf (C₁ ⊓ C₂) :=
  inf_idem F ▸ IsFaceOf.inf h₁ h₂

/--
theorem `sInf` / 定理 `sInf`

English:
theorem sInf
  given: (F : Set (PointedCone R M)) (h : forall f in F, f.IsFaceOf C)
  proof: sm.1
  mem_of_smul_add_mem := by
    simp only [mem_inf, mem_sInf, and_imp]
    intro _ _ a xc yc a0 _ h'
    simpa [xc] using fun F Fs => (h F Fs).mem_of_smul_add_mem xc yc a0 (h' F Fs)

中文:
定理 sInf
  条件: (F : 集合 (PointedCone R M)) (h : 对任意 f in F, f.是FaceOf C)
  证明: sm.1
  mem_of_smul_add_mem := by
    simp only [mem_inf, mem_sInf, and_imp]
    intro _ _ a xc yc a0 _ h'
    simpa [xc] using fun F Fs => (h F Fs).mem_of_smul_add_mem xc yc a0 (h' F Fs)
-/
protected theorem sInf (F : Set (PointedCone R M)) (h : forall f in F, f.IsFaceOf C) :
    (C ⊓ sInf F).IsFaceOf C where
  le _ sm := sm.1
  mem_of_smul_add_mem := by
    simp only [mem_inf, mem_sInf, and_imp]
    intro _ _ a xc yc a0 _ h'
    simpa [xc] using fun F Fs => (h F Fs).mem_of_smul_add_mem xc yc a0 (h' F Fs)

/--
theorem `mem_of_add_mem_left` / 定理 `mem_of_add_mem_left`

English:
theorem mem_of_add_mem_left
  statement: (hF : F.IsFaceOf C) {x y : M}
  proof: by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one

中文:
定理 mem_of_add_mem_left
  结论: (hF : F.是FaceOf C) {x y : M}
  证明: by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one

Depends on / 依赖: Module, Module.subsingleton, hF.mem_of_smul_add_mem, mem_of_smul_add_mem, nontriviality, subsingleton, zero_lt_one
-/
theorem mem_of_add_mem_left (hF : F.IsFaceOf C) {x y : M}
    (hx : x in C) (hy : y in C) (hxy : x + y in F) : x in F := by
  nontriviality R using Module.subsingleton R M
  simpa [hxy] using hF.mem_of_smul_add_mem hx hy zero_lt_one

/--
theorem `mem_of_add_mem_right` / 定理 `mem_of_add_mem_right`

English:
theorem mem_of_add_mem_right
  statement: (hF : F.IsFaceOf C) {x y : M}
  proof: by
  rw [add_comm x y] at hxy; exact mem_of_add_mem_left hF hy hx hxy

中文:
定理 mem_of_add_mem_right
  结论: (hF : F.是FaceOf C) {x y : M}
  证明: by
  rw [add_comm x y] at hxy; exact mem_of_add_mem_left hF hy hx hxy

Depends on / 依赖: add_comm, mem_of_add_mem_left
-/
theorem mem_of_add_mem_right (hF : F.IsFaceOf C) {x y : M}
    (hx : x in C) (hy : y in C) (hxy : x + y in F) : y in F := by
  rw [add_comm x y] at hxy; exact mem_of_add_mem_left hF hy hx hxy

/--
theorem `add_mem_iff_mem` / 定理 `add_mem_iff_mem`

English:
theorem add_mem_iff_mem
  given: (hF : F.IsFaceOf C) {x y : M} (hx : x in C) (hy : y in C)
  proof: by
  refine ⟨?_, fun ⟨hx, hy⟩ => F.add_mem hx hy⟩
  exact fun h => ⟨mem_of_add_mem_left hF hx hy h, mem_of_add_mem_right hF hx hy h⟩

中文:
定理 add_mem_iff_mem
  条件: (hF : F.是FaceOf C) {x y : M} (hx : x in C) (hy : y in C)
  证明: by
  refine ⟨?_, fun ⟨hx, hy⟩ => F.add_mem hx hy⟩
  exact fun h => ⟨mem_of_add_mem_left hF hx hy h, mem_of_add_mem_right hF hx hy h⟩

Depends on / 依赖: F.add_mem, add_mem, mem_of_add_mem_left, mem_of_add_mem_right
-/
theorem add_mem_iff_mem (hF : F.IsFaceOf C) {x y : M} (hx : x in C) (hy : y in C) :
    x + y in F ↔ x in F ∧ y in F := by
  refine ⟨?_, fun ⟨hx, hy⟩ => F.add_mem hx hy⟩
  exact fun h => ⟨mem_of_add_mem_left hF hx hy h, mem_of_add_mem_right hF hx hy h⟩

/--
theorem `mem_of_sum_mem` / 定理 `mem_of_sum_mem`

English:
theorem mem_of_sum_mem
  statement: {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C)
  proof: by classical
  apply hF.mem_of_add_mem_left (hsC i) (sum_mem (fun j (_ : j in Finset.univ.erase i) => hsC j))
  simp [hs]

中文:
定理 mem_of_sum_mem
  结论: {ι : 类型} [有限类型 ι] {f : ι -> M} (hF : F.是FaceOf C)
  证明: by classical
  apply hF.mem_of_add_mem_left (hsC i) (sum_mem (fun j (_ : j in Finset.univ.erase i) => hsC j))
  simp [hs]

Depends on / 依赖: Finset, Finset.univ.erase, classical, hF.mem_of_add_mem_left, mem_of_add_mem_left, sum_mem
-/
theorem mem_of_sum_mem {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C)
    (hsC : forall i : ι, f i in C) (hs : ∑ i : ι, f i in F) (i : ι) : f i in F := by classical
  apply hF.mem_of_add_mem_left (hsC i) (sum_mem (fun j (_ : j in Finset.univ.erase i) => hsC j))
  simp [hs]

/--
theorem `sum_mem_iff_mem` / 定理 `sum_mem_iff_mem`

English:
theorem sum_mem_iff_mem
  statement: {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C)
  proof: ⟨mem_of_sum_mem hF hsC, fun a => Submodule.sum_mem F fun c _ => a c⟩

中文:
定理 sum_mem_iff_mem
  结论: {ι : 类型} [有限类型 ι] {f : ι -> M} (hF : F.是FaceOf C)
  证明: ⟨mem_of_sum_mem hF hsC, fun a => Submodule.sum_mem F fun c _ => a c⟩

Depends on / 依赖: Submodule, Submodule.sum_mem, mem_of_sum_mem, sum_mem
-/
theorem sum_mem_iff_mem {ι : Type*} [Fintype ι] {f : ι -> M} (hF : F.IsFaceOf C)
    (hsC : forall i, f i in C) : ∑ i, f i in F ↔ forall i, f i in F :=
  ⟨mem_of_sum_mem hF hsC, fun a => Submodule.sum_mem F fun c _ => a c⟩

/--
theorem `mem_of_sum_smul_mem` / 定理 `mem_of_sum_smul_mem`

English:
theorem mem_of_sum_smul_mem
  statement: {ι : Type*} [Fintype ι] {f : ι -> M} {c : ι -> R}
  proof: by classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton i] at hs
  · refine hF.mem_of_smul_add_mem (hsC i) ?_ hci hs
    exact C.sum_mem fun i _ => C.smul_mem (hc i) (hsC i)
  · simp

中文:
定理 mem_of_sum_smul_mem
  结论: {ι : 类型} [有限类型 ι] {f : ι -> M} {c : ι -> R}
  证明: by classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton i] at hs
  · refine hF.mem_of_smul_add_mem (hsC i) ?_ hci hs
    exact C.sum_mem fun i _ => C.smul_mem (hc i) (hsC i)
  · simp

Depends on / 依赖: C.smul_mem, C.sum_mem, Finset, Finset.sum_eq_add_sum_sdiff_singleton, classical, hF.mem_of_smul_add_mem, mem_of_smul_add_mem, smul_mem, sum_eq_add_sum_sdiff_singleton, sum_mem
-/
theorem mem_of_sum_smul_mem {ι : Type*} [Fintype ι] {f : ι -> M} {c : ι -> R}
    (hF : F.IsFaceOf C) (hsC : forall i : ι, f i in C) (hc : forall i, 0 <= c i) (hs : ∑ i : ι, c i • f i in F)
    (i : ι) (hci : 0 < c i) : f i in F := by classical
  rw [Finset.sum_eq_add_sum_sdiff_singleton i] at hs
  · refine hF.mem_of_smul_add_mem (hsC i) ?_ hci hs
    exact C.sum_mem fun i _ => C.smul_mem (hc i) (hsC i)
  · simp

/-- The face of a face of a cone is also a face of the cone. -/
@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C)
  statement: F₂.IsFaceOf C
  proof: by
  refine ⟨h₁.1.trans h₂.1, fun hx hy ha hxy => h₁.2 (h₂.2 hx hy ha (h₁.le hxy)) ?_ ha hxy⟩
  exact h₂.mem_of_add_mem_right (smul_mem _ ha.le hx) hy (h₁.le hxy)

中文:
定理 trans
  条件: (h₁ : F₂.是FaceOf F₁) (h₂ : F₁.是FaceOf C)
  结论: F₂.是FaceOf C
  证明: by
  refine ⟨h₁.1.trans h₂.1, fun hx hy ha hxy => h₁.2 (h₂.2 hx hy ha (h₁.le hxy)) ?_ ha hxy⟩
  exact h₂.mem_of_add_mem_right (smul_mem _ ha.le hx) hy (h₁.le hxy)
-/
protected theorem trans (h₁ : F₂.IsFaceOf F₁) (h₂ : F₁.IsFaceOf C) : F₂.IsFaceOf C := by
  refine ⟨h₁.1.trans h₂.1, fun hx hy ha hxy => h₁.2 (h₂.2 hx hy ha (h₁.le hxy)) ?_ ha hxy⟩
  exact h₂.mem_of_add_mem_right (smul_mem _ ha.le hx) hy (h₁.le hxy)

section Map

variable [AddCommGroup N] [Module R N]

/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (f : M ->ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C)
  proof: map_mono hF.le
  mem_of_smul_add_mem := by
    rintro _ _ a ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha ⟨z, hz₁, hz₂⟩
    dsimp at hz₂
    rw [← map_smul]; rw [← map_add] at hz₂
    exact ⟨x, hF.mem_of_smul_add_mem hx hy ha (hf hz₂ ▸ hz₁), rfl⟩

中文:
定理 map
  条件: (f : M ->ₗ[R] N) (hf : 函数.单射 f) (hF : F.是FaceOf C)
  证明: map_mono hF.le
  mem_of_smul_add_mem := by
    rintro _ _ a ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha ⟨z, hz₁, hz₂⟩
    dsimp at hz₂
    rw [← map_smul]; rw [← map_add] at hz₂
    exact ⟨x, hF.mem_of_smul_add_mem hx hy ha (hf hz₂ ▸ hz₁), rfl⟩
-/
protected theorem map (f : M ->ₗ[R] N) (hf : Function.Injective f) (hF : F.IsFaceOf C) :
    (F.map f).IsFaceOf (C.map f) where
  le := map_mono hF.le
  mem_of_smul_add_mem := by
    rintro _ _ a ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha ⟨z, hz₁, hz₂⟩
    dsimp at hz₂
    rw [← map_smul]; rw [← map_add] at hz₂
    exact ⟨x, hF.mem_of_smul_add_mem hx hy ha (hf hz₂ ▸ hz₁), rfl⟩

/--
theorem `map_equiv` / 定理 `map_equiv`

English:
theorem map_equiv
  given: (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C)
  proof: hF.map _ e.injective

中文:
定理 map_equiv
  条件: (e : M ≃ₗ[R] N) (hF : F.是FaceOf C)
  证明: hF.map _ e.injective

Depends on / 依赖: e.injective, hF.map, injective
-/
theorem map_equiv (e : M ≃ₗ[R] N) (hF : F.IsFaceOf C) :
    (F.map (e : M ->ₗ[R] N)).IsFaceOf (C.map e) := hF.map _ e.injective

/--
theorem `of_map_injective` / 定理 `of_map_injective`

English:
theorem of_map_injective
  statement: {f : M ->ₗ[R] N} (hf : Function.Injective f)
  proof: by
  obtain ⟨sub, hF⟩ := hc
  refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
· obtain ⟨y, yC, hy⟩ := mem_map.mp sub (mem_map_of_mem xf)
    rwa [hf hy] at yC
  · simp only [mem_map, forall_exists_index, and_imp] at hF
    obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
    convert hx'
    exact hf hhx'.symm

中文:
定理 of_map_injective
  结论: {f : M ->ₗ[R] N} (hf : 函数.单射 f)
  证明: by
  obtain ⟨sub, hF⟩ := hc
  refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
· obtain ⟨y, yC, hy⟩ := mem_map.mp sub (mem_map_of_mem xf)
    rwa [hf hy] at yC
  · simp only [mem_map, forall_exists_index, and_imp] at hF
    obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
    convert hx'
    exact hf hhx'.symm

Depends on / 依赖: and_imp, convert, forall_exists_index, mem_map, mem_map.mp, mem_map_of_mem
-/
theorem of_map_injective {f : M ->ₗ[R] N} (hf : Function.Injective f)
    (hc : (map f F).IsFaceOf (map f C)) : F.IsFaceOf C := by
  obtain ⟨sub, hF⟩ := hc
  refine ⟨fun x xf => ?_, fun hx hy ha h => ?_⟩
· obtain ⟨y, yC, hy⟩ := mem_map.mp sub (mem_map_of_mem xf)
    rwa [hf hy] at yC
  · simp only [mem_map, forall_exists_index, and_imp] at hF
    obtain ⟨_, ⟨hx', hhx'⟩⟩ := hF _ hx rfl _ hy rfl ha _ h (by simp)
    convert hx'
    exact hf hhx'.symm

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  given: (f : N ->ₗ[R] M) (hF : F.IsFaceOf C)
  statement: (F.comap f).IsFaceOf (C.comap f)
  proof: by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem

中文:
定理 comap
  条件: (f : N ->ₗ[R] M) (hF : F.是FaceOf C)
  结论: (F.comap f).是FaceOf (C.comap f)
  证明: by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem
-/
protected theorem comap (f : N ->ₗ[R] M) (hF : F.IsFaceOf C) : (F.comap f).IsFaceOf (C.comap f) := by
  refine ⟨comap_mono hF.le, ?_⟩
  simp only [mem_comap, map_add, map_smul]
  exact hF.mem_of_smul_add_mem

/--
theorem `of_comap_surjective` / 定理 `of_comap_surjective`

English:
theorem of_comap_surjective
  statement: {f : N ->ₗ[R] M} (hf : Function.Surjective f)
  proof: by
  refine ⟨fun x xF => ?_, fun {x y _} xC yC a0 h => ?_⟩
  · rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

中文:
定理 of_comap_surjective
  结论: {f : N ->ₗ[R] M} (hf : 函数.满射 f)
  证明: by
  refine ⟨fun x xF => ?_, fun {x y _} xC yC a0 h => ?_⟩
  · rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

Depends on / 依赖: choose_spec, mem_comap, mem_comap.mp
-/
theorem of_comap_surjective {f : N ->ₗ[R] M} (hf : Function.Surjective f)
    (hc : (F.comap f).IsFaceOf (C.comap f)) : F.IsFaceOf C := by
  refine ⟨fun x xF => ?_, fun {x y _} xC yC a0 h => ?_⟩
  · rw [← (hf x).choose_spec] at xF ⊢
    exact mem_comap.mp (hc.1 xF)
  · rw [← (hf x).choose_spec] at h ⊢ xC
    rw [← (hf y).choose_spec] at h yC
    exact hc.2 xC yC a0 (by simpa)

end Map

end IsFaceOf

/--
theorem `isFaceOf_map_iff` / 定理 `isFaceOf_map_iff`

English:
theorem isFaceOf_map_iff
  given: [AddCommGroup N] [Module R N] {f : M ->ₗ[R] N} (hf : Function.Injective f)
  proof: ⟨IsFaceOf.of_map_injective hf, IsFaceOf.map _ hf⟩

中文:
定理 isFaceOf_map_iff
  条件: [加法交换群 N] [模 R N] {f : M ->ₗ[R] N} (hf : 函数.单射 f)
  证明: ⟨IsFaceOf.of_map_injective hf, IsFaceOf.map _ hf⟩

Depends on / 依赖: IsFaceOf, IsFaceOf.map, IsFaceOf.of_map_injective, of_map_injective
-/
theorem isFaceOf_map_iff [AddCommGroup N] [Module R N] {f : M ->ₗ[R] N} (hf : Function.Injective f) :
    (F.map f).IsFaceOf (C.map f) ↔ F.IsFaceOf C :=
  ⟨IsFaceOf.of_map_injective hf, IsFaceOf.map _ hf⟩

/--
theorem `isFaceOf_comap_iff` / 定理 `isFaceOf_comap_iff`

English:
theorem isFaceOf_comap_iff
  statement: [AddCommGroup N] [Module R N] {f : N ->ₗ[R] M}
  proof: ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

中文:
定理 isFaceOf_comap_iff
  结论: [加法交换群 N] [模 R N] {f : N ->ₗ[R] M}
  证明: ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

Depends on / 依赖: IsFaceOf, IsFaceOf.comap, IsFaceOf.of_comap_surjective, of_comap_surjective
-/
theorem isFaceOf_comap_iff [AddCommGroup N] [Module R N] {f : N ->ₗ[R] M}
    (hf : Function.Surjective f) : (F.comap f).IsFaceOf (C.comap f) ↔ F.IsFaceOf C :=
  ⟨IsFaceOf.of_comap_surjective hf, IsFaceOf.comap _⟩

end Semiring

section DivisionRing

variable [DivisionRing R] [LinearOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable {C F F₁ F₂ : PointedCone R M}

namespace IsFaceOf

/--
theorem `of_mem_of_add_mem_left` / 定理 `of_mem_of_add_mem_left`

English:
theorem of_mem_of_add_mem_left
  given: (h₁ : F <= C) (h₂ : forall {x y : M}, x in C -> y in C -> x + y in F -> x in F)
  proof: by
  refine ⟨h₁, fun hx hy ha haxy => ?_⟩
  simpa [← smul_assoc, inv_mul_cancel₀ (ne_of_gt ha)] using smul_mem _
(inv_nonneg.mpr (le_of_lt ha)) h₂ (smul_mem _ (le_of_lt ha) hx) hy haxy

中文:
定理 of_mem_of_add_mem_left
  条件: (h₁ : F <= C) (h₂ : 对任意 {x y : M}, x in C -> y in C -> x + y in F -> x in F)
  证明: by
  refine ⟨h₁, fun hx hy ha haxy => ?_⟩
  simpa [← smul_assoc, inv_mul_cancel₀ (ne_of_gt ha)] using smul_mem _
(inv_nonneg.mpr (le_of_lt ha)) h₂ (smul_mem _ (le_of_lt ha) hx) hy haxy

Depends on / 依赖: inv_nonneg, inv_nonneg.mpr, le_of_lt, ne_of_gt, smul_assoc, smul_mem
-/
theorem of_mem_of_add_mem_left (h₁ : F <= C) (h₂ : forall {x y : M}, x in C -> y in C -> x + y in F -> x in F) :
    F.IsFaceOf C := by
  refine ⟨h₁, fun hx hy ha haxy => ?_⟩
  simpa [← smul_assoc, inv_mul_cancel₀ (ne_of_gt ha)] using smul_mem _
(inv_nonneg.mpr (le_of_lt ha)) h₂ (smul_mem _ (le_of_lt ha) hx) hy haxy

/--
lemma `lineal` / 引理 `lineal`

English:
lemma lineal
  given: (C : PointedCone R M)
  statement: IsFaceOf C.lineal C
  proof: by
  apply of_mem_of_add_mem_left (lineal_le C)
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

中文:
引理 lineal
  条件: (C : PointedCone R M)
  结论: 是FaceOf C.lineal C
  证明: by
  apply of_mem_of_add_mem_left (lineal_le C)
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

Depends on / 依赖: add_mem, lineal_le, neg_add_cancel_comm, neg_add_rev, of_mem_of_add_mem_left, true_and
-/
lemma lineal (C : PointedCone R M) : IsFaceOf C.lineal C := by
  apply of_mem_of_add_mem_left (lineal_le C)
  intro _ _ xc yc xyf
  simp [neg_add_rev, xc, true_and] at xyf ⊢
  simpa [neg_add_cancel_comm] using add_mem xyf.2 yc

/--
lemma `lineal_le` / 引理 `lineal_le`

English:
lemma lineal_le
  given: (hF : F.IsFaceOf C)
  statement: C.lineal <= F
  proof: fun _ hx => hF.mem_of_add_mem_left hx.1 hx.2 (by simp)

中文:
引理 lineal_le
  条件: (hF : F.是FaceOf C)
  结论: C.lineal <= F
  证明: fun _ hx => hF.mem_of_add_mem_left hx.1 hx.2 (by simp)

Depends on / 依赖: hF.mem_of_add_mem_left, mem_of_add_mem_left
-/
lemma lineal_le (hF : F.IsFaceOf C) : C.lineal <= F :=
  fun _ hx => hF.mem_of_add_mem_left hx.1 hx.2 (by simp)

/--
lemma `lineal_congr` / 引理 `lineal_congr`

English:
lemma lineal_congr
  given: (hF : F.IsFaceOf C)
  statement: F.lineal = C.lineal
  proof: by
  ext
  refine ⟨fun ⟨hx, hx'⟩ => ⟨hF.le hx, hF.le hx'⟩, fun ⟨hx, hx'⟩ => ⟨?_, ?_⟩⟩
  · exact hF.mem_of_add_mem_left hx hx' (by simp)
  · exact hF.mem_of_add_mem_left hx' hx (by simp)

中文:
引理 lineal_congr
  条件: (hF : F.是FaceOf C)
  结论: F.lineal = C.lineal
  证明: by
  ext
  refine ⟨fun ⟨hx, hx'⟩ => ⟨hF.le hx, hF.le hx'⟩, fun ⟨hx, hx'⟩ => ⟨?_, ?_⟩⟩
  · exact hF.mem_of_add_mem_left hx hx' (by simp)
  · exact hF.mem_of_add_mem_left hx' hx (by simp)

Depends on / 依赖: hF.le, hF.mem_of_add_mem_left, mem_of_add_mem_left
-/
lemma lineal_congr (hF : F.IsFaceOf C) : F.lineal = C.lineal := by
  ext
  refine ⟨fun ⟨hx, hx'⟩ => ⟨hF.le hx, hF.le hx'⟩, fun ⟨hx, hx'⟩ => ⟨?_, ?_⟩⟩
  · exact hF.mem_of_add_mem_left hx hx' (by simp)
  · exact hF.mem_of_add_mem_left hx' hx (by simp)

section Prod

variable [AddCommGroup N] [Module R N]

/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  statement: {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
  proof: by
  refine ⟨fun x hx => by simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩, ?_⟩
  simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
  intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
  exact ⟨hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁, hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂⟩

中文:
定理 乘积
  结论: {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
  证明: by
  refine ⟨fun x hx => by simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩, ?_⟩
  simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
  intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
  exact ⟨hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁, hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂⟩
-/
protected theorem prod {C₁ F₁ : PointedCone R M} {C₂ F₂ : PointedCone R N}
    (hF₁ : F₁.IsFaceOf C₁) (hF₂ : F₂.IsFaceOf C₂) : IsFaceOf (F₁.prod F₂) (C₁.prod C₂) := by
  refine ⟨fun x hx => by simpa [mem_prod] using ⟨hF₁.le hx.1, hF₂.le hx.2⟩, ?_⟩
  simp only [mem_prod, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, and_imp, Prod.forall]
  intro _ _ _ _ _ xc₁ xc₂ yc₁ yc₂ a0 hab₁ hab₂
  exact ⟨hF₁.mem_of_smul_add_mem xc₁ yc₁ a0 hab₁, hF₂.mem_of_smul_add_mem xc₂ yc₂ a0 hab₂⟩

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  statement: {C₁ : PointedCone R M} {C₂ : PointedCone R N}
  proof: by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩

中文:
定理 fst
  结论: {C₁ : PointedCone R M} {C₂ : PointedCone R N}
  证明: by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩
-/
protected theorem fst {C₁ : PointedCone R M} {C₂ : PointedCone R N}
    {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.fst R M N)).IsFaceOf C₁ := by
  constructor
  · intro x hx
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right] at hx
    exact (Set.mem_prod.mp <| hF.le hx.choose_spec).1
  · simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro x y a hx hy ha z h
    refine ⟨0, hF.mem_of_smul_add_mem (x := (x, 0)) (y := (y, z)) ?_ ?_ ha (by simpa)⟩
    · exact mem_prod.mp ⟨hx, zero_mem C₂⟩
    · exact mem_prod.mp ⟨hy, (hF.le h).2⟩

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  statement: {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
  proof: by
  have := hF.map _ (LinearEquiv.prodComm R M N).injective
  convert IsFaceOf.fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

中文:
定理 snd
  结论: {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
  证明: by
  have := hF.map _ (LinearEquiv.prodComm R M N).injective
  convert IsFaceOf.fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp
-/
protected theorem snd {C₁ : PointedCone R M} {C₂ : PointedCone R N} {F : PointedCone R (M × N)}
    (hF : F.IsFaceOf (C₁.prod C₂)) : (F.map (.snd R M N)).IsFaceOf C₂ := by
  have := hF.map _ (LinearEquiv.prodComm R M N).injective
  convert IsFaceOf.fst (by simpa [PointedCone.map, Submodule.map])
  ext; simp

end Prod

end IsFaceOf

end DivisionRing

end PointedCone
