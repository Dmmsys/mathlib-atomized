/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Torsors of group actions

Further results for torsors, that are not in `Mathlib/Algebra/AddTorsor/Defs.lean` to avoid
increasing imports there.
-/

@[expose] public section

open scoped Pointwise


section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

namespace Set

@[to_additive]
/--
theorem `singleton_sdiv_self` / 定理 `singleton_sdiv_self`

English:
theorem singleton_sdiv_self
  given: (p : P)
  statement: ({p} : Set P) /ₛ {p} = {(1 : G)}
  proof: by
  rw [Set.singleton_sdiv_singleton]; rw [sdiv_self]

@[to_additive (attr := simp)]

中文:
定理 singleton_sdiv_self
  条件: (p : P)
  结论: ({p} : 集合 P) /ₛ {p} = {(1 : G)}
  证明: by
  rw [Set.singleton_sdiv_singleton]; rw [sdiv_self]

@[to_additive (attr := simp)]

Depends on / 依赖: Set.singleton_sdiv_singleton, sdiv_self, singleton_sdiv_singleton
-/
theorem singleton_sdiv_self (p : P) : ({p} : Set P) /ₛ {p} = {(1 : G)} := by
  rw [Set.singleton_sdiv_singleton]; rw [sdiv_self]

@[to_additive (attr := simp)]
/--
theorem `one_mem_sdiv_iff` / 定理 `one_mem_sdiv_iff`

English:
theorem one_mem_sdiv_iff
  given: {s t : Set P}
  statement: (1 : G) in s /ₛ t ↔ ¬Disjoint s t
  proof: by
  simp [not_disjoint_iff_nonempty_inter, mem_sdiv, Set.Nonempty]

@[to_additive]

中文:
定理 one_mem_sdiv_iff
  条件: {s t : 集合 P}
  结论: (1 : G) in s /ₛ t ↔ ¬Disjoint s t
  证明: by
  simp [not_disjoint_iff_nonempty_inter, mem_sdiv, Set.Nonempty]

@[to_additive]

Depends on / 依赖: Nonempty, Set.Nonempty, mem_sdiv, not_disjoint_iff_nonempty_inter
-/
theorem one_mem_sdiv_iff {s t : Set P} : (1 : G) in s /ₛ t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_sdiv, Set.Nonempty]

@[to_additive]
/--
theorem `Nonempty.one_mem_sdiv_self` / 定理 `Nonempty.one_mem_sdiv_self`

English:
theorem Nonempty.one_mem_sdiv_self
  given: {s : Set P} (h : s.Nonempty)
  statement: (1 : G) in s /ₛ s
  proof: let ⟨p, hp⟩ := h
  ⟨p, hp, p, hp, sdiv_self _⟩

中文:
定理 非空.one_mem_sdiv_self
  条件: {s : 集合 P} (h : s.非空)
  结论: (1 : G) in s /ₛ s
  证明: let ⟨p, hp⟩ := h
  ⟨p, hp, p, hp, sdiv_self _⟩

Depends on / 依赖: sdiv_self
-/
theorem Nonempty.one_mem_sdiv_self {s : Set P} (h : s.Nonempty) : (1 : G) in s /ₛ s :=
  let ⟨p, hp⟩ := h
  ⟨p, hp, p, hp, sdiv_self _⟩

end Set
/-- If dividing two points by the same point produces equal results, those points are equal. -/
@[to_additive /-- If the same point subtracted from two points produces equal
results, those points are equal. -/]
/--
theorem `sdiv_left_cancel` / 定理 `sdiv_left_cancel`

English:
theorem sdiv_left_cancel
  given: {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p)
  statement: p₁ = p₂
  proof: by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

中文:
定理 sdiv_left_cancel
  条件: {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p)
  结论: p₁ = p₂
  证明: by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

Depends on / 依赖: div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq
-/
theorem sdiv_left_cancel {p₁ p₂ p : P} (h : p₁ /ₛ p = p₂ /ₛ p) : p₁ = p₂ := by
  rwa [← div_eq_one, sdiv_div_sdiv_cancel_right, sdiv_eq_one_iff_eq] at h

/-- Dividing two points by the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp) /-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/]
/--
theorem `sdiv_left_cancel_iff` / 定理 `sdiv_left_cancel_iff`

English:
theorem sdiv_left_cancel_iff
  given: {p₁ p₂ p : P}
  statement: p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂
  proof: ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

中文:
定理 sdiv_left_cancel_iff
  条件: {p₁ p₂ p : P}
  结论: p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂
  证明: ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

Depends on / 依赖: sdiv_left_cancel
-/
theorem sdiv_left_cancel_iff {p₁ p₂ p : P} : p₁ /ₛ p = p₂ /ₛ p ↔ p₁ = p₂ :=
  ⟨sdiv_left_cancel, fun h => h ▸ rfl⟩

/-- Dividing by the point `p` is an injective function. -/
@[to_additive /-- Subtracting the point `p` is an injective function. -/]
/--
theorem `sdiv_left_injective` / 定理 `sdiv_left_injective`

English:
theorem sdiv_left_injective
  given: (p : P)
  statement: Function.Injective ((· /ₛ p) : P -> G)
  proof: fun _ _ =>
  sdiv_left_cancel

中文:
定理 sdiv_left_injective
  条件: (p : P)
  结论: 函数.单射 ((· /ₛ p) : P -> G)
  证明: fun _ _ =>
  sdiv_left_cancel
-/
theorem sdiv_left_injective (p : P) : Function.Injective ((· /ₛ p) : P -> G) := fun _ _ =>
  sdiv_left_cancel

/-- If dividing the same point by two points produces equal results, those points are equal. -/
@[to_additive /-- If subtracting two points from the same point produces equal
results, those points are equal. -/]
/--
theorem `sdiv_right_cancel` / 定理 `sdiv_right_cancel`

English:
theorem sdiv_right_cancel
  given: {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂)
  statement: p₁ = p₂
  proof: by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul]; rw [← h]; rw [sdiv_smul]

中文:
定理 sdiv_right_cancel
  条件: {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂)
  结论: p₁ = p₂
  证明: by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul]; rw [← h]; rw [sdiv_smul]

Depends on / 依赖: sdiv_smul, smul_left_cancel
-/
theorem sdiv_right_cancel {p₁ p₂ p : P} (h : p /ₛ p₁ = p /ₛ p₂) : p₁ = p₂ := by
  refine smul_left_cancel (p /ₛ p₂) ?_
  rw [sdiv_smul]; rw [← h]; rw [sdiv_smul]

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp)]
/--
theorem `sdiv_right_cancel_iff` / 定理 `sdiv_right_cancel_iff`

English:
theorem sdiv_right_cancel_iff
  given: {p₁ p₂ p : P}
  statement: p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂
  proof: ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

中文:
定理 sdiv_right_cancel_iff
  条件: {p₁ p₂ p : P}
  结论: p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂
  证明: ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

Depends on / 依赖: sdiv_right_cancel
-/
theorem sdiv_right_cancel_iff {p₁ p₂ p : P} : p /ₛ p₁ = p /ₛ p₂ ↔ p₁ = p₂ :=
  ⟨sdiv_right_cancel, fun h => h ▸ rfl⟩

/-- Dividing the point `p` by other points is an injective function. -/
@[to_additive /-- Subtracting a point from the point `p` is an injective function. -/]
/--
theorem `sdiv_right_injective` / 定理 `sdiv_right_injective`

English:
theorem sdiv_right_injective
  given: (p : P)
  statement: Function.Injective ((p /ₛ ·) : P -> G)
  proof: fun _ _ =>
  sdiv_right_cancel

中文:
定理 sdiv_right_injective
  条件: (p : P)
  结论: 函数.单射 ((p /ₛ ·) : P -> G)
  证明: fun _ _ =>
  sdiv_right_cancel
-/
theorem sdiv_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P -> G) := fun _ _ =>
  sdiv_right_cancel

end General

section comm

variable {G : Type*} {P : Type*} [CommGroup G] [Torsor G P]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
/--
theorem `sdiv_div_sdiv_cancel_left` / 定理 `sdiv_div_sdiv_cancel_left`

English:
theorem sdiv_div_sdiv_cancel_left
  given: (p₁ p₂ p₃ : P)
  statement: (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂
  proof: by
  rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]; rw [mul_comm]; rw [sdiv_mul_sdiv_cancel]

@[to_additive (attr := simp)]

中文:
定理 sdiv_div_sdiv_cancel_left
  条件: (p₁ p₂ p₃ : P)
  结论: (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂
  证明: by
  rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]; rw [mul_comm]; rw [sdiv_mul_sdiv_cancel]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, inv_sdiv_eq_sdiv_rev, mul_comm, sdiv_mul_sdiv_cancel
-/
theorem sdiv_div_sdiv_cancel_left (p₁ p₂ p₃ : P) : (p₃ /ₛ p₂) / (p₃ /ₛ p₁) = p₁ /ₛ p₂ := by
  rw [div_eq_mul_inv]; rw [inv_sdiv_eq_sdiv_rev]; rw [mul_comm]; rw [sdiv_mul_sdiv_cancel]

@[to_additive (attr := simp)]
/--
theorem `smul_sdiv_smul_cancel_left` / 定理 `smul_sdiv_smul_cancel_left`

English:
theorem smul_sdiv_smul_cancel_left
  given: (v : G) (p₁ p₂ : P)
  statement: (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂
  proof: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_cancel_left]

@[to_additive]

中文:
定理 smul_sdiv_smul_cancel_left
  条件: (v : G) (p₁ p₂ : P)
  结论: (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂
  证明: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_cancel_left]

@[to_additive]

Depends on / 依赖: mul_div_cancel_left, sdiv_smul_eq_sdiv_div, smul_sdiv_assoc
-/
theorem smul_sdiv_smul_cancel_left (v : G) (p₁ p₂ : P) : (v • p₁) /ₛ (v • p₂) = p₁ /ₛ p₂ := by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_cancel_left]

@[to_additive]
/--
theorem `smul_sdiv_smul_comm` / 定理 `smul_sdiv_smul_comm`

English:
theorem smul_sdiv_smul_comm
  given: (v₁ v₂ : G) (p₁ p₂ : P)
  proof: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_assoc]; rw [← mul_comm_div]

@[to_additive]

中文:
定理 smul_sdiv_smul_comm
  条件: (v₁ v₂ : G) (p₁ p₂ : P)
  证明: by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_assoc]; rw [← mul_comm_div]

@[to_additive]

Depends on / 依赖: mul_comm_div, mul_div_assoc, sdiv_smul_eq_sdiv_div, smul_sdiv_assoc
-/
theorem smul_sdiv_smul_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ • p₁) /ₛ (v₂ • p₂) = (v₁ / v₂) * (p₁ /ₛ p₂) := by
  rw [sdiv_smul_eq_sdiv_div]; rw [smul_sdiv_assoc]; rw [mul_div_assoc]; rw [← mul_comm_div]

@[to_additive]
/--
theorem `div_mul_sdiv_comm` / 定理 `div_mul_sdiv_comm`

English:
theorem div_mul_sdiv_comm
  given: (v₁ v₂ : G) (p₁ p₂ : P)
  proof: .symm smul_sdiv_smul_comm _ _ _ _

@[to_additive]

中文:
定理 div_mul_sdiv_comm
  条件: (v₁ v₂ : G) (p₁ p₂ : P)
  证明: .symm smul_sdiv_smul_comm _ _ _ _

@[to_additive]

Depends on / 依赖: smul_sdiv_smul_comm
-/
theorem div_mul_sdiv_comm (v₁ v₂ : G) (p₁ p₂ : P) :
    (v₁ / v₂) * (p₁ /ₛ p₂) = (v₁ • p₁) /ₛ (v₂ • p₂) :=
.symm smul_sdiv_smul_comm _ _ _ _

@[to_additive]
/--
theorem `sdiv_smul_comm` / 定理 `sdiv_smul_comm`

English:
theorem sdiv_smul_comm
  given: (p₁ p₂ p₃ : P)
  statement: (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁
  proof: by
  rw [← @sdiv_eq_one_iff_eq G]; rw [smul_sdiv_assoc]; rw [sdiv_smul_eq_sdiv_div]
  simp

@[to_additive]

中文:
定理 sdiv_smul_comm
  条件: (p₁ p₂ p₃ : P)
  结论: (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁
  证明: by
  rw [← @sdiv_eq_one_iff_eq G]; rw [smul_sdiv_assoc]; rw [sdiv_smul_eq_sdiv_div]
  simp

@[to_additive]

Depends on / 依赖: sdiv_eq_one_iff_eq, sdiv_smul_eq_sdiv_div, smul_sdiv_assoc
-/
theorem sdiv_smul_comm (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂ : G) • p₃ = (p₃ /ₛ p₂) • p₁ := by
  rw [← @sdiv_eq_one_iff_eq G]; rw [smul_sdiv_assoc]; rw [sdiv_smul_eq_sdiv_div]
  simp

@[to_additive]
/--
theorem `smul_eq_smul_iff_div_eq_sdiv` / 定理 `smul_eq_smul_iff_div_eq_sdiv`

English:
theorem smul_eq_smul_iff_div_eq_sdiv
  given: {v₁ v₂ : G} {p₁ p₂ : P}
  proof: by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv]; rw [inv_mul_eq_div]

@[to_additive]

中文:
定理 smul_eq_smul_iff_div_eq_sdiv
  条件: {v₁ v₂ : G} {p₁ p₂ : P}
  证明: by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv]; rw [inv_mul_eq_div]

@[to_additive]

Depends on / 依赖: inv_mul_eq_div, smul_eq_smul_iff_inv_mul_eq_sdiv
-/
theorem smul_eq_smul_iff_div_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₂ / v₁ = p₁ /ₛ p₂ := by
  rw [smul_eq_smul_iff_inv_mul_eq_sdiv]; rw [inv_mul_eq_div]

@[to_additive]
/--
theorem `sdiv_div_sdiv_comm` / 定理 `sdiv_div_sdiv_comm`

English:
theorem sdiv_div_sdiv_comm
  given: (p₁ p₂ p₃ p₄ : P)
  proof: by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul_comm]; rw [sdiv_smul_eq_sdiv_div]

中文:
定理 sdiv_div_sdiv_comm
  条件: (p₁ p₂ p₃ p₄ : P)
  证明: by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul_comm]; rw [sdiv_smul_eq_sdiv_div]

Depends on / 依赖: sdiv_smul_comm, sdiv_smul_eq_sdiv_div
-/
theorem sdiv_div_sdiv_comm (p₁ p₂ p₃ p₄ : P) :
    (p₁ /ₛ p₂) / (p₃ /ₛ p₄) = (p₁ /ₛ p₃) / (p₂ /ₛ p₄) := by
  rw [← sdiv_smul_eq_sdiv_div]; rw [sdiv_smul_comm]; rw [sdiv_smul_eq_sdiv_div]

namespace Set

@[to_additive (attr := simp)]
/--
lemma `smul_set_sdiv_smul_set` / 引理 `smul_set_sdiv_smul_set`

English:
lemma smul_set_sdiv_smul_set
  given: (v : G) (s t : Set P)
  statement: (v • s) /ₛ (v • t) = s /ₛ t
  proof: by
  ext; simp [mem_sdiv, mem_smul_set]

中文:
引理 smul_set_sdiv_smul_set
  条件: (v : G) (s t : 集合 P)
  结论: (v • s) /ₛ (v • t) = s /ₛ t
  证明: by
  ext; simp [mem_sdiv, mem_smul_set]

Depends on / 依赖: mem_sdiv, mem_smul_set
-/
lemma smul_set_sdiv_smul_set (v : G) (s t : Set P) : (v • s) /ₛ (v • t) = s /ₛ t := by
  ext; simp [mem_sdiv, mem_smul_set]

end Set

end comm

namespace Prod

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

@[to_additive]
/--
Instance `instTorsor` / 实例 `instTorsor`

English:
instance instTorsor
  signature: : Torsor (G × G') (P × P') where
  body: (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sd

中文:
实例 instTorsor
  签名: : Torsor (G × G') (P × P') where
  定义体: (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sd
-/
instance instTorsor : Torsor (G × G') (P × P') where
  smul v p := (v.1 • p.1, v.2 • p.2)
  one_smul _ := Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul _ _ _ := Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)
  sdiv p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  sdiv_smul' _ _ := Prod.ext (sdiv_smul _ _) (sdiv_smul _ _)
  smul_sdiv' _ _ := Prod.ext (smul_sdiv _ _) (smul_sdiv _ _)

@[to_additive (attr := simp)]
/--
theorem `fst_smul` / 定理 `fst_smul`

English:
theorem fst_smul
  given: (v : G × G') (p : P × P')
  statement: (v • p).1 = v.1 • p.1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_smul
  条件: (v : G × G') (p : P × P')
  结论: (v • p).1 = v.1 • p.1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_smul (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_smul` / 定理 `snd_smul`

English:
theorem snd_smul
  given: (v : G × G') (p : P × P')
  statement: (v • p).2 = v.2 • p.2
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_smul
  条件: (v : G × G') (p : P × P')
  结论: (v • p).2 = v.2 • p.2
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_smul (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_smul_mk` / 定理 `mk_smul_mk`

English:
theorem mk_smul_mk
  given: (v : G) (v' : G') (p : P) (p' : P')
  statement: (v, v') • (p, p') = (v • p, v' • p')
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_smul_mk
  条件: (v : G) (v' : G') (p : P) (p' : P')
  结论: (v, v') • (p, p') = (v • p, v' • p')
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: IsAffine, IsAffineOpen, MorphismProperty, MorphismProperty.RespectsIso.mk, Opens.map, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso, RespectsIso, cancel_left_of_respectsIso, cancel_right_of_respectsIso, e.hom, e.hom.base, hU.preimage_of_isIso, introv, morphismRestrict_comp, preimage_of_isIso
-/
theorem mk_smul_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • p, v' • p') :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `fst_sdiv` / 定理 `fst_sdiv`

English:
theorem fst_sdiv
  given: (p₁ p₂ : P × P')
  statement: (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 fst_sdiv
  条件: (p₁ p₂ : P × P')
  结论: (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem fst_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `snd_sdiv` / 定理 `snd_sdiv`

English:
theorem snd_sdiv
  given: (p₁ p₂ : P × P')
  statement: (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 snd_sdiv
  条件: (p₁ p₂ : P × P')
  结论: (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem snd_sdiv (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `mk_sdiv_mk` / 定理 `mk_sdiv_mk`

English:
theorem mk_sdiv_mk
  given: (p₁ p₂ : P) (p₁' p₂' : P')
  proof: rfl

中文:
定理 mk_sdiv_mk
  条件: (p₁ p₂ : P) (p₁' p₂' : P')
  证明: rfl
-/
theorem mk_sdiv_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') /ₛ (p₂, p₂') : G × G') = (p₁ /ₛ p₂, p₁' /ₛ p₂') :=
  rfl

end Prod

namespace Set

variable {G G' P P' : Type*} [Group G] [Group G'] [Torsor G P] [Torsor G' P']

@[to_additive prod_vsub_prod_comm]
/--
theorem `prod_sdiv_prod_comm` / 定理 `prod_sdiv_prod_comm`

English:
theorem prod_sdiv_prod_comm
  given: (s₁ s₂ : Set P) (t₁ t₂ : Set P')
  proof: by
  aesop (add norm simp [mem_sdiv, mem_prod])

中文:
定理 prod_sdiv_prod_comm
  条件: (s₁ s₂ : 集合 P) (t₁ t₂ : 集合 P')
  证明: by
  aesop (add norm simp [mem_sdiv, mem_prod])

Depends on / 依赖: mem_prod, mem_sdiv
-/
theorem prod_sdiv_prod_comm (s₁ s₂ : Set P) (t₁ t₂ : Set P') :
    (s₁ ×ˢ t₁) /ₛ (s₂ ×ˢ t₂) = (s₁ /ₛ s₂) ×ˢ (t₁ /ₛ t₂) := by
  aesop (add norm simp [mem_sdiv, mem_prod])

end Set

namespace Pi

universe u v w

variable {I : Type u} {fg : I -> Type v} [forall i, Group (fg i)] {fp : I -> Type w}
  [forall i, Torsor (fg i) (fp i)]

/-- A product of `Torsor`s is a `Torsor`. -/
@[to_additive /-- A product of `AddTorsor`s is an `AddTorsor`. -/]
/--
Instance `instTorsor` / 实例 `instTorsor`

English:
instance instTorsor
  signature: : Torsor (forall i, fg i) (forall i, fp i) where
  body: p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[to_additive (attr := simp)]

中文:
实例 instTorsor
  签名: : Torsor (对任意 i, fg i) (对任意 i, fp i) where
  定义体: p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[to_additive (attr := simp)]
-/
instance instTorsor : Torsor (forall i, fg i) (forall i, fp i) where
  sdiv p₁ p₂ i := p₁ i /ₛ p₂ i
  sdiv_smul' p₁ p₂ := funext fun i => sdiv_smul (p₁ i) (p₂ i)
  smul_sdiv' g p := funext fun i => smul_sdiv (g i) (p i)

@[to_additive (attr := simp)]
/--
theorem `sdiv_apply` / 定理 `sdiv_apply`

English:
theorem sdiv_apply
  given: (p q : forall i, fp i) (i : I)
  statement: (p /ₛ q) i = p i /ₛ q i
  proof: rfl

@[to_additive (attr := push ←)]

中文:
定理 sdiv_apply
  条件: (p q : 对任意 i, fp i) (i : I)
  结论: (p /ₛ q) i = p i /ₛ q i
  证明: rfl

@[to_additive (attr := push ←)]
-/
theorem sdiv_apply (p q : forall i, fp i) (i : I) : (p /ₛ q) i = p i /ₛ q i :=
  rfl

@[to_additive (attr := push ←)]
/--
theorem `sdiv_def` / 定理 `sdiv_def`

English:
theorem sdiv_def
  given: (p q : forall i, fp i)
  statement: p /ₛ q = fun i => p i /ₛ q i
  proof: rfl

中文:
定理 sdiv_def
  条件: (p q : 对任意 i, fp i)
  结论: p /ₛ q = fun i => p i /ₛ q i
  证明: rfl

Depends on / 依赖: P.RespectsIso, RespectsIso, eq_targetAffineLocally, infer_instance, isLocal_affineProperty
-/
theorem sdiv_def (p q : forall i, fp i) : p /ₛ q = fun i => p i /ₛ q i :=
  rfl

end Pi

namespace Equiv

variable (G : Type*) (P : Type*) [Group G] [Torsor G P]

@[to_additive (attr := simp)]
/--
theorem `constSMul_one` / 定理 `constSMul_one`

English:
theorem constSMul_one
  statement: constSMul P (1 : G) = 1
  proof: ext one_smul G

中文:
定理 constSMul_one
  结论: constSMul P (1 : G) = 1
  证明: ext one_smul G

Depends on / 依赖: one_smul
-/
theorem constSMul_one : constSMul P (1 : G) = 1 :=
ext one_smul G

variable {G}

@[to_additive (attr := simp)]
/--
theorem `constSMul_mul` / 定理 `constSMul_mul`

English:
theorem constSMul_mul
  given: (v₁ v₂ : G)
  statement: constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂
  proof: ext mul_smul v₁ v₂

中文:
定理 constSMul_mul
  条件: (v₁ v₂ : G)
  结论: constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂
  证明: ext mul_smul v₁ v₂

Depends on / 依赖: mul_smul
-/
theorem constSMul_mul (v₁ v₂ : G) : constSMul P (v₁ * v₂) = constSMul P v₁ * constSMul P v₂ :=
ext mul_smul v₁ v₂

/--
Definition of `constVAddHom` / `constVAddHom` 的定义

English:
definition constVAddHom
  signature: (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]
  body: constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' v v' := constVAdd_add P v.toAdd v'.toAdd

中文:
定义 constVAddHom
  签名: (G : 类型) (P : 类型) [加法群 G] [加法Torsor G P]
  定义体: constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' v v' := constVAdd_add P v.toAdd v'.toAdd

Depends on / 依赖: constVAdd, v.toAdd
-/
def constVAddHom (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P] :
    Multiplicative G ->* Equiv.Perm P where
  toFun v := constVAdd P (v.toAdd)
  map_one' := constVAdd_zero G P
  map_mul' v v' := constVAdd_add P v.toAdd v'.toAdd

/--
Definition of `constSMulHom` / `constSMulHom` 的定义

English:
definition constSMulHom
  signature: : G ->* Equiv.Perm P where
  body: constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

中文:
定义 constSMulHom
  签名: : G ->* 等价.置换 P where
  定义体: constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

Depends on / 依赖: constSMul
-/
def constSMulHom : G ->* Equiv.Perm P where
  toFun v := constSMul P v
  map_one' := constSMul_one G P
  map_mul' := constSMul_mul P

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

open Function

@[simp]
/--
theorem `left_vsub_pointReflection` / 定理 `left_vsub_pointReflection`

English:
theorem left_vsub_pointReflection
  given: (x y : P)
  statement: x -ᵥ pointReflection x y = y -ᵥ x
  proof: neg_injective by simp

@[simp]

中文:
定理 left_vsub_pointReflection
  条件: (x y : P)
  结论: x -ᵥ pointReflection x y = y -ᵥ x
  证明: neg_injective by simp

@[simp]

Depends on / 依赖: neg_injective
-/
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
neg_injective by simp

@[simp]
/--
theorem `right_vsub_pointReflection` / 定理 `right_vsub_pointReflection`

English:
theorem right_vsub_pointReflection
  given: (x y : P)
  statement: y -ᵥ pointReflection x y = 2 • (y -ᵥ x)
  proof: neg_injective by simp [← neg_nsmul]

中文:
定理 right_vsub_pointReflection
  条件: (x y : P)
  结论: y -ᵥ pointReflection x y = 2 • (y -ᵥ x)
  证明: neg_injective by simp [← neg_nsmul]

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.mk, P.arrow_mk_iso_iff, Q.arrow_mk_iso_iff, Y.ofRestrict, Y.openCoverOfIsOpenCover, affineRefinement, affineRefinement.openCover, arrow_mk_iso_iff, eq_targetAffineLocally, image_of_isOpenImmersion, isLocal_affineProperty, morphismRestrict, morphismRestrictEq, morphismRestrictRestrict, neg_injective, neg_nsmul, ofRestrict, of_openCover, openCover
-/
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
neg_injective by simp [← neg_nsmul]

/--
theorem `pointReflection_fixed_iff_of_injective_two_nsmul` / 定理 `pointReflection_fixed_iff_of_injective_two_nsmul`

English:
theorem pointReflection_fixed_iff_of_injective_two_nsmul
  given: {x y : P} (h : Injective (2 • · : G -> G))
  proof: by
  rw [pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [neg_eq_iff_add_eq_zero]; rw [← two_nsmul]; rw [← nsmul_zero 2]; rw [h.eq_iff]; rw [vsub_eq_zero_iff_eq]; rw [eq_comm]

中文:
定理 pointReflection_fixed_iff_of_injective_two_nsmul
  条件: {x y : P} (h : 单射 (2 • · : G -> G))
  证明: by
  rw [pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [neg_eq_iff_add_eq_zero]; rw [← two_nsmul]; rw [← nsmul_zero 2]; rw [h.eq_iff]; rw [vsub_eq_zero_iff_eq]; rw [eq_comm]

Depends on / 依赖: eq_comm, eq_iff, eq_vadd_iff_vsub_eq, h.eq_iff, neg_eq_iff_add_eq_zero, neg_vsub_eq_vsub_rev, nsmul_zero, pointReflection_apply, two_nsmul, vsub_eq_zero_iff_eq
-/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P} (h : Injective (2 • · : G -> G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply]; rw [eq_comm]; rw [eq_vadd_iff_vsub_eq]; rw [← neg_vsub_eq_vsub_rev]; rw [neg_eq_iff_add_eq_zero]; rw [← two_nsmul]; rw [← nsmul_zero 2]; rw [h.eq_iff]; rw [vsub_eq_zero_iff_eq]; rw [eq_comm]

/--
theorem `injective_pointReflection_left_of_injective_two_nsmul` / 定理 `injective_pointReflection_left_of_injective_two_nsmul`

English:
theorem injective_pointReflection_left_of_injective_two_nsmul
  statement: {G P : Type*} [AddCommGroup G]
  proof: fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

中文:
定理 injective_pointReflection_left_of_injective_two_nsmul
  结论: {G P : 类型} [加法交换群 G]
  证明: fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

Depends on / 依赖: eq_iff, h.eq_iff, neg_eq_iff_add_eq_zero, neg_vsub_eq_vsub_rev, nsmul_zero, pointReflection, pointReflection_apply, two_nsmul, vadd_eq_vadd_iff_sub_eq_vsub, vsub_eq_zero_iff_eq, vsub_sub_vsub_cancel_right
-/
theorem injective_pointReflection_left_of_injective_two_nsmul {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (2 • · : G -> G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero,
    ← two_nsmul, ← nsmul_zero 2, h.eq_iff, vsub_eq_zero_iff_eq] at hy

/--
lemma `pointReflection_eq_subLeft` / 引理 `pointReflection_eq_subLeft`

English:
lemma pointReflection_eq_subLeft
  given: {G : Type*} [AddCommGroup G] (x : G)
  proof: by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

中文:
引理 pointReflection_eq_subLeft
  条件: {G : 类型} [加法交换群 G] (x : G)
  证明: by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

Depends on / 依赖: pointReflection, sub_add_eq_add_sub, two_nsmul
-/
lemma pointReflection_eq_subLeft {G : Type*} [AddCommGroup G] (x : G) :
    pointReflection x = Equiv.subLeft (2 • x) := by
  ext; simp [pointReflection, sub_add_eq_add_sub, two_nsmul]

end Equiv

/-- Pullback of a torsor along an injective map. -/
@[to_additive /-- Pullback of an add torsor along an injective map. -/]
/--
Definition of `Function.Injective.torsor` / `Function.Injective.torsor` 的定义

English:
abbreviation Function.Injective.torsor
  signature: {G P Q : Type*}
  body: hf.mulAction f smul
sdiv_smul' x y := hf by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

中文:
缩写 函数.单射.torsor
  签名: {G P Q : 类型}
  定义体: hf.mulAction f smul
sdiv_smul' x y := hf by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

Depends on / 依赖: HasOfPostcompProperty, HasOfPostcompProperty.of_le, Scheme, hf.mulAction, monomorphisms, mulAction, of_le
-/
abbrev Function.Injective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q] [Nonempty Q] (f : Q -> P)
    (hf : Function.Injective f)
    (smul : forall (c : G) (x : Q), f (c • x) = c • f x)
    (sdiv : forall (x y : Q), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
sdiv_smul' x y := hf by simp only [sdiv, smul, sdiv_smul]
  smul_sdiv' c x := by simp [sdiv, smul]

/-- Pushforward of a torsor along a surjective map. -/
@[to_additive /-- Pushforward of an add torsor along a surjective map. -/]
/--
Definition of `Function.Surjective.torsor` / `Function.Surjective.torsor` 的定义

English:
abbreviation Function.Surjective.torsor
  signature: {G P Q : Type*}
  body: hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]

中文:
缩写 函数.满射.torsor
  签名: {G P Q : 类型}
  定义体: hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]

Depends on / 依赖: hf.mulAction, mulAction
-/
abbrev Function.Surjective.torsor {G P Q : Type*}
    [Group G] [Torsor G P] [SMul G Q] [SDiv G Q]
    (f : P -> Q) (hf : Surjective f)
    (smul : forall (c : G) (x : P), f (c • x) = c • f x)
    (sdiv : forall (x y : P), x /ₛ y = f x /ₛ f y) : Torsor G Q where
  __ := hf.mulAction f smul
  nonempty := Torsor.nonempty.map f
  sdiv_smul' := by simp [hf.forall, ← smul, ← sdiv]
  smul_sdiv' := by simp [hf.forall, ← smul, ← sdiv]
