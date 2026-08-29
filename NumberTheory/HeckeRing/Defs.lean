/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Hecke rings: definitions

This file introduces the abstract Hecke ring of a *Hecke pair* `(H, Δ)` and, more generally, the
Hecke coset modules attached to a triple `(H₁, Δ, H₂)`, following [Shimura][shimura1971],
Chapter 3, and [Krieg][krieg1990], Chapter I. It sets up the underlying types: the compatibility
conditions `IsHeckeTriple Δ H₁ H₂` on a submonoid `Δ` of a group `G` and a pair of subgroups
of `G`, the double-coset quotient `HeckeCoset Δ H₁ H₂` of `Δ` by `H₁gH₂ = H₁hH₂`, and the Hecke
coset module `HeckeCosetModule Δ H₁ H₂ Z` of formal finitely-supported linear combinations of
double cosets.
The convolution product `HeckeCosetModule Δ H₁ H₂ Z × HeckeCosetModule Δ H₂ H₃ Z →
HeckeCosetModule Δ H₁ H₃ Z` and the ring structure on the diagonal Hecke ring `𝕋 Δ H Z` are
developed in later files.

The relevance of the submonoid `Δ` may not be immediately obvious; a natural example is
`H = GL₂(ℤ)` inside `G = GL₂(ℚ)` with `Δ` the submonoid of integral matrices with nonzero
determinant, which is the Hecke pair underlying the classical Hecke operators `T_n`. Mixed
subgroups `H₁ ≠ H₂` arise for Hecke operators between different levels, e.g. `H₁ = Γ₀(N)` and
`H₂ = Γ₀(M)` inside the same `Δ`.

## Main definitions

* `IsHeckeTriple Δ H₁ H₂`: `(H₁, Δ, H₂)` is a Hecke triple, i.e. `H₁ ≤ Δ`, `H₂ ≤ Δ`,
  `Commensurable H₁ H₂` and `Δ ≤ commensurator H₂`, making the double cosets `H₁\Δ/H₂` finite
  unions of left cosets. The classical Hecke pair `(H, Δ)` is the diagonal case
  `IsHeckeTriple Δ H H`.
* `HeckeCoset Δ H₁ H₂`: the quotient of `Δ` by the relation `H₁gH₂ = H₁hH₂`, i.e. the double
  cosets `H₁\Δ/H₂` forming the basis of the Hecke coset module.
* `HeckeCosetModule Δ H₁ H₂ Z`: the Hecke coset module with coefficients in `Z`, the
  finitely-supported `Z`-linear combinations of double cosets.
* `HeckeRing Δ H Z`, notation `𝕋 Δ H Z`: the Hecke ring, the diagonal case
  `HeckeCosetModule Δ H H Z` of the Hecke coset module.

## Implementation notes

The data `(Δ, H₁, H₂)` enters unbundled, with the compatibility conditions collected in the
Prop-valued class `IsHeckeTriple`: the types `HeckeCoset Δ H₁ H₂` and `HeckeCosetModule Δ H₁ H₂ Z`
are built from the data alone and depend on no proofs, and a single ambient `Δ` shared by all
levels
(as in [Shimura][shimura1971]) means products of double cosets over different subgroups,
`H₁g₁H₂ * H₂g₂H₃ ⊆ Δ`, need no compatibility hypotheses. The conditions are only needed for the
finiteness of the coset decompositions, which enters through the `Fintype` instance on
`DoubleCoset.DecompQuotient` in later files. Requiring `Δ` to be a submonoid rather than a
subsemigroup loses no generality, since `H₁ ≤ Δ` already forces `1 ∈ Δ`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971]
* [A. Krieg, *Hecke algebras*][krieg1990]
-/

@[expose] public section

open Subgroup Subgroup.Commensurable
open scoped Pointwise

variable {G : Type*} [Group G]

/--
Definition of `IsHeckeTriple` / `IsHeckeTriple` 的定义

English:
class IsHeckeTriple
  parameters: (Δ : Submonoid G) (H₁ H₂ : Subgroup G)
  axioms and operations (4):
    - left_le : H₁.toSubmonoid <= Δ
    - right_le : H₂.toSubmonoid <= Δ
    - commensurable : Commensurable H₁ H₂
    - le_commensurator_right : Δ <= (commensurator H₂).toSubmonoid

中文:
类 是HeckeTriple
  参数: (Δ : 子幺半群 G) (H₁ H₂ : 子群 G)
  公理与运算 (4 个):
    - left_le : H₁.toSubmonoid <= Δ
    - right_le : H₂.toSubmonoid <= Δ
    - commensurable : Commensurable H₁ H₂
    - le_commensurator_right : Δ <= (commensurator H₂).toSubmonoid
-/
class IsHeckeTriple (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Prop where
  /-- The left subgroup is contained in `Δ`. -/
  left_le : H₁.toSubmonoid <= Δ
  /-- The right subgroup is contained in `Δ`. -/
  right_le : H₂.toSubmonoid <= Δ
  /-- The two subgroups are commensurable. -/
  commensurable : Commensurable H₁ H₂
  /-- The submonoid `Δ` lies in the commensurator of the right subgroup (hence, the subgroups
  being commensurable, also in that of the left one; see `le_commensurator_left`). -/
  le_commensurator_right : Δ <= (commensurator H₂).toSubmonoid

namespace IsHeckeTriple

variable {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

/--
theorem `of_diagonal` / 定理 `of_diagonal`

English:
theorem of_diagonal
  statement: {H : Subgroup G} (h : H.toSubmonoid <= Δ)
  proof: ⟨h, h, .refl H, hc⟩

中文:
定理 of_diagonal
  结论: {H : 子群 G} (h : H.toSubmonoid <= Δ)
  证明: ⟨h, h, .refl H, hc⟩
-/
theorem of_diagonal {H : Subgroup G} (h : H.toSubmonoid <= Δ)
    (hc : Δ <= (commensurator H).toSubmonoid) : IsHeckeTriple Δ H H :=
  ⟨h, h, .refl H, hc⟩

/--
theorem `mem_of_mem_left` / 定理 `mem_of_mem_left`

English:
theorem mem_of_mem_left
  given: (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₁)
  statement: x in Δ
  proof: left_le H₂ hx

中文:
定理 mem_of_mem_left
  条件: (H₂ : 子群 G) [是HeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₁)
  结论: x in Δ
  证明: left_le H₂ hx

Depends on / 依赖: left_le
-/
theorem mem_of_mem_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₁) : x in Δ :=
  left_le H₂ hx

/--
theorem `mem_of_mem_right` / 定理 `mem_of_mem_right`

English:
theorem mem_of_mem_right
  given: (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₂)
  statement: x in Δ
  proof: right_le H₁ hx

中文:
定理 mem_of_mem_right
  条件: (H₁ : 子群 G) [是HeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₂)
  结论: x in Δ
  证明: right_le H₁ hx

Depends on / 依赖: right_le
-/
theorem mem_of_mem_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x in H₂) : x in Δ :=
  right_le H₁ hx

/--
theorem `le_commensurator_left` / 定理 `le_commensurator_left`

English:
theorem le_commensurator_left
  given: (H₂ : Subgroup G) [h : IsHeckeTriple Δ H₁ H₂]
  proof: by
  rw [h.commensurable.eq]
  exact h.le_commensurator_right

中文:
定理 le_commensurator_left
  条件: (H₂ : 子群 G) [h : 是HeckeTriple Δ H₁ H₂]
  证明: by
  rw [h.commensurable.eq]
  exact h.le_commensurator_right

Depends on / 依赖: commensurable, h.commensurable.eq, h.le_commensurator_right, le_commensurator_right
-/
theorem le_commensurator_left (H₂ : Subgroup G) [h : IsHeckeTriple Δ H₁ H₂] :
    Δ <= (commensurator H₁).toSubmonoid := by
  rw [h.commensurable.eq]
  exact h.le_commensurator_right

/--
theorem `mem_commensurator_right` / 定理 `mem_commensurator_right`

English:
theorem mem_commensurator_right
  given: (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ)
  proof: le_commensurator_right H₁ g.2

中文:
定理 mem_commensurator_right
  条件: (H₁ : 子群 G) [是HeckeTriple Δ H₁ H₂] (g : Δ)
  证明: le_commensurator_right H₁ g.2

Depends on / 依赖: le_commensurator_right
-/
theorem mem_commensurator_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) in commensurator H₂ :=
  le_commensurator_right H₁ g.2

/--
theorem `mem_commensurator_left` / 定理 `mem_commensurator_left`

English:
theorem mem_commensurator_left
  given: (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ)
  proof: le_commensurator_left H₂ g.2

中文:
定理 mem_commensurator_left
  条件: (H₂ : 子群 G) [是HeckeTriple Δ H₁ H₂] (g : Δ)
  证明: le_commensurator_left H₂ g.2

Depends on / 依赖: le_commensurator_left
-/
theorem mem_commensurator_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) in commensurator H₁ :=
  le_commensurator_left H₂ g.2

/--
theorem `commensurable_conjAct_right` / 定理 `commensurable_conjAct_right`

English:
theorem commensurable_conjAct_right
  given: [IsHeckeTriple Δ H₁ H₂] (g : Δ)
  proof: by
  have hg : Commensurable (ConjAct.toConjAct (g : G) • H₂) H₂ := mem_commensurator_right H₁ g
  exact hg.trans (commensurable (Δ := Δ)).symm

中文:
定理 commensurable_conjAct_right
  条件: [是HeckeTriple Δ H₁ H₂] (g : Δ)
  证明: by
  have hg : Commensurable (ConjAct.toConjAct (g : G) • H₂) H₂ := mem_commensurator_right H₁ g
  exact hg.trans (commensurable (Δ := Δ)).symm

Depends on / 依赖: Commensurable, ConjAct, ConjAct.toConjAct, commensurable, hg.trans, mem_commensurator_right, toConjAct
-/
theorem commensurable_conjAct_right [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    Commensurable (ConjAct.toConjAct (g : G) • H₂) H₁ := by
  have hg : Commensurable (ConjAct.toConjAct (g : G) • H₂) H₂ := mem_commensurator_right H₁ g
  exact hg.trans (commensurable (Δ := Δ)).symm

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
  proof: ⟨left_le H₂, right_le H₂,
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator_right H₂⟩

中文:
定理 trans
  条件: [是HeckeTriple Δ H₁ H₂] [是HeckeTriple Δ H₂ H₃]
  证明: ⟨left_le H₂, right_le H₂,
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator_right H₂⟩

Depends on / 依赖: commensurable, le_commensurator_right, left_le, right_le
-/
theorem trans [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] :
    IsHeckeTriple Δ H₁ H₃ :=
  ⟨left_le H₂, right_le H₂,
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator_right H₂⟩

/--
theorem `diag_left` / 定理 `diag_left`

English:
theorem diag_left
  given: [IsHeckeTriple Δ H₁ H₂]
  statement: IsHeckeTriple Δ H₁ H₁
  proof: ⟨left_le H₂, left_le H₂, .refl H₁, le_commensurator_left H₂⟩

中文:
定理 diag_left
  条件: [是HeckeTriple Δ H₁ H₂]
  结论: 是HeckeTriple Δ H₁ H₁
  证明: ⟨left_le H₂, left_le H₂, .refl H₁, le_commensurator_left H₂⟩

Depends on / 依赖: le_commensurator_left, left_le
-/
theorem diag_left [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₁ H₁ :=
  ⟨left_le H₂, left_le H₂, .refl H₁, le_commensurator_left H₂⟩

/--
theorem `diag_right` / 定理 `diag_right`

English:
theorem diag_right
  given: [IsHeckeTriple Δ H₁ H₂]
  statement: IsHeckeTriple Δ H₂ H₂
  proof: ⟨right_le H₁, right_le H₁, .refl H₂, le_commensurator_right H₁⟩

中文:
定理 diag_right
  条件: [是HeckeTriple Δ H₁ H₂]
  结论: 是HeckeTriple Δ H₂ H₂
  证明: ⟨right_le H₁, right_le H₁, .refl H₂, le_commensurator_right H₁⟩

Depends on / 依赖: le_commensurator_right, right_le
-/
theorem diag_right [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₂ H₂ :=
  ⟨right_le H₁, right_le H₁, .refl H₂, le_commensurator_right H₁⟩

end IsHeckeTriple

/--
Definition of `HeckeCoset.setoid` / `HeckeCoset.setoid` 的定义

English:
abbreviation HeckeCoset.setoid
  signature: (Δ : Submonoid G) (H₁ H₂ : Subgroup G)
  body: (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

中文:
缩写 HeckeCoset.setoid
  签名: (Δ : 子幺半群 G) (H₁ H₂ : 子群 G)
  定义体: (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

Depends on / 依赖: DoubleCoset, DoubleCoset.setoid, Subtype, Subtype.val, setoid
-/
abbrev HeckeCoset.setoid (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Setoid Δ :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/--
Definition of `HeckeCoset` / `HeckeCoset` 的定义

English:
definition HeckeCoset
  signature: (Δ : Submonoid G) (H₁ H₂ : Subgroup G)
  body: Quotient (HeckeCoset.setoid Δ H₁ H₂)

中文:
定义 HeckeCoset
  签名: (Δ : 子幺半群 G) (H₁ H₂ : 子群 G)
  定义体: Quotient (HeckeCoset.setoid Δ H₁ H₂)

Depends on / 依赖: HeckeCoset, HeckeCoset.setoid, Quotient, setoid
-/
def HeckeCoset (Δ : Submonoid G) (H₁ H₂ : Subgroup G) := Quotient (HeckeCoset.setoid Δ H₁ H₂)

namespace HeckeCoset

variable {Δ : Submonoid G}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (H₁ H₂ : Subgroup G) (g : Δ)
  body: Quotient.mk (setoid Δ H₁ H₂) g

中文:
定义 mk
  签名: (H₁ H₂ : 子群 G) (g : Δ)
  定义体: Quotient.mk (setoid Δ H₁ H₂) g

Depends on / 依赖: Quotient, Quotient.mk, setoid
-/
def mk (H₁ H₂ : Subgroup G) (g : Δ) : HeckeCoset Δ H₁ H₂ :=
  Quotient.mk (setoid Δ H₁ H₂) g

variable (Δ) in
instance (H₁ H₂ : Subgroup G) : Inhabited (HeckeCoset Δ H₁ H₂) := ⟨mk H₁ H₂ ⟨1, Δ.one_mem⟩⟩

variable (Δ) in
/-- The identity double coset `H1H = H` of the diagonal (Hecke pair) case. -/
instance (H : Subgroup G) : One (HeckeCoset Δ H H) := ⟨mk H H ⟨1, Δ.one_mem⟩⟩

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  given: (H : Subgroup G)
  statement: (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩
  proof: rfl

中文:
引理 one_def
  条件: (H : 子群 G)
  结论: (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩
  证明: rfl
-/
lemma one_def (H : Subgroup G) : (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩ := rfl

end HeckeCoset

/--
Definition of `HeckeCosetModule` / `HeckeCosetModule` 的定义

English:
definition HeckeCosetModule
  signature: (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero Z]
  body: HeckeCoset Δ H₁ H₂ ->₀ Z

中文:
定义 HeckeCosetModule
  签名: (Δ : 子幺半群 G) (H₁ H₂ : 子群 G) (Z : 类型) [零 Z]
  定义体: HeckeCoset Δ H₁ H₂ ->₀ Z

Depends on / 依赖: HeckeCoset
-/
def HeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCoset Δ H₁ H₂ ->₀ Z

/--
Definition of `HeckeRing` / `HeckeRing` 的定义

English:
abbreviation HeckeRing
  signature: (Δ : Submonoid G) (H : Subgroup G) (Z : Type*) [Zero Z]
  body: HeckeCosetModule Δ H H Z

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

中文:
缩写 HeckeRing
  签名: (Δ : 子幺半群 G) (H : 子群 G) (Z : 类型) [零 Z]
  定义体: HeckeCosetModule Δ H H Z

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

Depends on / 依赖: HeckeCosetModule
-/
abbrev HeckeRing (Δ : Submonoid G) (H : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCosetModule Δ H H Z

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

namespace HeckeCosetModule

variable (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: Z] : FunLike (HeckeCosetModule Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z
  body: inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ ->₀ Z) (HeckeCoset Δ H₁ H₂) Z)

中文:
实例 [零
  签名: Z] : 函数状 (HeckeCosetModule Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z
  定义体: inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ ->₀ Z) (HeckeCoset Δ H₁ H₂) Z)

Depends on / 依赖: FunLike, HeckeCoset
-/
instance [Zero Z] : FunLike (HeckeCosetModule Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z :=
  inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ ->₀ Z) (HeckeCoset Δ H₁ H₂) Z)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: Z] : AddCommMonoid (HeckeCosetModule Δ H₁ H₂ Z)
  body: inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ ->₀ Z))

中文:
实例 [加法交换幺半群
  签名: Z] : 加法交换幺半群 (HeckeCosetModule Δ H₁ H₂ Z)
  定义体: inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ ->₀ Z))

Depends on / 依赖: AddCommMonoid, HeckeCoset
-/
noncomputable instance [AddCommMonoid Z] : AddCommMonoid (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ ->₀ Z))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: Z] : AddCommGroup (HeckeCosetModule Δ H₁ H₂ Z)
  body: inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ ->₀ Z))

中文:
实例 [加法交换群
  签名: Z] : 加法交换群 (HeckeCosetModule Δ H₁ H₂ Z)
  定义体: inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ ->₀ Z))

Depends on / 依赖: AddCommGroup, HeckeCoset
-/
noncomputable instance [AddCommGroup Z] : AddCommGroup (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ ->₀ Z))

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
  body: Equiv.refl _

@[simp]

中文:
定义 of
  签名: {Δ : 子幺半群 G} {H₁ H₂ : 子群 G} {Z : 类型} [零 Z]
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def of {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] :
    (HeckeCoset Δ H₁ H₂ ->₀ Z) ≃ HeckeCosetModule Δ H₁ H₂ Z :=
  Equiv.refl _

@[simp]
/--
lemma `of_apply` / 引理 `of_apply`

English:
lemma of_apply
  statement: {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
  proof: rfl

@[ext]

中文:
引理 of_apply
  结论: {Δ : 子幺半群 G} {H₁ H₂ : 子群 G} {Z : 类型} [零 Z]
  证明: rfl

@[ext]
-/
lemma of_apply {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    (f : HeckeCoset Δ H₁ H₂ ->₀ Z) (D : HeckeCoset Δ H₁ H₂) : of f D = f D :=
  rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
  proof: Finsupp.ext h

中文:
引理 ext
  结论: {Δ : 子幺半群 G} {H₁ H₂ : 子群 G} {Z : 类型} [零 Z]
  证明: Finsupp.ext h

Depends on / 依赖: Finsupp, Finsupp.ext
-/
lemma ext {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    {f g : HeckeCosetModule Δ H₁ H₂ Z} (h : forall D, f D = g D) : f = g :=
  Finsupp.ext h

end HeckeCosetModule
