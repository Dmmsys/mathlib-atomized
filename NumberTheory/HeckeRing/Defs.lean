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

/-- A *Hecke triple* `(H₁, Δ, H₂)`: the compatibility conditions on a submonoid `Δ` and a pair
of subgroups `H₁, H₂` of `G` making the double cosets `H₁\Δ/H₂` finite unions of left cosets:
both subgroups are contained in `Δ`, they are commensurable, and `Δ` commensurates them. The
classical Hecke pair `(H, Δ)` of [Shimura][shimura1971], Chapter 3, is the diagonal case
`IsHeckeTriple Δ H H`. -/
/-
**IsHeckeTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{G : Type u_1} → [inst : Group G] → Submonoid G → Subgroup G → Subgroup G 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *Hecke triple* `(H₁, Δ, H₂)`: the compatibility conditions on a submonoid `Δ` 
and a pair
of subgroups `H₁, H₂` of `G` making the double cosets `H₁\Δ/H₂` finite unions of
 left cosets:
both subgroups are contained in `Δ`, they are commensurable, and `Δ` commensurat
es them. The
classical Hecke pair `(H, Δ)` of [Shimura][shimura1971], Chapter 3, is the diago
nal case
`IsHeckeTriple Δ H H`.
-/
class IsHeckeTriple (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Prop where
  /-- The left subgroup is contained in `Δ`. -/
  left_le : H₁.toSubmonoid ≤ Δ
  /-- The right subgroup is contained in `Δ`. -/
  right_le : H₂.toSubmonoid ≤ Δ
  /-- The two subgroups are commensurable. -/
  commensurable : Commensurable H₁ H₂
  /-- The submonoid `Δ` lies in the commensurator of the right subgroup (hence, the subgroups
  being commensurable, also in that of the left one; see `le_commensurator_left`). -/
  le_commensurator_right : Δ ≤ (commensurator H₂).toSubmonoid

namespace IsHeckeTriple

variable {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}

/-- The Hecke triple `(H, Δ, H)` coming from a pair `(H, Δ)` with `H ≤ Δ ≤ commensurator H`. -/
/-
**IsHeckeTriple.of_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：of_diagonal {H : Subgroup G} (h : H.toSubmonoid <= Δ) (hc : Δ <= (commensu
rator H).toSubmonoid) : IsHeckeTriple Δ H H
参数：h : H.toSubmonoid <= Δ；hc : Δ <= (commensurator H).toSubmonoid。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Commensurable.refl`：∀ {G : Type u_1} [inst : Group G] (H : Subg
roup G), H.Commensurable H

--- 原说明 ---
The Hecke triple `(H, Δ, H)` coming from a pair `(H, Δ)` with `H ≤ Δ ≤ commensur
ator H`.
-/
theorem of_diagonal {H : Subgroup G} (h : H.toSubmonoid ≤ Δ)
    (hc : Δ ≤ (commensurator H).toSubmonoid) : IsHeckeTriple Δ H H :=
  ⟨h, h, .refl H, hc⟩

/-- Elements of the left subgroup lie in `Δ`. -/
/-
**IsHeckeTriple.mem_of_mem_left** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：mem_of_mem_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x 
in H₁) : x in Δ
参数：H₂ : Subgroup G；hx : x in H₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.left_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid 
G} {H₁ : Subgroup G} (H₂ : Subgroup G) [self : IsHeckeTriple Δ H₁ H₂],   H₁.toSu
bmonoid ≤ Δ

--- 原说明 ---
Elements of the left subgroup lie in `Δ`.
-/
theorem mem_of_mem_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x ∈ H₁) : x ∈ Δ :=
  left_le H₂ hx

/-- Elements of the right subgroup lie in `Δ`. -/
/-
**IsHeckeTriple.mem_of_mem_right** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：mem_of_mem_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x
 in H₂) : x in Δ
参数：H₁ : Subgroup G；hx : x in H₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.right_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid
 G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₂.toS
ubmonoid ≤ Δ

--- 原说明 ---
Elements of the right subgroup lie in `Δ`.
-/
theorem mem_of_mem_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] {x : G} (hx : x ∈ H₂) : x ∈ Δ :=
  right_le H₁ hx

/-- The submonoid `Δ` lies in the commensurator of the left subgroup. -/
/-
**IsHeckeTriple.le_commensurator_left** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：le_commensurator_left (H₂ : Subgroup G) [h : IsHeckeTriple Δ H₁ H₂] : Δ <=
 (commensurator H₁).toSubmonoid
参数：H₂ : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.Commensurable.eq`：eq {H K : Subgroup G} (hk : Commensurable H K
) : commensurator H = commensurator K
· 使用定理 `IsHeckeTriple.commensurable`：∀ {G : Type u_1} {inst : Group G} (Δ : Subm
onoid G) {H₁ H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₁.Commensurable
 H₂
· 使用定理 `IsHeckeTriple.le_commensurator_right`：∀ {G : Type u_1} {inst : Group G} 
{Δ : Submonoid G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁
 H₂],   Δ ≤ (Subgroup.Comm…

--- 原说明 ---
The submonoid `Δ` lies in the commensurator of the left subgroup.
-/
theorem le_commensurator_left (H₂ : Subgroup G) [h : IsHeckeTriple Δ H₁ H₂] :
    Δ ≤ (commensurator H₁).toSubmonoid := by
  rw [h.commensurable.eq]
  exact h.le_commensurator_right

/-- Elements of `Δ` lie in the commensurator of the right subgroup. -/
/-
**IsHeckeTriple.mem_commensurator_right** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple
`。
形式化陈述：mem_commensurator_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) 
: (g : G) in commensurator H₂
参数：H₁ : Subgroup G；g : Δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.le_commensurator_right`：∀ {G : Type u_1} {inst : Group G} 
{Δ : Submonoid G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁
 H₂],   Δ ≤ (Subgroup.Comm…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Elements of `Δ` lie in the commensurator of the right subgroup.
-/
theorem mem_commensurator_right (H₁ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) ∈ commensurator H₂ :=
  le_commensurator_right H₁ g.2

/-- Elements of `Δ` lie in the commensurator of the left subgroup. -/
/-
**IsHeckeTriple.mem_commensurator_left** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`
。
形式化陈述：mem_commensurator_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
 (g : G) in commensurator H₁
参数：H₂ : Subgroup G；g : Δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.le_commensurator_left`：le_commensurator_left (H₂ : Subgrou
p G) [h : IsHeckeTriple Δ H₁ H₂] : Δ <= (commensurator H₁).toSubmonoid
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Elements of `Δ` lie in the commensurator of the left subgroup.
-/
theorem mem_commensurator_left (H₂ : Subgroup G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    (g : G) ∈ commensurator H₁ :=
  le_commensurator_left H₂ g.2

/-- Conjugating the right subgroup of a Hecke triple `(H₁, Δ, H₂)` by an element of `Δ` gives a
subgroup commensurable with the left one. -/
/-
**IsHeckeTriple.commensurable_conjAct_right** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTr
iple`。
形式化陈述：commensurable_conjAct_right [IsHeckeTriple Δ H₁ H₂] (g : Δ) : Commensurabl
e (ConjAct.toConjAct (g : G) • H₂) H₁
参数：g : Δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.mem_commensurator_right`：mem_commensurator_right (H₁ : Sub
group G) [IsHeckeTriple Δ H₁ H₂] (g : Δ) : (g : G) in commensurator H₂
· 使用定理 `Subgroup.Commensurable.trans`：trans {H K L : Subgroup G} (hhk : Commensu
rable H K) (hkl : Commensurable K L) : Commensurable H L
· 使用定理 `Subgroup.Commensurable.symm`：symm {H K : Subgroup G} : Commensurable H K
 -> Commensurable K H
· 使用定理 `IsHeckeTriple.commensurable`：∀ {G : Type u_1} {inst : Group G} (Δ : Subm
onoid G) {H₁ H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₁.Commensurable
 H₂

--- 原说明 ---
Conjugating the right subgroup of a Hecke triple `(H₁, Δ, H₂)` by an element of 
`Δ` gives a
subgroup commensurable with the left one.
-/
theorem commensurable_conjAct_right [IsHeckeTriple Δ H₁ H₂] (g : Δ) :
    Commensurable (ConjAct.toConjAct (g : G) • H₂) H₁ := by
  have hg : Commensurable (ConjAct.toConjAct (g : G) • H₂) H₂ := mem_commensurator_right H₁ g
  exact hg.trans (commensurable (Δ := Δ)).symm

/-- Hecke coset module data compose. Not an instance, since the middle subgroup cannot be
inferred from the goal. -/
/-
**IsHeckeTriple.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：trans [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] : IsHeckeTriple Δ H₁
 H₃
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.left_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid 
G} {H₁ : Subgroup G} (H₂ : Subgroup G) [self : IsHeckeTriple Δ H₁ H₂],   H₁.toSu
bmonoid ≤ Δ
· 使用定理 `IsHeckeTriple.right_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid
 G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₂.toS
ubmonoid ≤ Δ
· 使用定理 `Subgroup.Commensurable.trans`：trans {H K L : Subgroup G} (hhk : Commensu
rable H K) (hkl : Commensurable K L) : Commensurable H L
· 使用定理 `IsHeckeTriple.commensurable`：∀ {G : Type u_1} {inst : Group G} (Δ : Subm
onoid G) {H₁ H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₁.Commensurable
 H₂
· 使用定理 `IsHeckeTriple.le_commensurator_right`：∀ {G : Type u_1} {inst : Group G} 
{Δ : Submonoid G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁
 H₂],   Δ ≤ (Subgroup.Comm…

--- 原说明 ---
Hecke coset module data compose. Not an instance, since the middle subgroup cann
ot be
inferred from the goal.
-/
theorem trans [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃] :
    IsHeckeTriple Δ H₁ H₃ :=
  ⟨left_le H₂, right_le H₂,
    (commensurable (Δ := Δ) (H₁ := H₁) (H₂ := H₂)).trans
      (commensurable (Δ := Δ) (H₁ := H₂) (H₂ := H₃)),
    le_commensurator_right H₂⟩

/-- The left diagonal datum `(H₁, Δ, H₁)`. Not an instance, since `H₂` cannot be inferred. -/
/-
**IsHeckeTriple.diag_left** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：diag_left [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₁ H₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.left_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid 
G} {H₁ : Subgroup G} (H₂ : Subgroup G) [self : IsHeckeTriple Δ H₁ H₂],   H₁.toSu
bmonoid ≤ Δ
· 使用定理 `Subgroup.Commensurable.refl`：∀ {G : Type u_1} [inst : Group G] (H : Subg
roup G), H.Commensurable H
· 使用定理 `IsHeckeTriple.le_commensurator_left`：le_commensurator_left (H₂ : Subgrou
p G) [h : IsHeckeTriple Δ H₁ H₂] : Δ <= (commensurator H₁).toSubmonoid

--- 原说明 ---
The left diagonal datum `(H₁, Δ, H₁)`. Not an instance, since `H₂` cannot be inf
erred.
-/
theorem diag_left [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₁ H₁ :=
  ⟨left_le H₂, left_le H₂, .refl H₁, le_commensurator_left H₂⟩

/-- The right diagonal datum `(H₂, Δ, H₂)`. Not an instance, since `H₁` cannot be inferred. -/
/-
**IsHeckeTriple.diag_right** 是 Mathlib 中的一个定理，位于命名空间 `IsHeckeTriple`。
形式化陈述：diag_right [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₂ H₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHeckeTriple.right_le`：∀ {G : Type u_1} {inst : Group G} {Δ : Submonoid
 G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁ H₂],   H₂.toS
ubmonoid ≤ Δ
· 使用定理 `Subgroup.Commensurable.refl`：∀ {G : Type u_1} [inst : Group G] (H : Subg
roup G), H.Commensurable H
· 使用定理 `IsHeckeTriple.le_commensurator_right`：∀ {G : Type u_1} {inst : Group G} 
{Δ : Submonoid G} (H₁ : Subgroup G) {H₂ : Subgroup G} [self : IsHeckeTriple Δ H₁
 H₂],   Δ ≤ (Subgroup.Comm…

--- 原说明 ---
The right diagonal datum `(H₂, Δ, H₂)`. Not an instance, since `H₁` cannot be in
ferred.
-/
theorem diag_right [IsHeckeTriple Δ H₁ H₂] : IsHeckeTriple Δ H₂ H₂ :=
  ⟨right_le H₁, right_le H₁, .refl H₂, le_commensurator_right H₁⟩

end IsHeckeTriple

/-- The setoid on `Δ` identifying elements with the same double coset `H₁gH₂ = H₁hH₂`, pulled
back from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is an `abbrev` rather than a global instance: the subgroups `H₁, H₂` cannot be inferred
from the submonoid `Δ`, so this cannot participate in instance search (and a global instance
would also create a `Setoid` diamond on `↥Δ` with the left-coset setoid). The quotient map is
`HeckeCoset.mk`. -/
/-
**HeckeCoset.setoid** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HeckeCoset.setoid (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Setoid Δ
参数：Δ : Submonoid G；H₁ H₂ : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid on `Δ` identifying elements with the same double coset `H₁gH₂ = H₁hH₂
`, pulled
back from `DoubleCoset.setoid` along the inclusion `Δ ↪ G`.

This is an `abbrev` rather than a global instance: the subgroups `H₁, H₂` cannot
 be inferred
from the submonoid `Δ`, so this cannot participate in instance search (and a glo
bal instance
would also create a `Setoid` diamond on `↥Δ` with the left-coset setoid). The qu
otient map is
`HeckeCoset.mk`.
-/
abbrev HeckeCoset.setoid (Δ : Submonoid G) (H₁ H₂ : Subgroup G) : Setoid Δ :=
  (DoubleCoset.setoid (H₁ : Set G) H₂).comap Subtype.val

/-- A Hecke double coset: an equivalence class of `Δ`-elements under `H₁gH₂ = H₁hH₂`. This is
the basis type for the `HeckeCosetModule`. -/
/-
**HeckeCoset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HeckeCoset (Δ : Submonoid G) (H₁ H₂ : Subgroup G)
参数：Δ : Submonoid G；H₁ H₂ : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Hecke double coset: an equivalence class of `Δ`-elements under `H₁gH₂ = H₁hH₂`
. This is
the basis type for the `HeckeCosetModule`.
-/
def HeckeCoset (Δ : Submonoid G) (H₁ H₂ : Subgroup G) := Quotient (HeckeCoset.setoid Δ H₁ H₂)

namespace HeckeCoset

variable {Δ : Submonoid G}

/-- The double coset `H₁gH₂` of an element `g : Δ`. -/
/-
**HeckeCoset.mk** 是 Mathlib 中的一个定义，位于命名空间 `HeckeCoset`。
形式化陈述：mk (H₁ H₂ : Subgroup G) (g : Δ) : HeckeCoset Δ H₁ H₂
参数：H₁ H₂ : Subgroup G；g : Δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double coset `H₁gH₂` of an element `g : Δ`.
-/
def mk (H₁ H₂ : Subgroup G) (g : Δ) : HeckeCoset Δ H₁ H₂ :=
  Quotient.mk (setoid Δ H₁ H₂) g

variable (Δ) in
/-
**HeckeCoset.** 是 Mathlib 中的一个实例，位于命名空间 `HeckeCoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H₁ H₂ : Subgroup G) : Inhabited (HeckeCoset Δ H₁ H₂) := ⟨mk H₁ H₂ ⟨1, Δ.one_mem⟩⟩

variable (Δ) in
/-- The identity double coset `H1H = H` of the diagonal (Hecke pair) case. -/
/-
**HeckeCoset.** 是 Mathlib 中的一个实例，位于命名空间 `HeckeCoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity double coset `H1H = H` of the diagonal (Hecke pair) case.
-/
instance (H : Subgroup G) : One (HeckeCoset Δ H H) := ⟨mk H H ⟨1, Δ.one_mem⟩⟩
/-
**HeckeCoset.one_def** 是 Mathlib 中的一个引理，位于命名空间 `HeckeCoset`。
形式化陈述：one_def (H : Subgroup G) : (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_def (H : Subgroup G) : (1 : HeckeCoset Δ H H) = mk H H ⟨1, Δ.one_mem⟩ := rfl

end HeckeCoset

/-- The Hecke coset module with coefficients in `Z`: the finitely-supported `Z`-linear
combinations of double cosets `H₁\Δ/H₂`. For `H₁ = H₂` this is the underlying module of the
Hecke ring `𝕋 Δ H Z` (see `HeckeRing`). The coefficients `Z` need only carry a `Zero` for the
type to make sense; algebraic structure is added by the instances below at the weakest level each
requires. -/
/-
**HeckeCosetModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero 
Z]
参数：Δ : Submonoid G；H₁ H₂ : Subgroup G；Z : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hecke coset module with coefficients in `Z`: the finitely-supported `Z`-line
ar
combinations of double cosets `H₁\Δ/H₂`. For `H₁ = H₂` this is the underlying mo
dule of the
Hecke ring `𝕋 Δ H Z` (see `HeckeRing`). The coefficients `Z` need only carry a `
Zero` for the
type to make sense; algebraic structure is added by the instances below at the w
eakest level each
requires.
-/
def HeckeCosetModule (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCoset Δ H₁ H₂ →₀ Z

/-- The Hecke ring `𝕋 Δ H Z` with coefficients in `Z`: the diagonal Hecke coset module
`HeckeCosetModule Δ H H Z`, the finitely-supported `Z`-linear combinations of double cosets
`H\Δ/H`. The convolution product making it a ring is developed in later files. -/
/-
**HeckeRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HeckeRing (Δ : Submonoid G) (H : Subgroup G) (Z : Type*) [Zero Z]
参数：Δ : Submonoid G；H : Subgroup G；Z : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hecke ring `𝕋 Δ H Z` with coefficients in `Z`: the diagonal Hecke coset modu
le
`HeckeCosetModule Δ H H Z`, the finitely-supported `Z`-linear combinations of do
uble cosets
`H\Δ/H`. The convolution product making it a ring is developed in later files.
-/
abbrev HeckeRing (Δ : Submonoid G) (H : Subgroup G) (Z : Type*) [Zero Z] :=
  HeckeCosetModule Δ H H Z

@[inherit_doc]
scoped[HeckeCosetModule] notation "𝕋" => HeckeRing

namespace HeckeCosetModule

variable (Δ : Submonoid G) (H₁ H₂ : Subgroup G) (Z : Type*)

/-- Elements of `HeckeCosetModule Δ H₁ H₂ Z` are functions `HeckeCoset Δ H₁ H₂ → Z` (finitely
supported). -/
/-
**HeckeCosetModule.** 是 Mathlib 中的一个实例，位于命名空间 `HeckeCosetModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Elements of `HeckeCosetModule Δ H₁ H₂ Z` are functions `HeckeCoset Δ H₁ H₂ → Z` 
(finitely
supported).
-/
instance [Zero Z] : FunLike (HeckeCosetModule Δ H₁ H₂ Z) (HeckeCoset Δ H₁ H₂) Z :=
  inferInstanceAs (FunLike (HeckeCoset Δ H₁ H₂ →₀ Z) (HeckeCoset Δ H₁ H₂) Z)
/-
**HeckeCosetModule.** 是 Mathlib 中的一个实例，位于命名空间 `HeckeCosetModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [AddCommMonoid Z] : AddCommMonoid (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommMonoid (HeckeCoset Δ H₁ H₂ →₀ Z))
/-
**HeckeCosetModule.** 是 Mathlib 中的一个实例，位于命名空间 `HeckeCosetModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [AddCommGroup Z] : AddCommGroup (HeckeCosetModule Δ H₁ H₂ Z) :=
  inferInstanceAs (AddCommGroup (HeckeCoset Δ H₁ H₂ →₀ Z))

/-- The sanctioned constructor of `HeckeCosetModule Δ H₁ H₂ Z` from a finitely-supported function
on double cosets. Build elements through `of` rather than relying on the definitional unfolding
`HeckeCosetModule Δ H₁ H₂ Z = (HeckeCoset Δ H₁ H₂ →₀ Z)`. -/
/-
**HeckeCosetModule.of** 是 Mathlib 中的一个定义，位于命名空间 `HeckeCosetModule`。
形式化陈述：of {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] : (HeckeCos
et Δ H₁ H₂ ->₀ Z) ≃ HeckeCosetModule Δ H₁ H₂ Z
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The sanctioned constructor of `HeckeCosetModule Δ H₁ H₂ Z` from a finitely-suppo
rted function
on double cosets. Build elements through `of` rather than relying on the definit
ional unfolding
`HeckeCosetModule Δ H₁ H₂ Z = (HeckeCoset Δ H₁ H₂ →₀ Z)`.
-/
def of {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] :
    (HeckeCoset Δ H₁ H₂ →₀ Z) ≃ HeckeCosetModule Δ H₁ H₂ Z :=
  Equiv.refl _

@[simp]
/-
**HeckeCosetModule.of_apply** 是 Mathlib 中的一个引理，位于命名空间 `HeckeCosetModule`。
形式化陈述：of_apply {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] (f : 
HeckeCoset Δ H₁ H₂ ->₀ Z) (D : HeckeCoset Δ H₁ H₂) : of f D = f D
参数：f : HeckeCoset Δ H₁ H₂ ->₀ Z；D : HeckeCoset Δ H₁ H₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_apply {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    (f : HeckeCoset Δ H₁ H₂ →₀ Z) (D : HeckeCoset Δ H₁ H₂) : of f D = f D :=
  rfl

@[ext]
/-
**HeckeCosetModule.ext** 是 Mathlib 中的一个引理，位于命名空间 `HeckeCosetModule`。
形式化陈述：ext {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z] {f g : Hec
keCosetModule Δ H₁ H₂ Z} (h : forall D, f D = g D) : f = g
参数：h : forall D, f D = g D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
lemma ext {Δ : Submonoid G} {H₁ H₂ : Subgroup G} {Z : Type*} [Zero Z]
    {f g : HeckeCosetModule Δ H₁ H₂ Z} (h : ∀ D, f D = g D) : f = g :=
  Finsupp.ext h

end HeckeCosetModule

