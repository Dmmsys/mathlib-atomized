/-
Copyright (c) 2026 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
module

public import Mathlib.Topology.MetricSpace.Cover

/-!
# Delone sets

A **Delone set** `D ⊆ X` in a metric space is a set which is both:

* **Uniformly Discrete**: there exists `packingRadius > 0` such that distinct points of `D`
  are separated by a distance strictly greater than `packingRadius`;
* **Relatively Dense**: there exists `coveringRadius > 0` such that every point of `X`
  lies within distance `coveringRadius` of some point of `D`.

The `DeloneSet` structure stores the set together with explicit radii witnessing
these properties. The definitions use metric entourages so that the theory fits
naturally into the uniformity framework.

Delone sets appear in discrete geometry, crystallography, aperiodic order, and tiling theory.

## Main definitions

* `Delone.DeloneSet X`: The main structure representing a Delone set in a metric space `X`.
* `DeloneSet.mapBilipschitz`: Transports a Delone set along a bilipschitz equivalence,
  scaling the radii.
* `DeloneSet.mapIsometry` Preserves the packing and covering radii exactly.

## Basic properties

* `packingRadius_lt_dist_of_mem_ne` : Distinct points in a Delone set are further apart than
  the packing radius.
* `exists_dist_le_coveringRadius` : Every point of the space lies within the covering radius
  of the set.
* `subset_ball_singleton` : Any ball of sufficiently small radius contains at most one point of
  the set.

## Implementation notes

* **Bundled Structure**: `DeloneSet` is bundled as a structure rather than a predicate
  (e.g., `IsDelone`). This facilitates dynamical systems constructions like hulls and patches by
  ensuring operations automatically preserve the required properties, eliminating the need to
  manually pass around proofs that the set remains Delone.
* **Explicit Data**: Since radii are stored as explicit data, the map from `DeloneSet X` to `Set X`
  is not injective. We provide a `Membership` instance and `mem_carrier` to allow the convenience
  of `∈` notation while ensuring radii remain bundled, computationally accessible, and tracked by
  extensionality.
-/

@[expose] public section

open Metric
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

namespace Delone

/-- A **Delone set** consists of a set together with explicit radii
witnessing uniform discreteness and relative denseness. -/
@[ext]
/-
**Delone.DeloneSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `Delone`。
形式化陈述：(X : Type u_3) → [MetricSpace X] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **Delone set** consists of a set together with explicit radii
witnessing uniform discreteness and relative denseness.
-/
structure DeloneSet (X : Type*) [MetricSpace X] where
  /-- The underlying set. -/
  carrier : Set X
  /-- Radius such that distinct points of `carrier` are separated by more than `r`. -/
  packingRadius : ℝ≥0
  packingRadius_pos : 0 < packingRadius
  isSeparated_packingRadius : IsSeparated packingRadius carrier
  /-- Radius such that every point of the space is within `R` of `carrier`. -/
  coveringRadius : ℝ≥0
  coveringRadius_pos : 0 < coveringRadius
  isCover_coveringRadius : IsCover coveringRadius .univ carrier

namespace DeloneSet

/-- The underlying set of points of a Delone set. -/
/-
**Delone.DeloneSet.toSet** 是 Mathlib 中的一个定义，位于命名空间 `Delone.DeloneSet`。
形式化陈述：{X : Type u_1} → [inst : MetricSpace X] → Delone.DeloneSet X → Set X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying set of points of a Delone set.
-/
@[coe] def toSet (D : DeloneSet X) : Set X := D.carrier
/-
**Delone.DeloneSet.** 是 Mathlib 中的一个实例，位于命名空间 `Delone.DeloneSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying set of points of a Delone set.
-/
instance : Coe (DeloneSet X) (Set X) where
  coe := DeloneSet.toSet
/-
**Delone.DeloneSet.** 是 Mathlib 中的一个实例，位于命名空间 `Delone.DeloneSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership X (DeloneSet X) where
  mem D x := x ∈ (D : Set X)

@[simp, norm_cast]
/-
**Delone.DeloneSet.mem_coe** 是 Mathlib 中的一个引理，位于命名空间 `Delone.DeloneSet`。
形式化陈述：mem_coe {D : DeloneSet X} {x : X} : x in (D : Set X) ↔ x in D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_coe {D : DeloneSet X} {x : X} : x ∈ (D : Set X) ↔ x ∈ D := .rfl
/-
**Delone.DeloneSet.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `Delone.DeloneSet`。
形式化陈述：∀ {X : Type u_1} [inst : MetricSpace X] {D : Delone.DeloneSet X} {x : X}, 
x ∈ D.carrier ↔ x ∈ D
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_carrier {D : DeloneSet X} {x : X} :
    x ∈ D.carrier ↔ x ∈ D := .rfl
/-
**Delone.DeloneSet.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Delone.DeloneSet`。
形式化陈述：nonempty [Nonempty X] (D : DeloneSet X) : (D : Set X).Nonempty
参数：D : DeloneSet X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.IsCover.nonempty`：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] 
{ε : NNReal} {s N : Set X},   Metric.IsCover ε s N → s.Nonempty → N.Nonempty
· 使用定理 `Delone.DeloneSet.isCover_coveringRadius`：∀ {X : Type u_3} [inst : Metric
Space X] (self : Delone.DeloneSet X),   Metric.IsCover self.coveringRadius Set.u
niv self.carrier
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
-/
lemma nonempty [Nonempty X] (D : DeloneSet X) : (D : Set X).Nonempty :=
  D.isCover_coveringRadius.nonempty Set.univ_nonempty

/-- Copy of a Delone set with new fields equal to the old ones.
Useful to fix definitional equalities. -/
/-
**Delone.DeloneSet.copy** 是 Mathlib 中的一个定义，位于命名空间 `Delone.DeloneSet`。
形式化陈述：{X : Type u_1} →   [inst : MetricSpace X] →     (D : Delone.DeloneSet X) →
       (carrier : Set X) →         (packingRadius coveringRadius : NNReal) →    
       carrier = D.carrier → packingRadius = D.packingRadius → coveringRadius = 
D.coveringRadius → Delone.DeloneSet X
参数：D : Delone.DeloneSet X；carrier : Set X；packingRadius coveringRadius : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a Delone set with new fields equal to the old ones.
Useful to fix definitional equalities.
-/
protected def copy (D : DeloneSet X) (carrier : Set X) (packingRadius coveringRadius : ℝ≥0)
    (h_carrier : carrier = D.carrier) (h_packing : packingRadius = D.packingRadius)
    (h_covering : coveringRadius = D.coveringRadius) :
    DeloneSet X where
  carrier := carrier
  packingRadius := packingRadius
  packingRadius_pos := by simpa [h_packing] using D.packingRadius_pos
  isSeparated_packingRadius := by
    simpa [h_carrier, h_packing] using D.isSeparated_packingRadius
  coveringRadius := coveringRadius
  coveringRadius_pos := by simpa [h_covering] using D.coveringRadius_pos
  isCover_coveringRadius := by
    simpa [h_carrier, h_covering] using D.isCover_coveringRadius
/-
**Delone.DeloneSet.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `Delone.DeloneSet`。
形式化陈述：copy_eq (D : DeloneSet X) (carrier packingRadius coveringRadius h_carrier 
h_packing h_covering) : D.copy carrier packingRadius coveringRadius h_carrier h_
packing h_covering = D
参数：D : DeloneSet X；carrier packingRadius coveringRadius h_carrier h_packing h_co
vering。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Delone.DeloneSet.ext`：∀ {X : Type u_3} {inst : MetricSpace X} {x y : Del
one.DeloneSet X},   x.carrier = y.carrier → x.packingRadius = y.packingRadius → 
x.covering…
-/
theorem copy_eq (D : DeloneSet X)
    (carrier packingRadius coveringRadius h_carrier h_packing h_covering) :
    D.copy carrier packingRadius coveringRadius h_carrier h_packing h_covering = D :=
  DeloneSet.ext h_carrier h_packing h_covering
/-
**Delone.DeloneSet.packingRadius_lt_dist_of_mem_ne** 是 Mathlib 中的一个引理，位于命名空间 `De
lone.DeloneSet`。
形式化陈述：packingRadius_lt_dist_of_mem_ne (D : DeloneSet X) {x y : X} (hx : x in D) 
(hy : y in D) (hne : x != y) : D.packingRadius < dist x y
参数：D : DeloneSet X；hx : x in D；hy : y in D；hne : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `Delone.DeloneSet.isSeparated_packingRadius`：∀ {X : Type u_3} [inst : Met
ricSpace X] (self : Delone.DeloneSet X),   Metric.IsSeparated (↑self.packingRadi
us) self.carrier
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
-/
lemma packingRadius_lt_dist_of_mem_ne (D : DeloneSet X) {x y : X}
    (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) :
    D.packingRadius < dist x y := by
  have hsep : ENNReal.ofReal D.packingRadius < ENNReal.ofReal (dist x y) := by
    simpa [edist_dist] using D.isSeparated_packingRadius hx hy hne
  exact (ENNReal.ofReal_lt_ofReal_iff (h := dist_pos.mpr hne)).1 hsep
/-
**Delone.DeloneSet.exists_dist_le_coveringRadius** 是 Mathlib 中的一个引理，位于命名空间 `Delo
ne.DeloneSet`。
形式化陈述：exists_dist_le_coveringRadius (D : DeloneSet X) (x : X) : exists y in D, d
ist x y <= D.coveringRadius
参数：D : DeloneSet X；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Delone.DeloneSet.isCover_coveringRadius`：∀ {X : Type u_3} [inst : Metric
Space X] (self : Delone.DeloneSet X),   Metric.IsCover self.coveringRadius Set.u
niv self.carrier
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
-/
lemma exists_dist_le_coveringRadius (D : DeloneSet X) (x : X) :
    ∃ y ∈ D, dist x y ≤ D.coveringRadius := by
  obtain ⟨y, hy, hdist⟩ := D.isCover_coveringRadius (x := x) (by trivial)
  exact ⟨y, hy, by simpa [edist_dist] using hdist⟩
/-
**Delone.DeloneSet.eq_of_mem_ball** 是 Mathlib 中的一个引理，位于命名空间 `Delone.DeloneSet`。
形式化陈述：eq_of_mem_ball (D : DeloneSet X) {r : Real>=0} (hr : r <= D.packingRadius 
/ 2) {x y z : X} (hx : x in D) (hy : y in D) (hxz : x in ball z r) (hyz : y in b
all z r) : x = y
参数：D : DeloneSet X；hr : r <= D.packingRadius / 2；hx : x in D；hy : y in D；hxz : x
 in ball z r；hyz : y in ball z r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用引理 `Delone.DeloneSet.packingRadius_lt_dist_of_mem_ne`：packingRadius_lt_dist_
of_mem_ne (D : DeloneSet X) {x y : X} (hx : x in D) (hy : y in D) (hne : x != y)
 : D.packingRadius < dist x y
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `add_lt_add_of_lt_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < 
d → a + c < …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
-/
lemma eq_of_mem_ball (D : DeloneSet X) {r : ℝ≥0} (hr : r ≤ D.packingRadius / 2)
    {x y z : X} (hx : x ∈ D) (hy : y ∈ D) (hxz : x ∈ ball z r) (hyz : y ∈ ball z r) :
    x = y := by
  by_contra hne
  exact (D.packingRadius_lt_dist_of_mem_ne hx hy hne).not_gt <| calc
    dist x y ≤ dist x z + dist y z := dist_triangle_right x y z
    _ < r + r := by gcongr <;> simpa
    _ ≤ D.packingRadius := by rw [← add_halves D.packingRadius, NNReal.coe_add]; gcongr

/-- There exists a radius `r > 0` such that any ball of radius `r`
centered at a point of `D` contains at most one point of `D`. -/
/-
**Delone.DeloneSet.subset_ball_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Delone.Delon
eSet`。
形式化陈述：subset_ball_singleton (D : DeloneSet X) : exists r > 0, forall {x y z}, x 
in D -> y in D -> x in ball z r -> y in ball z r -> x = y
参数：D : DeloneSet X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Delone.DeloneSet.packingRadius_pos`：∀ {X : Type u_3} [inst : MetricSpace
 X] (self : Delone.DeloneSet X), 0 < self.packingRadius
· 使用引理 `Delone.DeloneSet.eq_of_mem_ball`：eq_of_mem_ball (D : DeloneSet X) {r : R
eal>=0} (hr : r <= D.packingRadius / 2) {x y z : X} (hx : x in D) (hy : y in D) 
(hxz : x in ball z r)…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
There exists a radius `r > 0` such that any ball of radius `r`
centered at a point of `D` contains at most one point of `D`.
-/
lemma subset_ball_singleton (D : DeloneSet X) :
    ∃ r > 0, ∀ {x y z}, x ∈ D → y ∈ D → x ∈ ball z r → y ∈ ball z r → x = y :=
  ⟨D.packingRadius / 2, half_pos D.packingRadius_pos, fun hx hy => D.eq_of_mem_ball le_rfl hx hy⟩

/-- Bilipschitz maps send Delone sets to Delone sets. -/
@[simps]
/-
**Delone.DeloneSet.mapBilipschitz** 是 Mathlib 中的一个定义，位于命名空间 `Delone.DeloneSet`。
形式化陈述：mapBilipschitz (f : X ≃ Y) (K₁ K₂ : Real>=0) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
 (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) (D : DeloneSet X) : D
eloneSet Y where carrier
参数：f : X ≃ Y；K₁ K₂ : Real>=0；hK₁ : 0 < K₁；hK₂ : 0 < K₂；hf₁ : AntilipschitzWith K
₁ f；hf₂ : LipschitzWith K₂ f；D : DeloneSet X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bilipschitz maps send Delone sets to Delone sets.
-/
noncomputable def mapBilipschitz (f : X ≃ Y) (K₁ K₂ : ℝ≥0) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) (D : DeloneSet X) : DeloneSet Y where
  carrier := f '' D.carrier
  packingRadius := D.packingRadius / K₁
  packingRadius_pos := div_pos D.packingRadius_pos hK₁
  isSeparated_packingRadius := D.isSeparated_packingRadius.image_antilipschitz hf₁ hK₁
  coveringRadius := K₂ * D.coveringRadius
  coveringRadius_pos := mul_pos hK₂ D.coveringRadius_pos
  isCover_coveringRadius := D.isCover_coveringRadius.image_lipschitz_of_surjective hf₂ f.surjective

set_option backward.isDefEq.respectTransparency false in
/-
**Delone.DeloneSet.mapBilipschitz_refl** 是 Mathlib 中的一个定理，位于命名空间 `Delone.DeloneS
et`。
形式化陈述：∀ {X : Type u_1} [inst : MetricSpace X] (D : Delone.DeloneSet X) (hK1 hK2 
: 0 < 1)   (hA : AntilipschitzWith 1 ⇑(Equiv.refl X)) (hL : LipschitzWith 1 ⇑(Eq
uiv.refl X)),   Delone.DeloneSet.mapBilipschitz (Equiv.refl X) 1 1 hK1 hK2 hA hL
 D = D
参数：D : Delone.DeloneSet X；hK1 hK2 : 0 < 1；hA : AntilipschitzWith 1 ⇑(Equiv.refl 
X)；hL : LipschitzWith 1 ⇑(Equiv.refl X)；Equiv.refl X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Delone.DeloneSet.ext`：∀ {X : Type u_3} {inst : MetricSpace X} {x y : Del
one.DeloneSet X},   x.carrier = y.carrier → x.packingRadius = y.packingRadius → 
x.covering…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Delone.DeloneSet.mk.congr_simp`：∀ {X : Type u_3} [inst : MetricSpace X] 
(carrier carrier_1 : Set X) (e_carrier : carrier = carrier_1)   (packingRadius p
ackingRadius_1 : NNR…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapBilipschitz_refl (D : DeloneSet X) (hK1 hK2 hA hL) :
    D.mapBilipschitz (.refl X) 1 1 hK1 hK2 hA hL = D := by
  ext <;> simp only [mapBilipschitz, Equiv.refl_apply, Set.image_id', div_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-
**Delone.DeloneSet.mapBilipschitz_trans** 是 Mathlib 中的一个引理，位于命名空间 `Delone.Delone
Set`。
形式化陈述：mapBilipschitz_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X 
≃ Y) (g : Y ≃ Z) (K₁f K₂f K₁g K₂g : Real>=0) (hf₁_pos : 0 < K₁f) (hf₂_pos : 0 < 
K₂f) (hg₁_pos : 0 < K₁g) (hg₂_pos : 0 < K₂g) (hf_anti : AntilipschitzWith K₁f f)
 (hf_lip : LipschitzWith K₂f f) (hg_anti : AntilipschitzWith K₁g g) (hg_lip : Li
pschitzWith K₂g g) : (D.mapBilipschitz f K₁f K₂f hf₁_pos hf₂_pos hf_anti hf_lip)
.mapBilipschitz g K₁g K₂g hg₁_pos hg₂_pos hg_anti hg_lip = D.mapBilipschitz (f.t
rans g) (K₁f * K₁g) (K₂g *
参数：D : DeloneSet X；f : X ≃ Y；g : Y ≃ Z；K₁f K₂f K₁g K₂g : Real>=0；hf₁_pos : 0 < K
₁f；hf₂_pos : 0 < K₂f；hg₁_pos : 0 < K₁g；hg₂_pos : 0 < K₂g；hf_anti : Antilipschitz
With K₁f f；hf_lip : LipschitzWith K₂f f；hg_anti : AntilipschitzWith K₁g g；hg_lip
 : LipschitzWith K₂g g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Delone.DeloneSet.ext`：∀ {X : Type u_3} {inst : MetricSpace X} {x y : Del
one.DeloneSet X},   x.carrier = y.carrier → x.packingRadius = y.packingRadius → 
x.covering…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `AntilipschitzWith.comp`：comp {Kg : Real>=0} {g : β -> γ} (hg : Antilipsc
hitzWith Kg g) {Kf : Real>=0} {f : α -> β} (hf : AntilipschitzWith Kf f) : Antil
ipschitzWith…
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Delone.DeloneSet.mapBilipschitz_carrier`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : MetricSpace X] [inst_1 : MetricSpace Y] (f : X ≃ Y) (K₁ K₂ : NNReal)   
(hK₁ : 0 < K₁) (hK₂ : 0 < K₂)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `exists_exists_and_eq_and`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β} {p
 : α → Prop} {q : β → Prop},   (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q 
(f a)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Delone.DeloneSet.mapBilipschitz_packingRadius`：∀ {X : Type u_1} {Y : Typ
e u_2} [inst : MetricSpace X] [inst_1 : MetricSpace Y] (f : X ≃ Y) (K₁ K₂ : NNRe
al)   (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)…
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Delone.DeloneSet.mapBilipschitz_coveringRadius`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : MetricSpace X] [inst_1 : MetricSpace Y] (f : X ≃ Y) (K₁ K₂ : NNR
eal)   (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mapBilipschitz_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X)
    (f : X ≃ Y) (g : Y ≃ Z) (K₁f K₂f K₁g K₂g : ℝ≥0)
    (hf₁_pos : 0 < K₁f) (hf₂_pos : 0 < K₂f)
    (hg₁_pos : 0 < K₁g) (hg₂_pos : 0 < K₂g)
    (hf_anti : AntilipschitzWith K₁f f) (hf_lip : LipschitzWith K₂f f)
    (hg_anti : AntilipschitzWith K₁g g) (hg_lip : LipschitzWith K₂g g) :
    (D.mapBilipschitz f K₁f K₂f hf₁_pos hf₂_pos hf_anti hf_lip).mapBilipschitz
      g K₁g K₂g hg₁_pos hg₂_pos hg_anti hg_lip =
    D.mapBilipschitz (f.trans g) (K₁f * K₁g) (K₂g * K₂f)
      (mul_pos hf₁_pos hg₁_pos) (mul_pos hg₂_pos hf₂_pos)
      (hg_anti.comp hf_anti) (hg_lip.comp hf_lip) := by
  ext
  · simp only [mapBilipschitz_carrier, Equiv.trans_apply, Set.mem_image]
    exact exists_exists_and_eq_and
  · simp only [mapBilipschitz_packingRadius, NNReal.coe_div, div_div]
  · simp only [mapBilipschitz_coveringRadius, NNReal.coe_mul, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The image of a Delone set under an isometry. This is a specialization of
`DeloneSet.mapBilipschitz` where the packing and covering radii are preserved because the
Lipschitz constants are both 1. -/
@[simps!]
/-
**Delone.DeloneSet.mapIsometry** 是 Mathlib 中的一个定义，位于命名空间 `Delone.DeloneSet`。
形式化陈述：mapIsometry (f : X ≃ᵢ Y) : DeloneSet X ≃ DeloneSet Y where toFun D
参数：f : X ≃ᵢ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a Delone set under an isometry. This is a specialization of
`DeloneSet.mapBilipschitz` where the packing and covering radii are preserved be
cause the
Lipschitz constants are both 1.
-/
noncomputable def mapIsometry (f : X ≃ᵢ Y) : DeloneSet X ≃ DeloneSet Y where
  toFun D := (D.mapBilipschitz f.toEquiv 1 1 zero_lt_one zero_lt_one
      f.isometry.antilipschitz f.isometry.lipschitz).copy (f '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  invFun D := (D.mapBilipschitz f.symm.toEquiv 1 1 zero_lt_one zero_lt_one
      f.symm.isometry.antilipschitz f.symm.isometry.lipschitz).copy (f.symm '' D.carrier)
      D.packingRadius D.coveringRadius rfl (by simp [mapBilipschitz]) (by simp [mapBilipschitz])
  left_inv D := by ext <;> simp [copy_eq]
  right_inv D := by ext <;> simp [copy_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**Delone.DeloneSet.mapIsometry_refl** 是 Mathlib 中的一个定理，位于命名空间 `Delone.DeloneSet`
。
形式化陈述：∀ {X : Type u_1} [inst : MetricSpace X] (D : Delone.DeloneSet X),   (Delon
e.DeloneSet.mapIsometry (IsometryEquiv.refl X)) D = D
参数：D : Delone.DeloneSet X；Delone.DeloneSet.mapIsometry (IsometryEquiv.refl X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Delone.DeloneSet.ext`：∀ {X : Type u_3} {inst : MetricSpace X} {x y : Del
one.DeloneSet X},   x.carrier = y.carrier → x.packingRadius = y.packingRadius → 
x.covering…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `isometry_id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Isometry id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Delone.DeloneSet.mk.congr_simp`：∀ {X : Type u_3} [inst : MetricSpace X] 
(carrier carrier_1 : Set X) (e_carrier : carrier = carrier_1)   (packingRadius p
ackingRadius_1 : NNR…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mapIsometry_refl (D : DeloneSet X) : D.mapIsometry (.refl X) = D := by
  ext <;> simp [mapIsometry, IsometryEquiv.refl, DeloneSet.copy]
/-
**Delone.DeloneSet.mapIsometry_symm** 是 Mathlib 中的一个引理，位于命名空间 `Delone.DeloneSet`
。
形式化陈述：mapIsometry_symm (f : X ≃ᵢ Y) : (mapIsometry f).symm = mapIsometry f.symm
参数：f : X ≃ᵢ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma mapIsometry_symm (f : X ≃ᵢ Y) : (mapIsometry f).symm = mapIsometry f.symm := rfl
/-
**Delone.DeloneSet.mapIsometry_trans** 是 Mathlib 中的一个引理，位于命名空间 `Delone.DeloneSet
`。
形式化陈述：mapIsometry_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X ≃ᵢ 
Y) (g : Y ≃ᵢ Z) : D.mapIsometry (f.trans g) = (D.mapIsometry f).mapIsometry g
参数：D : DeloneSet X；f : X ≃ᵢ Y；g : Y ≃ᵢ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Delone.DeloneSet.ext`：∀ {X : Type u_3} {inst : MetricSpace X} {x y : Del
one.DeloneSet X},   x.carrier = y.carrier → x.packingRadius = y.packingRadius → 
x.covering…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapIsometry_trans {Z : Type*} [MetricSpace Z] (D : DeloneSet X) (f : X ≃ᵢ Y) (g : Y ≃ᵢ Z) :
    D.mapIsometry (f.trans g) = (D.mapIsometry f).mapIsometry g := by
  ext <;> simp [mapIsometry, DeloneSet.copy]

end DeloneSet

end Delone

