/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Pointwise
public import Mathlib.Topology.Algebra.Order.UpperLower
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Upper/lower/order-connected sets in normed groups

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.

## TODO

Is there a way to generalise `IsClosed.upperClosure_pi`/`IsClosed.lowerClosure_pi` so that they also
apply to `ℝ`, `ℝ × ℝ`, `EuclideanSpace ι ℝ`? `_pi` has been appended to their names to disambiguate
from the other possible lemmas, but we will want there to be a single set of lemmas for all
situations.
-/

public section

open Bornology Function Metric Set
open scoped Pointwise

variable {α ι : Type*}

section NormedOrderedGroup
variable [NormedCommGroup α] [Preorder α] [IsOrderedMonoid α] {s : Set α}

@[to_additive IsUpperSet.thickening]
/-
**IsUpperSet.thickening'** 是 Mathlib 中的一个定理，位于命名空间 `IsUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] {s : Set α},   IsUpperSet s → ∀ (ε : ℝ), IsUpperSet (Metric.thickeni
ng ε s)
参数：ε : ℝ；Metric.thickening ε s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_mul_one`：ball_mul_one : ball 1 δ * s = thickening δ s
· 使用定理 `IsUpperSet.mul_left`：IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSe
t (s * t)
-/
protected theorem IsUpperSet.thickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsLowerSet.thickening]
/-
**IsLowerSet.thickening'** 是 Mathlib 中的一个定理，位于命名空间 `IsLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] {s : Set α},   IsLowerSet s → ∀ (ε : ℝ), IsLowerSet (Metric.thickeni
ng ε s)
参数：ε : ℝ；Metric.thickening ε s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_mul_one`：ball_mul_one : ball 1 δ * s = thickening δ s
· 使用定理 `IsLowerSet.mul_left`：IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSe
t (s * t)
-/
protected theorem IsLowerSet.thickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left

@[to_additive IsUpperSet.cthickening]
/-
**IsUpperSet.cthickening'** 是 Mathlib 中的一个定理，位于命名空间 `IsUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] {s : Set α},   IsUpperSet s → ∀ (ε : ℝ), IsUpperSet (Metric.cthicken
ing ε s)
参数：ε : ℝ；Metric.cthickening ε s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_eq_iInter_thickening''`：cthickening_eq_iInter_thicken
ing'' (δ : Real) (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : max 0 δ < ε),
 thickening ε E
· 使用定理 `isUpperSet_iInter₂`：isUpperSet_iInter₂ {f : forall i, κ i -> Set α} (hf 
: forall i j, IsUpperSet (f i j)) : IsUpperSet (⋂ (i) (j), f i j)
· 使用定理 `IsUpperSet.thickening'`：∀ {α : Type u_1} [inst : NormedCommGroup α] [ins
t_1 : Preorder α] [IsOrderedMonoid α] {s : Set α},   IsUpperSet s → ∀ (ε : ℝ), I
sUpperSet (M…
-/
protected theorem IsUpperSet.cthickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isUpperSet_iInter₂ fun δ _ => hs.thickening' _

@[to_additive IsLowerSet.cthickening]
/-
**IsLowerSet.cthickening'** 是 Mathlib 中的一个定理，位于命名空间 `IsLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] {s : Set α},   IsLowerSet s → ∀ (ε : ℝ), IsLowerSet (Metric.cthicken
ing ε s)
参数：ε : ℝ；Metric.cthickening ε s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_eq_iInter_thickening''`：cthickening_eq_iInter_thicken
ing'' (δ : Real) (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : max 0 δ < ε),
 thickening ε E
· 使用定理 `isLowerSet_iInter₂`：∀ {α : Type u_1} {ι : Sort u_3} {κ : ι → Sort u_4} [
inst : LE α] {f : (i : ι) → κ i → Set α},   (∀ (i : ι) (j : κ i), IsLowerSet (f 
i j)) → …
· 使用定理 `IsLowerSet.thickening'`：∀ {α : Type u_1} [inst : NormedCommGroup α] [ins
t_1 : Preorder α] [IsOrderedMonoid α] {s : Set α},   IsLowerSet s → ∀ (ε : ℝ), I
sLowerSet (M…
-/
protected theorem IsLowerSet.cthickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (cthickening ε s) := by
  rw [cthickening_eq_iInter_thickening'']
  exact isLowerSet_iInter₂ fun δ _ => hs.thickening' _
/-
**upperClosure_interior_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] (s : Set α),   ↑(upperClosure (interior s)) ⊆ interior ↑(upperClosur
e s)
参数：s : Set α；upperClosure (interior s)；upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperClosure_min`：upperClosure_min (h : s subseteq t) (ht : IsUpperSet t
) : ↑(upperClosure s) subseteq t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `IsUpperSet.interior`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSe
t (interi…
· 使用定理 `IsOrderedMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Topolo
gicalSpace α] [inst_1 : CommGroup α] [inst_2 : Preorder α] [IsOrderedMonoid α]  
 [ContinuousConstSMul α α], H…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `SeminormedCommGroup.toIsTopologicalGroup`：∀ {E : Type u_2} [inst : Semin
ormedCommGroup E], IsTopologicalGroup E
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
-/
@[to_additive upperClosure_interior_subset] lemma upperClosure_interior_subset' (s : Set α) :
    (upperClosure (interior s) : Set α) ⊆ interior (upperClosure s) :=
  upperClosure_min (interior_mono subset_upperClosure) (upperClosure s).upper.interior
/-
**lowerClosure_interior_subset'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : NormedCommGroup α] [inst_1 : Preorder α] [IsOrder
edMonoid α] (s : Set α),   ↑(lowerClosure (interior s)) ⊆ interior ↑(lowerClosur
e s)
参数：s : Set α；lowerClosure (interior s)；lowerClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerClosure_min`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, s 
⊆ t → IsLowerSet t → ↑(lowerClosure s) ⊆ t
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用定理 `IsLowerSet.interior`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSe
t (interi…
· 使用定理 `IsOrderedMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Topolo
gicalSpace α] [inst_1 : CommGroup α] [inst_2 : Preorder α] [IsOrderedMonoid α]  
 [ContinuousConstSMul α α], H…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `SeminormedCommGroup.toIsTopologicalGroup`：∀ {E : Type u_2} [inst : Semin
ormedCommGroup E], IsTopologicalGroup E
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
@[to_additive lowerClosure_interior_subset] lemma lowerClosure_interior_subset' (s : Set α) :
    (lowerClosure (interior s) : Set α) ⊆ interior (lowerClosure s) :=
  lowerClosure_min (interior_mono subset_lowerClosure) (lowerClosure s).lower.interior

end NormedOrderedGroup

/-! ### `ℝⁿ` -/


section Finite
variable [Finite ι] {s : Set (ι → ℝ)} {x y : ι → ℝ}

/-
**IsUpperSet.mem_interior_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x in closur
e s) (h : forall i, x i < y i) : y in interior s
参数：hs : IsUpperSet s；hx : x in closure s；h : forall i, x i < y i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Pi.exists_forall_pos_add_lt`：Pi.exists_forall_pos_add_lt [ExistsAddOfLE 
α] [Finite ι] {x y : ι -> α} (h : forall i, x i < y i) : exists ε, 0 < ε ∧ foral
l i, x i + ε < y …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `dist_pi_lt_iff`：dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 
< r) : dist f g < r ↔ forall b, dist (f b) (g b) < r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior`：mem_interior : x in interior s ↔ exists t subseteq s, IsOp
en t ∧ x in t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
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
（共 38 条，此处仅展示前 30 条）
-/
theorem IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x ∈ closure s)
    (h : ∀ i, x i < y i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, z i < y i := by
    refine fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm']
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((lt_sub_iff_add_lt.2 <| hyz _).trans (hw _ <| mem_univ _).1).le
/-
**IsLowerSet.mem_interior_of_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x in closur
e s) (h : forall i, y i < x i) : y in interior s
参数：hs : IsLowerSet s；hx : x in closure s；h : forall i, y i < x i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Pi.exists_forall_pos_add_lt`：Pi.exists_forall_pos_add_lt [ExistsAddOfLE 
α] [Finite ι] {x y : ι -> α} (h : forall i, x i < y i) : exists ε, 0 < ε ∧ foral
l i, x i + ε < y …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_le_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a - b ≤ c ↔ a - c ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `dist_pi_lt_iff`：dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 
< r) : dist f g < r ↔ forall b, dist (f b) (g b) < r
· 使用定理 `mem_interior`：mem_interior : x in interior s ↔ exists t subseteq s, IsOp
en t ∧ x in t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
（共 38 条，此处仅展示前 30 条）
-/
theorem IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x ∈ closure s)
    (h : ∀ i, y i < x i) : y ∈ interior s := by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, y i < z i := by
    refine fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (le_abs_self _).trans ?_)
    rw [← Real.norm_eq_abs, ← dist_eq_norm]
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine mem_interior.2 ⟨ball y δ, ?_, isOpen_ball, mem_ball_self hδ⟩
  rintro w hw
  refine hs (fun i => ?_) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((hw _ <| mem_univ _).2.trans <| hyz _).le

end Finite

section Fintype
variable [Fintype ι] {s : Set (ι → ℝ)} {a₁ a₂ b₁ b₂ x y : ι → ℝ} {δ : ℝ}

-- TODO: Generalise those lemmas so that they also apply to `ℝ` and `EuclideanSpace ι ℝ`
/-
**dist_inf_sup_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_inf_sup_pi (x y : ι -> Real) : dist (x ⊓ y) (x ⊔ y) = dist x y
参数：x y : ι -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.sup_congr`：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall 
a in s₂, f a = g a) : s₁.sup f = s₂.sup g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nndist_eq'`：Real.nndist_eq' (x y : Real) : nndist x y = Real.nnabs 
(y - x)
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `Real.toNNReal_abs`：∀ (x : ℝ), |x|.toNNReal = Real.nnabs x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dist_inf_sup_pi (x y : ι → ℝ) : dist (x ⊓ y) (x ⊔ y) = dist x y := by
  refine congr_arg NNReal.toReal (Finset.sup_congr rfl fun i _ ↦ ?_)
  simp only [Real.nndist_eq', max_sub_min_eq_abs, Pi.inf_apply,
    Pi.sup_apply, Real.nnabs_of_nonneg, abs_nonneg, Real.toNNReal_abs]
/-
**dist_mono_left_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_mono_left_pi : MonotoneOn (dist · y) (Ici y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nndist_eq`：Real.nndist_eq (x y : Real) : nndist x y = Real.nnabs (x
 - y)
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma dist_mono_left_pi : MonotoneOn (dist · y) (Ici y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy ↦ NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ ↦ ?_)
  rw [Real.nndist_eq, Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₁ i)),
    Real.nndist_eq, Real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₂ i))]
  grw [hy i] -- TODO(gcongr): we would like `grw [hy]` to work here
/-
**dist_mono_right_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_mono_right_pi : MonotoneOn (dist x) (Ici x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `dist_mono_left_pi`：dist_mono_left_pi : MonotoneOn (dist · y) (Ici y)
-/
lemma dist_mono_right_pi : MonotoneOn (dist x) (Ici x) := by
  simpa only [dist_comm] using dist_mono_left_pi (y := x)
/-
**dist_anti_left_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_anti_left_pi : AntitoneOn (dist · y) (Iic y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nndist_eq'`：Real.nndist_eq' (x y : Real) : nndist x y = Real.nnabs 
(y - x)
· 使用定理 `Real.nnabs_of_nonneg`：nnabs_of_nonneg {x : Real} (h : 0 <= x) : nnabs x 
= toNNReal x
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
-/
lemma dist_anti_left_pi : AntitoneOn (dist · y) (Iic y) := by
  refine fun y₁ hy₁ y₂ hy₂ hy ↦ NNReal.coe_le_coe.2 (Finset.sup_mono_fun fun i _ ↦ ?_)
  rw [Real.nndist_eq', Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₂ i ≤ y i)),
    Real.nndist_eq', Real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₁ i ≤ y i))]
  exact Real.toNNReal_mono (sub_le_sub_left (hy _) _)
/-
**dist_anti_right_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_anti_right_pi : AntitoneOn (dist x) (Iic x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用引理 `dist_anti_left_pi`：dist_anti_left_pi : AntitoneOn (dist · y) (Iic y)
-/
lemma dist_anti_right_pi : AntitoneOn (dist x) (Iic x) := by
  simpa only [dist_comm] using dist_anti_left_pi (y := x)
/-
**dist_le_dist_of_le_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_le_dist_of_le_pi (ha : a₂ <= a₁) (h₁ : a₁ <= b₁) (hb : b₁ <= b₂) : di
st a₁ b₁ <= dist a₂ b₂
参数：ha : a₂ <= a₁；h₁ : a₁ <= b₁；hb : b₁ <= b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `dist_mono_right_pi`：dist_mono_right_pi : MonotoneOn (dist x) (Ici x)
· 使用引理 `dist_anti_left_pi`：dist_anti_left_pi : AntitoneOn (dist · y) (Iic y)
-/
lemma dist_le_dist_of_le_pi (ha : a₂ ≤ a₁) (h₁ : a₁ ≤ b₁) (hb : b₁ ≤ b₂) :
    dist a₁ b₁ ≤ dist a₂ b₂ :=
  (dist_mono_right_pi h₁ (h₁.trans hb) hb).trans <|
    dist_anti_left_pi (ha.trans <| h₁.trans hb) (h₁.trans hb) ha
/-
**IsUpperSet.exists_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x in closure s) (h
δ : 0 < δ) : exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall
 y (δ / 4) subseteq interior s
参数：hs : IsUpperSet s；hx : x in closure s；hδ : 0 < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.closedBall_subset_closedBall'`：closedBall_subset_closedBall' (h :
 ε₁ + dist x y <= ε₂) : closedBall x ε₁ subseteq closedBall y ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.const_def`：const_def {y : β} : (fun _ : α => y) = const α y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pi_norm_const_le`：∀ {ι : Type u_1} {E : Type u_2} [inst : Fintype ι] [in
st_1 : SeminormedAddGroup E] (a : E), ‖fun x => a‖ ≤ ‖a‖
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 108 条，此处仅展示前 30 条）
-/
theorem IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x + const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_add_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith
/-
**IsLowerSet.exists_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x in closure s) (h
δ : 0 < δ) : exists y, closedBall y (δ / 4) subseteq closedBall x δ ∧ closedBall
 y (δ / 4) subseteq interior s
参数：hs : IsLowerSet s；hx : x in closure s；hδ : 0 < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.closedBall_subset_closedBall'`：closedBall_subset_closedBall' (h :
 ε₁ + dist x y <= ε₂) : closedBall x ε₁ subseteq closedBall y ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self_sub_left`：∀ {E : Type u_2} [inst : SeminormedAddCommGroup E] (
a b : E), dist (a - b) a = ‖b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.const_def`：const_def {y : β} : (fun _ : α => y) = const α y
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pi_norm_const_le`：∀ {ι : Type u_1} {E : Type u_2} [inst : Fintype ι] [in
st_1 : SeminormedAddGroup E] (a : E), ‖fun x => a‖ ≤ ‖a‖
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 107 条，此处仅展示前 30 条）
-/
theorem IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s := by
  refine ⟨x - const _ (3 / 4 * δ), closedBall_subset_closedBall' ?_, ?_⟩
  · grw [dist_self_sub_left, ← const_def, pi_norm_const_le]
    apply le_of_eq
    simp [abs_of_nonneg, hδ.le]
    ring
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => ?_
  rw [mem_closedBall, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith

end Fintype

section Finite
variable [Finite ι] {s : Set (ι → ℝ)}

/-!
#### Note

The closure and frontier of an antichain might not be antichains. Take for example the union
of the open segments from `(0, 2)` to `(1, 1)` and from `(2, 1)` to `(3, 0)`. `(1, 1)` and `(2, 1)`
are comparable and both in the closure/frontier.
-/

/-
**IsClosed.upperClosure_pi** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)}, IsClosed s → BddBelow s → I
sClosed ↑(upperClosure s)
参数：ι → ℝ；upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.instFirstCountableTopologyForallOfCountable`：∀ {ι : Typ
e u_1} {X : ι → Type u_2} [Countable ι] [inst : (i : ι) → TopologicalSpace (X i)
]   [∀ (i : ι), FirstCountableTopology (X i)], Fir…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.Tendsto.bddAbove_range`：Filter.Tendsto.bddAbove_range [IsDirected
Order α] {u : Nat -> α} (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u)
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `tendsto_subseq_of_bounded`：tendsto_subseq_of_bounded (hs : IsBounded s) 
{x : Nat -> X} (hx : forall n, x n in s) : exists a in closure s, exists φ : Nat
 -> Nat, Strict…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用引理 `BddBelow.isBounded_inter`：BddBelow.isBounded_inter (hs : BddBelow s) (ht
 : BddAbove t) : IsBounded (s inter t)
· 使用定理 `bddAbove_Iic`：bddAbove_Iic : BddAbove (Iic a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
#### Note

The closure and frontier of an antichain might not be antichains. Take for examp
le the union
of the open segments from `(0, 2)` to `(1, 1)` and from `(2, 1)` to `(3, 0)`. `(
1, 1)` and `(2, 1)`
are comparable and both in the closure/frontier.
-/
protected lemma IsClosed.upperClosure_pi (hs : IsClosed s) (hs' : BddBelow s) :
    IsClosed (upperClosure s : Set (ι → ℝ)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx ↦ ?_
  choose g hg hgf using hf
  obtain ⟨a, ha⟩ := hx.bddAbove_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddAbove_Iic) fun n ↦
    ⟨hg n, (hgf _).trans <| ha <| mem_range_self _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' hbf (hx.comp hφ.tendsto_atTop) fun _ ↦ hgf _⟩
/-
**IsClosed.lowerClosure_pi** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)}, IsClosed s → BddAbove s → I
sClosed ↑(lowerClosure s)
参数：ι → ℝ；lowerClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.instFirstCountableTopologyForallOfCountable`：∀ {ι : Typ
e u_1} {X : ι → Type u_2} [Countable ι] [inst : (i : ι) → TopologicalSpace (X i)
]   [∀ (i : ι), FirstCountableTopology (X i)], Fir…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BoundedGENhdsClass.of_closedIicTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIicTopology α], BoundedGENhdsClass
 α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.bddBelow_range`：Filter.Tendsto.bddBelow_range [IsCodirect
edOrder α] {u : Nat -> α} (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.range u)
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `tendsto_subseq_of_bounded`：tendsto_subseq_of_bounded (hs : IsBounded s) 
{x : Nat -> X} (hx : forall n, x n in s) : exists a in closure s, exists φ : Nat
 -> Nat, Strict…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用引理 `BddAbove.isBounded_inter`：BddAbove.isBounded_inter (hs : BddAbove s) (ht
 : BddBelow t) : IsBounded (s inter t)
· 使用定理 `bddBelow_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, BddBelow (Se
t.Ici a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
（共 32 条，此处仅展示前 30 条）
-/
protected lemma IsClosed.lowerClosure_pi (hs : IsClosed s) (hs' : BddAbove s) :
    IsClosed (lowerClosure s : Set (ι → ℝ)) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx ↦ ?_
  choose g hg hfg using hf
  have : BoundedGENhdsClass ℝ := by infer_instance
  obtain ⟨a, ha⟩ := hx.bddBelow_range
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.isBounded_inter bddBelow_Ici) fun n ↦
    ⟨hg n, (ha <| mem_range_self _).trans <| hfg _⟩
  exact ⟨b, closure_minimal inter_subset_left hs hb,
    le_of_tendsto_of_tendsto' (hx.comp hφ.tendsto_atTop) hbf fun _ ↦ hfg _⟩
/-
**IsClopen.upperClosure_pi** 是 Mathlib 中的一个定理，位于命名空间 `IsClopen`。
形式化陈述：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)}, IsClopen s → BddBelow s → I
sClopen ↑(upperClosure s)
参数：ι → ℝ；upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.upperClosure_pi`：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)},
 IsClosed s → BddBelow s → IsClosed ↑(upperClosure s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.upperClosure`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsOpen s → IsOpen ↑(uppe
rClosure …
· 使用定理 `IsOrderedAddMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : Preorder α] [IsOrderedAddMo
noid α]   [ContinuousConstVAdd α…
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `Pi.separatelyContinuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : 
(i : ι) → TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), S
eparatelyContinu…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsClopen.upperClosure_pi (hs : IsClopen s) (hs' : BddBelow s) :
    IsClopen (upperClosure s : Set (ι → ℝ)) := ⟨hs.1.upperClosure_pi hs', hs.2.upperClosure⟩
/-
**IsClopen.lowerClosure_pi** 是 Mathlib 中的一个定理，位于命名空间 `IsClopen`。
形式化陈述：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)}, IsClopen s → BddAbove s → I
sClopen ↑(lowerClosure s)
参数：ι → ℝ；lowerClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.lowerClosure_pi`：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)},
 IsClosed s → BddAbove s → IsClosed ↑(lowerClosure s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.lowerClosure`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsOpen s → IsOpen ↑(lowe
rClosure …
· 使用定理 `IsOrderedAddMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : Preorder α] [IsOrderedAddMo
noid α]   [ContinuousConstVAdd α…
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `Pi.separatelyContinuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : 
(i : ι) → TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), S
eparatelyContinu…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsClopen.lowerClosure_pi (hs : IsClopen s) (hs' : BddAbove s) :
    IsClopen (lowerClosure s : Set (ι → ℝ)) := ⟨hs.1.lowerClosure_pi hs', hs.2.lowerClosure⟩
/-
**closure_upperClosure_comm_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_upperClosure_comm_pi (hs : BddBelow s) : closure (upperClosure s :
 Set (ι -> Real)) = upperClosure (closure s)
参数：hs : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `upperClosure_anti`：upperClosure_anti : Antitone (upperClosure : Set α ->
 UpperSet α)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsClosed.upperClosure_pi`：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)},
 IsClosed s → BddBelow s → IsClosed ↑(upperClosure s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `BddBelow.closure`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : P
reorder α] [ClosedIciTopology α] {s : Set α},   BddBelow s → BddBelow (closure s
)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `upperClosure_min`：upperClosure_min (h : s subseteq t) (ht : IsUpperSet t
) : ↑(upperClosure s) subseteq t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `IsUpperSet.closure`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsUpperSet s → IsUpperSet
 (closur…
· 使用定理 `IsOrderedAddMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : Preorder α] [IsOrderedAddMo
noid α]   [ContinuousConstVAdd α…
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `Pi.separatelyContinuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : 
(i : ι) → TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), S
eparatelyContinu…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
-/
lemma closure_upperClosure_comm_pi (hs : BddBelow s) :
    closure (upperClosure s : Set (ι → ℝ)) = upperClosure (closure s) :=
  (closure_minimal (upperClosure_anti subset_closure) <|
      isClosed_closure.upperClosure_pi hs.closure).antisymm <|
    upperClosure_min (closure_mono subset_upperClosure) (upperClosure s).upper.closure
/-
**closure_lowerClosure_comm_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：closure_lowerClosure_comm_pi (hs : BddAbove s) : closure (lowerClosure s :
 Set (ι -> Real)) = lowerClosure (closure s)
参数：hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `lowerClosure_mono`：lowerClosure_mono : Monotone (lowerClosure : Set α ->
 LowerSet α)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsClosed.lowerClosure_pi`：∀ {ι : Type u_2} [Finite ι] {s : Set (ι → ℝ)},
 IsClosed s → BddAbove s → IsClosed ↑(lowerClosure s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `BddAbove.closure`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : P
reorder α] [ClosedIicTopology α] {s : Set α},   BddAbove s → BddAbove (closure s
)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `lowerClosure_min`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, s 
⊆ t → IsLowerSet t → ↑(lowerClosure s) ⊆ t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用定理 `IsLowerSet.closure`：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1
 : Preorder α] [HasUpperLowerClosure α] {s : Set α},   IsLowerSet s → IsLowerSet
 (closur…
· 使用定理 `IsOrderedAddMonoid.to_hasUpperLowerClosure`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [inst_1 : AddCommGroup α] [inst_2 : Preorder α] [IsOrderedAddMo
noid α]   [ContinuousConstVAdd α…
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `SeparatelyContinuousAdd.to_continuousVAdd`：∀ {M : Type u_3} [inst : Topo
logicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M], ContinuousConstVAd
d M M
· 使用定理 `Pi.separatelyContinuousAdd`：∀ {ι : Type u_1} {C : ι → Type u_6} [inst : 
(i : ι) → TopologicalSpace (C i)] [inst_1 : (i : ι) → Add (C i)]   [∀ (i : ι), S
eparatelyContinu…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
lemma closure_lowerClosure_comm_pi (hs : BddAbove s) :
    closure (lowerClosure s : Set (ι → ℝ)) = lowerClosure (closure s) :=
  (closure_minimal (lowerClosure_mono subset_closure) <|
        isClosed_closure.lowerClosure_pi hs.closure).antisymm <|
    lowerClosure_min (closure_mono subset_lowerClosure) (lowerClosure s).lower.closure

end Finite

