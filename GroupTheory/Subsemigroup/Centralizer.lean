/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.GroupTheory.Subsemigroup.Center

/-!
# Centralizers in semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

variable {M : Type*} {S T : Set M}
namespace Subsemigroup

section

variable [Semigroup M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive /-- The centralizer of a subset of an additive semigroup. -/]
/-
**Subsemigroup.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：centralizer : Subsemigroup M where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Set.mul_mem_centralizer`：mul_mem_centralizer (ha : a in centralizer S) (
hb : b in centralizer S) : a * b in centralizer S

--- 原说明 ---
The centralizer of a subset of a semigroup `M`.
-/
def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' := Set.mul_mem_centralizer

@[to_additive (attr := simp, norm_cast)]
/-
**Subsemigroup.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：coe_centralizer : ↑(centralizer S) = S.centralizer
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl

variable {S}

@[to_additive]
/-
**Subsemigroup.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_centralizer_iff {z : M} : z in centralizer S ↔ forall g in S, g * z = 
z * g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl

@[to_additive]
/-
**Subsemigroup.decidableMemCentralizer** 是 Mathlib 中的一个实例，位于命名空间 `Subsemigroup`。
形式化陈述：decidableMemCentralizer (a) [Decidable <| forall b in S, b * a = a * b] : 
Decidable (a in centralizer S)
参数：a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.mem_centralizer_iff`：mem_centralizer_iff {z : M} : z in cen
tralizer S ↔ forall g in S, g * z = z * g
-/
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
/-
**Subsemigroup.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：center_le_centralizer (S) : center M <= centralizer S
参数：S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer (S) : center M ≤ centralizer S :=
  S.center_subset_centralizer

@[to_additive]
/-
**Subsemigroup.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：centralizer_le (h : S subseteq T) : centralizer T <= centralizer S
参数：h : S subseteq T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.centralizer_subset`：centralizer_subset (h : S subseteq T) : centrali
zer T subseteq centralizer S
-/
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h

@[to_additive (attr := simp)]
/-
**Subsemigroup.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subsemig
roup`。
形式化陈述：centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s subseteq
 center M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s ⊆ center M :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

variable (M)
@[to_additive (attr := simp)]
/-
**Subsemigroup.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`。
形式化陈述：centralizer_univ : centralizer Set.univ = center M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)

variable {M} in
@[to_additive]
/-
**Subsemigroup.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Sub
semigroup`。
形式化陈述：closure_le_centralizer_centralizer (s : Set M) : closure s <= centralizer 
(centralizer s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemigroup.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set M) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is commutative. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` is commutative. -/]
/-
**Subsemigroup.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subsemigroup`
。
形式化陈述：isMulCommutative_closure {s : Set M} (hcomm : forall a in s, forall b in s
, a * b = b * a) : IsMulCommutative (closure s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subsemigroup.closure_le_centralizer_centralizer`：closure_le_centralizer_
centralizer (s : Set M) : closure s <= centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `Subsemigroup.instMulMemClass`：∀ {M : Type u_1} [inst : Mul M], MulMemCla
ss (Subsemigroup M) M
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …
-/
theorem isMulCommutative_closure {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative in
/-- If all the elements of a set `s` commute, then `closure s` is a commutative semigroup. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-09"))
/-- If all the elements of a set `s` commute, then `closure s` forms an additive
commutative semigroup. -/]
/-
**Subsemigroup.closureCommSemigroupOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Subsemigr
oup`。
形式化陈述：closureCommSemigroupOfComm {s : Set M} (hcomm : forall a in s, forall b in
 s, a * b = b * a) : CommSemigroup (closure s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.isMulCommutative_closure`：isMulCommutative_closure {s : Set
 M} (hcomm : forall a in s, forall b in s, a * b = b * a) : IsMulCommutative (cl
osure s)
-/
abbrev closureCommSemigroupOfComm {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemigroup (closure s) :=
  haveI := isMulCommutative_closure M hcomm
  inferInstance

@[to_additive]
/-
**Subsemigroup.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `Subsemigr
oup`。
形式化陈述：instIsMulCommutative_closure {S : Type*} [SetLike S M] [MulMemClass S M] (
s : S) [IsMulCommutative s] : IsMulCommutative (closure (s : Set M))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsemigroup.isMulCommutative_closure`：isMulCommutative_closure {s : Set
 M} (hcomm : forall a in s, forall b in s, a * b = b * a) : IsMulCommutative (cl
osure s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S M] [MulMemClass S M] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set M)) :=
  isMulCommutative_closure _ fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

end

end Subsemigroup

