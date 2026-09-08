/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Subsemigroup.Centralizer
public import Mathlib.GroupTheory.Submonoid.Center

/-!
# Centralizers of magmas and monoids

## Main definitions

* `Submonoid.centralizer`: the centralizer of a subset of a monoid
* `AddSubmonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `Subgroup.centralizer`, `AddSubgroup.centralizer` in other files.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

variable {M : Type*} {S T : Set M}

namespace Submonoid

section

variable [Monoid M] (S)

/-- The centralizer of a subset of a monoid `M`. -/
@[to_additive /-- The centralizer of a subset of an additive monoid. -/]
/-
**Submonoid.centralizer** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：centralizer : Submonoid M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The centralizer of a subset of a monoid `M`.
-/
def centralizer : Submonoid M where
  carrier := S.centralizer
  one_mem' := S.one_mem_centralizer
  mul_mem' := Set.mul_mem_centralizer

@[to_additive (attr := simp, norm_cast)]
/-
**Submonoid.coe_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_centralizer : ↑(centralizer S) = S.centralizer
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl

@[to_additive AddSubmonoid.centralizer_toAddSubsemigroup]
/-
**Submonoid.centralizer_toSubsemigroup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：centralizer_toSubsemigroup : (centralizer S).toSubsemigroup = Subsemigroup
.centralizer S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_toSubsemigroup : (centralizer S).toSubsemigroup = Subsemigroup.centralizer S :=
  rfl

variable {S}

@[to_additive]
/-
**Submonoid.mem_centralizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.center_le_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：center_le_centralizer (s) : center M <= centralizer s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.center_subset_centralizer`：center_subset_centralizer (S : Set M) : S
et.center M subseteq S.centralizer
-/
theorem center_le_centralizer (s) : center M ≤ centralizer s :=
  s.center_subset_centralizer

@[to_additive]
/-
**Submonoid.decidableMemCentralizer** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：decidableMemCentralizer (a) [Decidable <| forall b in S, b * a = a * b] : 
Decidable (a in centralizer S)
参数：a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_centralizer_iff`：mem_centralizer_iff {z : M} : z in centra
lizer S ↔ forall g in S, g * z = z * g
-/
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
/-
**Submonoid.centralizer_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
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
**Submonoid.centralizer_univ** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：centralizer_univ : centralizer Set.univ = center M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用引理 `Set.centralizer_univ`：centralizer_univ : centralizer univ = center M
-/
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)

@[to_additive]
/-
**Submonoid.le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：le_centralizer_centralizer {s : Submonoid M} : s <= centralizer (centraliz
er (s : Set M))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma le_centralizer_centralizer {s : Submonoid M} : s ≤ centralizer (centralizer (s : Set M)) :=
  Set.subset_centralizer_centralizer

@[to_additive (attr := simp)]
/-
**Submonoid.centralizer_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Submo
noid`。
形式化陈述：centralizer_centralizer_centralizer {s : Set M} : centralizer s.centralize
r.centralizer = centralizer s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.centralizer_centralizer_centralizer`：centralizer_centralizer_central
izer (S : Set M) : S.centralizer.centralizer.centralizer = S.centralizer
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma centralizer_centralizer_centralizer {s : Set M} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

variable {M} in
@[to_additive]
/-
**Submonoid.closure_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Submon
oid`。
形式化陈述：closure_le_centralizer_centralizer (s : Set M) : closure s <= centralizer 
(centralizer s)
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma closure_le_centralizer_centralizer (s : Set M) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive
/-- If all the elements of a set `s` commute, then `closure s` forms an additive
commutative monoid. -/]
/-
**Submonoid.isMulCommutative_closure** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：isMulCommutative_closure {s : Set M} (hcomm : forall a in s, forall b in s
, a * b = b * a) : IsMulCommutative (closure s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submonoid.closure_le_centralizer_centralizer`：closure_le_centralizer_cen
tralizer (s : Set M) : closure s <= centralizer (centralizer s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …
-/
theorem isMulCommutative_closure {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    IsMulCommutative (closure s) :=
  have := closure_le_centralizer_centralizer s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)

open scoped IsMulCommutative
/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive (attr := deprecated isMulCommutative_closure (since := "2026-03-09"))
/-- If all the elements of a set `s` commute, then `closure s` forms an additive
commutative monoid. -/]
/-
**Submonoid.closureCommMonoidOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submonoid`。
形式化陈述：closureCommMonoidOfComm {s : Set M} (hcomm : forall a in s, forall b in s,
 a * b = b * a) : CommMonoid (closure s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.isMulCommutative_closure`：isMulCommutative_closure {s : Set M}
 (hcomm : forall a in s, forall b in s, a * b = b * a) : IsMulCommutative (closu
re s)
-/
abbrev closureCommMonoidOfComm {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommMonoid (closure s) :=
  haveI := isMulCommutative_closure _ hcomm
  inferInstance

@[to_additive]
/-
**Submonoid.instIsMulCommutative_closure** 是 Mathlib 中的一个实例，位于命名空间 `Submonoid`。
形式化陈述：instIsMulCommutative_closure {S : Type*} [SetLike S M] [MulMemClass S M] (
s : S) [IsMulCommutative s] : IsMulCommutative (closure (s : Set M))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.isMulCommutative_closure`：isMulCommutative_closure {s : Set M}
 (hcomm : forall a in s, forall b in s, a * b = b * a) : IsMulCommutative (closu
re s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_closure {S : Type*} [SetLike S M] [MulMemClass S M] (s : S)
    [IsMulCommutative s] : IsMulCommutative (closure (s : Set M)) :=
  isMulCommutative_closure _ fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

end

end Submonoid

