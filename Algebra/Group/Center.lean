/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Set.Basic
public import Mathlib.Util.Delaborators

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib/GroupTheory/Subsemigroup/Center.lean` for the definition of the center as a
subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib/GroupTheory/Subsemigroup/Centralizer.lean` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso Finset MonoidWithZero Subsemigroup

variable {M : Type*} {S T : Set M}

/--
Definition of `IsAddCentral` / `IsAddCentral` 的定义

English:
structure IsAddCentral
  parameters: [Add M] (z : M)
  axioms and operations (3):
    - comm((a : M)) : AddCommute z a
    - left_assoc((b c : M)) : z + (b + c) = (z + b) + c
    - right_assoc((a b : M)) : (a + b) + z = a + (b + z)

中文:
结构 是加法中心
  参数: [加法 M] (z : M)
  公理与运算 (3 个):
    - comm((a : M)) : AddCommute z a
    - left_assoc((b c : M)) : z + (b + c) = (z + b) + c
    - right_assoc((a b : M)) : (a + b) + z = a + (b + z)
-/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : AddCommute z a
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
/--
Definition of `IsMulCentral` / `IsMulCentral` 的定义

English:
structure IsMulCentral
  parameters: [Mul M] (z : M)
  axioms and operations (3):
    - comm((a : M)) : Commute z a
    - left_assoc((b c : M)) : z * (b * c) = (z * b) * c
    - right_assoc((a b : M)) : (a * b) * z = a * (b * z)

中文:
结构 是MulCentral
  参数: [乘法 M] (z : M)
  公理与运算 (3 个):
    - comm((a : M)) : Commute z a
    - left_assoc((b c : M)) : z * (b * c) = (z * b) * c
    - right_assoc((a b : M)) : (a * b) * z = a * (b * z)
-/
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M) : Commute z a
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

attribute [mk_iff] IsMulCentral IsAddCentral
attribute [to_additive existing] isMulCentral_iff

namespace IsMulCentral

variable {a c : M} [Mul M]

@[to_additive]
/--
theorem `mid_assoc` / 定理 `mid_assoc`

English:
theorem mid_assoc
  given: {z : M} (h : IsMulCentral z) (a c)
  statement: a * z * c = a * (z * c)
  proof: by
  rw [h.comm]; rw [← h.right_assoc]; rw [← h.comm]; rw [← h.left_assoc]; rw [h.comm]

中文:
定理 mid_assoc
  条件: {z : M} (h : 是MulCentral z) (a c)
  结论: a * z * c = a * (z * c)
  证明: by
  rw [h.comm]; rw [← h.right_assoc]; rw [← h.comm]; rw [← h.left_assoc]; rw [h.comm]
-/
protected theorem mid_assoc {z : M} (h : IsMulCentral z) (a c) : a * z * c = a * (z * c) := by
  rw [h.comm]; rw [← h.right_assoc]; rw [← h.comm]; rw [← h.left_assoc]; rw [h.comm]

-- cf. `Commute.left_comm`
@[to_additive]
/--
theorem `left_comm` / 定理 `left_comm`

English:
theorem left_comm
  given: (h : IsMulCentral a) (b c)
  statement: a * (b * c) = b * (a * c)
  proof: by
  simp only [(h.comm _).eq, h.right_assoc]

中文:
定理 left_comm
  条件: (h : 是MulCentral a) (b c)
  结论: a * (b * c) = b * (a * c)
  证明: by
  simp only [(h.comm _).eq, h.right_assoc]
-/
protected theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [(h.comm _).eq, h.right_assoc]

-- cf. `Commute.right_comm`
@[to_additive]
/--
theorem `right_comm` / 定理 `right_comm`

English:
theorem right_comm
  given: (h : IsMulCentral c) (a b)
  statement: a * b * c = a * c * b
  proof: by
  simp only [h.right_assoc, h.mid_assoc, (h.comm _).eq]

中文:
定理 right_comm
  条件: (h : 是MulCentral c) (a b)
  结论: a * b * c = a * c * b
  证明: by
  simp only [h.right_assoc, h.mid_assoc, (h.comm _).eq]
-/
protected theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, h.mid_assoc, (h.comm _).eq]

end IsMulCentral

namespace Set

/-! ### Center -/

section Mul
variable [Mul M]

variable (M) in
/-- The center of a magma. -/
@[to_additive addCenter /-- The center of an additive magma. -/]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Set M
  body: { z | IsMulCentral z }

中文:
定义 center
  签名: : 集合 M
  定义体: { z | IsMulCentral z }

Depends on / 依赖: IsMulCentral
-/
def center : Set M :=
  { z | IsMulCentral z }

variable (S) in
/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer /-- The centralizer of a subset of an additive magma. -/]
/--
Definition of `centralizer` / `centralizer` 的定义

English:
definition centralizer
  signature: : Set M
  body: {c | forall m in S, m * c = c * m}

@[to_additive mem_addCenter_iff]

中文:
定义 centralizer
  签名: : 集合 M
  定义体: {c | forall m in S, m * c = c * m}

@[to_additive mem_addCenter_iff]
-/
def centralizer : Set M := {c | forall m in S, m * c = c * m}

@[to_additive mem_addCenter_iff]
/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {z : M}
  statement: z in center M ↔ IsMulCentral z
  proof: Iff.rfl

@[to_additive mem_addCentralizer]

中文:
定理 mem_center_iff
  条件: {z : M}
  结论: z in center M ↔ 是MulCentral z
  证明: Iff.rfl

@[to_additive mem_addCentralizer]

Depends on / 依赖: Iff.rfl
-/
theorem mem_center_iff {z : M} : z in center M ↔ IsMulCentral z :=
  Iff.rfl

@[to_additive mem_addCentralizer]
/--
lemma `mem_centralizer_iff` / 引理 `mem_centralizer_iff`

English:
lemma mem_centralizer_iff
  given: {c : M}
  statement: c in centralizer S ↔ forall m in S, m * c = c * m
  proof: Iff.rfl

@[to_additive (attr := simp) add_mem_addCenter]

中文:
引理 mem_centralizer_iff
  条件: {c : M}
  结论: c in centralizer S ↔ 对任意 m in S, m * c = c * m
  证明: Iff.rfl

@[to_additive (attr := simp) add_mem_addCenter]

Depends on / 依赖: Iff.rfl
-/
lemma mem_centralizer_iff {c : M} : c in centralizer S ↔ forall m in S, m * c = c * m := Iff.rfl

@[to_additive (attr := simp) add_mem_addCenter]
/--
theorem `mul_mem_center` / 定理 `mul_mem_center`

English:
theorem mul_mem_center
  given: {z₁ z₂ : M} (hz₁ : z₁ in Set.center M) (hz₂ : z₂ in Set.center M)
  proof: by
  simp only [commute_iff_eq, mem_center_iff, isMulCentral_iff] at *
  grind

@[to_additive addCenter_subset_addCentralizer]

中文:
定理 mul_mem_center
  条件: {z₁ z₂ : M} (hz₁ : z₁ in 集合.center M) (hz₂ : z₂ in 集合.center M)
  证明: by
  simp only [commute_iff_eq, mem_center_iff, isMulCentral_iff] at *
  grind

@[to_additive addCenter_subset_addCentralizer]

Depends on / 依赖: commute_iff_eq, isMulCentral_iff, mem_center_iff
-/
theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ in Set.center M) (hz₂ : z₂ in Set.center M) :
    z₁ * z₂ in Set.center M := by
  simp only [commute_iff_eq, mem_center_iff, isMulCentral_iff] at *
  grind

@[to_additive addCenter_subset_addCentralizer]
/--
lemma `center_subset_centralizer` / 引理 `center_subset_centralizer`

English:
lemma center_subset_centralizer
  given: (S : Set M)
  statement: Set.center M subseteq S.centralizer
  proof: fun _ hx m _ => (hx.comm m).symm

@[to_additive addCentralizer_union]

中文:
引理 center_subset_centralizer
  条件: (S : 集合 M)
  结论: 集合.center M subseteq S.centralizer
  证明: fun _ hx m _ => (hx.comm m).symm

@[to_additive addCentralizer_union]

Depends on / 依赖: hx.comm
-/
lemma center_subset_centralizer (S : Set M) : Set.center M subseteq S.centralizer :=
  fun _ hx m _ => (hx.comm m).symm

@[to_additive addCentralizer_union]
/--
lemma `centralizer_union` / 引理 `centralizer_union`

English:
lemma centralizer_union
  statement: centralizer (S union T) = centralizer S inter centralizer T
  proof: by
  simp [centralizer, or_imp, forall_and, ofPred_and]

@[to_additive (attr := gcongr) addCentralizer_subset]

中文:
引理 centralizer_union
  结论: centralizer (S union T) = centralizer S inter centralizer T
  证明: by
  simp [centralizer, or_imp, forall_and, ofPred_and]

@[to_additive (attr := gcongr) addCentralizer_subset]

Depends on / 依赖: centralizer, forall_and, ofPred_and, or_imp
-/
lemma centralizer_union : centralizer (S union T) = centralizer S inter centralizer T := by
  simp [centralizer, or_imp, forall_and, ofPred_and]

@[to_additive (attr := gcongr) addCentralizer_subset]
/--
lemma `centralizer_subset` / 引理 `centralizer_subset`

English:
lemma centralizer_subset
  given: (h : S subseteq T)
  statement: centralizer T subseteq centralizer S
  proof: fun _ ht s hs => ht s (h hs)

@[to_additive subset_addCentralizer_addCentralizer]

中文:
引理 centralizer_subset
  条件: (h : S subseteq T)
  结论: centralizer T subseteq centralizer S
  证明: fun _ ht s hs => ht s (h hs)

@[to_additive subset_addCentralizer_addCentralizer]
-/
lemma centralizer_subset (h : S subseteq T) : centralizer T subseteq centralizer S := fun _ ht s hs => ht s (h hs)

@[to_additive subset_addCentralizer_addCentralizer]
/--
lemma `subset_centralizer_centralizer` / 引理 `subset_centralizer_centralizer`

English:
lemma subset_centralizer_centralizer
  statement: S subseteq S.centralizer.centralizer
  proof: fun x hx _ hy => (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]

中文:
引理 subset_centralizer_centralizer
  结论: S subseteq S.centralizer.centralizer
  证明: fun x hx _ hy => (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
-/
lemma subset_centralizer_centralizer : S subseteq S.centralizer.centralizer :=
  fun x hx _ hy => (hy x hx).symm

@[to_additive (attr := simp) addCentralizer_addCentralizer_addCentralizer]
/--
lemma `centralizer_centralizer_centralizer` / 引理 `centralizer_centralizer_centralizer`

English:
lemma centralizer_centralizer_centralizer
  given: (S : Set M)
  proof: by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
exact fun x hx y hy => hx y Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]

中文:
引理 centralizer_centralizer_centralizer
  条件: (S : 集合 M)
  证明: by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
exact fun x hx y hy => hx y Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]

Depends on / 依赖: Set.Subset.antisymm, Set.subset_centralizer_centralizer, Subset, antisymm, subset_centralizer_centralizer
-/
lemma centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
exact fun x hx y hy => hx y Set.subset_centralizer_centralizer hy

@[to_additive decidableMemAddCentralizer]
/--
Instance `decidableMemCentralizer` / 实例 `decidableMemCentralizer`

English:
instance decidableMemCentralizer
  signature: [forall a : M, Decidable <| forall b in S, b * a = a * b]
  body: fun _ => decidable_of_iff' _ mem_centralizer_iff

@[to_additive addCentralizer_addCentralizer_comm_of_comm]

中文:
实例 decidableMemCentralizer
  签名: [对任意 a : M, 可判定 <| 对任意 b in S, b * a = a * b]
  定义体: fun _ => decidable_of_iff' _ mem_centralizer_iff

@[to_additive addCentralizer_addCentralizer_comm_of_comm]

Depends on / 依赖: decidable_of_iff, mem_centralizer_iff
-/
instance decidableMemCentralizer [forall a : M, Decidable <| forall b in S, b * a = a * b] :
    DecidablePred (· in centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff

@[to_additive addCentralizer_addCentralizer_comm_of_comm]
/--
lemma `centralizer_centralizer_comm_of_comm` / 引理 `centralizer_centralizer_comm_of_comm`

English:
lemma centralizer_centralizer_comm_of_comm
  given: (h_comm : forall x in S, forall y in S, x * y = y * x)
  proof: fun _ h₁ _ h₂ => h₂ _ fun _ h₃ => h₁ _ fun _ h₄ => h_comm _ h₄ _ h₃

@[to_additive (attr := simp) addCentralizer_empty]

中文:
引理 centralizer_centralizer_comm_of_comm
  条件: (h_comm : 对任意 x in S, 对任意 y in S, x * y = y * x)
  证明: fun _ h₁ _ h₂ => h₂ _ fun _ h₃ => h₁ _ fun _ h₄ => h_comm _ h₄ _ h₃

@[to_additive (attr := simp) addCentralizer_empty]

Depends on / 依赖: h_comm
-/
lemma centralizer_centralizer_comm_of_comm (h_comm : forall x in S, forall y in S, x * y = y * x) :
    forall x in S.centralizer.centralizer, forall y in S.centralizer.centralizer, x * y = y * x :=
  fun _ h₁ _ h₂ => h₂ _ fun _ h₃ => h₁ _ fun _ h₄ => h_comm _ h₄ _ h₃

@[to_additive (attr := simp) addCentralizer_empty]
/--
theorem `centralizer_empty` / 定理 `centralizer_empty`

English:
theorem centralizer_empty
  statement: (∅ : Set M).centralizer = ⊤
  proof: by simp [centralizer]

中文:
定理 centralizer_empty
  结论: (∅ : 集合 M).centralizer = ⊤
  证明: by simp [centralizer]

Depends on / 依赖: centralizer
-/
theorem centralizer_empty : (∅ : Set M).centralizer = ⊤ := by simp [centralizer]

/-- The centralizer of the product of non-empty sets is equal to the product of the centralizers. -/
@[to_additive addCentralizer_prod]
/--
theorem `centralizer_prod` / 定理 `centralizer_prod`

English:
theorem centralizer_prod
  statement: {N : Type*} [Mul N] {S : Set M} {T : Set N}
  proof: by
  ext
  simp only [mem_prod, mem_centralizer_iff, Prod.forall, Prod.mul_def]
  grind [Set.Nonempty]

@[to_additive prod_addCentralizer_subset_addCentralizer_prod]

中文:
定理 centralizer_prod
  结论: {N : 类型} [乘法 N] {S : 集合 M} {T : 集合 N}
  证明: by
  ext
  simp only [mem_prod, mem_centralizer_iff, Prod.forall, Prod.mul_def]
  grind [Set.Nonempty]

@[to_additive prod_addCentralizer_subset_addCentralizer_prod]

Depends on / 依赖: Nonempty, Prod.forall, Prod.mul_def, Set.Nonempty, mem_centralizer_iff, mem_prod, mul_def
-/
theorem centralizer_prod {N : Type*} [Mul N] {S : Set M} {T : Set N}
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (S ×ˢ T).centralizer = S.centralizer ×ˢ T.centralizer := by
  ext
  simp only [mem_prod, mem_centralizer_iff, Prod.forall, Prod.mul_def]
  grind [Set.Nonempty]

@[to_additive prod_addCentralizer_subset_addCentralizer_prod]
/--
theorem `prod_centralizer_subset_centralizer_prod` / 定理 `prod_centralizer_subset_centralizer_prod`

English:
theorem prod_centralizer_subset_centralizer_prod
  given: {N : Type*} [Mul N] (S : Set M) (T : Set N)
  proof: by
  simp_all [subset_def, mem_centralizer_iff]

@[to_additive addCenter_prod]

中文:
定理 prod_centralizer_subset_centralizer_prod
  条件: {N : 类型} [乘法 N] (S : 集合 M) (T : 集合 N)
  证明: by
  simp_all [subset_def, mem_centralizer_iff]

@[to_additive addCenter_prod]

Depends on / 依赖: mem_centralizer_iff, subset_def
-/
theorem prod_centralizer_subset_centralizer_prod {N : Type*} [Mul N] (S : Set M) (T : Set N) :
    S.centralizer ×ˢ T.centralizer subseteq (S ×ˢ T).centralizer := by
  simp_all [subset_def, mem_centralizer_iff]

@[to_additive addCenter_prod]
/--
theorem `center_prod` / 定理 `center_prod`

English:
theorem center_prod
  given: {N : Type*} [Mul N]
  proof: by
  aesop (add simp [forall_and, commute_iff_eq, isMulCentral_iff, mem_center_iff])

中文:
定理 center_prod
  条件: {N : 类型} [乘法 N]
  证明: by
  aesop (add simp [forall_and, commute_iff_eq, isMulCentral_iff, mem_center_iff])
-/
protected theorem center_prod {N : Type*} [Mul N] :
    center (M × N) = center M ×ˢ center N := by
  aesop (add simp [forall_and, commute_iff_eq, isMulCentral_iff, mem_center_iff])

open Function in
@[to_additive addCenter_pi]
/--
theorem `center_pi` / 定理 `center_pi`

English:
theorem center_pi
  given: {ι : Type*} {A : ι -> Type*} [Π i, Mul (A i)]
  proof: by
  classical
  ext x
  simp only [mem_pi, mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  refine ⟨fun ⟨h1, h2, h3⟩ i => ?_, by grind⟩
  exact ⟨fun a => by simpa using h1 (update x i a) i,
    fun b c => by simpa using h2 (update x i b) (u

中文:
定理 center_pi
  条件: {ι : 类型} {A : ι -> 类型} [Π i, 乘法 (A i)]
  证明: by
  classical
  ext x
  simp only [mem_pi, mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  refine ⟨fun ⟨h1, h2, h3⟩ i => ?_, by grind⟩
  exact ⟨fun a => by simpa using h1 (update x i a) i,
    fun b c => by simpa using h2 (update x i b) (u
-/
protected theorem center_pi {ι : Type*} {A : ι -> Type*} [Π i, Mul (A i)] :
    center (Π i, A i) = univ.pi fun i => center (A i) := by
  classical
  ext x
  simp only [mem_pi, mem_center_iff, isMulCentral_iff, mem_univ, forall_true_left,
    commute_iff_eq, funext_iff, Pi.mul_def]
  refine ⟨fun ⟨h1, h2, h3⟩ i => ?_, by grind⟩
  exact ⟨fun a => by simpa using h1 (update x i a) i,
    fun b c => by simpa using h2 (update x i b) (update x i c) i,
    fun a b => by simpa using h3 (update x i a) (update x i b) i⟩

end Mul

section Semigroup
variable [Semigroup M] {a b : M}

@[to_additive]
/--
theorem `_root_.Semigroup.mem_center_iff` / 定理 `_root_.Semigroup.mem_center_iff`

English:
theorem _root_.Semigroup.mem_center_iff
  given: {z : M}
  proof: ⟨fun a g => by rw [IsMulCentral.comm a g],
  fun h => ⟨fun _ => (h _).symm, fun _ _ => (mul_assoc z _ _).symm, fun _ _ => mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]

中文:
定理 _root_.半群.mem_center_iff
  条件: {z : M}
  证明: ⟨fun a g => by rw [IsMulCentral.comm a g],
  fun h => ⟨fun _ => (h _).symm, fun _ _ => (mul_assoc z _ _).symm, fun _ _ => mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]

Depends on / 依赖: IsMulCentral, IsMulCentral.comm
-/
theorem _root_.Semigroup.mem_center_iff {z : M} :
    z in Set.center M ↔ forall g, g * z = z * g := ⟨fun a g => by rw [IsMulCentral.comm a g],
  fun h => ⟨fun _ => (h _).symm, fun _ _ => (mul_assoc z _ _).symm, fun _ _ => mul_assoc _ _ z⟩ ⟩

@[to_additive (attr := simp) add_mem_addCentralizer]
/--
lemma `mul_mem_centralizer` / 引理 `mul_mem_centralizer`

English:
lemma mul_mem_centralizer
  given: (ha : a in centralizer S) (hb : b in centralizer S)
  proof: fun g hg => by
  rw [mul_assoc]; rw [← hb g hg]; rw [← mul_assoc]; rw [ha g hg]; rw [mul_assoc]

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]

中文:
引理 mul_mem_centralizer
  条件: (ha : a in centralizer S) (hb : b in centralizer S)
  证明: fun g hg => by
  rw [mul_assoc]; rw [← hb g hg]; rw [← mul_assoc]; rw [ha g hg]; rw [mul_assoc]

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]

Depends on / 依赖: mul_assoc
-/
lemma mul_mem_centralizer (ha : a in centralizer S) (hb : b in centralizer S) :
    a * b in centralizer S := fun g hg => by
  rw [mul_assoc]; rw [← hb g hg]; rw [← mul_assoc]; rw [ha g hg]; rw [mul_assoc]

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
/--
theorem `centralizer_eq_top_iff_subset` / 定理 `centralizer_eq_top_iff_subset`

English:
theorem centralizer_eq_top_iff_subset
  statement: centralizer S = Set.univ ↔ S subseteq center M
  proof: eq_top_iff.trans ⟨
    fun h _ hx => Semigroup.mem_center_iff.mpr fun _ => by rw [h trivial _ hx],
    fun h _ _ _ hm => (h hm).comm _⟩

中文:
定理 centralizer_eq_top_iff_subset
  结论: centralizer S = 集合.univ ↔ S subseteq center M
  证明: eq_top_iff.trans ⟨
    fun h _ hx => Semigroup.mem_center_iff.mpr fun _ => by rw [h trivial _ hx],
    fun h _ _ _ hm => (h hm).comm _⟩

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff.mpr, eq_top_iff, eq_top_iff.trans, mem_center_iff
-/
theorem centralizer_eq_top_iff_subset : centralizer S = Set.univ ↔ S subseteq center M :=
eq_top_iff.trans ⟨
    fun h _ hx => Semigroup.mem_center_iff.mpr fun _ => by rw [h trivial _ hx],
    fun h _ _ _ hm => (h hm).comm _⟩

variable (M) in
@[to_additive (attr := simp) addCentralizer_univ]
/--
lemma `centralizer_univ` / 引理 `centralizer_univ`

English:
lemma centralizer_univ
  statement: centralizer univ = center M
  proof: Subset.antisymm (fun _ ha => Semigroup.mem_center_iff.mpr fun b => ha b (Set.mem_univ b))
  fun _ ha b _ => (ha.comm b).symm

中文:
引理 centralizer_univ
  结论: centralizer univ = center M
  证明: Subset.antisymm (fun _ ha => Semigroup.mem_center_iff.mpr fun b => ha b (Set.mem_univ b))
  fun _ ha b _ => (ha.comm b).symm

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff.mpr, Set.mem_univ, Subset, Subset.antisymm, antisymm, ha.comm, mem_center_iff, mem_univ
-/
lemma centralizer_univ : centralizer univ = center M :=
  Subset.antisymm (fun _ ha => Semigroup.mem_center_iff.mpr fun b => ha b (Set.mem_univ b))
  fun _ ha b _ => (ha.comm b).symm

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
@[to_additive decidableMemAddCenter]
/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: [forall a : M, Decidable <| forall b : M, b * a = a * b]
  body: fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

中文:
实例 decidableMemCenter
  签名: [对任意 a : M, 可判定 <| 对任意 b : M, b * a = a * b]
  定义体: fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff, decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter [forall a : M, Decidable <| forall b : M, b * a = a * b] :
    DecidablePred (· in center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
/--
theorem `center_eq_univ` / 定理 `center_eq_univ`

English:
theorem center_eq_univ
  statement: center M = univ
  proof: (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

@[to_additive (attr := simp) addCentralizer_eq_univ]

中文:
定理 center_eq_univ
  结论: center M = univ
  证明: (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

@[to_additive (attr := simp) addCentralizer_eq_univ]

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff.mpr, Subset, Subset.antisymm, antisymm, mem_center_iff, mul_comm, subset_univ
-/
theorem center_eq_univ : center M = univ :=
  (Subset.antisymm (subset_univ _)) fun _ _ => Semigroup.mem_center_iff.mpr (fun _ => mul_comm _ _)

@[to_additive (attr := simp) addCentralizer_eq_univ]
/--
lemma `centralizer_eq_univ` / 引理 `centralizer_eq_univ`

English:
lemma centralizer_eq_univ
  statement: centralizer S = univ
  proof: eq_univ_of_forall fun _ _ _ => mul_comm _ _

中文:
引理 centralizer_eq_univ
  结论: centralizer S = univ
  证明: eq_univ_of_forall fun _ _ _ => mul_comm _ _

Depends on / 依赖: eq_univ_of_forall, mul_comm
-/
lemma centralizer_eq_univ : centralizer S = univ :=
  eq_univ_of_forall fun _ _ _ => mul_comm _ _

end CommSemigroup

section MulOneClass
variable [MulOneClass M]

@[to_additive (attr := simp) zero_mem_addCenter]
/--
theorem `one_mem_center` / 定理 `one_mem_center`

English:
theorem one_mem_center
  statement: (1 : M) in Set.center M where
  proof: by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

@[to_additive (attr := simp) zero_mem_addCentralizer]

中文:
定理 one_mem_center
  结论: (1 : M) in 集合.center M where
  证明: by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

@[to_additive (attr := simp) zero_mem_addCentralizer]

Depends on / 依赖: commute_iff_eq, left_assoc, mul_one, one_mul, right_assoc
-/
theorem one_mem_center : (1 : M) in Set.center M where
  comm _ := by rw [commute_iff_eq, one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]

@[to_additive (attr := simp) zero_mem_addCentralizer]
/--
lemma `one_mem_centralizer` / 引理 `one_mem_centralizer`

English:
lemma one_mem_centralizer
  statement: (1 : M) in centralizer S
  proof: by simp [mem_centralizer_iff]

中文:
引理 one_mem_centralizer
  结论: (1 : M) in centralizer S
  证明: by simp [mem_centralizer_iff]

Depends on / 依赖: mem_centralizer_iff
-/
lemma one_mem_centralizer : (1 : M) in centralizer S := by simp [mem_centralizer_iff]

end MulOneClass

section Monoid
variable [Monoid M]

@[to_additive subset_addCenter_add_units]
/--
theorem `subset_center_units` / 定理 `subset_center_units`

English:
theorem subset_center_units
  statement: ((↑) : Mˣ -> M) ⁻¹' center M subseteq Set.center Mˣ
  proof: fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.val_inj]; rw [Units.val_mul]; rw [Units.val_mul]; rw [ha.comm]

@[to_additive (attr := simp)]

中文:
定理 subset_center_units
  结论: ((↑) : Mˣ -> M) ⁻¹' center M subseteq 集合.center Mˣ
  证明: fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.val_inj]; rw [Units.val_mul]; rw [Units.val_mul]; rw [ha.comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Semigroup, Units.val_inj, Units.val_mul, _root_, _root_.Semigroup.mem_center_iff, ha.comm, mem_center_iff, val_inj, val_mul
-/
theorem subset_center_units : ((↑) : Mˣ -> M) ⁻¹' center M subseteq Set.center Mˣ :=
  fun _ ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← Units.val_inj]; rw [Units.val_mul]; rw [Units.val_mul]; rw [ha.comm]

@[to_additive (attr := simp)]
/--
theorem `units_inv_mem_center` / 定理 `units_inv_mem_center`

English:
theorem units_inv_mem_center
  given: {a : Mˣ} (ha : ↑a in Set.center M)
  statement: ↑a⁻¹ in Set.center M
  proof: by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]

中文:
定理 units_inv_mem_center
  条件: {a : Mˣ} (ha : ↑a in 集合.center M)
  结论: ↑a⁻¹ in 集合.center M
  证明: by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]

Depends on / 依赖: Commute, Commute.units_inv_right, Semigroup, Semigroup.mem_center_iff, mem_center_iff, units_inv_right
-/
theorem units_inv_mem_center {a : Mˣ} (ha : ↑a in Set.center M) : ↑a⁻¹ in Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.units_inv_right <| ha ·)

@[simp]
/--
theorem `invOf_mem_center` / 定理 `invOf_mem_center`

English:
theorem invOf_mem_center
  given: {a : M} [Invertible a] (ha : a in Set.center M)
  statement: ⅟a in Set.center M
  proof: by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

中文:
定理 invOf_mem_center
  条件: {a : M} [可逆 a] (ha : a in 集合.center M)
  结论: ⅟a in 集合.center M
  证明: by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

Depends on / 依赖: Commute, Commute.invOf_right, Semigroup, Semigroup.mem_center_iff, invOf_right, mem_center_iff
-/
theorem invOf_mem_center {a : M} [Invertible a] (ha : a in Set.center M) : ⅟a in Set.center M := by
  rw [Semigroup.mem_center_iff] at *
  exact (Commute.invOf_right <| ha ·)

end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCenter]
/--
theorem `inv_mem_center` / 定理 `inv_mem_center`

English:
theorem inv_mem_center
  given: (ha : a in Set.center M)
  statement: a⁻¹ in Set.center M
  proof: by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj]; rw [mul_inv_rev]; rw [inv_inv]; rw [ha.comm]; rw [mul_inv_rev]; rw [inv_inv]

@[to_additive (attr := simp) sub_mem_addCenter]

中文:
定理 inv_mem_center
  条件: (ha : a in 集合.center M)
  结论: a⁻¹ in 集合.center M
  证明: by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj]; rw [mul_inv_rev]; rw [inv_inv]; rw [ha.comm]; rw [mul_inv_rev]; rw [inv_inv]

@[to_additive (attr := simp) sub_mem_addCenter]

Depends on / 依赖: Semigroup, _root_, _root_.Semigroup.mem_center_iff, ha.comm, inv_inj, inv_inv, mem_center_iff, mul_inv_rev
-/
theorem inv_mem_center (ha : a in Set.center M) : a⁻¹ in Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj]; rw [mul_inv_rev]; rw [inv_inv]; rw [ha.comm]; rw [mul_inv_rev]; rw [inv_inv]

@[to_additive (attr := simp) sub_mem_addCenter]
/--
theorem `div_mem_center` / 定理 `div_mem_center`

English:
theorem div_mem_center
  given: (ha : a in Set.center M) (hb : b in Set.center M)
  statement: a / b in Set.center M
  proof: by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

中文:
定理 div_mem_center
  条件: (ha : a in 集合.center M) (hb : b in 集合.center M)
  结论: a / b in 集合.center M
  证明: by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

Depends on / 依赖: div_eq_mul_inv, inv_mem_center, mul_mem_center
-/
theorem div_mem_center (ha : a in Set.center M) (hb : b in Set.center M) : a / b in Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)

end DivisionMonoid

section Group
variable [Group M] {a b : M}

@[to_additive (attr := simp) neg_mem_addCentralizer]
/--
lemma `inv_mem_centralizer` / 引理 `inv_mem_centralizer`

English:
lemma inv_mem_centralizer
  given: (ha : a in centralizer S)
  statement: a⁻¹ in centralizer S
  proof: fun g hg => by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[to_additive (attr := simp) sub_mem_addCentralizer]

中文:
引理 inv_mem_centralizer
  条件: (ha : a in centralizer S)
  结论: a⁻¹ in centralizer S
  证明: fun g hg => by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[to_additive (attr := simp) sub_mem_addCentralizer]

Depends on / 依赖: eq_inv_mul_iff_mul_eq, mul_assoc, mul_inv_eq_iff_eq_mul
-/
lemma inv_mem_centralizer (ha : a in centralizer S) : a⁻¹ in centralizer S :=
  fun g hg => by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[to_additive (attr := simp) sub_mem_addCentralizer]
/--
lemma `div_mem_centralizer` / 引理 `div_mem_centralizer`

English:
lemma div_mem_centralizer
  given: (ha : a in centralizer S) (hb : b in centralizer S)
  proof: by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

中文:
引理 div_mem_centralizer
  条件: (ha : a in centralizer S) (hb : b in centralizer S)
  证明: by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

Depends on / 依赖: div_eq_mul_inv, inv_mem_centralizer, mul_mem_centralizer
-/
lemma div_mem_centralizer (ha : a in centralizer S) (hb : b in centralizer S) :
    a / b in centralizer S := by
  simpa only [div_eq_mul_inv] using mul_mem_centralizer ha (inv_mem_centralizer hb)

end Group
end Set
