/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The topological abelianization of the absolute Galois group.

We define the absolute Galois group of a field `K` and its topological abelianization.

## Main definitions
- `Field.absoluteGaloisGroup` : The Galois group of the field extension `K^al/K`, where `K^al` is an
  algebraic closure of `K`.
- `Field.absoluteGaloisGroupAbelianization` : The topological abelianization of
  `Field.absoluteGaloisGroup K`, that is, the quotient of `Field.absoluteGaloisGroup K` by the
  topological closure of its commutator subgroup.

## Main results
- `Field.absoluteGaloisGroup.commutator_closure_isNormal` : the topological closure of the
  commutator of `absoluteGaloisGroup` is a normal subgroup.

## Tags
field, algebraic closure, galois group, abelianization

-/

@[expose] public noncomputable section

namespace Field

variable (K : Type*) [Field K]

/-! ### The absolute Galois group -/

/-- The absolute Galois group of `K`, defined as the Galois group of the field extension `K^al/K`,
  where `K^al` is an algebraic closure of `K`. -/
/-
**Field.absoluteGaloisGroup** 是 Mathlib 中的一个定义，位于命名空间 `Field`。
形式化陈述：absoluteGaloisGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute Galois group of `K`, defined as the Galois group of the field exten
sion `K^al/K`,
  where `K^al` is an algebraic closure of `K`.
-/
def absoluteGaloisGroup := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K
deriving Group, TopologicalSpace, IsTopologicalGroup

/-- `absoluteGaloisGroup` is a topological space with the Krull topology. -/
add_decl_doc instTopologicalSpaceAbsoluteGaloisGroup

local notation "G_K" => absoluteGaloisGroup

/-! ### The topological abelianization of the absolute Galois group -/

/-
**Field.absoluteGaloisGroup.commutator_closure_isNormal** 是 Mathlib 中的一个定理，位于命名空
间 `Field.absoluteGaloisGroup`。
形式化陈述：∀ (K : Type u_1) [inst : Field K], (commutator (Field.absoluteGaloisGroup 
K)).topologicalClosure.Normal
参数：K : Type u_1；commutator (Field.absoluteGaloisGroup K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.is_normal_topologicalClosure`：Subgroup.is_normal_topologicalClo
sure {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (N : Subg
roup G) [N.Normal] : (Subgr…
· 使用定理 `Field.instIsTopologicalGroupAbsoluteGaloisGroup`：∀ (K : Type u_1) [inst 
: Field K], IsTopologicalGroup (Field.absoluteGaloisGroup K)
· 使用定理 `instNormalCommutator`：∀ (G : Type u_1) [inst : Group G], (commutator G).
Normal

--- 原说明 ---
### The topological abelianization of the absolute Galois group
-/
instance absoluteGaloisGroup.commutator_closure_isNormal :
    (commutator (G_K K)).topologicalClosure.Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (G_K K))

/-- The topological abelianization of `absoluteGaloisGroup`, that is, the quotient of
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup. -/
/-
**Field.absoluteGaloisGroupAbelianization** 是 Mathlib 中的一个缩写定义，位于命名空间 `Field`。
形式化陈述：absoluteGaloisGroupAbelianization
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.instIsTopologicalGroupAbsoluteGaloisGroup`：∀ (K : Type u_1) [inst 
: Field K], IsTopologicalGroup (Field.absoluteGaloisGroup K)

--- 原说明 ---
The topological abelianization of `absoluteGaloisGroup`, that is, the quotient o
f
  `absoluteGaloisGroup` by the topological closure of its commutator subgroup.
-/
abbrev absoluteGaloisGroupAbelianization := TopologicalAbelianization (G_K K)

local notation "G_K_ab" => absoluteGaloisGroupAbelianization

end Field

