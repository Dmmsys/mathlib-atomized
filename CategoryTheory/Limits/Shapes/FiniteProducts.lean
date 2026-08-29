/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/

public section


universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/--
Definition of `HasFiniteProducts` / `HasFiniteProducts` 的定义

English:
class HasFiniteProducts
  parameters: : Prop where
  axioms and operations (1):
    - out((n : Nat)) : HasLimitsOfShape (Discrete (Fin n)) C

中文:
类 有FiniteProducts
  参数: : 命题 where
  公理与运算 (1 个):
    - out((n : 自然数)) : 有形状极限 (离散 (有限集 n)) C
-/
class HasFiniteProducts : Prop where
  /-- `C` has finite products -/
  out (n : Nat) : HasLimitsOfShape (Discrete (Fin n)) C

/-- If `C` has finite limits then it has finite products. -/
instance (priority := 10) hasFiniteProducts_of_hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteProducts C :=
  ⟨fun _ => inferInstance⟩

/--
Instance `hasLimitsOfShape_discrete` / 实例 `hasLimitsOfShape_discrete`

English:
instance hasLimitsOfShape_discrete
  signature: [HasFiniteProducts C] (ι : Type w) [Finite ι]
  body: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

中文:
实例 hasLimitsOfShape_discrete
  签名: [有FiniteProducts C] (ι : 类型 w) [有限 ι]
  定义体: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, HasFiniteProducts, HasFiniteProducts.out, HasLimitsOfShape, e.symm, equivalence, exists_equiv_fin, hasLimitsOfShape_of_equivalence
-/
instance hasLimitsOfShape_discrete [HasFiniteProducts C] (ι : Type w) [Finite ι] :
    HasLimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasLimitsOfShape (Discrete (Fin n)) C := HasFiniteProducts.out n
  exact hasLimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

/-- We can now write this for powers. -/
noncomputable example [HasFiniteProducts C] (X : C) : C :=
  ∏ᶜ fun _ : Fin 5 => X

/--
theorem `hasFiniteProducts_of_hasProducts` / 定理 `hasFiniteProducts_of_hasProducts`

English:
theorem hasFiniteProducts_of_hasProducts
  given: [HasProducts.{w} C]
  statement: HasFiniteProducts C
  proof: ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

中文:
定理 hasFiniteProducts_of_hasProducts
  条件: [HasProducts.{w} C]
  结论: 有FiniteProducts C
  证明: ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, equivalence, hasLimitsOfShape_of_equivalence
-/
theorem hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

/--
Definition of `HasFiniteCoproducts` / `HasFiniteCoproducts` 的定义

English:
class HasFiniteCoproducts
  parameters: : Prop where
  axioms and operations (1):
    - out((n : Nat)) : HasColimitsOfShape (Discrete (Fin n)) C

中文:
类 有FiniteCoproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - out((n : 自然数)) : 有形状余极限 (离散 (有限集 n)) C
-/
class HasFiniteCoproducts : Prop where
  /-- `C` has all finite coproducts -/
  out (n : Nat) : HasColimitsOfShape (Discrete (Fin n)) C

/--
Instance `hasColimitsOfShape_discrete` / 实例 `hasColimitsOfShape_discrete`

English:
instance hasColimitsOfShape_discrete
  signature: [HasFiniteCoproducts C] (ι : Type w) [Finite ι]
  body: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

中文:
实例 hasColimitsOfShape_discrete
  签名: [有FiniteCoproducts C] (ι : 类型 w) [有限 ι]
  定义体: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

Depends on / 依赖: Discrete, Discrete.equivalence, Finite, Finite.exists_equiv_fin, HasColimitsOfShape, HasFiniteCoproducts, HasFiniteCoproducts.out, e.symm, equivalence, exists_equiv_fin, hasColimitsOfShape_of_equivalence
-/
instance hasColimitsOfShape_discrete [HasFiniteCoproducts C] (ι : Type w) [Finite ι] :
    HasColimitsOfShape (Discrete ι) C := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  have : HasColimitsOfShape (Discrete (Fin n)) C := HasFiniteCoproducts.out n
  exact hasColimitsOfShape_of_equivalence (Discrete.equivalence e.symm)

/-- If `C` has finite colimits then it has finite coproducts. -/
instance (priority := 10) hasFiniteCoproducts_of_hasFiniteColimits [HasFiniteColimits C] :
    HasFiniteCoproducts C :=
  ⟨fun J => by infer_instance⟩

/--
theorem `hasFiniteCoproducts_of_hasCoproducts` / 定理 `hasFiniteCoproducts_of_hasCoproducts`

English:
theorem hasFiniteCoproducts_of_hasCoproducts
  given: [HasCoproducts.{w} C]
  statement: HasFiniteCoproducts C
  proof: ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

中文:
定理 hasFiniteCoproducts_of_hasCoproducts
  条件: [HasCoproducts.{w} C]
  结论: 有FiniteCoproducts C
  证明: ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

Depends on / 依赖: Discrete, Discrete.equivalence, Equiv.ulift, equivalence, hasColimitsOfShape_of_equivalence
-/
theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

end CategoryTheory.Limits
