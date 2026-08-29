/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Data.Countable.Defs
/-!
# Countable limits and colimits

A typeclass for categories with all countable (co)limits.

We also prove that all cofiltered limits over countable preorders are isomorphic to sequential
limits, see `sequentialFunctor_initial`.

## Projects

* There is a series of `proof_wanted` at the bottom of this file, implying that all cofiltered
  limits over countable categories are isomorphic to sequential limits.

* Prove the dual result for filtered colimits.

-/

@[expose] public section

open CategoryTheory Opposite CountableCategory

variable (C : Type*) [Category* C] (J : Type*) [Countable J]

namespace CategoryTheory.Limits

/--
Definition of `HasCountableLimits` / `HasCountableLimits` 的定义

English:
class HasCountableLimits
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [SmallCategory J] [CountableCategory J]) : HasLimitsOfShape J C  [default: by infer_instance]

中文:
类 有余untableLimits
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [小范畴 J] [余untable范畴 J]) : 有形状极限 J C  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class HasCountableLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasLimitsOfShape J C := by infer_instance

instance (priority := 100) hasFiniteLimits_of_hasCountableLimits [HasCountableLimits C] :
    HasFiniteLimits C where
  out J := HasCountableLimits.out J

instance (priority := 100) hasCountableLimits_of_hasLimits [HasLimits C] :
    HasCountableLimits C where
  out := inferInstance

universe v in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCountableLimits
  signature: C] [Category.{v} J] [CountableCategory J] : HasLimitsOfShape J C
  body: have : HasLimitsOfShape (HomAsType J) C := HasCountableLimits.out (HomAsType J)
  hasLimitsOfShape_of_equivalence (homAsTypeEquiv J)

中文:
实例 [有余untableLimits
  签名: C] [范畴.{v} J] [余untable范畴 J] : 有形状极限 J C
  定义体: have : HasLimitsOfShape (HomAsType J) C := HasCountableLimits.out (HomAsType J)
  hasLimitsOfShape_of_equivalence (homAsTypeEquiv J)

Depends on / 依赖: HasCountableLimits, HasCountableLimits.out, HasLimitsOfShape, HomAsType, hasLimitsOfShape_of_equivalence, homAsTypeEquiv
-/
instance [HasCountableLimits C] [Category.{v} J] [CountableCategory J] : HasLimitsOfShape J C :=
  have : HasLimitsOfShape (HomAsType J) C := HasCountableLimits.out (HomAsType J)
  hasLimitsOfShape_of_equivalence (homAsTypeEquiv J)

/--
Definition of `HasCountableProducts` / `HasCountableProducts` 的定义

English:
class HasCountableProducts
  parameters: where
  axioms and operations (1):
    - out((J : Type) [Countable J]) : HasProductsOfShape J C

中文:
类 有余untableProducts
  参数: where
  公理与运算 (1 个):
    - out((J : 类型) [可数 J]) : HasProductsOfShape J C
-/
class HasCountableProducts where
  out (J : Type) [Countable J] : HasProductsOfShape J C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCountableProducts
  signature: C] (J
  body: have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasLimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableProducts.out _
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

中文:
实例 [有余untableProducts
  签名: C] (J
  定义体: have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasLimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableProducts.out _
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

Depends on / 依赖: Countable, Countable.of_equiv, Discrete, Discrete.equivalence, HasCountableProducts, HasCountableProducts.out, HasLimitsOfShape, Shrink, equivShrink, equivalence, hasLimitsOfShape_of_equivalence, of_equiv
-/
instance [HasCountableProducts C] (J : Type*) [Countable J] : HasProductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasLimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableProducts.out _
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

instance (priority := 100) hasCountableProducts_of_hasProducts [HasProducts C] :
    HasCountableProducts C where
  out _ :=
    have : HasProducts.{0} C := has_smallest_products_of_hasProducts
    inferInstance

instance (priority := 100) hasCountableProducts_of_hasCountableLimits [HasCountableLimits C] :
    HasCountableProducts C where
  out _ := inferInstance

instance (priority := 100) hasFiniteProducts_of_hasCountableProducts [HasCountableProducts C] :
    HasFiniteProducts C where
  out _ := inferInstance

/--
Definition of `HasCountableColimits` / `HasCountableColimits` 的定义

English:
class HasCountableColimits
  parameters: : Prop where
  axioms and operations (1):
    - out((J : Type) [SmallCategory J] [CountableCategory J]) : HasColimitsOfShape J C

中文:
类 有余untableColimits
  参数: : 命题 where
  公理与运算 (1 个):
    - out((J : 类型) [小范畴 J] [余untable范畴 J]) : 有形状余极限 J C
-/
class HasCountableColimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has countably many objects and morphisms -/
  out (J : Type) [SmallCategory J] [CountableCategory J] : HasColimitsOfShape J C

instance (priority := 100) hasFiniteColimits_of_hasCountableColimits [HasCountableColimits C] :
    HasFiniteColimits C where
  out J := HasCountableColimits.out J

instance (priority := 100) hasCountableColimits_of_hasColimits [HasColimits C] :
    HasCountableColimits C where
  out := inferInstance

-- See note [instance argument order]
universe v in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCountableColimits
  signature: C] (J
  body: have : HasColimitsOfShape (HomAsType J) C := HasCountableColimits.out (HomAsType J)
  hasColimitsOfShape_of_equivalence (homAsTypeEquiv J)

中文:
实例 [有余untableColimits
  签名: C] (J
  定义体: have : HasColimitsOfShape (HomAsType J) C := HasCountableColimits.out (HomAsType J)
  hasColimitsOfShape_of_equivalence (homAsTypeEquiv J)

Depends on / 依赖: HasColimitsOfShape, HasCountableColimits, HasCountableColimits.out, HomAsType, hasColimitsOfShape_of_equivalence, homAsTypeEquiv
-/
instance [HasCountableColimits C] (J : Type*) [Category.{v} J] [CountableCategory J] :
    HasColimitsOfShape J C :=
  have : HasColimitsOfShape (HomAsType J) C := HasCountableColimits.out (HomAsType J)
  hasColimitsOfShape_of_equivalence (homAsTypeEquiv J)

/--
Definition of `HasCountableCoproducts` / `HasCountableCoproducts` 的定义

English:
class HasCountableCoproducts
  parameters: where
  axioms and operations (1):
    - out((J : Type) [Countable J]) : HasCoproductsOfShape J C

中文:
类 有余untableCoproducts
  参数: where
  公理与运算 (1 个):
    - out((J : 类型) [可数 J]) : HasCoproductsOfShape J C
-/
class HasCountableCoproducts where
  out (J : Type) [Countable J] : HasCoproductsOfShape J C

instance (priority := 100) hasCountableCoproducts_of_hasCoproducts [HasCoproducts C] :
    HasCountableCoproducts C where
  out _ :=
    have : HasCoproducts.{0} C := has_smallest_coproducts_of_hasCoproducts
    inferInstance

-- See note [instance argument order]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCountableCoproducts
  signature: C] (J
  body: have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasColimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableCoproducts.out _
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

中文:
实例 [有余untableCoproducts
  签名: C] (J
  定义体: have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasColimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableCoproducts.out _
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

Depends on / 依赖: Countable, Countable.of_equiv, Discrete, Discrete.equivalence, HasColimitsOfShape, HasCountableCoproducts, HasCountableCoproducts.out, Shrink, equivShrink, equivalence, hasColimitsOfShape_of_equivalence, of_equiv
-/
instance [HasCountableCoproducts C] (J : Type*) [Countable J] : HasCoproductsOfShape J C :=
  have : Countable (Shrink.{0} J) := Countable.of_equiv _ (equivShrink.{0} J)
  have : HasColimitsOfShape (Discrete (Shrink.{0} J)) C := HasCountableCoproducts.out _
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{0} J)).symm

instance (priority := 100) hasCountableCoproducts_of_hasCountableColimits [HasCountableColimits C] :
    HasCountableCoproducts C where
  out _ := inferInstance

instance (priority := 100) hasFiniteCoproducts_of_hasCountableCoproducts
    [HasCountableCoproducts C] : HasFiniteCoproducts C where
  out _ := inferInstance

section Preorder

namespace IsFiltered

attribute [local instance] IsFiltered.nonempty

variable {C} [Preorder J] [IsFiltered J]

/--
Definition of `sequentialFunctor_obj` / `sequentialFunctor_obj` 的定义

English:
definition sequentialFunctor_obj
  signature: : Nat -> J
  body: fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

中文:
定义 sequentialFunctor_obj
  签名: : 自然数 -> J
  定义体: fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose
-/
noncomputable def sequentialFunctor_obj : Nat -> J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

/--
theorem `sequentialFunctor_map` / 定理 `sequentialFunctor_map`

English:
theorem sequentialFunctor_map
  statement: Monotone (sequentialFunctor_obj J)
  proof: monotone_nat_of_le_succ fun n =>
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

中文:
定理 sequentialFunctor_map
  结论: 递增 (sequentialFunctor_obj J)
  证明: monotone_nat_of_le_succ fun n =>
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, choose_spec, choose_spec.choose_spec.choose, cocone_objs, exists_surjective_nat, leOfHom, monotone_nat_of_le_succ, sequentialFunctor_obj
-/
theorem sequentialFunctor_map : Monotone (sequentialFunctor_obj J) :=
  monotone_nat_of_le_succ fun n =>
    leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
Definition of `sequentialFunctor` / `sequentialFunctor` 的定义

English:
definition sequentialFunctor
  signature: : Nat ⥤ J where
  body: sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))

中文:
定义 sequentialFunctor
  签名: : 自然数 ⥤ J where
  定义体: sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))

Depends on / 依赖: sequentialFunctor_obj
-/
noncomputable def sequentialFunctor : Nat ⥤ J where
  obj n := sequentialFunctor_obj J n
  map h := homOfLE (sequentialFunctor_map J (leOfHom h))

/--
theorem `sequentialFunctor_final_aux` / 定理 `sequentialFunctor_final_aux`

English:
theorem sequentialFunctor_final_aux
  given: (j : J)
  statement: exists (n : Nat), j <= sequentialFunctor_obj J n
  proof: by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

中文:
定理 sequentialFunctor_final_aux
  条件: (j : J)
  结论: 存在 (n : 自然数), j <= sequentialFunctor_obj J n
  证明: by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

Depends on / 依赖: IsFilteredOrEmpty, IsFilteredOrEmpty.cocone_objs, choose_spec, choose_spec.choose, cocone_objs, exists_surjective_nat, leOfHom, sequentialFunctor_obj
-/
theorem sequentialFunctor_final_aux (j : J) : exists (n : Nat), j <= sequentialFunctor_obj J n := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsFilteredOrEmpty.cocone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

/--
Instance `sequentialFunctor_final` / 实例 `sequentialFunctor_final`

English:
instance sequentialFunctor_final
  signature: : (sequentialFunctor J).Final where
  body: by
    obtain ⟨n, (g : d <= (sequentialFunctor J).obj n)⟩ := sequentialFunctor_final_aux J d
    have : Nonempty (StructuredArrow d (sequentialFunctor J)) :=
      ⟨StructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : j.right <= i.right
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨StructuredArrow.homMk (homOfLE h) rfl⟩

中文:
实例 sequentialFunctor_final
  签名: : (sequentialFunctor J).终 where
  定义体: by
    obtain ⟨n, (g : d <= (sequentialFunctor J).obj n)⟩ := sequentialFunctor_final_aux J d
    have : Nonempty (StructuredArrow d (sequentialFunctor J)) :=
      ⟨StructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : j.right <= i.right
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨StructuredArrow.homMk (homOfLE h) rfl⟩

Depends on / 依赖: List.getLast_cons, List.getLast_singleton, List.isChain_cons_cons, List.isChain_singleton, Nonempty, StructuredArrow, StructuredArrow.mk, and_true, getLast_cons, getLast_singleton, homOfLE, i.right, isChain_cons_cons, isChain_singleton, isConnected_of_zigzag, j.right, le_of_lt, ne_eq, not_false_eq_true, or_comm
-/
instance sequentialFunctor_final : (sequentialFunctor J).Final where
  out d := by
    obtain ⟨n, (g : d <= (sequentialFunctor J).obj n)⟩ := sequentialFunctor_final_aux J d
    have : Nonempty (StructuredArrow d (sequentialFunctor J)) :=
      ⟨StructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : j.right <= i.right
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨StructuredArrow.homMk (homOfLE h) rfl⟩

end IsFiltered

namespace IsCofiltered

attribute [local instance] IsCofiltered.nonempty

variable {C} [Preorder J] [IsCofiltered J]

/--
Definition of `sequentialFunctor_obj` / `sequentialFunctor_obj` 的定义

English:
definition sequentialFunctor_obj
  signature: : Nat -> J
  body: fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

中文:
定义 sequentialFunctor_obj
  签名: : 自然数 -> J
  定义体: fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose
-/
noncomputable def sequentialFunctor_obj : Nat -> J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj n)).choose

/--
theorem `sequentialFunctor_map` / 定理 `sequentialFunctor_map`

English:
theorem sequentialFunctor_map
  statement: Antitone (sequentialFunctor_obj J)
  proof: antitone_nat_of_succ_le fun n =>
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

中文:
定理 sequentialFunctor_map
  结论: 递减 (sequentialFunctor_obj J)
  证明: antitone_nat_of_succ_le fun n =>
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, antitone_nat_of_succ_le, choose_spec, choose_spec.choose_spec.choose, cone_objs, exists_surjective_nat, leOfHom, sequentialFunctor_obj
-/
theorem sequentialFunctor_map : Antitone (sequentialFunctor_obj J) :=
  antitone_nat_of_succ_le fun n =>
    leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (sequentialFunctor_obj J n)).choose_spec.choose_spec.choose

/--
Definition of `sequentialFunctor` / `sequentialFunctor` 的定义

English:
definition sequentialFunctor
  signature: : Natᵒᵖ ⥤ J where
  body: sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

中文:
定义 sequentialFunctor
  签名: : 自然数ᵒᵖ ⥤ J where
  定义体: sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

Depends on / 依赖: sequentialFunctor_obj
-/
noncomputable def sequentialFunctor : Natᵒᵖ ⥤ J where
  obj n := sequentialFunctor_obj J (unop n)
  map h := homOfLE (sequentialFunctor_map J (leOfHom h.unop))

/--
theorem `sequentialFunctor_initial_aux` / 定理 `sequentialFunctor_initial_aux`

English:
theorem sequentialFunctor_initial_aux
  given: (j : J)
  statement: exists (n : Nat), sequentialFunctor_obj J n <= j
  proof: by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

中文:
定理 sequentialFunctor_initial_aux
  条件: (j : J)
  结论: 存在 (n : 自然数), sequentialFunctor_obj J n <= j
  证明: by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

Depends on / 依赖: IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, choose_spec, choose_spec.choose, cone_objs, exists_surjective_nat, leOfHom, sequentialFunctor_obj
-/
theorem sequentialFunctor_initial_aux (j : J) : exists (n : Nat), sequentialFunctor_obj J n <= j := by
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec j
  refine ⟨m + 1, ?_⟩
  simpa only [h] using! leOfHom (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
    (sequentialFunctor_obj J m)).choose_spec.choose

/--
Instance `sequentialFunctor_initial` / 实例 `sequentialFunctor_initial`

English:
instance sequentialFunctor_initial
  signature: : (sequentialFunctor J).Initial where
  body: by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ <= d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : (unop i.left) <= (unop j.left)
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category* J] [IsCofiltered J] :
    exists (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

中文:
实例 sequentialFunctor_initial
  签名: : (sequentialFunctor J).初始 where
  定义体: by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ <= d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : (unop i.left) <= (unop j.left)
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category* J] [IsCofiltered J] :
    exists (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, List.getLast_cons, List.getLast_singleton, List.isChain_cons_cons, List.isChain_singleton, Nonempty, and_true, getLast_cons, getLast_singleton, homOfLE, i.left, isChain_cons_cons, isChain_singleton, isConnected_of_zigzag, j.left, ne_eq, not_false_eq_true, or_comm, reduceCtorEq
-/
instance sequentialFunctor_initial : (sequentialFunctor J).Initial where
  out d := by
    obtain ⟨n, (g : (sequentialFunctor J).obj ⟨n⟩ <= d)⟩ := sequentialFunctor_initial_aux J d
    have : Nonempty (CostructuredArrow (sequentialFunctor J) d) :=
      ⟨CostructuredArrow.mk (homOfLE g)⟩
    apply isConnected_of_zigzag
    refine fun i j => ⟨[j], ?_⟩
    simp only [List.isChain_cons_cons, Zag, List.isChain_singleton, and_true, ne_eq,
      not_false_eq_true, List.getLast_cons, List.getLast_singleton', reduceCtorEq]
    clear! C
    wlog! h : (unop i.left) <= (unop j.left)
    · exact or_comm.1 (this J d n g inferInstance j i (le_of_lt h))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

@[stacks 0032]
proof_wanted preorder_of_cofiltered (J : Type*) [Category* J] [IsCofiltered J] :
    exists (I : Type*) (_ : Preorder I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
The proof of `preorder_of_cofiltered` should give a countable `I` in the case that `J` is a
countable category.
-/
proof_wanted preorder_of_cofiltered_countable
    (J : Type*) [SmallCategory J] [IsCofiltered J] [CountableCategory J] :
    exists (I : Type) (_ : Preorder I) (_ : Countable I) (_ : IsCofiltered I) (F : I ⥤ J), F.Initial

/--
Put together `sequentialFunctor_initial` and `preorder_of_cofiltered_countable`.
-/
proof_wanted hasCofilteredCountableLimits_of_hasSequentialLimits [HasLimitsOfShape Natᵒᵖ C] :
    forall (J : Type) [SmallCategory J] [IsCofiltered J] [CountableCategory J], HasLimitsOfShape J C

/--
This is the countable version of `CategoryTheory.Limits.has_limits_of_finite_and_cofiltered`, given
all of the above.
-/
proof_wanted hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits [HasFiniteLimits C]
  [HasLimitsOfShape Natᵒᵖ C] : HasCountableLimits C

/--
For this we need to dualize this whole section.
-/
proof_wanted hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits
  [HasFiniteColimits C] [HasLimitsOfShape Nat C] : HasCountableColimits C

end IsCofiltered

end Preorder

end CategoryTheory.Limits
