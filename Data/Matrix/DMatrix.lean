/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# Dependent-typed matrices
-/

@[expose] public section


universe u u' v w z

/--
Definition of `DMatrix` / `DMatrix` 的定义

English:
definition DMatrix
  signature: (m : Type u) (n : Type u') (α : m -> n -> Type v)
  body: forall i j, α i j

中文:
定义 DMatrix
  签名: (m : 类型u) (n : 类型u') (α : m -> n -> 类型v)
  定义体: forall i j, α i j
-/
def DMatrix (m : Type u) (n : Type u') (α : m -> n -> Type v) : Type max u u' v :=
  forall i j, α i j

variable {m n : Type*}
variable {α : m -> n -> Type v}

namespace DMatrix

section Ext

variable {M N : DMatrix m n α}

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  statement: (forall i j, M i j = N i j) ↔ M = N
  proof: ⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]

中文:
定理 ext_iff
  结论: (对任意 i j, M i j = N i j) ↔ M = N
  证明: ⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]
-/
theorem ext_iff : (forall i j, M i j = N i j) ↔ M = N :=
⟨fun h => funext fun i => funext h i, fun h => by simp [h]⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: (forall i j, M i j = N i j) -> M = N
  proof: ext_iff.mp

中文:
定理 ext
  结论: (对任意 i j, M i j = N i j) -> M = N
  证明: ext_iff.mp

Depends on / 依赖: ext_iff, ext_iff.mp
-/
theorem ext : (forall i j, M i j = N i j) -> M = N :=
  ext_iff.mp

end Ext

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (M : DMatrix m n α) {β : m -> n -> Type w} (f : forall ⦃i j⦄, α i j -> β i j)
  body: fun i j => f (M i j)

@[simp]

中文:
定义 map
  签名: (M : DMatrix m n α) {β : m -> n -> Type w} (f : 对任意 ⦃i j⦄, α i j -> β i j)
  定义体: fun i j => f (M i j)

@[simp]
-/
def map (M : DMatrix m n α) {β : m -> n -> Type w} (f : forall ⦃i j⦄, α i j -> β i j) : DMatrix m n β :=
  fun i j => f (M i j)

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  statement: {M : DMatrix m n α} {β : m -> n -> Type w} {f : forall ⦃i j⦄, α i j -> β i j} {i : m}
  proof: rfl

@[simp]

中文:
定理 map_apply
  结论: {M : DMatrix m n α} {β : m -> n -> Type w} {f : 对任意 ⦃i j⦄, α i j -> β i j} {i : m}
  证明: rfl

@[simp]
-/
theorem map_apply {M : DMatrix m n α} {β : m -> n -> Type w} {f : forall ⦃i j⦄, α i j -> β i j} {i : m}
    {j : n} : M.map f i j = f (M i j) := rfl

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {M : DMatrix m n α} {β : m -> n -> Type w} {γ : m -> n -> Type z}
  proof: by ext; simp

中文:
定理 map_map
  结论: {M : DMatrix m n α} {β : m -> n -> Type w} {γ : m -> n -> Type z}
  证明: by ext; simp
-/
theorem map_map {M : DMatrix m n α} {β : m -> n -> Type w} {γ : m -> n -> Type z}
    {f : forall ⦃i j⦄, α i j -> β i j} {g : forall ⦃i j⦄, β i j -> γ i j} :
    (M.map f).map g = M.map fun _ _ x => g (f x) := by ext; simp

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (M : DMatrix m n α)

中文:
定义 transpose
  签名: (M : DMatrix m n α)
-/
def transpose (M : DMatrix m n α) : DMatrix n m fun j i => α i j
  | x, y => M y x

@[inherit_doc]
scoped postfix:1024 "ᵀ" => DMatrix.transpose

/--
Definition of `col` / `col` 的定义

English:
definition col
  signature: {α : m -> Type v} (w : forall i, α i)

中文:
定义 col
  签名: {α : m -> 类型v} (w : 对任意 i, α i)
-/
def col {α : m -> Type v} (w : forall i, α i) : DMatrix m Unit fun i _j => α i
  | x, _y => w x

/--
Definition of `row` / `row` 的定义

English:
definition row
  signature: {α : n -> Type v} (v : forall j, α j)

中文:
定义 row
  签名: {α : n -> 类型v} (v : 对任意 j, α j)
-/
def row {α : n -> Type v} (v : forall j, α j) : DMatrix Unit n fun _i j => α j
  | _x, y => v y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Inhabited (α i j)] : Inhabited (DMatrix m n α)
  body: inferInstanceAs Inhabited forall i j, α i j

中文:
实例 [forall
  签名: i j, Inhabited (α i j)] : Inhabited (DMatrix m n α)
  定义体: inferInstanceAs Inhabited forall i j, α i j

Depends on / 依赖: Inhabited
-/
instance [forall i j, Inhabited (α i j)] : Inhabited (DMatrix m n α) :=
inferInstanceAs Inhabited forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Add (α i j)] : Add (DMatrix m n α)
  body: inferInstanceAs Add forall i j, α i j

中文:
实例 [forall
  签名: i j, Add (α i j)] : Add (DMatrix m n α)
  定义体: inferInstanceAs Add forall i j, α i j
-/
instance [forall i j, Add (α i j)] : Add (DMatrix m n α) :=
inferInstanceAs Add forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α)
  body: inferInstanceAs AddSemigroup forall i j, α i j

中文:
实例 [forall
  签名: i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α)
  定义体: inferInstanceAs AddSemigroup forall i j, α i j

Depends on / 依赖: AddSemigroup
-/
instance [forall i j, AddSemigroup (α i j)] : AddSemigroup (DMatrix m n α) :=
inferInstanceAs AddSemigroup forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α)
  body: inferInstanceAs AddCommSemigroup forall i j, α i j

中文:
实例 [forall
  签名: i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α)
  定义体: inferInstanceAs AddCommSemigroup forall i j, α i j

Depends on / 依赖: AddCommSemigroup
-/
instance [forall i j, AddCommSemigroup (α i j)] : AddCommSemigroup (DMatrix m n α) :=
inferInstanceAs AddCommSemigroup forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Zero (α i j)] : Zero (DMatrix m n α)
  body: inferInstanceAs Zero forall i j, α i j

中文:
实例 [forall
  签名: i j, Zero (α i j)] : Zero (DMatrix m n α)
  定义体: inferInstanceAs Zero forall i j, α i j
-/
instance [forall i j, Zero (α i j)] : Zero (DMatrix m n α) :=
inferInstanceAs Zero forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α)
  body: inferInstanceAs AddMonoid forall i j, α i j

中文:
实例 [forall
  签名: i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α)
  定义体: inferInstanceAs AddMonoid forall i j, α i j

Depends on / 依赖: AddMonoid
-/
instance [forall i j, AddMonoid (α i j)] : AddMonoid (DMatrix m n α) :=
inferInstanceAs AddMonoid forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α)
  body: inferInstanceAs AddCommMonoid forall i j, α i j

中文:
实例 [forall
  签名: i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α)
  定义体: inferInstanceAs AddCommMonoid forall i j, α i j

Depends on / 依赖: AddCommMonoid
-/
instance [forall i j, AddCommMonoid (α i j)] : AddCommMonoid (DMatrix m n α) :=
inferInstanceAs AddCommMonoid forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Neg (α i j)] : Neg (DMatrix m n α)
  body: inferInstanceAs Neg forall i j, α i j

中文:
实例 [forall
  签名: i j, Neg (α i j)] : Neg (DMatrix m n α)
  定义体: inferInstanceAs Neg forall i j, α i j
-/
instance [forall i j, Neg (α i j)] : Neg (DMatrix m n α) :=
inferInstanceAs Neg forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Sub (α i j)] : Sub (DMatrix m n α)
  body: inferInstanceAs Sub forall i j, α i j

中文:
实例 [forall
  签名: i j, Sub (α i j)] : Sub (DMatrix m n α)
  定义体: inferInstanceAs Sub forall i j, α i j
-/
instance [forall i j, Sub (α i j)] : Sub (DMatrix m n α) :=
inferInstanceAs Sub forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddGroup (α i j)] : AddGroup (DMatrix m n α)
  body: inferInstanceAs AddGroup forall i j, α i j

中文:
实例 [forall
  签名: i j, AddGroup (α i j)] : AddGroup (DMatrix m n α)
  定义体: inferInstanceAs AddGroup forall i j, α i j

Depends on / 依赖: AddGroup
-/
instance [forall i j, AddGroup (α i j)] : AddGroup (DMatrix m n α) :=
inferInstanceAs AddGroup forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α)
  body: inferInstanceAs AddCommGroup forall i j, α i j

中文:
实例 [forall
  签名: i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α)
  定义体: inferInstanceAs AddCommGroup forall i j, α i j

Depends on / 依赖: AddCommGroup
-/
instance [forall i j, AddCommGroup (α i j)] : AddCommGroup (DMatrix m n α) :=
inferInstanceAs AddCommGroup forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Unique (α i j)] : Unique (DMatrix m n α)
  body: inferInstanceAs Unique forall i j, α i j

中文:
实例 [forall
  签名: i j, Unique (α i j)] : Unique (DMatrix m n α)
  定义体: inferInstanceAs Unique forall i j, α i j

Depends on / 依赖: Unique
-/
instance [forall i j, Unique (α i j)] : Unique (DMatrix m n α) :=
inferInstanceAs Unique forall i j, α i j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α)
  body: inferInstanceAs Subsingleton forall i j, α i j

@[simp]

中文:
实例 [forall
  签名: i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α)
  定义体: inferInstanceAs Subsingleton forall i j, α i j

@[simp]

Depends on / 依赖: Subsingleton
-/
instance [forall i j, Subsingleton (α i j)] : Subsingleton (DMatrix m n α) :=
inferInstanceAs Subsingleton forall i j, α i j

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [forall i j, Zero (α i j)] (i j)
  statement: (0 : DMatrix m n α) i j = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: [对任意 i j, Zero (α i j)] (i j)
  结论: (0 : DMatrix m n α) i j = 0
  证明: rfl

@[simp]
-/
theorem zero_apply [forall i j, Zero (α i j)] (i j) : (0 : DMatrix m n α) i j = 0 := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [forall i j, Neg (α i j)] (M : DMatrix m n α) (i j)
  statement: (-M) i j = -M i j
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: [对任意 i j, Neg (α i j)] (M : DMatrix m n α) (i j)
  结论: (-M) i j = -M i j
  证明: rfl

@[simp]
-/
theorem neg_apply [forall i j, Neg (α i j)] (M : DMatrix m n α) (i j) : (-M) i j = -M i j := rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [forall i j, Add (α i j)] (M N : DMatrix m n α) (i j)
  statement: (M + N) i j = M i j + N i j
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: [对任意 i j, Add (α i j)] (M N : DMatrix m n α) (i j)
  结论: (M + N) i j = M i j + N i j
  证明: rfl

@[simp]
-/
theorem add_apply [forall i j, Add (α i j)] (M N : DMatrix m n α) (i j) : (M + N) i j = M i j + N i j :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: [forall i j, Sub (α i j)] (M N : DMatrix m n α) (i j)
  statement: (M - N) i j = M i j - N i j
  proof: rfl

@[simp]

中文:
定理 sub_apply
  条件: [对任意 i j, Sub (α i j)] (M N : DMatrix m n α) (i j)
  结论: (M - N) i j = M i j - N i j
  证明: rfl

@[simp]
-/
theorem sub_apply [forall i j, Sub (α i j)] (M N : DMatrix m n α) (i j) : (M - N) i j = M i j - N i j :=
  rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: [forall i j, Zero (α i j)] {β : m -> n -> Type w} [forall i j, Zero (β i j)]
  proof: by ext; simp [h]

中文:
定理 map_zero
  结论: [对任意 i j, Zero (α i j)] {β : m -> n -> Type w} [对任意 i j, Zero (β i j)]
  证明: by ext; simp [h]
-/
theorem map_zero [forall i j, Zero (α i j)] {β : m -> n -> Type w} [forall i j, Zero (β i j)]
    {f : forall ⦃i j⦄, α i j -> β i j} (h : forall i j, f (0 : α i j) = 0) :
    (0 : DMatrix m n α).map f = 0 := by ext; simp [h]

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w} [forall i j, AddMonoid (β i j)]
  proof: by
  ext; simp

中文:
定理 map_add
  结论: [对任意 i j, AddMonoid (α i j)] {β : m -> n -> Type w} [对任意 i j, AddMonoid (β i j)]
  证明: by
  ext; simp
-/
theorem map_add [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w} [forall i j, AddMonoid (β i j)]
    (f : forall ⦃i j⦄, α i j ->+ β i j) (M N : DMatrix m n α) :
    ((M + N).map fun i j => @f i j) = (M.map fun i j => @f i j) + N.map fun i j => @f i j := by
  ext; simp

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  statement: [forall i j, AddGroup (α i j)] {β : m -> n -> Type w} [forall i j, AddGroup (β i j)]
  proof: by
  ext; simp

中文:
定理 map_sub
  结论: [对任意 i j, AddGroup (α i j)] {β : m -> n -> Type w} [对任意 i j, AddGroup (β i j)]
  证明: by
  ext; simp
-/
theorem map_sub [forall i j, AddGroup (α i j)] {β : m -> n -> Type w} [forall i j, AddGroup (β i j)]
    (f : forall ⦃i j⦄, α i j ->+ β i j) (M N : DMatrix m n α) :
    ((M - N).map fun i j => @f i j) = (M.map fun i j => @f i j) - N.map fun i j => @f i j := by
  ext; simp

/--
Instance `subsingleton_of_empty_left` / 实例 `subsingleton_of_empty_left`

English:
instance subsingleton_of_empty_left
  signature: [IsEmpty m]
  body: ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

中文:
实例 subsingleton_of_empty_left
  签名: [IsEmpty m]
  定义体: ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

Depends on / 依赖: isEmptyElim
-/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

/--
Instance `subsingleton_of_empty_right` / 实例 `subsingleton_of_empty_right`

English:
instance subsingleton_of_empty_right
  signature: [IsEmpty n]
  body: ⟨fun M N => by ext i j; exact isEmptyElim j⟩

中文:
实例 subsingleton_of_empty_right
  签名: [IsEmpty n]
  定义体: ⟨fun M N => by ext i j; exact isEmptyElim j⟩

Depends on / 依赖: isEmptyElim
-/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (DMatrix m n α) :=
  ⟨fun M N => by ext i j; exact isEmptyElim j⟩

end DMatrix

/--
Definition of `AddMonoidHom.mapDMatrix` / `AddMonoidHom.mapDMatrix` 的定义

English:
definition AddMonoidHom.mapDMatrix
  signature: [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w}
  body: M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f

@[simp]

中文:
定义 AddMonoidHom.mapDMatrix
  签名: [对任意 i j, AddMonoid (α i j)] {β : m -> n -> Type w}
  定义体: M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f

@[simp]

Depends on / 依赖: M.map
-/
def AddMonoidHom.mapDMatrix [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w}
    [forall i j, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) : DMatrix m n α ->+ DMatrix m n β where
  toFun M := M.map fun i j => @f i j
  map_zero' := by simp
  map_add' := DMatrix.map_add f

@[simp]
/--
theorem `AddMonoidHom.mapDMatrix_apply` / 定理 `AddMonoidHom.mapDMatrix_apply`

English:
theorem AddMonoidHom.mapDMatrix_apply
  statement: [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w}
  proof: rfl

中文:
定理 AddMonoidHom.mapDMatrix_apply
  结论: [对任意 i j, AddMonoid (α i j)] {β : m -> n -> Type w}
  证明: rfl
-/
theorem AddMonoidHom.mapDMatrix_apply [forall i j, AddMonoid (α i j)] {β : m -> n -> Type w}
    [forall i j, AddMonoid (β i j)] (f : forall ⦃i j⦄, α i j ->+ β i j) (M : DMatrix m n α) :
    AddMonoidHom.mapDMatrix f M = M.map fun i j => @f i j := rfl
