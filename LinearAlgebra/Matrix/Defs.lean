/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin, Lu-Ming Zhang
-/
module

public import Mathlib.Algebra.Module.Pi
public import Batteries.Data.Fin.Lemmas
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matrices

This file defines basic properties of matrices up to the module structure.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `Matrix m n α`. For the typical approach of counting rows and columns,
`Matrix (Fin m) (Fin n) α` can be used.

## Main definitions

* `Matrix.transpose`: transpose of a matrix, turning rows into columns and vice versa
* `Matrix.submatrix`: take a submatrix by reindexing rows and columns
* `Matrix.module`: matrices are a module over the ring of entries
* `Set.matrix`: set of matrices with entries in a given set

## Notation

The scope `Matrix` gives the following notation:

* `ᵀ` for `Matrix.transpose`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.
-/

@[expose] public section

assert_not_exists Algebra TrivialStar

universe u u' v w

/-- `Matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
@[wikidata Q44337]
/--
Definition of `Matrix` / `Matrix` 的定义

English:
definition Matrix
  signature: (m : Type u) (n : Type u') (α : Type v)
  body: m -> n -> α

中文:
定义 矩阵
  签名: (m : 类型u) (n : 类型u') (α : 类型v)
  定义体: m -> n -> α
-/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m -> n -> α

variable {l m n o : Type*} {m' : o -> Type*} {n' : o -> Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

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
Definition of `of` / `of` 的定义

English:
definition of
  signature: : (m -> n -> α) ≃ Matrix m n α
  body: Equiv.refl _

@[simp]

中文:
定义 of
  签名: : (m -> n -> α) ≃ 矩阵 m n α
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def of : (m -> n -> α) ≃ Matrix m n α :=
  Equiv.refl _

@[simp]
/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  given: (f : m -> n -> α) (i j)
  statement: of f i j = f i j
  proof: rfl

@[simp]

中文:
定理 of_apply
  条件: (f : m -> n -> α) (i j)
  结论: of f i j = f i j
  证明: rfl

@[simp]
-/
theorem of_apply (f : m -> n -> α) (i j) : of f i j = f i j :=
  rfl

@[simp]
/--
theorem `of_symm_apply` / 定理 `of_symm_apply`

English:
theorem of_symm_apply
  given: (f : Matrix m n α) (i j)
  statement: of.symm f i j = f i j
  proof: rfl

中文:
定理 of_symm_apply
  条件: (f : 矩阵 m n α) (i j)
  结论: of.symm f i j = f i j
  证明: rfl
-/
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j :=
  rfl

/--
Definition of `ofArray` / `ofArray` 的定义

English:
definition ofArray
  signature: {m n : Nat} (A : Array R) (hA : A.size = m * n)
  body: fun i j => A[Fin.mkDivMod i j]

@[simp]

中文:
定义 ofArray
  签名: {m n : 自然数} (A : 数组 R) (hA : A.size = m * n)
  定义体: fun i j => A[Fin.mkDivMod i j]

@[simp]

Depends on / 依赖: Fin.mkDivMod, mkDivMod
-/
def ofArray {m n : Nat} (A : Array R) (hA : A.size = m * n) : Matrix (Fin m) (Fin n) R :=
  fun i j => A[Fin.mkDivMod i j]

@[simp]
/--
theorem `ofArray_apply` / 定理 `ofArray_apply`

English:
theorem ofArray_apply
  given: {m n : Nat} (A : Array R) (hA : A.size = m * n) (i : Fin m) (j : Fin n)
  proof: rfl

中文:
定理 ofArray_apply
  条件: {m n : 自然数} (A : 数组 R) (hA : A.size = m * n) (i : 有限集 m) (j : 有限集 n)
  证明: rfl
-/
theorem ofArray_apply {m n : Nat} (A : Array R) (hA : A.size = m * n) (i : Fin m) (j : Fin n) :
    ofArray A hA i j = A[Fin.mkDivMod i j] := rfl

/-- The matrix constructed from the row-major array of `A`'s entries is `A`. -/
@[simp]
/--
theorem `ofArray_ofFn` / 定理 `ofArray_ofFn`

English:
theorem ofArray_ofFn
  given: {m n : Nat} (A : Matrix (Fin m) (Fin n) R)
  proof: by
  ext i j
  rw [ofArray_apply]; rw [Fin.getElem_fin]; rw [Array.getElem_ofFn]; rw [Fin.divNat_mkDivMod]; rw [Fin.modNat_mkDivMod]

中文:
定理 ofArray_ofFn
  条件: {m n : 自然数} (A : 矩阵 (有限集 m) (有限集 n) R)
  证明: by
  ext i j
  rw [ofArray_apply]; rw [Fin.getElem_fin]; rw [Array.getElem_ofFn]; rw [Fin.divNat_mkDivMod]; rw [Fin.modNat_mkDivMod]

Depends on / 依赖: Array.getElem_ofFn, Fin.divNat_mkDivMod, Fin.getElem_fin, Fin.modNat_mkDivMod, divNat_mkDivMod, getElem_fin, getElem_ofFn, modNat_mkDivMod, ofArray_apply
-/
theorem ofArray_ofFn {m n : Nat} (A : Matrix (Fin m) (Fin n) R) :
    ofArray (.ofFn fun k : Fin (m * n) => A k.divNat k.modNat) Array.size_ofFn = A := by
  ext i j
  rw [ofArray_apply]; rw [Fin.getElem_fin]; rw [Array.getElem_ofFn]; rw [Fin.divNat_mkDivMod]; rw [Fin.modNat_mkDivMod]

/--
lemma `ofArray_eq_of_getD` / 引理 `ofArray_eq_of_getD`

English:
lemma ofArray_eq_of_getD
  given: [Zero R] {m n : Nat} (A : Array R) (hA : A.size = m * n)
  proof: by
  ext i j
  have : n * i.val + j.val < m * n := (Fin.mkDivMod i j).isLt
  simp [ofArray, hA, this]

中文:
引理 ofArray_eq_of_getD
  条件: [零 R] {m n : 自然数} (A : 数组 R) (hA : A.size = m * n)
  证明: by
  ext i j
  have : n * i.val + j.val < m * n := (Fin.mkDivMod i j).isLt
  simp [ofArray, hA, this]

Depends on / 依赖: Fin.mkDivMod, i.val, j.val, mkDivMod, ofArray
-/
lemma ofArray_eq_of_getD [Zero R] {m n : Nat} (A : Array R) (hA : A.size = m * n) :
    ofArray A hA = .of fun i j => A.getD (n * i.val + j.val) 0 := by
  ext i j
  have : n * i.val + j.val < m * n := (Fin.mkDivMod i j).isLt
  simp [ofArray, hA, this]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (M : Matrix m n α) (f : α -> β)
  body: of fun i j => f (M i j)

@[simp]

中文:
定义 map
  签名: (M : 矩阵 m n α) (f : α -> β)
  定义体: of fun i j => f (M i j)

@[simp]
-/
def map (M : Matrix m n α) (f : α -> β) : Matrix m n β :=
  of fun i j => f (M i j)

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {M : Matrix m n α} {f : α -> β} {i : m} {j : n}
  statement: M.map f i j = f (M i j)
  proof: rfl

@[simp]

中文:
定理 map_apply
  条件: {M : 矩阵 m n α} {f : α -> β} {i : m} {j : n}
  结论: M.map f i j = f (M i j)
  证明: rfl

@[simp]
-/
theorem map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (M : Matrix m n α)
  statement: M.map id = M
  proof: by
  ext
  rfl

@[simp]

中文:
定理 map_id
  条件: (M : 矩阵 m n α)
  结论: M.map id = M
  证明: by
  ext
  rfl

@[simp]
-/
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext
  rfl

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: (M : Matrix m n α)
  statement: M.map (·) = M
  proof: map_id M

@[simp]

中文:
定理 map_id'
  条件: (M : 矩阵 m n α)
  结论: M.map (·) = M
  证明: map_id M

@[simp]

Depends on / 依赖: map_id
-/
theorem map_id' (M : Matrix m n α) : M.map (·) = M := map_id M

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g : β -> γ}
  proof: by
  ext
  rfl

中文:
定理 map_map
  条件: {M : 矩阵 m n α} {β γ : 类型} {f : α -> β} {g : β -> γ}
  证明: by
  ext
  rfl
-/
theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g : β -> γ} :
    (M.map f).map g = M.map (g ∘ f) := by
  ext
  rfl

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (hf : Function.Injective f)
  proof: fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j

中文:
定理 map_injective
  条件: {f : α -> β} (hf : 函数.单射 f)
  证明: fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j
-/
theorem map_injective {f : α -> β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun _ _ h =>
ext fun i j => hf ext_iff.mpr h i j

/--
theorem `map_involutive` / 定理 `map_involutive`

English:
theorem map_involutive
  given: {f : α -> α} (hf : Function.Involutive f)
  proof: by intro; simp [hf]

中文:
定理 map_involutive
  条件: {f : α -> α} (hf : 函数.对合 f)
  证明: by intro; simp [hf]
-/
theorem map_involutive {f : α -> α} (hf : Function.Involutive f) :
    Function.Involutive fun M : Matrix m n α => M.map f := by intro; simp [hf]

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (M : Matrix m n α)
  body: of fun x y => M y x

中文:
定义 transpose
  签名: (M : 矩阵 m n α)
  定义体: of fun x y => M y x
-/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x

-- TODO: set as an equation lemma for `transpose`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `transpose_apply` / 定理 `transpose_apply`

English:
theorem transpose_apply
  given: (M : Matrix m n α) (i j)
  statement: transpose M i j = M j i
  proof: rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

中文:
定理 transpose_apply
  条件: (M : 矩阵 m n α) (i j)
  结论: transpose M i j = M j i
  证明: rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose
-/
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Inhabited α]
  body: inferInstanceAs Inhabited (m -> n -> α)

中文:
实例 inhabited
  签名: [可居 α]
  定义体: inferInstanceAs Inhabited (m -> n -> α)

Depends on / 依赖: Inhabited
-/
instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
inferInstanceAs Inhabited (m -> n -> α)

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: [Add α]
  body: inferInstanceAs Add (m -> n -> α)

中文:
实例 add
  签名: [加法 α]
  定义体: inferInstanceAs Add (m -> n -> α)
-/
instance add [Add α] : Add (Matrix m n α) :=
inferInstanceAs Add (m -> n -> α)

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul R α]
  body: fun i => a • b i

中文:
实例 smul
  签名: [标量乘法 R α]
  定义体: fun i => a • b i
-/
instance smul [SMul R α] : SMul R (Matrix m n α) where
  smul a b := fun i => a • b i

/--
Instance `addSemigroup` / 实例 `addSemigroup`

English:
instance addSemigroup
  signature: [AddSemigroup α]
  body: inferInstanceAs AddSemigroup (m -> n -> α)

中文:
实例 addSemigroup
  签名: [加法半群 α]
  定义体: inferInstanceAs AddSemigroup (m -> n -> α)

Depends on / 依赖: AddSemigroup
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
inferInstanceAs AddSemigroup (m -> n -> α)

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: [AddCommSemigroup α]
  body: inferInstanceAs AddCommSemigroup (m -> n -> α)

中文:
实例 addCommSemigroup
  签名: [加法交换半群 α]
  定义体: inferInstanceAs AddCommSemigroup (m -> n -> α)

Depends on / 依赖: AddCommSemigroup
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
inferInstanceAs AddCommSemigroup (m -> n -> α)

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: [Zero α]
  body: inferInstanceAs Zero (m -> n -> α)

中文:
实例 zero
  签名: [零 α]
  定义体: inferInstanceAs Zero (m -> n -> α)
-/
instance zero [Zero α] : Zero (Matrix m n α) :=
inferInstanceAs Zero (m -> n -> α)

/--
Instance `addZeroClass` / 实例 `addZeroClass`

English:
instance addZeroClass
  signature: [AddZeroClass α]
  body: inferInstanceAs AddZeroClass (m -> n -> α)

中文:
实例 addZeroClass
  签名: [加法零类 α]
  定义体: inferInstanceAs AddZeroClass (m -> n -> α)

Depends on / 依赖: AddZeroClass
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
inferInstanceAs AddZeroClass (m -> n -> α)

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: [AddMonoid α]
  body: inferInstanceAs AddMonoid (m -> n -> α)

中文:
实例 addMonoid
  签名: [加法幺半群 α]
  定义体: inferInstanceAs AddMonoid (m -> n -> α)

Depends on / 依赖: AddMonoid
-/
instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) :=
inferInstanceAs AddMonoid (m -> n -> α)

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: [AddCommMonoid α]
  body: inferInstanceAs AddCommMonoid (m -> n -> α)

中文:
实例 addCommMonoid
  签名: [加法交换幺半群 α]
  定义体: inferInstanceAs AddCommMonoid (m -> n -> α)

Depends on / 依赖: AddCommMonoid
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
inferInstanceAs AddCommMonoid (m -> n -> α)

/--
Instance `neg` / 实例 `neg`

English:
instance neg
  signature: [Neg α]
  body: inferInstanceAs Neg (m -> n -> α)

中文:
实例 neg
  签名: [取负 α]
  定义体: inferInstanceAs Neg (m -> n -> α)
-/
instance neg [Neg α] : Neg (Matrix m n α) :=
inferInstanceAs Neg (m -> n -> α)

/--
Instance `involutiveNeg` / 实例 `involutiveNeg`

English:
instance involutiveNeg
  signature: [InvolutiveNeg α]
  body: inferInstanceAs InvolutiveNeg (m -> n -> α)

中文:
实例 involutiveNeg
  签名: [InvolutiveNeg α]
  定义体: inferInstanceAs InvolutiveNeg (m -> n -> α)

Depends on / 依赖: InvolutiveNeg
-/
instance involutiveNeg [InvolutiveNeg α] : InvolutiveNeg (Matrix m n α) :=
inferInstanceAs InvolutiveNeg (m -> n -> α)

/--
Instance `sub` / 实例 `sub`

English:
instance sub
  signature: [Sub α]
  body: inferInstanceAs Sub (m -> n -> α)

中文:
实例 sub
  签名: [减法 α]
  定义体: inferInstanceAs Sub (m -> n -> α)
-/
instance sub [Sub α] : Sub (Matrix m n α) :=
inferInstanceAs Sub (m -> n -> α)

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: [AddGroup α]
  body: inferInstanceAs AddGroup (m -> n -> α)

中文:
实例 addGroup
  签名: [加法群 α]
  定义体: inferInstanceAs AddGroup (m -> n -> α)

Depends on / 依赖: AddGroup
-/
instance addGroup [AddGroup α] : AddGroup (Matrix m n α) :=
inferInstanceAs AddGroup (m -> n -> α)

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: [AddCommGroup α]
  body: inferInstanceAs AddCommGroup (m -> n -> α)

中文:
实例 addCommGroup
  签名: [加法交换群 α]
  定义体: inferInstanceAs AddCommGroup (m -> n -> α)

Depends on / 依赖: AddCommGroup
-/
instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
inferInstanceAs AddCommGroup (m -> n -> α)

/--
Instance `unique` / 实例 `unique`

English:
instance unique
  signature: [Unique α]
  body: inferInstanceAs Unique (m -> n -> α)

中文:
实例 unique
  签名: [唯一 α]
  定义体: inferInstanceAs Unique (m -> n -> α)

Depends on / 依赖: Unique
-/
instance unique [Unique α] : Unique (Matrix m n α) :=
inferInstanceAs Unique (m -> n -> α)

/--
Instance `subsingleton` / 实例 `subsingleton`

English:
instance subsingleton
  signature: [Subsingleton α]
  body: inferInstanceAs Subsingleton m -> n -> α

中文:
实例 subsingleton
  签名: [子单例 α]
  定义体: inferInstanceAs Subsingleton m -> n -> α

Depends on / 依赖: Subsingleton
-/
instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
inferInstanceAs Subsingleton m -> n -> α

/--
Instance `nonempty` / 实例 `nonempty`

English:
instance nonempty
  signature: [Nonempty m] [Nonempty n] [Nontrivial α]
  body: Function.nontrivial

中文:
实例 nonempty
  签名: [非空 m] [非空 n] [非平凡 α]
  定义体: Function.nontrivial

Depends on / 依赖: Function, Function.nontrivial, nontrivial
-/
instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMul R α] [SMul S α] [SMulCommClass R S α]
  body: Pi.smulCommClass

中文:
实例 smulCommClass
  签名: [标量乘法 R α] [标量乘法 S α] [标量交换类 R S α]
  定义体: Pi.smulCommClass

Depends on / 依赖: Pi.smulCommClass, smulCommClass
-/
instance smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] :
    SMulCommClass R S (Matrix m n α) :=
  Pi.smulCommClass

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α]
  body: Pi.isScalarTower

中文:
实例 isScalarTower
  签名: [标量乘法 R S] [标量乘法 R α] [标量乘法 S α] [标量塔 R S α]
  定义体: Pi.isScalarTower

Depends on / 依赖: Pi.isScalarTower, isScalarTower
-/
instance isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] :
    IsScalarTower R S (Matrix m n α) :=
  Pi.isScalarTower

/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α]
  body: Pi.isCentralScalar

中文:
实例 isCentralScalar
  签名: [标量乘法 R α] [标量乘法 Rᵐᵒᵖ α] [中心标量 R α]
  定义体: Pi.isCentralScalar

Depends on / 依赖: Pi.isCentralScalar, isCentralScalar
-/
instance isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] :
    IsCentralScalar R (Matrix m n α) :=
  Pi.isCentralScalar

/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: [Monoid R] [MulAction R α]
  body: inferInstanceAs MulAction R (m -> n -> α)

中文:
实例 mulAction
  签名: [幺半群 R] [乘法作用 R α]
  定义体: inferInstanceAs MulAction R (m -> n -> α)

Depends on / 依赖: MulAction
-/
instance mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
inferInstanceAs MulAction R (m -> n -> α)

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: [Monoid R] [AddMonoid α] [DistribMulAction R α]
  body: inferInstanceAs DistribMulAction R (m -> n -> α)

中文:
实例 distribMulAction
  签名: [幺半群 R] [加法幺半群 α] [分配乘法作用 R α]
  定义体: inferInstanceAs DistribMulAction R (m -> n -> α)

Depends on / 依赖: DistribMulAction
-/
instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Matrix m n α) :=
inferInstanceAs DistribMulAction R (m -> n -> α)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: [Semiring R] [AddCommMonoid α] [Module R α]
  body: inferInstanceAs Module R (m -> n -> α)

中文:
实例 module
  签名: [半环 R] [加法交换幺半群 α] [模 R α]
  定义体: inferInstanceAs Module R (m -> n -> α)

Depends on / 依赖: Module
-/
instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
inferInstanceAs Module R (m -> n -> α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsAddCommutative α] : IsAddCommutative Matrix m n α
  body: inferInstanceAs IsAddCommutative m -> n -> α

中文:
实例 [加法
  签名: α] [是加法交换 α] : 是加法交换 矩阵 m n α
  定义体: inferInstanceAs IsAddCommutative m -> n -> α

Depends on / 依赖: IsAddCommutative
-/
instance [Add α] [IsAddCommutative α] : IsAddCommutative Matrix m n α :=
inferInstanceAs IsAddCommutative m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMagma
  signature: α] : AddCommMagma Matrix m n α
  body: inferInstanceAs AddCommMagma m -> n -> α

中文:
实例 [加法交换原群
  签名: α] : 加法交换原群 矩阵 m n α
  定义体: inferInstanceAs AddCommMagma m -> n -> α

Depends on / 依赖: AddCommMagma
-/
instance [AddCommMagma α] : AddCommMagma Matrix m n α :=
inferInstanceAs AddCommMagma m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsLeftCancelAdd α] : IsLeftCancelAdd Matrix m n α
  body: inferInstanceAs IsLeftCancelAdd m -> n -> α

中文:
实例 [加法
  签名: α] [是左消去加法 α] : 是左消去加法 矩阵 m n α
  定义体: inferInstanceAs IsLeftCancelAdd m -> n -> α

Depends on / 依赖: IsLeftCancelAdd
-/
instance [Add α] [IsLeftCancelAdd α] : IsLeftCancelAdd Matrix m n α :=
inferInstanceAs IsLeftCancelAdd m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsRightCancelAdd α] : IsRightCancelAdd Matrix m n α
  body: inferInstanceAs IsRightCancelAdd m -> n -> α

中文:
实例 [加法
  签名: α] [是右消去加法 α] : 是右消去加法 矩阵 m n α
  定义体: inferInstanceAs IsRightCancelAdd m -> n -> α

Depends on / 依赖: IsRightCancelAdd
-/
instance [Add α] [IsRightCancelAdd α] : IsRightCancelAdd Matrix m n α :=
inferInstanceAs IsRightCancelAdd m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] [IsCancelAdd α] : IsCancelAdd Matrix m n α
  body: inferInstanceAs IsCancelAdd m -> n -> α

中文:
实例 [加法
  签名: α] [是消去加法 α] : 是消去加法 矩阵 m n α
  定义体: inferInstanceAs IsCancelAdd m -> n -> α

Depends on / 依赖: IsCancelAdd
-/
instance [Add α] [IsCancelAdd α] : IsCancelAdd Matrix m n α :=
inferInstanceAs IsCancelAdd m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddLeftCancelSemigroup
  signature: α] : AddLeftCancelSemigroup Matrix m n α
  body: inferInstanceAs AddLeftCancelSemigroup m -> n -> α

中文:
实例 [加法左消去半群
  签名: α] : 加法左消去半群 矩阵 m n α
  定义体: inferInstanceAs AddLeftCancelSemigroup m -> n -> α

Depends on / 依赖: AddLeftCancelSemigroup
-/
instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup Matrix m n α :=
inferInstanceAs AddLeftCancelSemigroup m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddRightCancelSemigroup
  signature: α] : AddRightCancelSemigroup Matrix m n α
  body: inferInstanceAs AddRightCancelSemigroup m -> n -> α

中文:
实例 [加法右消去半群
  签名: α] : 加法右消去半群 矩阵 m n α
  定义体: inferInstanceAs AddRightCancelSemigroup m -> n -> α

Depends on / 依赖: AddRightCancelSemigroup
-/
instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup Matrix m n α :=
inferInstanceAs AddRightCancelSemigroup m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddLeftCancelMonoid
  signature: α] : AddLeftCancelMonoid Matrix m n α
  body: inferInstanceAs AddLeftCancelMonoid m -> n -> α

中文:
实例 [加法左消去幺半群
  签名: α] : 加法左消去幺半群 矩阵 m n α
  定义体: inferInstanceAs AddLeftCancelMonoid m -> n -> α

Depends on / 依赖: AddLeftCancelMonoid
-/
instance [AddLeftCancelMonoid α] : AddLeftCancelMonoid Matrix m n α :=
inferInstanceAs AddLeftCancelMonoid m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddRightCancelMonoid
  signature: α] : AddRightCancelMonoid Matrix m n α
  body: inferInstanceAs AddRightCancelMonoid m -> n -> α

中文:
实例 [加法右消去幺半群
  签名: α] : 加法右消去幺半群 矩阵 m n α
  定义体: inferInstanceAs AddRightCancelMonoid m -> n -> α

Depends on / 依赖: AddRightCancelMonoid
-/
instance [AddRightCancelMonoid α] : AddRightCancelMonoid Matrix m n α :=
inferInstanceAs AddRightCancelMonoid m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCancelMonoid
  signature: α] : AddCancelMonoid Matrix m n α
  body: inferInstanceAs AddCancelMonoid m -> n -> α

中文:
实例 [加法消去幺半群
  签名: α] : 加法消去幺半群 矩阵 m n α
  定义体: inferInstanceAs AddCancelMonoid m -> n -> α

Depends on / 依赖: AddCancelMonoid
-/
instance [AddCancelMonoid α] : AddCancelMonoid Matrix m n α :=
inferInstanceAs AddCancelMonoid m -> n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCancelCommMonoid
  signature: α] : AddCancelCommMonoid Matrix m n α
  body: inferInstanceAs AddCancelCommMonoid m -> n -> α

中文:
实例 [加法消去交换幺半群
  签名: α] : 加法消去交换幺半群 矩阵 m n α
  定义体: inferInstanceAs AddCancelCommMonoid m -> n -> α

Depends on / 依赖: AddCancelCommMonoid
-/
instance [AddCancelCommMonoid α] : AddCancelCommMonoid Matrix m n α :=
inferInstanceAs AddCancelCommMonoid m -> n -> α

section

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: [Zero α] (i : m) (j : n)
  statement: (0 : Matrix m n α) i j = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: [零 α] (i : m) (j : n)
  结论: (0 : 矩阵 m n α) i j = 0
  证明: rfl

@[simp]
-/
theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 := rfl

@[simp]
/--
theorem `of_symm_zero` / 定理 `of_symm_zero`

English:
theorem of_symm_zero
  given: [Zero α]
  statement: of.symm (0 : Matrix m n α) = (0 : m -> n -> α)
  proof: rfl

@[simp]

中文:
定理 of_symm_zero
  条件: [零 α]
  结论: of.symm (0 : 矩阵 m n α) = (0 : m -> n -> α)
  证明: rfl

@[simp]
-/
theorem of_symm_zero [Zero α] : of.symm (0 : Matrix m n α) = (0 : m -> n -> α) := rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: [Add α] (A B : Matrix m n α) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: [加法 α] (A B : 矩阵 m n α) (i : m) (j : n)
  证明: rfl

@[simp]
-/
theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
    (A + B) i j = (A i j) + (B i j) := rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
定理 smul_apply
  条件: [标量乘法 β α] (r : β) (A : 矩阵 m n α) (i : m) (j : n)
  证明: rfl

@[simp]
-/
theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
    (r • A) i j = r • (A i j) := rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: [Sub α] (A B : Matrix m n α) (i : m) (j : n)
  proof: rfl

@[simp]

中文:
定理 sub_apply
  条件: [减法 α] (A B : 矩阵 m n α) (i : m) (j : n)
  证明: rfl

@[simp]
-/
theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
    (A - B) i j = (A i j) - (B i j) := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: [Neg α] (A : Matrix m n α) (i : m) (j : n)
  proof: rfl

中文:
定理 neg_apply
  条件: [取负 α] (A : 矩阵 m n α) (i : m) (j : n)
  证明: rfl
-/
theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
    (-A) i j = -(A i j) := rfl

/--
theorem `dite_apply` / 定理 `dite_apply`

English:
theorem dite_apply
  statement: (P : Prop) [Decidable P]
  proof: by
  by_cases h : P <;> simp [h]

中文:
定理 dite_apply
  结论: (P : 命题) [可判定 P]
  证明: by
  by_cases h : P <;> simp [h]
-/
protected theorem dite_apply (P : Prop) [Decidable P]
    (A : P -> Matrix m n α) (B : ¬P -> Matrix m n α) (i : m) (j : n) :
    dite P A B i j = dite P (A · i j) (B · i j) := by
  by_cases h : P <;> simp [h]

/--
theorem `ite_apply` / 定理 `ite_apply`

English:
theorem ite_apply
  statement: (P : Prop) [Decidable P]
  proof: Matrix.dite_apply _ _ _ _ _

中文:
定理 ite_apply
  结论: (P : 命题) [可判定 P]
  证明: Matrix.dite_apply _ _ _ _ _
-/
protected theorem ite_apply (P : Prop) [Decidable P]
    (A : Matrix m n α) (B : Matrix m n α) (i : m) (j : n) :
    (if P then A else B) i j = if P then A i j else B i j :=
  Matrix.dite_apply _ _ _ _ _

end

/-! simp-normal form pulls `of` to the outside. -/

@[simp]
/--
theorem `of_zero` / 定理 `of_zero`

English:
theorem of_zero
  given: [Zero α]
  statement: of (0 : m -> n -> α) = 0
  proof: rfl

@[simp]

中文:
定理 of_zero
  条件: [零 α]
  结论: of (0 : m -> n -> α) = 0
  证明: rfl

@[simp]
-/
theorem of_zero [Zero α] : of (0 : m -> n -> α) = 0 :=
  rfl

@[simp]
/--
theorem `of_add_of` / 定理 `of_add_of`

English:
theorem of_add_of
  given: [Add α] (f g : m -> n -> α)
  statement: of f + of g = of (f + g)
  proof: rfl

@[simp]

中文:
定理 of_add_of
  条件: [加法 α] (f g : m -> n -> α)
  结论: of f + of g = of (f + g)
  证明: rfl

@[simp]
-/
theorem of_add_of [Add α] (f g : m -> n -> α) : of f + of g = of (f + g) :=
  rfl

@[simp]
/--
theorem `of_sub_of` / 定理 `of_sub_of`

English:
theorem of_sub_of
  given: [Sub α] (f g : m -> n -> α)
  statement: of f - of g = of (f - g)
  proof: rfl

@[simp]

中文:
定理 of_sub_of
  条件: [减法 α] (f g : m -> n -> α)
  结论: of f - of g = of (f - g)
  证明: rfl

@[simp]
-/
theorem of_sub_of [Sub α] (f g : m -> n -> α) : of f - of g = of (f - g) :=
  rfl

@[simp]
/--
theorem `neg_of` / 定理 `neg_of`

English:
theorem neg_of
  given: [Neg α] (f : m -> n -> α)
  statement: -of f = of (-f)
  proof: rfl

@[simp]

中文:
定理 neg_of
  条件: [取负 α] (f : m -> n -> α)
  结论: -of f = of (-f)
  证明: rfl

@[simp]
-/
theorem neg_of [Neg α] (f : m -> n -> α) : -of f = of (-f) :=
  rfl

@[simp]
/--
theorem `smul_of` / 定理 `smul_of`

English:
theorem smul_of
  given: [SMul R α] (r : R) (f : m -> n -> α)
  statement: r • of f = of (r • f)
  proof: rfl

@[simp]

中文:
定理 smul_of
  条件: [标量乘法 R α] (r : R) (f : m -> n -> α)
  结论: r • of f = of (r • f)
  证明: rfl

@[simp]
-/
theorem smul_of [SMul R α] (r : R) (f : m -> n -> α) : r • of f = of (r • f) :=
  rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: [Zero α] [Zero β] (f : α -> β) (h : f 0 = 0)
  proof: by
  ext
  simp [h]

中文:
定理 map_zero
  条件: [零 α] [零 β] (f : α -> β) (h : f 0 = 0)
  证明: by
  ext
  simp [h]
-/
protected theorem map_zero [Zero α] [Zero β] (f : α -> β) (h : f 0 = 0) :
    (0 : Matrix m n α).map f = 0 := by
  ext
  simp [h]

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: [Add α] [Add β] (f : α -> β) (hf : forall a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
  proof: ext fun _ _ => hf _ _

中文:
定理 map_add
  结论: [加法 α] [加法 β] (f : α -> β) (hf : 对任意 a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
  证明: ext fun _ _ => hf _ _
-/
protected theorem map_add [Add α] [Add β] (f : α -> β) (hf : forall a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
    (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  statement: [Neg α] [Neg β] (f : α -> β) (hf : forall a, f (-a) = -f a)
  proof: ext fun _ _ => hf _

中文:
定理 map_neg
  结论: [取负 α] [取负 β] (f : α -> β) (hf : 对任意 a, f (-a) = -f a)
  证明: ext fun _ _ => hf _
-/
protected theorem map_neg [Neg α] [Neg β] (f : α -> β) (hf : forall a, f (-a) = -f a)
    (M : Matrix m n α) : (-M).map f = -(M.map f) :=
  ext fun _ _ => hf _

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  statement: [Sub α] [Sub β] (f : α -> β) (hf : forall a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
  proof: ext fun _ _ => hf _ _

中文:
定理 map_sub
  结论: [减法 α] [减法 β] (f : α -> β) (hf : 对任意 a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
  证明: ext fun _ _ => hf _ _
-/
protected theorem map_sub [Sub α] [Sub β] (f : α -> β) (hf : forall a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: [SMul R α] [SMul R β] (f : α -> β) (r : R) (hf : forall a, f (r • a) = r • f a)
  proof: ext fun _ _ => hf _

中文:
定理 map_smul
  结论: [标量乘法 R α] [标量乘法 R β] (f : α -> β) (r : R) (hf : 对任意 a, f (r • a) = r • f a)
  证明: ext fun _ _ => hf _
-/
protected theorem map_smul [SMul R α] [SMul R β] (f : α -> β) (r : R) (hf : forall a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  statement: [SMul R α] [SMul S β] (f : α -> β) (σ : R -> S) (r : R)
  proof: ext fun _ _ => hf _

中文:
定理 map_smulₛₗ
  结论: [标量乘法 R α] [标量乘法 S β] (f : α -> β) (σ : R -> S) (r : R)
  证明: ext fun _ _ => hf _
-/
protected theorem map_smulₛₗ [SMul R α] [SMul S β] (f : α -> β) (σ : R -> S) (r : R)
    (hf : forall a, f (r • a) = σ r • f a)
    (M : Matrix m n α) : (r • M).map f = σ r • M.map f :=
  ext fun _ _ => hf _

/--
theorem `map_smul'` / 定理 `map_smul'`

English:
theorem map_smul'
  statement: [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α)
  proof: ext fun _ _ => hf _ _

中文:
定理 map_smul'
  结论: [乘法 α] [乘法 β] (f : α -> β) (r : α) (A : 矩阵 n n α)
  证明: ext fun _ _ => hf _ _
-/
theorem map_smul' [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α)
    (hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f :=
  ext fun _ _ => hf _ _

/--
theorem `map_op_smul'` / 定理 `map_op_smul'`

English:
theorem map_op_smul'
  statement: [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α)
  proof: ext fun _ _ => hf _ _

中文:
定理 map_op_smul'
  结论: [乘法 α] [乘法 β] (f : α -> β) (r : α) (A : 矩阵 n n α)
  证明: ext fun _ _ => hf _ _
-/
theorem map_op_smul' [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α)
    (hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
    (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f :=
  ext fun _ _ => hf _ _

/--
theorem `_root_.IsSMulRegular.matrix` / 定理 `_root_.IsSMulRegular.matrix`

English:
theorem _root_.IsSMulRegular.matrix
  given: [SMul R S] {k : R} (hk : IsSMulRegular S k)
  proof: IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

中文:
定理 _root_.IsSMulRegular.matrix
  条件: [标量乘法 R S] {k : R} (hk : IsSMulRegular S k)
  证明: IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

Depends on / 依赖: IsSMulRegular, IsSMulRegular.pi
-/
theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) :
    IsSMulRegular (Matrix m n S) k :=
  IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk

/--
theorem `_root_.IsLeftRegular.matrix` / 定理 `_root_.IsLeftRegular.matrix`

English:
theorem _root_.IsLeftRegular.matrix
  given: [Mul α] {k : α} (hk : IsLeftRegular k)
  proof: hk.isSMulRegular.matrix

中文:
定理 _root_.IsLeftRegular.matrix
  条件: [乘法 α] {k : α} (hk : IsLeftRegular k)
  证明: hk.isSMulRegular.matrix

Depends on / 依赖: hk.isSMulRegular.matrix, isSMulRegular, matrix
-/
theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) :
    IsSMulRegular (Matrix m n α) k :=
  hk.isSMulRegular.matrix

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
  签名: [是空 m]
  定义体: ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

Depends on / 依赖: isEmptyElim
-/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩

/--
Instance `subsingleton_of_empty_right` / 实例 `subsingleton_of_empty_right`

English:
instance subsingleton_of_empty_right
  signature: [IsEmpty n]
  body: ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩

中文:
实例 subsingleton_of_empty_right
  签名: [是空 n]
  定义体: ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩

Depends on / 依赖: isEmptyElim
-/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩

/--
Definition of `ofAddEquiv` / `ofAddEquiv` 的定义

English:
definition ofAddEquiv
  signature: [Add α]
  body: of
  map_add' _ _ := rfl

中文:
定义 ofAddEquiv
  签名: [加法 α]
  定义体: of
  map_add' _ _ := rfl
-/
def ofAddEquiv [Add α] : (m -> n -> α) ≃+ Matrix m n α where
  __ := of
  map_add' _ _ := rfl

/--
lemma `coe_ofAddEquiv` / 引理 `coe_ofAddEquiv`

English:
lemma coe_ofAddEquiv
  given: [Add α]
  proof: rfl

中文:
引理 coe_ofAddEquiv
  条件: [加法 α]
  证明: rfl
-/
@[simp] lemma coe_ofAddEquiv [Add α] :
    ⇑(ofAddEquiv : (m -> n -> α) ≃+ Matrix m n α) = of := rfl
/--
lemma `coe_ofAddEquiv_symm` / 引理 `coe_ofAddEquiv_symm`

English:
lemma coe_ofAddEquiv_symm
  given: [Add α]
  proof: rfl

中文:
引理 coe_ofAddEquiv_symm
  条件: [加法 α]
  证明: rfl
-/
@[simp] lemma coe_ofAddEquiv_symm [Add α] :
    ⇑(ofAddEquiv.symm : Matrix m n α ≃+ (m -> n -> α)) = of.symm := rfl

/--
lemma `isAddUnit_iff` / 引理 `isAddUnit_iff`

English:
lemma isAddUnit_iff
  given: [AddMonoid α] {A : Matrix m n α}
  proof: by
  simp_rw [isAddUnit_iff_exists, Classical.skolem, forall_and,
    ← Matrix.ext_iff, add_apply, zero_apply]
  rfl

中文:
引理 isAddUnit_iff
  条件: [加法幺半群 α] {A : 矩阵 m n α}
  证明: by
  simp_rw [isAddUnit_iff_exists, Classical.skolem, forall_and,
    ← Matrix.ext_iff, add_apply, zero_apply]
  rfl
-/
@[simp] lemma isAddUnit_iff [AddMonoid α] {A : Matrix m n α} :
    IsAddUnit A ↔ forall i j, IsAddUnit (A i j) := by
  simp_rw [isAddUnit_iff_exists, Classical.skolem, forall_and,
    ← Matrix.ext_iff, add_apply, zero_apply]
  rfl

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
/--
theorem `transpose_transpose` / 定理 `transpose_transpose`

English:
theorem transpose_transpose
  given: (M : Matrix m n α)
  statement: Mᵀᵀ = M
  proof: by
  ext
  rfl

中文:
定理 transpose_transpose
  条件: (M : 矩阵 m n α)
  结论: Mᵀᵀ = M
  证明: by
  ext
  rfl
-/
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

variable (n α) in
/--
theorem `transpose_involutive` / 定理 `transpose_involutive`

English:
theorem transpose_involutive
  statement: (transpose : Matrix n n α -> Matrix n n α).Involutive
  proof: transpose_transpose

中文:
定理 transpose_involutive
  结论: (transpose : 矩阵 n n α -> 矩阵 n n α).对合
  证明: transpose_transpose

Depends on / 依赖: transpose_transpose
-/
theorem transpose_involutive : (transpose : Matrix n n α -> Matrix n n α).Involutive :=
  transpose_transpose

/--
theorem `transpose_injective` / 定理 `transpose_injective`

English:
theorem transpose_injective
  statement: Function.Injective (transpose : Matrix m n α -> Matrix n m α)
  proof: fun _ _ h => ext fun i j => ext_iff.2 h j i

中文:
定理 transpose_injective
  结论: 函数.单射 (transpose : 矩阵 m n α -> 矩阵 n m α)
  证明: fun _ _ h => ext fun i j => ext_iff.2 h j i

Depends on / 依赖: ext_iff
-/
theorem transpose_injective : Function.Injective (transpose : Matrix m n α -> Matrix n m α) :=
  fun _ _ h => ext fun i j => ext_iff.2 h j i

/--
theorem `transpose_inj` / 定理 `transpose_inj`

English:
theorem transpose_inj
  given: {A B : Matrix m n α}
  statement: Aᵀ = Bᵀ ↔ A = B
  proof: transpose_injective.eq_iff

@[simp]

中文:
定理 transpose_inj
  条件: {A B : 矩阵 m n α}
  结论: Aᵀ = Bᵀ ↔ A = B
  证明: transpose_injective.eq_iff

@[simp]
-/
@[simp] theorem transpose_inj {A B : Matrix m n α} : Aᵀ = Bᵀ ↔ A = B := transpose_injective.eq_iff

@[simp]
/--
theorem `transpose_zero` / 定理 `transpose_zero`

English:
theorem transpose_zero
  given: [Zero α]
  statement: (0 : Matrix m n α)ᵀ = 0
  proof: rfl

@[simp]

中文:
定理 transpose_zero
  条件: [零 α]
  结论: (0 : 矩阵 m n α)ᵀ = 0
  证明: rfl

@[simp]
-/
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := rfl

@[simp]
/--
theorem `transpose_eq_zero` / 定理 `transpose_eq_zero`

English:
theorem transpose_eq_zero
  given: [Zero α] {M : Matrix m n α}
  statement: Mᵀ = 0 ↔ M = 0
  proof: transpose_inj

@[simp]

中文:
定理 transpose_eq_zero
  条件: [零 α] {M : 矩阵 m n α}
  结论: Mᵀ = 0 ↔ M = 0
  证明: transpose_inj

@[simp]

Depends on / 依赖: transpose_inj
-/
theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

@[simp]
/--
theorem `transpose_add` / 定理 `transpose_add`

English:
theorem transpose_add
  given: [Add α] (M : Matrix m n α) (N : Matrix m n α)
  statement: (M + N)ᵀ = Mᵀ + Nᵀ
  proof: by
  ext
  simp

@[simp]

中文:
定理 transpose_add
  条件: [加法 α] (M : 矩阵 m n α) (N : 矩阵 m n α)
  结论: (M + N)ᵀ = Mᵀ + Nᵀ
  证明: by
  ext
  simp

@[simp]
-/
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext
  simp

@[simp]
/--
theorem `transpose_sub` / 定理 `transpose_sub`

English:
theorem transpose_sub
  given: [Sub α] (M : Matrix m n α) (N : Matrix m n α)
  statement: (M - N)ᵀ = Mᵀ - Nᵀ
  proof: by
  ext
  simp

@[simp]

中文:
定理 transpose_sub
  条件: [减法 α] (M : 矩阵 m n α) (N : 矩阵 m n α)
  结论: (M - N)ᵀ = Mᵀ - Nᵀ
  证明: by
  ext
  simp

@[simp]
-/
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext
  simp

@[simp]
/--
theorem `transpose_smul` / 定理 `transpose_smul`

English:
theorem transpose_smul
  given: {R : Type*} [SMul R α] (c : R) (M : Matrix m n α)
  statement: (c • M)ᵀ = c • Mᵀ
  proof: rfl

@[simp]

中文:
定理 transpose_smul
  条件: {R : 类型} [标量乘法 R α] (c : R) (M : 矩阵 m n α)
  结论: (c • M)ᵀ = c • Mᵀ
  证明: rfl

@[simp]
-/
theorem transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ :=
  rfl

@[simp]
/--
theorem `transpose_neg` / 定理 `transpose_neg`

English:
theorem transpose_neg
  given: [Neg α] (M : Matrix m n α)
  statement: (-M)ᵀ = -Mᵀ
  proof: rfl

中文:
定理 transpose_neg
  条件: [取负 α] (M : 矩阵 m n α)
  结论: (-M)ᵀ = -Mᵀ
  证明: rfl
-/
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ :=
  rfl

/--
theorem `transpose_map` / 定理 `transpose_map`

English:
theorem transpose_map
  given: {f : α -> β} {M : Matrix m n α}
  statement: Mᵀ.map f = (M.map f)ᵀ
  proof: rfl

中文:
定理 transpose_map
  条件: {f : α -> β} {M : 矩阵 m n α}
  结论: Mᵀ.map f = (M.map f)ᵀ
  证明: rfl
-/
theorem transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
  rfl

end Transpose

/--
Definition of `submatrix` / `submatrix` 的定义

English:
definition submatrix
  signature: (A : Matrix m n α) (r : l -> m) (c : o -> n)
  body: of fun i j => A (r i) (c j)

@[simp]

中文:
定义 submatrix
  签名: (A : 矩阵 m n α) (r : l -> m) (c : o -> n)
  定义体: of fun i j => A (r i) (c j)

@[simp]
-/
def submatrix (A : Matrix m n α) (r : l -> m) (c : o -> n) : Matrix l o α :=
  of fun i j => A (r i) (c j)

@[simp]
/--
theorem `submatrix_apply` / 定理 `submatrix_apply`

English:
theorem submatrix_apply
  given: (A : Matrix m n α) (r : l -> m) (c : o -> n) (i j)
  proof: rfl

@[simp]

中文:
定理 submatrix_apply
  条件: (A : 矩阵 m n α) (r : l -> m) (c : o -> n) (i j)
  证明: rfl

@[simp]
-/
theorem submatrix_apply (A : Matrix m n α) (r : l -> m) (c : o -> n) (i j) :
    A.submatrix r c i j = A (r i) (c j) :=
  rfl

@[simp]
/--
theorem `submatrix_id_id` / 定理 `submatrix_id_id`

English:
theorem submatrix_id_id
  given: (A : Matrix m n α)
  statement: A.submatrix id id = A
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 submatrix_id_id
  条件: (A : 矩阵 m n α)
  结论: A.submatrix id id = A
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `submatrix_submatrix` / 定理 `submatrix_submatrix`

English:
theorem submatrix_submatrix
  statement: {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l -> m) (c₁ : o -> n)
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 submatrix_submatrix
  结论: {l₂ o₂ : 类型} (A : 矩阵 m n α) (r₁ : l -> m) (c₁ : o -> n)
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem submatrix_submatrix {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l -> m) (c₁ : o -> n)
    (r₂ : l₂ -> l) (c₂ : o₂ -> o) :
    (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `transpose_submatrix` / 定理 `transpose_submatrix`

English:
theorem transpose_submatrix
  given: (A : Matrix m n α) (r : l -> m) (c : o -> n)
  proof: ext fun _ _ => rfl

中文:
定理 transpose_submatrix
  条件: (A : 矩阵 m n α) (r : l -> m) (c : o -> n)
  证明: ext fun _ _ => rfl
-/
theorem transpose_submatrix (A : Matrix m n α) (r : l -> m) (c : o -> n) :
    (A.submatrix r c)ᵀ = Aᵀ.submatrix c r :=
  ext fun _ _ => rfl

/--
theorem `submatrix_add` / 定理 `submatrix_add`

English:
theorem submatrix_add
  given: [Add α] (A B : Matrix m n α)
  proof: rfl

中文:
定理 submatrix_add
  条件: [加法 α] (A B : 矩阵 m n α)
  证明: rfl
-/
theorem submatrix_add [Add α] (A B : Matrix m n α) :
    ((A + B).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = A.submatrix + B.submatrix :=
  rfl

/--
theorem `submatrix_neg` / 定理 `submatrix_neg`

English:
theorem submatrix_neg
  given: [Neg α] (A : Matrix m n α)
  proof: rfl

中文:
定理 submatrix_neg
  条件: [取负 α] (A : 矩阵 m n α)
  证明: rfl
-/
theorem submatrix_neg [Neg α] (A : Matrix m n α) :
    ((-A).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = -A.submatrix :=
  rfl

/--
theorem `submatrix_sub` / 定理 `submatrix_sub`

English:
theorem submatrix_sub
  given: [Sub α] (A B : Matrix m n α)
  proof: rfl

@[simp]

中文:
定理 submatrix_sub
  条件: [减法 α] (A B : 矩阵 m n α)
  证明: rfl

@[simp]
-/
theorem submatrix_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = A.submatrix - B.submatrix :=
  rfl

@[simp]
/--
theorem `submatrix_zero` / 定理 `submatrix_zero`

English:
theorem submatrix_zero
  given: [Zero α]
  proof: rfl

中文:
定理 submatrix_zero
  条件: [零 α]
  证明: rfl
-/
theorem submatrix_zero [Zero α] :
    ((0 : Matrix m n α).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = 0 :=
  rfl

/--
theorem `submatrix_smul` / 定理 `submatrix_smul`

English:
theorem submatrix_smul
  given: {R : Type*} [SMul R α] (r : R) (A : Matrix m n α)
  proof: rfl

中文:
定理 submatrix_smul
  条件: {R : 类型} [标量乘法 R α] (r : R) (A : 矩阵 m n α)
  证明: rfl
-/
theorem submatrix_smul {R : Type*} [SMul R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = r • A.submatrix :=
  rfl

/--
theorem `submatrix_map` / 定理 `submatrix_map`

English:
theorem submatrix_map
  given: (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : Matrix m n α)
  proof: rfl

中文:
定理 submatrix_map
  条件: (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : 矩阵 m n α)
  证明: rfl
-/
theorem submatrix_map (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : Matrix m n α) :
    (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f :=
  rfl

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (eₘ : m ≃ l) (eₙ : n ≃ o)
  body: M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp

@[simp]

中文:
定义 reindex
  签名: (eₘ : m ≃ l) (eₙ : n ≃ o)
  定义体: M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp

@[simp]

Depends on / 依赖: M.submatrix, submatrix
-/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where
  toFun M := M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp

@[simp]
/--
theorem `reindex_apply` / 定理 `reindex_apply`

English:
theorem reindex_apply
  given: (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α)
  proof: rfl

中文:
定理 reindex_apply
  条件: (eₘ : m ≃ l) (eₙ : n ≃ o) (M : 矩阵 m n α)
  证明: rfl
-/
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm :=
  rfl

/--
theorem `reindex_refl_refl` / 定理 `reindex_refl_refl`

English:
theorem reindex_refl_refl
  given: (A : Matrix m n α)
  statement: reindex (Equiv.refl _) (Equiv.refl _) A = A
  proof: A.submatrix_id_id

@[simp]

中文:
定理 reindex_refl_refl
  条件: (A : 矩阵 m n α)
  结论: reindex (等价.refl _) (等价.refl _) A = A
  证明: A.submatrix_id_id

@[simp]

Depends on / 依赖: A.submatrix_id_id, submatrix_id_id
-/
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl _) A = A :=
  A.submatrix_id_id

@[simp]
/--
theorem `reindex_symm` / 定理 `reindex_symm`

English:
theorem reindex_symm
  given: (eₘ : m ≃ l) (eₙ : n ≃ o)
  proof: rfl

@[simp]

中文:
定理 reindex_symm
  条件: (eₘ : m ≃ l) (eₙ : n ≃ o)
  证明: rfl

@[simp]
-/
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl

@[simp]
/--
theorem `reindex_trans` / 定理 `reindex_trans`

English:
theorem reindex_trans
  given: {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂)
  proof: Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)

中文:
定理 reindex_trans
  条件: {l₂ o₂ : 类型} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂)
  证明: Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)

Depends on / 依赖: A.submatrix_submatrix, Equiv.ext, submatrix_submatrix
-/
theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
      (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)

/--
theorem `transpose_reindex` / 定理 `transpose_reindex`

English:
theorem transpose_reindex
  given: (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α)
  proof: rfl

中文:
定理 transpose_reindex
  条件: (eₘ : m ≃ l) (eₙ : n ≃ o) (M : 矩阵 m n α)
  证明: rfl
-/
theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl

/--
Definition of `subLeft` / `subLeft` 的定义

English:
abbreviation subLeft
  signature: {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α)
  body: submatrix A id (Fin.castAdd r)

中文:
缩写 subLeft
  签名: {m l r : 自然数} (A : 矩阵 (有限集 m) (有限集 (l + r)) α)
  定义体: submatrix A id (Fin.castAdd r)

Depends on / 依赖: Fin.castAdd, castAdd, submatrix
-/
abbrev subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin l) α :=
  submatrix A id (Fin.castAdd r)

/--
Definition of `subRight` / `subRight` 的定义

English:
abbreviation subRight
  signature: {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α)
  body: submatrix A id (Fin.natAdd l)

中文:
缩写 subRight
  签名: {m l r : 自然数} (A : 矩阵 (有限集 m) (有限集 (l + r)) α)
  定义体: submatrix A id (Fin.natAdd l)

Depends on / 依赖: Fin.natAdd, natAdd, submatrix
-/
abbrev subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin r) α :=
  submatrix A id (Fin.natAdd l)

/--
Definition of `subUp` / `subUp` 的定义

English:
abbreviation subUp
  signature: {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α)
  body: submatrix A (Fin.castAdd d) id

中文:
缩写 subUp
  签名: {d u n : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 n) α)
  定义体: submatrix A (Fin.castAdd d) id

Depends on / 依赖: Fin.castAdd, castAdd, submatrix
-/
abbrev subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) (Fin n) α :=
  submatrix A (Fin.castAdd d) id

/--
Definition of `subDown` / `subDown` 的定义

English:
abbreviation subDown
  signature: {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α)
  body: submatrix A (Fin.natAdd u) id

中文:
缩写 subDown
  签名: {d u n : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 n) α)
  定义体: submatrix A (Fin.natAdd u) id

Depends on / 依赖: Fin.natAdd, natAdd, submatrix
-/
abbrev subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d) (Fin n) α :=
  submatrix A (Fin.natAdd u) id

/--
Definition of `subUpRight` / `subUpRight` 的定义

English:
abbreviation subUpRight
  signature: {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α)
  body: subUp (subRight A)

中文:
缩写 subUpRight
  签名: {d u l r : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 (l + r)) α)
  定义体: subUp (subRight A)

Depends on / 依赖: subRight
-/
abbrev subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin r) α :=
  subUp (subRight A)

/--
Definition of `subDownRight` / `subDownRight` 的定义

English:
abbreviation subDownRight
  signature: {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α)
  body: subDown (subRight A)

中文:
缩写 subDownRight
  签名: {d u l r : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 (l + r)) α)
  定义体: subDown (subRight A)

Depends on / 依赖: subDown, subRight
-/
abbrev subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)

/--
Definition of `subUpLeft` / `subUpLeft` 的定义

English:
abbreviation subUpLeft
  signature: {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α)
  body: subUp (subLeft A)

中文:
缩写 subUpLeft
  签名: {d u l r : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 (l + r)) α)
  定义体: subUp (subLeft A)

Depends on / 依赖: subLeft
-/
abbrev subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin l) α :=
  subUp (subLeft A)

/--
Definition of `subDownLeft` / `subDownLeft` 的定义

English:
abbreviation subDownLeft
  signature: {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α)
  body: subDown (subLeft A)

中文:
缩写 subDownLeft
  签名: {d u l r : 自然数} (A : 矩阵 (有限集 (u + d)) (有限集 (l + r)) α)
  定义体: subDown (subLeft A)

Depends on / 依赖: subDown, subLeft
-/
abbrev subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin l) α :=
  subDown (subLeft A)

section RowCol

/--
Definition of `row` / `row` 的定义

English:
definition row
  signature: (A : Matrix m n α)
  body: A

中文:
定义 row
  签名: (A : 矩阵 m n α)
  定义体: A
-/
def row (A : Matrix m n α) : m -> n -> α := A

/--
Definition of `col` / `col` 的定义

English:
definition col
  signature: (A : Matrix m n α)
  body: Aᵀ

中文:
定义 col
  签名: (A : 矩阵 m n α)
  定义体: Aᵀ
-/
def col (A : Matrix m n α) : n -> m -> α := Aᵀ

/--
lemma `row_eq_self` / 引理 `row_eq_self`

English:
lemma row_eq_self
  given: (A : Matrix m n α)
  statement: A.row = of.symm A
  proof: rfl

中文:
引理 row_eq_self
  条件: (A : 矩阵 m n α)
  结论: A.row = of.symm A
  证明: rfl
-/
lemma row_eq_self (A : Matrix m n α) : A.row = of.symm A := rfl

/--
lemma `col_eq_transpose` / 引理 `col_eq_transpose`

English:
lemma col_eq_transpose
  given: (A : Matrix m n α)
  statement: A.col = of.symm Aᵀ
  proof: rfl

@[simp]

中文:
引理 col_eq_transpose
  条件: (A : 矩阵 m n α)
  结论: A.col = of.symm Aᵀ
  证明: rfl

@[simp]
-/
lemma col_eq_transpose (A : Matrix m n α) : A.col = of.symm Aᵀ := rfl

@[simp]
/--
lemma `of_row` / 引理 `of_row`

English:
lemma of_row
  given: (f : m -> n -> α)
  statement: (Matrix.of f).row = f
  proof: rfl

@[simp]

中文:
引理 of_row
  条件: (f : m -> n -> α)
  结论: (矩阵.of f).row = f
  证明: rfl

@[simp]
-/
lemma of_row (f : m -> n -> α) : (Matrix.of f).row = f := rfl

@[simp]
/--
lemma `of_col` / 引理 `of_col`

English:
lemma of_col
  given: (f : m -> n -> α)
  statement: (Matrix.of f)ᵀ.col = f
  proof: rfl

中文:
引理 of_col
  条件: (f : m -> n -> α)
  结论: (矩阵.of f)ᵀ.col = f
  证明: rfl
-/
lemma of_col (f : m -> n -> α) : (Matrix.of f)ᵀ.col = f := rfl

/--
lemma `row_def` / 引理 `row_def`

English:
lemma row_def
  given: (A : Matrix m n α)
  statement: A.row = fun i => A i
  proof: rfl

中文:
引理 row_def
  条件: (A : 矩阵 m n α)
  结论: A.row = fun i => A i
  证明: rfl
-/
lemma row_def (A : Matrix m n α) : A.row = fun i => A i := rfl

/--
lemma `col_def` / 引理 `col_def`

English:
lemma col_def
  given: (A : Matrix m n α)
  statement: A.col = fun j => Aᵀ j
  proof: rfl

@[simp]

中文:
引理 col_def
  条件: (A : 矩阵 m n α)
  结论: A.col = fun j => Aᵀ j
  证明: rfl

@[simp]
-/
lemma col_def (A : Matrix m n α) : A.col = fun j => Aᵀ j := rfl

@[simp]
/--
lemma `row_apply` / 引理 `row_apply`

English:
lemma row_apply
  given: (A : Matrix m n α) (i : m) (j : n)
  statement: A.row i j = A i j
  proof: rfl

中文:
引理 row_apply
  条件: (A : 矩阵 m n α) (i : m) (j : n)
  结论: A.row i j = A i j
  证明: rfl
-/
lemma row_apply (A : Matrix m n α) (i : m) (j : n) : A.row i j = A i j := rfl

/--
lemma `row_apply'` / 引理 `row_apply'`

English:
lemma row_apply'
  given: (A : Matrix m n α) (i : m)
  statement: A.row i = A i
  proof: rfl

@[simp]

中文:
引理 row_apply'
  条件: (A : 矩阵 m n α) (i : m)
  结论: A.row i = A i
  证明: rfl

@[simp]
-/
lemma row_apply' (A : Matrix m n α) (i : m) : A.row i = A i := rfl

@[simp]
/--
lemma `col_apply` / 引理 `col_apply`

English:
lemma col_apply
  given: (A : Matrix m n α) (i : n) (j : m)
  statement: A.col i j = A j i
  proof: rfl

中文:
引理 col_apply
  条件: (A : 矩阵 m n α) (i : n) (j : m)
  结论: A.col i j = A j i
  证明: rfl
-/
lemma col_apply (A : Matrix m n α) (i : n) (j : m) : A.col i j = A j i := rfl

/--
lemma `col_apply'` / 引理 `col_apply'`

English:
lemma col_apply'
  given: (A : Matrix m n α) (i : n)
  statement: A.col i = fun j => A j i
  proof: rfl

中文:
引理 col_apply'
  条件: (A : 矩阵 m n α) (i : n)
  结论: A.col i = fun j => A j i
  证明: rfl
-/
lemma col_apply' (A : Matrix m n α) (i : n) : A.col i = fun j => A j i := rfl

section

/-- Two matrices agree if their rows agree. -/
@[local ext]
/--
lemma `ext_row` / 引理 `ext_row`

English:
lemma ext_row
  given: {A B : Matrix m n α} (h : forall i, A.row i = B.row i)
  statement: A = B
  proof: ext fun i j => congr_fun (h i) j

中文:
引理 ext_row
  条件: {A B : 矩阵 m n α} (h : 对任意 i, A.row i = B.row i)
  结论: A = B
  证明: ext fun i j => congr_fun (h i) j

Depends on / 依赖: congr_fun
-/
lemma ext_row {A B : Matrix m n α} (h : forall i, A.row i = B.row i) : A = B :=
  ext fun i j => congr_fun (h i) j

/-- Two matrices agree if their columns agree. -/
@[local ext]
/--
lemma `ext_col` / 引理 `ext_col`

English:
lemma ext_col
  given: {A B : Matrix m n α} (h : forall j, A.col j = B.col j)
  statement: A = B
  proof: ext fun i j => congr_fun (h j) i

中文:
引理 ext_col
  条件: {A B : 矩阵 m n α} (h : 对任意 j, A.col j = B.col j)
  结论: A = B
  证明: ext fun i j => congr_fun (h j) i

Depends on / 依赖: congr_fun
-/
lemma ext_col {A B : Matrix m n α} (h : forall j, A.col j = B.col j) : A = B :=
  ext fun i j => congr_fun (h j) i

end

/--
lemma `row_submatrix` / 引理 `row_submatrix`

English:
lemma row_submatrix
  given: {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀)
  proof: rfl

中文:
引理 row_submatrix
  条件: {m₀ n₀ : 类型} (A : 矩阵 m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀)
  证明: rfl
-/
lemma row_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀) :
    (A.submatrix r c).row i = (A.submatrix id c).row (r i) := rfl

/--
lemma `row_submatrix_eq_comp` / 引理 `row_submatrix_eq_comp`

English:
lemma row_submatrix_eq_comp
  given: {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀)
  proof: rfl

中文:
引理 row_submatrix_eq_comp
  条件: {m₀ n₀ : 类型} (A : 矩阵 m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀)
  证明: rfl
-/
lemma row_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (i : m₀) :
    (A.submatrix r c).row i = A.row (r i) ∘ c := rfl

/--
lemma `col_submatrix` / 引理 `col_submatrix`

English:
lemma col_submatrix
  given: {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀)
  proof: rfl

中文:
引理 col_submatrix
  条件: {m₀ n₀ : 类型} (A : 矩阵 m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀)
  证明: rfl
-/
lemma col_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀) :
    (A.submatrix r c).col j = (A.submatrix r id).col (c j) := rfl

/--
lemma `col_submatrix_eq_comp` / 引理 `col_submatrix_eq_comp`

English:
lemma col_submatrix_eq_comp
  given: {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀)
  proof: rfl

中文:
引理 col_submatrix_eq_comp
  条件: {m₀ n₀ : 类型} (A : 矩阵 m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀)
  证明: rfl
-/
lemma col_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> n) (j : n₀) :
    (A.submatrix r c).col j = A.col (c j) ∘ r := rfl

/--
lemma `row_map` / 引理 `row_map`

English:
lemma row_map
  given: (A : Matrix m n α) (f : α -> β) (i : m)
  statement: (A.map f).row i = f ∘ A.row i
  proof: rfl

中文:
引理 row_map
  条件: (A : 矩阵 m n α) (f : α -> β) (i : m)
  结论: (A.map f).row i = f ∘ A.row i
  证明: rfl
-/
lemma row_map (A : Matrix m n α) (f : α -> β) (i : m) : (A.map f).row i = f ∘ A.row i := rfl

/--
lemma `col_map` / 引理 `col_map`

English:
lemma col_map
  given: (A : Matrix m n α) (f : α -> β) (j : n)
  statement: (A.map f).col j = f ∘ A.col j
  proof: rfl

@[simp]

中文:
引理 col_map
  条件: (A : 矩阵 m n α) (f : α -> β) (j : n)
  结论: (A.map f).col j = f ∘ A.col j
  证明: rfl

@[simp]
-/
lemma col_map (A : Matrix m n α) (f : α -> β) (j : n) : (A.map f).col j = f ∘ A.col j := rfl

@[simp]
/--
lemma `row_transpose` / 引理 `row_transpose`

English:
lemma row_transpose
  given: (A : Matrix m n α)
  statement: Aᵀ.row = A.col
  proof: rfl

@[simp]

中文:
引理 row_transpose
  条件: (A : 矩阵 m n α)
  结论: Aᵀ.row = A.col
  证明: rfl

@[simp]
-/
lemma row_transpose (A : Matrix m n α) : Aᵀ.row = A.col := rfl

@[simp]
/--
lemma `col_transpose` / 引理 `col_transpose`

English:
lemma col_transpose
  given: (A : Matrix m n α)
  statement: Aᵀ.col = A.row
  proof: rfl

中文:
引理 col_transpose
  条件: (A : 矩阵 m n α)
  结论: Aᵀ.col = A.row
  证明: rfl
-/
lemma col_transpose (A : Matrix m n α) : Aᵀ.col = A.row := rfl

end RowCol

end Matrix

namespace Set

/--
Definition of `matrix` / `matrix` 的定义

English:
definition matrix
  signature: (S : Set α)
  body: {M | forall i j, M i j in S}

中文:
定义 matrix
  签名: (S : 集合 α)
  定义体: {M | forall i j, M i j in S}
-/
def matrix (S : Set α) : Set (Matrix m n α) := {M | forall i j, M i j in S}

/--
theorem `mem_matrix` / 定理 `mem_matrix`

English:
theorem mem_matrix
  given: {S : Set α} {M : Matrix m n α}
  proof: .rfl

中文:
定理 mem_matrix
  条件: {S : 集合 α} {M : 矩阵 m n α}
  证明: .rfl
-/
theorem mem_matrix {S : Set α} {M : Matrix m n α} :
    M in S.matrix ↔ forall i j, M i j in S := .rfl

/--
theorem `matrix_eq_pi` / 定理 `matrix_eq_pi`

English:
theorem matrix_eq_pi
  given: {S : Set α}
  proof: by
  ext
  simp [Set.mem_matrix]

中文:
定理 matrix_eq_pi
  条件: {S : 集合 α}
  证明: by
  ext
  simp [Set.mem_matrix]

Depends on / 依赖: Set.mem_matrix, mem_matrix
-/
theorem matrix_eq_pi {S : Set α} :
    S.matrix = of.symm ⁻¹' Set.univ.pi fun (_ : m) => Set.univ.pi fun (_ : n) => S := by
  ext
  simp [Set.mem_matrix]

end Set

namespace Matrix

variable {S : Set α}

@[simp]
/--
theorem `transpose_mem_matrix_iff` / 定理 `transpose_mem_matrix_iff`

English:
theorem transpose_mem_matrix_iff
  given: {M : Matrix m n α}
  proof: forall_comm

中文:
定理 transpose_mem_matrix_iff
  条件: {M : 矩阵 m n α}
  证明: forall_comm

Depends on / 依赖: forall_comm
-/
theorem transpose_mem_matrix_iff {M : Matrix m n α} :
    Mᵀ in S.matrix ↔ M in S.matrix := forall_comm

/--
theorem `submatrix_mem_matrix` / 定理 `submatrix_mem_matrix`

English:
theorem submatrix_mem_matrix
  given: {M : Matrix m n α} {r : l -> m} {c : o -> n} (hM : M in S.matrix)
  proof: by simp_all [Set.mem_matrix]

中文:
定理 submatrix_mem_matrix
  条件: {M : 矩阵 m n α} {r : l -> m} {c : o -> n} (hM : M in S.matrix)
  证明: by simp_all [Set.mem_matrix]

Depends on / 依赖: Set.mem_matrix, mem_matrix
-/
theorem submatrix_mem_matrix {M : Matrix m n α} {r : l -> m} {c : o -> n} (hM : M in S.matrix) :
    M.submatrix r c in S.matrix := by simp_all [Set.mem_matrix]

/--
theorem `submatrix_mem_matrix_iff` / 定理 `submatrix_mem_matrix_iff`

English:
theorem submatrix_mem_matrix_iff
  statement: {M : Matrix m n α} {r : l -> m} {c : o -> n}
  proof: ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), submatrix_mem_matrix⟩

中文:
定理 submatrix_mem_matrix_iff
  结论: {M : 矩阵 m n α} {r : l -> m} {c : o -> n}
  证明: ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), submatrix_mem_matrix⟩

Depends on / 依赖: hc.forall.mpr, hr.forall.mpr, submatrix_mem_matrix
-/
theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l -> m} {c : o -> n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c in S.matrix ↔ M in S.matrix :=
  ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), submatrix_mem_matrix⟩

end Matrix
