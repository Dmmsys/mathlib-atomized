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
/-
**Matrix** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v
参数：m : Type u；n : Type u'；α : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Matrix m n R` is the type of matrices with entries in `R`, whose rows are index
ed by `m`
and whose columns are indexed by `n`.
-/
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

/-
**Matrix.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext_iff : (forall i j, M i j = N i j) ↔ M = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩

@[ext]
/-
**Matrix.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ext : (forall i j, M i j = N i j) -> M = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem ext : (∀ i j, M i j = N i j) → M = N :=
  ext_iff.mp

end Ext

/-- Cast a function into a matrix.

The two sides of the equivalence are definitionally equal types. We want to use an explicit cast
to distinguish the types because `Matrix` has different instances to pi types (such as `Pi.mul`,
which performs elementwise multiplication, vs `Matrix.mul`).

If you are defining a matrix, in terms of its entries, use `of (fun i j ↦ _)`. The
purpose of this approach is to ensure that terms of the form `(fun i j ↦ _) * (fun i j ↦ _)` do not
appear, as the type of `*` can be misleading.
-/
/-
**Matrix.of** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：of : (m -> n -> α) ≃ Matrix m n α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Cast a function into a matrix.

The two sides of the equivalence are definitionally equal types. We want to use 
an explicit cast
to distinguish the types because `Matrix` has different instances to pi types (s
uch as `Pi.mul`,
which performs elementwise multiplication, vs `Matrix.mul`).

If you are defining a matrix, in terms of its entries, use `of (fun i j ↦ _)`. T
he
purpose of this approach is to ensure that terms of the form `(fun i j ↦ _) * (f
un i j ↦ _)` do not
appear, as the type of `*` can be misleading.
-/
def of : (m → n → α) ≃ Matrix m n α :=
  Equiv.refl _

@[simp]
/-
**Matrix.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_apply (f : m -> n -> α) (i j) : of f i j = f i j
参数：f : m -> n -> α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply (f : m → n → α) (i j) : of f i j = f i j :=
  rfl

@[simp]
/-
**Matrix.of_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j
参数：f : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem of_symm_apply (f : Matrix m n α) (i j) : of.symm f i j = f i j :=
  rfl

/-- Construct a matrix from an array in row-major ordering. -/
/-
**Matrix.ofArray** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：ofArray {m n : Nat} (A : Array R) (hA : A.size = m * n) : Matrix (Fin m) (
Fin n) R
参数：A : Array R；hA : A.size = m * n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a matrix from an array in row-major ordering.
-/
def ofArray {m n : ℕ} (A : Array R) (hA : A.size = m * n) : Matrix (Fin m) (Fin n) R :=
  fun i j => A[Fin.mkDivMod i j]

@[simp]
/-
**Matrix.ofArray_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofArray_apply {m n : Nat} (A : Array R) (hA : A.size = m * n) (i : Fin m) 
(j : Fin n) : ofArray A hA i j = A[Fin.mkDivMod i j]
参数：A : Array R；hA : A.size = m * n；i : Fin m；j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofArray_apply {m n : ℕ} (A : Array R) (hA : A.size = m * n) (i : Fin m) (j : Fin n) :
    ofArray A hA i j = A[Fin.mkDivMod i j] := rfl

/-- The matrix constructed from the row-major array of `A`'s entries is `A`. -/
@[simp]
/-
**Matrix.ofArray_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofArray_ofFn {m n : Nat} (A : Matrix (Fin m) (Fin n) R) : ofArray (.ofFn f
un k : Fin (m * n) => A k.divNat k.modNat) Array.size_ofFn = A
参数：A : Matrix (Fin m) (Fin n) R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Array.size_ofFn`：∀ {α : Type u_1} {n : ℕ} {f : Fin n → α}, (Array.ofFn f
).size = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.ofArray_apply`：ofArray_apply {m n : Nat} (A : Array R) (hA : A.si
ze = m * n) (i : Fin m) (j : Fin n) : ofArray A hA i j = A[Fin.mkDivMod i j]
· 使用定理 `Fin.getElem_fin`：∀ {Cont : Type u_1} {Elem : Type u_2} {Dom : Cont → ℕ →
 Prop} {n : ℕ} [inst : GetElem Cont ℕ Elem Dom] (a : Cont)   (i : Fin n) (h : Do
m a ↑…
· 使用定理 `Array.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α} {i : ℕ} (h 
: i < (Array.ofFn f).size), (Array.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `Fin.divNat_mkDivMod`：∀ {m n : ℕ} (i : Fin m) (j : Fin n), (i.mkDivMod j)
.divNat = i
· 使用定理 `Fin.modNat_mkDivMod`：∀ {m n : ℕ} (i : Fin m) (j : Fin n), (i.mkDivMod j)
.modNat = j

--- 原说明 ---
The matrix constructed from the row-major array of `A`'s entries is `A`.
-/
theorem ofArray_ofFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    ofArray (.ofFn fun k : Fin (m * n) ↦ A k.divNat k.modNat) Array.size_ofFn = A := by
  ext i j
  rw [ofArray_apply, Fin.getElem_fin, Array.getElem_ofFn, Fin.divNat_mkDivMod,
    Fin.modNat_mkDivMod]
/-
**Matrix.ofArray_eq_of_getD** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ofArray_eq_of_getD [Zero R] {m n : Nat} (A : Array R) (hA : A.size = m * n
) : ofArray A hA = .of fun i j => A.getD (n * i.val + j.val) 0
参数：A : Array R；hA : A.size = m * n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Array.getD_eq_getD_getElem?`：∀ {α : Type u_1} {xs : Array α} {i : ℕ} {d 
: α}, xs.getD i d = xs[i]?.getD d
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `Array.instLawfulGetElemNatLtSize`：∀ {α : Type u_1}, LawfulGetElem (Array
 α) ℕ α fun xs i => i < xs.size
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofArray_eq_of_getD [Zero R] {m n : ℕ} (A : Array R) (hA : A.size = m * n) :
    ofArray A hA = .of fun i j ↦ A.getD (n * i.val + j.val) 0 := by
  ext i j
  have : n * i.val + j.val < m * n := (Fin.mkDivMod i j).isLt
  simp [ofArray, hA, this]

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`.

This is available in bundled forms as:
* `AddMonoidHom.mapMatrix`
* `LinearMap.mapMatrix`
* `RingHom.mapMatrix`
* `AlgHom.mapMatrix`
* `Equiv.mapMatrix`
* `AddEquiv.mapMatrix`
* `LinearEquiv.mapMatrix`
* `RingEquiv.mapMatrix`
* `AlgEquiv.mapMatrix`
-/
/-
**Matrix.map** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：map (M : Matrix m n α) (f : α -> β) : Matrix m n β
参数：M : Matrix m n α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`
.

This is available in bundled forms as:
* `AddMonoidHom.mapMatrix`
* `LinearMap.mapMatrix`
* `RingHom.mapMatrix`
* `AlgHom.mapMatrix`
* `Equiv.mapMatrix`
* `AddEquiv.mapMatrix`
* `LinearEquiv.mapMatrix`
* `RingEquiv.mapMatrix`
* `AlgEquiv.mapMatrix`
-/
def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
  of fun i j => f (M i j)

@[simp]
/-
**Matrix.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_apply {M : Matrix m n α} {f : α -> β} {i : m} {j : n} : M.map f i j = 
f (M i j)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} : M.map f i j = f (M i j) :=
  rfl

@[simp]
/-
**Matrix.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_id (M : Matrix m n α) : M.map id = M
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem map_id (M : Matrix m n α) : M.map id = M := by
  ext
  rfl

@[simp]
/-
**Matrix.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_id' (M : Matrix m n α) : M.map (·) = M
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.map_id`：map_id (M : Matrix m n α) : M.map id = M
-/
theorem map_id' (M : Matrix m n α) : M.map (·) = M := map_id M

@[simp]
/-
**Matrix.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g : β -> γ} : (M.ma
p f).map g = M.map (g ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem map_map {M : Matrix m n α} {β γ : Type*} {f : α → β} {g : β → γ} :
    (M.map f).map g = M.map (g ∘ f) := by
  ext
  rfl
/-
**Matrix.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_injective {f : α -> β} (hf : Function.Injective f) : Function.Injectiv
e fun M : Matrix m n α => M.map f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective fun M : Matrix m n α => M.map f := fun _ _ h =>
  ext fun i j => hf <| ext_iff.mpr h i j
/-
**Matrix.map_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_involutive {f : α -> α} (hf : Function.Involutive f) : Function.Involu
tive fun M : Matrix m n α => M.map f
参数：hf : Function.Involutive f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.map_map`：map_map {M : Matrix m n α} {β γ : Type*} {f : α -> β} {g
 : β -> γ} : (M.map f).map g = M.map (g ∘ f)
· 使用定理 `Function.Involutive.comp_self`：comp_self : f ∘ f = id
· 使用定理 `Matrix.map_id`：map_id (M : Matrix m n α) : M.map id = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_involutive {f : α → α} (hf : Function.Involutive f) :
    Function.Involutive fun M : Matrix m n α ↦ M.map f := by intro; simp [hf]

/-- The transpose of a matrix.

This is available in bundled forms as:
* `Matrix.transposeAddEquiv`
* `Matrix.transposeLinearEquiv`
* `Matrix.transposeRingEquiv`
* `Matrix.transposeAlgEquiv`
* `RingEquiv.mopMatrix`
* `AlgEquiv.mopMatrix`
-/
/-
**Matrix.transpose** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transpose (M : Matrix m n α) : Matrix n m α
参数：M : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transpose of a matrix.

This is available in bundled forms as:
* `Matrix.transposeAddEquiv`
* `Matrix.transposeLinearEquiv`
* `Matrix.transposeRingEquiv`
* `Matrix.transposeAlgEquiv`
* `RingEquiv.mopMatrix`
* `AlgEquiv.mopMatrix`
-/
def transpose (M : Matrix m n α) : Matrix n m α :=
  of fun x y => M y x

-- TODO: set as an equation lemma for `transpose`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.transpose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i
参数：M : Matrix m n α；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_apply (M : Matrix m n α) (i j) : transpose M i j = M j i :=
  rfl

@[inherit_doc]
scoped postfix:1024 "ᵀ" => Matrix.transpose
/-
**Matrix.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：inhabited [Inhabited α] : Inhabited (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited [Inhabited α] : Inhabited (Matrix m n α) :=
  inferInstanceAs <| Inhabited (m → n → α)
/-
**Matrix.add** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：add [Add α] : Add (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add [Add α] : Add (Matrix m n α) :=
  inferInstanceAs <| Add (m → n → α)
/-
**Matrix.smul** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：smul [SMul R α] : SMul R (Matrix m n α) where smul a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [SMul R α] : SMul R (Matrix m n α) where
  smul a b := fun i ↦ a • b i
/-
**Matrix.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup [AddSemigroup α] : AddSemigroup (Matrix m n α) :=
  inferInstanceAs <| AddSemigroup (m → n → α)
/-
**Matrix.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup (Matrix m n α) :=
  inferInstanceAs <| AddCommSemigroup (m → n → α)
/-
**Matrix.zero** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：zero [Zero α] : Zero (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zero [Zero α] : Zero (Matrix m n α) :=
  inferInstanceAs <| Zero (m → n → α)
/-
**Matrix.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addZeroClass [AddZeroClass α] : AddZeroClass (Matrix m n α) :=
  inferInstanceAs <| AddZeroClass (m → n → α)
/-
**Matrix.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addMonoid [AddMonoid α] : AddMonoid (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid [AddMonoid α] : AddMonoid (Matrix m n α) :=
  inferInstanceAs <| AddMonoid (m → n → α)
/-
**Matrix.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [AddCommMonoid α] : AddCommMonoid (Matrix m n α) :=
  inferInstanceAs <| AddCommMonoid (m → n → α)
/-
**Matrix.neg** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：neg [Neg α] : Neg (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neg [Neg α] : Neg (Matrix m n α) :=
  inferInstanceAs <| Neg (m → n → α)
/-
**Matrix.involutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：involutiveNeg [InvolutiveNeg α] : InvolutiveNeg (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance involutiveNeg [InvolutiveNeg α] : InvolutiveNeg (Matrix m n α) :=
  inferInstanceAs <| InvolutiveNeg (m → n → α)
/-
**Matrix.sub** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：sub [Sub α] : Sub (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sub [Sub α] : Sub (Matrix m n α) :=
  inferInstanceAs <| Sub (m → n → α)
/-
**Matrix.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addGroup [AddGroup α] : AddGroup (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroup [AddGroup α] : AddGroup (Matrix m n α) :=
  inferInstanceAs <| AddGroup (m → n → α)
/-
**Matrix.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup [AddCommGroup α] : AddCommGroup (Matrix m n α) :=
  inferInstanceAs <| AddCommGroup (m → n → α)
/-
**Matrix.unique** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：unique [Unique α] : Unique (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique [Unique α] : Unique (Matrix m n α) :=
  inferInstanceAs <| Unique (m → n → α)
/-
**Matrix.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：subsingleton [Subsingleton α] : Subsingleton (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance subsingleton [Subsingleton α] : Subsingleton (Matrix m n α) :=
  inferInstanceAs <| Subsingleton <| m → n → α
/-
**Matrix.nonempty** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n
 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonempty [Nonempty m] [Nonempty n] [Nontrivial α] : Nontrivial (Matrix m n α) :=
  Function.nontrivial
/-
**Matrix.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] : SMulCommClass 
R S (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass [SMul R α] [SMul S α] [SMulCommClass R S α] :
    SMulCommClass R S (Matrix m n α) :=
  Pi.smulCommClass
/-
**Matrix.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] : IsS
calarTower R S (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower [SMul R S] [SMul R α] [SMul S α] [IsScalarTower R S α] :
    IsScalarTower R S (Matrix m n α) :=
  Pi.isScalarTower
/-
**Matrix.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentral
Scalar R (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCentralScalar [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] :
    IsCentralScalar R (Matrix m n α) :=
  Pi.isCentralScalar
/-
**Matrix.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction [Monoid R] [MulAction R α] : MulAction R (Matrix m n α) :=
  inferInstanceAs <| MulAction R (m → n → α)
/-
**Matrix.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] : Distrib
MulAction R (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    DistribMulAction R (Matrix m n α) :=
  inferInstanceAs <| DistribMulAction R (m → n → α)
/-
**Matrix.module** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n 
α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module [Semiring R] [AddCommMonoid α] [Module R α] : Module R (Matrix m n α) :=
  inferInstanceAs <| Module R (m → n → α)
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsAddCommutative α] : IsAddCommutative <| Matrix m n α :=
  inferInstanceAs <| IsAddCommutative <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMagma α] : AddCommMagma <| Matrix m n α :=
  inferInstanceAs <| AddCommMagma <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsLeftCancelAdd α] : IsLeftCancelAdd <| Matrix m n α :=
  inferInstanceAs <| IsLeftCancelAdd <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsRightCancelAdd α] : IsRightCancelAdd <| Matrix m n α :=
  inferInstanceAs <| IsRightCancelAdd <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] [IsCancelAdd α] : IsCancelAdd <| Matrix m n α :=
  inferInstanceAs <| IsCancelAdd <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup <| Matrix m n α :=
  inferInstanceAs <| AddLeftCancelSemigroup <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup <| Matrix m n α :=
  inferInstanceAs <| AddRightCancelSemigroup <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddLeftCancelMonoid α] : AddLeftCancelMonoid <| Matrix m n α :=
  inferInstanceAs <| AddLeftCancelMonoid <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddRightCancelMonoid α] : AddRightCancelMonoid <| Matrix m n α :=
  inferInstanceAs <| AddRightCancelMonoid <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCancelMonoid α] : AddCancelMonoid <| Matrix m n α :=
  inferInstanceAs <| AddCancelMonoid <| m → n → α
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCancelCommMonoid α] : AddCancelCommMonoid <| Matrix m n α :=
  inferInstanceAs <| AddCancelCommMonoid <| m → n → α

section

@[simp]
/-
**Matrix.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0
参数：i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [Zero α] (i : m) (j : n) : (0 : Matrix m n α) i j = 0 := rfl

@[simp]
/-
**Matrix.of_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_symm_zero [Zero α] : of.symm (0 : Matrix m n α) = (0 : m -> n -> α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem of_symm_zero [Zero α] : of.symm (0 : Matrix m n α) = (0 : m → n → α) := rfl

@[simp]
/-
**Matrix.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) : (A + B) i j = (A 
i j) + (B i j)
参数：A B : Matrix m n α；i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply [Add α] (A B : Matrix m n α) (i : m) (j : n) :
    (A + B) i j = (A i j) + (B i j) := rfl

@[simp]
/-
**Matrix.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) : (r • A)
 i j = r • (A i j)
参数：r : β；A : Matrix m n α；i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [SMul β α] (r : β) (A : Matrix m n α) (i : m) (j : n) :
    (r • A) i j = r • (A i j) := rfl

@[simp]
/-
**Matrix.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) : (A - B) i j = (A 
i j) - (B i j)
参数：A B : Matrix m n α；i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply [Sub α] (A B : Matrix m n α) (i : m) (j : n) :
    (A - B) i j = (A i j) - (B i j) := rfl

@[simp]
/-
**Matrix.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) : (-A) i j = -(A i j)
参数：A : Matrix m n α；i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply [Neg α] (A : Matrix m n α) (i : m) (j : n) :
    (-A) i j = -(A i j) := rfl
/-
**Matrix.dite_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} (P : Prop) [inst : Decidable 
P] (A : P → Matrix m n α)   (B : ¬P → Matrix m n α) (i : m) (j : n), dite P A B 
i j = if x : P then A x i j else B x i j
参数：P : Prop；A : P → Matrix m n α；B : ¬P → Matrix m n α；i : m；j : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
protected theorem dite_apply (P : Prop) [Decidable P]
    (A : P → Matrix m n α) (B : ¬P → Matrix m n α) (i : m) (j : n) :
    dite P A B i j = dite P (A · i j) (B · i j) := by
  by_cases h : P <;> simp [h]
/-
**Matrix.ite_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} (P : Prop) [inst : Decidable 
P] (A B : Matrix m n α) (i : m) (j : n),   (if P then A else B) i j = if P then 
A i j else B i j
参数：P : Prop；A B : Matrix m n α；i : m；j : n；if P then A else B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.dite_apply`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} (P : Pro
p) [inst : Decidable P] (A : P → Matrix m n α)   (B : ¬P → Matrix m n α) (i : m)
 (j : n…
-/
protected theorem ite_apply (P : Prop) [Decidable P]
    (A : Matrix m n α) (B : Matrix m n α) (i : m) (j : n) :
    (if P then A else B) i j = if P then A i j else B i j :=
  Matrix.dite_apply _ _ _ _ _

end

/-! simp-normal form pulls `of` to the outside. -/

@[simp]
/-
**Matrix.of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_zero [Zero α] : of (0 : m -> n -> α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
simp-normal form pulls `of` to the outside.
-/
theorem of_zero [Zero α] : of (0 : m → n → α) = 0 :=
  rfl

@[simp]
/-
**Matrix.of_add_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_add_of [Add α] (f g : m -> n -> α) : of f + of g = of (f + g)
参数：f g : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_add_of [Add α] (f g : m → n → α) : of f + of g = of (f + g) :=
  rfl

@[simp]
/-
**Matrix.of_sub_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：of_sub_of [Sub α] (f g : m -> n -> α) : of f - of g = of (f - g)
参数：f g : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_sub_of [Sub α] (f g : m → n → α) : of f - of g = of (f - g) :=
  rfl

@[simp]
/-
**Matrix.neg_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：neg_of [Neg α] (f : m -> n -> α) : -of f = of (-f)
参数：f : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_of [Neg α] (f : m → n → α) : -of f = of (-f) :=
  rfl

@[simp]
/-
**Matrix.smul_of** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：smul_of [SMul R α] (r : R) (f : m -> n -> α) : r • of f = of (r • f)
参数：r : R；f : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_of [SMul R α] (r : R) (f : m → n → α) : r • of f = of (r • f) :=
  rfl

@[simp]
/-
**Matrix.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [inst : Zero α] 
[inst_1 : Zero β] (f : α → β),   f 0 = 0 → Matrix.map 0 f = 0
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem map_zero [Zero α] [Zero β] (f : α → β) (h : f 0 = 0) :
    (0 : Matrix m n α).map f = 0 := by
  ext
  simp [h]
/-
**Matrix.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [inst : Add α] [
inst_1 : Add β] (f : α → β),   (∀ (a₁ a₂ : α), f (a₁ + a₂) = f a₁ + f a₂) → ∀ (M
 N : Matrix m n α), (M + N).map f = M.map f + N.map f
参数：f : α → β；∀ (a₁ a₂ : α), f (a₁ + a₂) = f a₁ + f a₂；M N : Matrix m n α；M + N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
protected theorem map_add [Add α] [Add β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ + a₂) = f a₁ + f a₂)
    (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  ext fun _ _ => hf _ _
/-
**Matrix.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [inst : Neg α] [
inst_1 : Neg β] (f : α → β),   (∀ (a : α), f (-a) = -f a) → ∀ (M : Matrix m n α)
, (-M).map f = -M.map f
参数：f : α → β；∀ (a : α), f (-a) = -f a；M : Matrix m n α；-M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
protected theorem map_neg [Neg α] [Neg β] (f : α → β) (hf : ∀ a, f (-a) = -f a)
    (M : Matrix m n α) : (-M).map f = -(M.map f) :=
  ext fun _ _ => hf _
/-
**Matrix.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w} [inst : Sub α] [
inst_1 : Sub β] (f : α → β),   (∀ (a₁ a₂ : α), f (a₁ - a₂) = f a₁ - f a₂) → ∀ (M
 N : Matrix m n α), (M - N).map f = M.map f - N.map f
参数：f : α → β；∀ (a₁ a₂ : α), f (a₁ - a₂) = f a₁ - f a₂；M N : Matrix m n α；M - N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
protected theorem map_sub [Sub α] [Sub β] (f : α → β) (hf : ∀ a₁ a₂, f (a₁ - a₂) = f a₁ - f a₂)
    (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  ext fun _ _ => hf _ _
/-
**Matrix.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {α : Type v} {β : Type w} [
inst : SMul R α] [inst_1 : SMul R β]   (f : α → β) (r : R), (∀ (a : α), f (r • a
) = r • f a) → ∀ (M : Matrix m n α), (r • M).map f = r • M.map f
参数：f : α → β；r : R；∀ (a : α), f (r • a) = r • f a；M : Matrix m n α；r • M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
protected theorem map_smul [SMul R α] [SMul R β] (f : α → β) (r : R) (hf : ∀ a, f (r • a) = r • f a)
    (M : Matrix m n α) : (r • M).map f = r • M.map f :=
  ext fun _ _ => hf _
/-
**Matrix.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {R : Type u_7} {α : Type v} {β : Type w} [
inst : SMul R α] [inst_1 : SMul R β]   (f : α → β) (r : R), (∀ (a : α), f (r • a
) = r • f a) → ∀ (M : Matrix m n α), (r • M).map f = r • M.map f
参数：f : α → β；r : R；∀ (a : α), f (r • a) = r • f a；M : Matrix m n α；r • M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
protected theorem map_smulₛₗ [SMul R α] [SMul S β] (f : α → β) (σ : R → S) (r : R)
    (hf : ∀ a, f (r • a) = σ r • f a)
    (M : Matrix m n α) : (r • M).map f = σ r • M.map f :=
  ext fun _ _ => hf _

/-- The scalar action via `Mul.toSMul` is transformed by the same map as the elements
of the matrix, when `f` preserves multiplication. -/
/-
**Matrix.map_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_smul' [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α) (hf : fo
rall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f
参数：f : α -> β；r : α；A : Matrix n n α；hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a
₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
The scalar action via `Mul.toSMul` is transformed by the same map as the element
s
of the matrix, when `f` preserves multiplication.
-/
theorem map_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (r • A).map f = f r • A.map f :=
  ext fun _ _ => hf _ _

/-- The scalar action via `mul.toOppositeSMul` is transformed by the same map as the
elements of the matrix, when `f` preserves multiplication. -/
/-
**Matrix.map_op_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：map_op_smul' [Mul α] [Mul β] (f : α -> β) (r : α) (A : Matrix n n α) (hf :
 forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) : (MulOpposite.op r • A).map f = MulOp
posite.op (f r) • A.map f
参数：f : α -> β；r : α；A : Matrix n n α；hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a
₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N

--- 原说明 ---
The scalar action via `mul.toOppositeSMul` is transformed by the same map as the
elements of the matrix, when `f` preserves multiplication.
-/
theorem map_op_smul' [Mul α] [Mul β] (f : α → β) (r : α) (A : Matrix n n α)
    (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂) :
    (MulOpposite.op r • A).map f = MulOpposite.op (f r) • A.map f :=
  ext fun _ _ => hf _ _
/-
**Matrix._root_.IsSMulRegular.matrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSMulRegular.matrix [SMul R S] {k : R} (hk : IsSMulRegular S k) :
    IsSMulRegular (Matrix m n S) k :=
  IsSMulRegular.pi fun _ => IsSMulRegular.pi fun _ => hk
/-
**Matrix._root_.IsLeftRegular.matrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsLeftRegular.matrix [Mul α] {k : α} (hk : IsLeftRegular k) :
    IsSMulRegular (Matrix m n α) k :=
  hk.isSMulRegular.matrix
/-
**Matrix.subsingleton_of_empty_left** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i
    exact isEmptyElim i⟩
/-
**Matrix.subsingleton_of_empty_right** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (Matrix m n α) :=
  ⟨fun M N => by
    ext i j
    exact isEmptyElim j⟩

/-- This is `Matrix.of` bundled as an additive equivalence. -/
/-
**Matrix.ofAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：ofAddEquiv [Add α] : (m -> n -> α) ≃+ Matrix m n α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Matrix.of` bundled as an additive equivalence.
-/
def ofAddEquiv [Add α] : (m → n → α) ≃+ Matrix m n α where
  __ := of
  map_add' _ _ := rfl
/-
**Matrix.coe_ofAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Add α], ⇑Matrix.ofAdd
Equiv = ⇑Matrix.of
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofAddEquiv [Add α] :
    ⇑(ofAddEquiv : (m → n → α) ≃+ Matrix m n α) = of := rfl
/-
**Matrix.coe_ofAddEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Add α], ⇑Matrix.ofAdd
Equiv.symm = ⇑Matrix.of.symm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofAddEquiv_symm [Add α] :
    ⇑(ofAddEquiv.symm : Matrix m n α ≃+ (m → n → α)) = of.symm := rfl
/-
**Matrix.isAddUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : AddMonoid α] {A : Mat
rix m n α},   IsAddUnit A ↔ ∀ (i : m) (j : n), IsAddUnit (A i j)
参数：i : m；j : n；A i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isAddUnit_iff [AddMonoid α] {A : Matrix m n α} :
    IsAddUnit A ↔ ∀ i j, IsAddUnit (A i j) := by
  simp_rw [isAddUnit_iff_exists, Classical.skolem, forall_and,
    ← Matrix.ext_iff, add_apply, zero_apply]
  rfl

end Matrix

open Matrix

namespace Matrix

section Transpose

@[simp]
/-
**Matrix.transpose_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem transpose_transpose (M : Matrix m n α) : Mᵀᵀ = M := by
  ext
  rfl

variable (n α) in
/-
**Matrix.transpose_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_involutive : (transpose : Matrix n n α -> Matrix n n α).Involuti
ve
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
-/
theorem transpose_involutive : (transpose : Matrix n n α → Matrix n n α).Involutive :=
  transpose_transpose
/-
**Matrix.transpose_injective** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_injective : Function.Injective (transpose : Matrix m n α -> Matr
ix n m α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.ext_iff`：ext_iff : (forall i j, M i j = N i j) ↔ M = N
-/
theorem transpose_injective : Function.Injective (transpose : Matrix m n α → Matrix n m α) :=
  fun _ _ h => ext fun i j => ext_iff.2 h j i
/-
**Matrix.transpose_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {A B : Matrix m n α}, A.trans
pose = B.transpose ↔ A = B
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.transpose_injective`：transpose_injective : Function.Injective (tr
anspose : Matrix m n α -> Matrix n m α)
-/
@[simp] theorem transpose_inj {A B : Matrix m n α} : Aᵀ = Bᵀ ↔ A = B := transpose_injective.eq_iff

@[simp]
/-
**Matrix.transpose_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_zero [Zero α] : (0 : Matrix m n α)ᵀ = 0 := rfl

@[simp]
/-
**Matrix.transpose_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.transpose_inj`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {A B 
: Matrix m n α}, A.transpose = B.transpose ↔ A = B
-/
theorem transpose_eq_zero [Zero α] {M : Matrix m n α} : Mᵀ = 0 ↔ M = 0 := transpose_inj

@[simp]
/-
**Matrix.transpose_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = M
ᵀ + Nᵀ
参数：M : Matrix m n α；N : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_add [Add α] (M : Matrix m n α) (N : Matrix m n α) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  ext
  simp

@[simp]
/-
**Matrix.transpose_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = M
ᵀ - Nᵀ
参数：M : Matrix m n α；N : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_sub [Sub α] (M : Matrix m n α) (N : Matrix m n α) : (M - N)ᵀ = Mᵀ - Nᵀ := by
  ext
  simp

@[simp]
/-
**Matrix.transpose_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)
ᵀ = c • Mᵀ
参数：c : R；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_smul {R : Type*} [SMul R α] (c : R) (M : Matrix m n α) : (c • M)ᵀ = c • Mᵀ :=
  rfl

@[simp]
/-
**Matrix.transpose_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ
参数：M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_neg [Neg α] (M : Matrix m n α) : (-M)ᵀ = -Mᵀ :=
  rfl
/-
**Matrix.transpose_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
  rfl

end Transpose

/-- Given maps `(r : l → m)` and `(c : o → n)` reindexing the rows and columns of
a matrix `M : Matrix m n α`, the matrix `M.submatrix r c : Matrix l o α` is defined
by `(M.submatrix r c) i j = M (r i) (c j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved. -/
/-
**Matrix.submatrix** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：submatrix (A : Matrix m n α) (r : l -> m) (c : o -> n) : Matrix l o α
参数：A : Matrix m n α；r : l -> m；c : o -> n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `(r : l → m)` and `(c : o → n)` reindexing the rows and columns of
a matrix `M : Matrix m n α`, the matrix `M.submatrix r c : Matrix l o α` is defi
ned
by `(M.submatrix r c) i j = M (r i) (c j)` for `(i,j) : l × o`.
Note that the total number of row and columns does not have to be preserved.
-/
def submatrix (A : Matrix m n α) (r : l → m) (c : o → n) : Matrix l o α :=
  of fun i j => A (r i) (c j)

@[simp]
/-
**Matrix.submatrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_apply (A : Matrix m n α) (r : l -> m) (c : o -> n) (i j) : A.sub
matrix r c i j = A (r i) (c j)
参数：A : Matrix m n α；r : l -> m；c : o -> n；i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_apply (A : Matrix m n α) (r : l → m) (c : o → n) (i j) :
    A.submatrix r c i j = A (r i) (c j) :=
  rfl

@[simp]
/-
**Matrix.submatrix_id_id** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem submatrix_id_id (A : Matrix m n α) : A.submatrix id id = A :=
  ext fun _ _ => rfl

@[simp]
/-
**Matrix.submatrix_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_submatrix {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l -> m) (c₁ :
 o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submatrix r₁ c₁).submatrix r₂ c₂ = A
.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂)
参数：A : Matrix m n α；r₁ : l -> m；c₁ : o -> n；r₂ : l₂ -> l；c₂ : o₂ -> o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem submatrix_submatrix {l₂ o₂ : Type*} (A : Matrix m n α) (r₁ : l → m) (c₁ : o → n)
    (r₂ : l₂ → l) (c₂ : o₂ → o) :
    (A.submatrix r₁ c₁).submatrix r₂ c₂ = A.submatrix (r₁ ∘ r₂) (c₁ ∘ c₂) :=
  ext fun _ _ => rfl

@[simp]
/-
**Matrix.transpose_submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_submatrix (A : Matrix m n α) (r : l -> m) (c : o -> n) : (A.subm
atrix r c)ᵀ = Aᵀ.submatrix c r
参数：A : Matrix m n α；r : l -> m；c : o -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem transpose_submatrix (A : Matrix m n α) (r : l → m) (c : o → n) :
    (A.submatrix r c)ᵀ = Aᵀ.submatrix c r :=
  ext fun _ _ => rfl
/-
**Matrix.submatrix_add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_add [Add α] (A B : Matrix m n α) : ((A + B).submatrix : (l -> m)
 -> (o -> n) -> Matrix l o α) = A.submatrix + B.submatrix
参数：A B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_add [Add α] (A B : Matrix m n α) :
    ((A + B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix + B.submatrix :=
  rfl
/-
**Matrix.submatrix_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_neg [Neg α] (A : Matrix m n α) : ((-A).submatrix : (l -> m) -> (
o -> n) -> Matrix l o α) = -A.submatrix
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_neg [Neg α] (A : Matrix m n α) :
    ((-A).submatrix : (l → m) → (o → n) → Matrix l o α) = -A.submatrix :=
  rfl
/-
**Matrix.submatrix_sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_sub [Sub α] (A B : Matrix m n α) : ((A - B).submatrix : (l -> m)
 -> (o -> n) -> Matrix l o α) = A.submatrix - B.submatrix
参数：A B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_sub [Sub α] (A B : Matrix m n α) :
    ((A - B).submatrix : (l → m) → (o → n) → Matrix l o α) = A.submatrix - B.submatrix :=
  rfl

@[simp]
/-
**Matrix.submatrix_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_zero [Zero α] : ((0 : Matrix m n α).submatrix : (l -> m) -> (o -
> n) -> Matrix l o α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_zero [Zero α] :
    ((0 : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = 0 :=
  rfl
/-
**Matrix.submatrix_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_smul {R : Type*} [SMul R α] (r : R) (A : Matrix m n α) : ((r • A
 : Matrix m n α).submatrix : (l -> m) -> (o -> n) -> Matrix l o α) = r • A.subma
trix
参数：r : R；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_smul {R : Type*} [SMul R α] (r : R) (A : Matrix m n α) :
    ((r • A : Matrix m n α).submatrix : (l → m) → (o → n) → Matrix l o α) = r • A.submatrix :=
  rfl
/-
**Matrix.submatrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_map (f : α -> β) (e₁ : l -> m) (e₂ : o -> n) (A : Matrix m n α) 
: (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f
参数：f : α -> β；e₁ : l -> m；e₂ : o -> n；A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submatrix_map (f : α → β) (e₁ : l → m) (e₂ : o → n) (A : Matrix m n α) :
    (A.map f).submatrix e₁ e₂ = (A.submatrix e₁ e₂).map f :=
  rfl

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
/-
**Matrix.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where toFu
n M
参数：eₘ : m ≃ l；eₙ : n ≃ o。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural map that reindexes a matrix's rows and columns with equivalent types
 is an
equivalence.
-/
def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α where
  toFun M := M.submatrix eₘ.symm eₙ.symm
  invFun M := M.submatrix eₘ eₙ
  left_inv M := by simp
  right_inv M := by simp

@[simp]
/-
**Matrix.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) : reindex eₘ eₙ
 M = M.submatrix eₘ.symm eₙ.symm
参数：eₘ : m ≃ l；eₙ : n ≃ o；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm :=
  rfl
/-
**Matrix.reindex_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl 
_) A = A
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
-/
theorem reindex_refl_refl (A : Matrix m n α) : reindex (Equiv.refl _) (Equiv.refl _) A = A :=
  A.submatrix_id_id

@[simp]
/-
**Matrix.reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) : (reindex eₘ eₙ).symm = (reindex e
ₘ.symm eₙ.symm : Matrix l o α ≃ _)
参数：eₘ : m ≃ l；eₙ : n ≃ o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
  rfl

@[simp]
/-
**Matrix.reindex_trans** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ
₂ : o ≃ o₂) : (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) = (reindex (eₘ.trans eₘ₂) 
(eₙ.trans eₙ₂) : Matrix m n α ≃ _)
参数：eₘ : m ≃ l；eₙ : n ≃ o；eₘ₂ : l ≃ l₂；eₙ₂ : o ≃ o₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem reindex_trans {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
    (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
      (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
  Equiv.ext fun A => (A.submatrix_submatrix eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm :)
/-
**Matrix.transpose_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) : (reindex 
eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ
参数：eₘ : m ≃ l；eₙ : n ≃ o；M : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    (reindex eₘ eₙ M)ᵀ = reindex eₙ eₘ Mᵀ :=
  rfl

/-- The left `n × l` part of an `n × (l+r)` matrix. -/
/-
**Matrix.subLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m
) (Fin l) α
参数：A : Matrix (Fin m) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left `n × l` part of an `n × (l+r)` matrix.
-/
abbrev subLeft {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin l) α :=
  submatrix A id (Fin.castAdd r)

/-- The right `n × r` part of an `n × (l+r)` matrix. -/
/-
**Matrix.subRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin 
m) (Fin r) α
参数：A : Matrix (Fin m) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right `n × r` part of an `n × (l+r)` matrix.
-/
abbrev subRight {m l r : Nat} (A : Matrix (Fin m) (Fin (l + r)) α) : Matrix (Fin m) (Fin r) α :=
  submatrix A id (Fin.natAdd l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
/-
**Matrix.subUp** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) 
(Fin n) α
参数：A : Matrix (Fin (u + d)) (Fin n) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top `u × n` part of a `(u+d) × n` matrix.
-/
abbrev subUp {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin u) (Fin n) α :=
  submatrix A (Fin.castAdd d) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
/-
**Matrix.subDown** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d
) (Fin n) α
参数：A : Matrix (Fin (u + d)) (Fin n) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom `d × n` part of a `(u+d) × n` matrix.
-/
abbrev subDown {d u n : Nat} (A : Matrix (Fin (u + d)) (Fin n) α) : Matrix (Fin d) (Fin n) α :=
  submatrix A (Fin.natAdd u) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
/-
**Matrix.subUpRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) : Ma
trix (Fin u) (Fin r) α
参数：A : Matrix (Fin (u + d)) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top-right `u × r` part of a `(u+d) × (l+r)` matrix.
-/
abbrev subUpRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin r) α :=
  subUp (subRight A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
/-
**Matrix.subDownRight** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) : 
Matrix (Fin d) (Fin r) α
参数：A : Matrix (Fin (u + d)) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix.
-/
abbrev subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
/-
**Matrix.subUpLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) : Mat
rix (Fin u) (Fin l) α
参数：A : Matrix (Fin (u + d)) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top-left `u × l` part of a `(u+d) × (l+r)` matrix.
-/
abbrev subUpLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin u) (Fin l) α :=
  subUp (subLeft A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
/-
**Matrix.subDownLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) : M
atrix (Fin d) (Fin l) α
参数：A : Matrix (Fin (u + d)) (Fin (l + r)) α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix.
-/
abbrev subDownLeft {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin l) α :=
  subDown (subLeft A)

section RowCol

/-- For an `m × n` `α`-matrix `A`, `A.row i` is the `i`th row of `A` as a vector in `n → α`.
`A.row` is defeq to `A`, but explicitly refers to the 'row function' of `A`
while avoiding defeq abuse and noisy eta-expansions,
such as in expressions like `Set.Injective A.row` and `Set.range A.row`.
(Note 2025-04-07 : the identifier `Matrix.row` used to refer to a matrix with all rows equal;
this is now called `Matrix.replicateRow`) -/
/-
**Matrix.row** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：row (A : Matrix m n α) : m -> n -> α
参数：A : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `m × n` `α`-matrix `A`, `A.row i` is the `i`th row of `A` as a vector in 
`n → α`.
`A.row` is defeq to `A`, but explicitly refers to the 'row function' of `A`
while avoiding defeq abuse and noisy eta-expansions,
such as in expressions like `Set.Injective A.row` and `Set.range A.row`.
(Note 2025-04-07 : the identifier `Matrix.row` used to refer to a matrix with al
l rows equal;
this is now called `Matrix.replicateRow`)
-/
def row (A : Matrix m n α) : m → n → α := A

/-- For an `m × n` `α`-matrix `A`, `A.col j` is the `j`th column of `A` as a vector in `m → α`.
`A.col` is defeq to `Aᵀ`, but refers to the 'column function' of `A`
while avoiding defeq abuse and noisy eta-expansions
(and without the simplifier unfolding transposes) in expressions like `Set.Injective A.col`
and `Set.range A.col`.
(Note 2025-04-07 : the identifier `Matrix.col` used to refer to a matrix with all columns equal;
this is now called `Matrix.replicateCol`) -/
/-
**Matrix.col** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：col (A : Matrix m n α) : n -> m -> α
参数：A : Matrix m n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `m × n` `α`-matrix `A`, `A.col j` is the `j`th column of `A` as a vector 
in `m → α`.
`A.col` is defeq to `Aᵀ`, but refers to the 'column function' of `A`
while avoiding defeq abuse and noisy eta-expansions
(and without the simplifier unfolding transposes) in expressions like `Set.Injec
tive A.col`
and `Set.range A.col`.
(Note 2025-04-07 : the identifier `Matrix.col` used to refer to a matrix with al
l columns equal;
this is now called `Matrix.replicateCol`)
-/
def col (A : Matrix m n α) : n → m → α := Aᵀ
/-
**Matrix.row_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_eq_self (A : Matrix m n α) : A.row = of.symm A
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_eq_self (A : Matrix m n α) : A.row = of.symm A := rfl
/-
**Matrix.col_eq_transpose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_eq_transpose (A : Matrix m n α) : A.col = of.symm Aᵀ
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_eq_transpose (A : Matrix m n α) : A.col = of.symm Aᵀ := rfl

@[simp]
/-
**Matrix.of_row** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：of_row (f : m -> n -> α) : (Matrix.of f).row = f
参数：f : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_row (f : m → n → α) : (Matrix.of f).row = f := rfl

@[simp]
/-
**Matrix.of_col** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：of_col (f : m -> n -> α) : (Matrix.of f)ᵀ.col = f
参数：f : m -> n -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_col (f : m → n → α) : (Matrix.of f)ᵀ.col = f := rfl
/-
**Matrix.row_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_def (A : Matrix m n α) : A.row = fun i => A i
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_def (A : Matrix m n α) : A.row = fun i ↦ A i := rfl
/-
**Matrix.col_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_def (A : Matrix m n α) : A.col = fun j => Aᵀ j
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_def (A : Matrix m n α) : A.col = fun j ↦ Aᵀ j := rfl

@[simp]
/-
**Matrix.row_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_apply (A : Matrix m n α) (i : m) (j : n) : A.row i j = A i j
参数：A : Matrix m n α；i : m；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_apply (A : Matrix m n α) (i : m) (j : n) : A.row i j = A i j := rfl

/-- A partially applied version of `Matrix.row_apply` -/
/-
**Matrix.row_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_apply' (A : Matrix m n α) (i : m) : A.row i = A i
参数：A : Matrix m n α；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partially applied version of `Matrix.row_apply`
-/
lemma row_apply' (A : Matrix m n α) (i : m) : A.row i = A i := rfl

@[simp]
/-
**Matrix.col_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_apply (A : Matrix m n α) (i : n) (j : m) : A.col i j = A j i
参数：A : Matrix m n α；i : n；j : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_apply (A : Matrix m n α) (i : n) (j : m) : A.col i j = A j i := rfl

/-- A partially applied version of `Matrix.col_apply` -/
/-
**Matrix.col_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_apply' (A : Matrix m n α) (i : n) : A.col i = fun j => A j i
参数：A : Matrix m n α；i : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partially applied version of `Matrix.col_apply`
-/
lemma col_apply' (A : Matrix m n α) (i : n) : A.col i = fun j ↦ A j i := rfl

section

/-- Two matrices agree if their rows agree. -/
@[local ext]
/-
**Matrix.ext_row** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ext_row {A B : Matrix m n α} (h : forall i, A.row i = B.row i) : A = B
参数：h : forall i, A.row i = B.row i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
Two matrices agree if their rows agree.
-/
lemma ext_row {A B : Matrix m n α} (h : ∀ i, A.row i = B.row i) : A = B :=
  ext fun i j => congr_fun (h i) j

/-- Two matrices agree if their columns agree. -/
@[local ext]
/-
**Matrix.ext_col** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ext_col {A B : Matrix m n α} (h : forall j, A.col j = B.col j) : A = B
参数：h : forall j, A.col j = B.col j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
Two matrices agree if their columns agree.
-/
lemma ext_col {A B : Matrix m n α} (h : ∀ j, A.col j = B.col j) : A = B :=
  ext fun i j => congr_fun (h j) i

end

/-
**Matrix.row_submatrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> 
n) (i : m₀) : (A.submatrix r c).row i = (A.submatrix id c).row (r i)
参数：A : Matrix m n α；r : m₀ -> m；c : n₀ -> n；i : m₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).row i = (A.submatrix id c).row (r i) := rfl
/-
**Matrix.row_submatrix_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c 
: n₀ -> n) (i : m₀) : (A.submatrix r c).row i = A.row (r i) ∘ c
参数：A : Matrix m n α；r : m₀ -> m；c : n₀ -> n；i : m₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (i : m₀) :
    (A.submatrix r c).row i = A.row (r i) ∘ c := rfl
/-
**Matrix.col_submatrix** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c : n₀ -> 
n) (j : n₀) : (A.submatrix r c).col j = (A.submatrix r id).col (c j)
参数：A : Matrix m n α；r : m₀ -> m；c : n₀ -> n；j : n₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_submatrix {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).col j = (A.submatrix r id).col (c j) := rfl
/-
**Matrix.col_submatrix_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ -> m) (c 
: n₀ -> n) (j : n₀) : (A.submatrix r c).col j = A.col (c j) ∘ r
参数：A : Matrix m n α；r : m₀ -> m；c : n₀ -> n；j : n₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_submatrix_eq_comp {m₀ n₀ : Type*} (A : Matrix m n α) (r : m₀ → m) (c : n₀ → n) (j : n₀) :
    (A.submatrix r c).col j = A.col (c j) ∘ r := rfl
/-
**Matrix.row_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_map (A : Matrix m n α) (f : α -> β) (i : m) : (A.map f).row i = f ∘ A.
row i
参数：A : Matrix m n α；f : α -> β；i : m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_map (A : Matrix m n α) (f : α → β) (i : m) : (A.map f).row i = f ∘ A.row i := rfl
/-
**Matrix.col_map** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_map (A : Matrix m n α) (f : α -> β) (j : n) : (A.map f).col j = f ∘ A.
col j
参数：A : Matrix m n α；f : α -> β；j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_map (A : Matrix m n α) (f : α → β) (j : n) : (A.map f).col j = f ∘ A.col j := rfl

@[simp]
/-
**Matrix.row_transpose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：row_transpose (A : Matrix m n α) : Aᵀ.row = A.col
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma row_transpose (A : Matrix m n α) : Aᵀ.row = A.col := rfl

@[simp]
/-
**Matrix.col_transpose** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：col_transpose (A : Matrix m n α) : Aᵀ.col = A.row
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma col_transpose (A : Matrix m n α) : Aᵀ.col = A.row := rfl

end RowCol

end Matrix

namespace Set

/-- Given a set `S`, `S.matrix` is the set of matrices `M`
all of whose entries `M i j` belong to `S`. -/
/-
**Set.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：matrix (S : Set α) : Set (Matrix m n α)
参数：S : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `S`, `S.matrix` is the set of matrices `M`
all of whose entries `M i j` belong to `S`.
-/
def matrix (S : Set α) : Set (Matrix m n α) := {M | ∀ i j, M i j ∈ S}
/-
**Set.mem_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_matrix {S : Set α} {M : Matrix m n α} : M in S.matrix ↔ forall i j, M 
i j in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_matrix {S : Set α} {M : Matrix m n α} :
    M ∈ S.matrix ↔ ∀ i j, M i j ∈ S := .rfl
/-
**Set.matrix_eq_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：matrix_eq_pi {S : Set α} : S.matrix = of.symm ⁻¹' Set.univ.pi fun (_ : m) 
=> Set.univ.pi fun (_ : n) => S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem matrix_eq_pi {S : Set α} :
    S.matrix = of.symm ⁻¹' Set.univ.pi fun (_ : m) ↦ Set.univ.pi fun (_ : n) ↦ S := by
  ext
  simp [Set.mem_matrix]

end Set

namespace Matrix

variable {S : Set α}

@[simp]
/-
**Matrix.transpose_mem_matrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：transpose_mem_matrix_iff {M : Matrix m n α} : Mᵀ in S.matrix ↔ M in S.matr
ix
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem transpose_mem_matrix_iff {M : Matrix m n α} :
    Mᵀ ∈ S.matrix ↔ M ∈ S.matrix := forall_comm
/-
**Matrix.submatrix_mem_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mem_matrix {M : Matrix m n α} {r : l -> m} {c : o -> n} (hM : M 
in S.matrix) : M.submatrix r c in S.matrix
参数：hM : M in S.matrix。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem submatrix_mem_matrix {M : Matrix m n α} {r : l → m} {c : o → n} (hM : M ∈ S.matrix) :
    M.submatrix r c ∈ S.matrix := by simp_all [Set.mem_matrix]
/-
**Matrix.submatrix_mem_matrix_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：submatrix_mem_matrix_iff {M : Matrix m n α} {r : l -> m} {c : o -> n} (hr 
: Function.Surjective r) (hc : Function.Surjective c) : M.submatrix r c in S.mat
rix ↔ M in S.matrix
参数：hr : Function.Surjective r；hc : Function.Surjective c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Matrix.submatrix_mem_matrix`：submatrix_mem_matrix {M : Matrix m n α} {r 
: l -> m} {c : o -> n} (hM : M in S.matrix) : M.submatrix r c in S.matrix
-/
theorem submatrix_mem_matrix_iff {M : Matrix m n α} {r : l → m} {c : o → n}
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    M.submatrix r c ∈ S.matrix ↔ M ∈ S.matrix :=
  ⟨(hr.forall.mpr fun _ => hc.forall.mpr fun _ => · _ _), submatrix_mem_matrix⟩

end Matrix

