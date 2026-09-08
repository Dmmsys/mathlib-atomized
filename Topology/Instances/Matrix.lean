/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `Matrix.topologicalRing`: square matrices form a topological ring

## Main results

* Sets of matrices:
  * `IsOpen.matrix`: the set of finite matrices with entries in an open set
    is itself an open set.
  * `IsCompact.matrix`: the set of matrices with entries in a compact set
    is itself a compact set.
* Continuity:
  * `Continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `Continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `Matrix.transpose_tsum`: transpose commutes with infinite sums
  * `Matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `Matrix.blockDiagonal_tsum`: block diagonal commutes with infinite sums
  * `Matrix.blockDiagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/

public section

assert_not_exists Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup -- guard against import creep

open Matrix

variable {X α l m n p S R : Type*} {m' n' : l → Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
  inferInstanceAs <| TopologicalSpace (m → n → R)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
  inferInstanceAs <| T2Space (m → n → R)

/-- The topology on finite matrices over a discrete space is discrete. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on finite matrices over a discrete space is discrete.
-/
instance [TopologicalSpace R] [Finite m] [Finite n] [DiscreteTopology R] :
    DiscreteTopology (Matrix m n R) :=
  inferInstanceAs <| DiscreteTopology (m → n → R)

section Set

/-
**IsOpen.matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.matrix [Finite m] [Finite n] [TopologicalSpace R] {S : Set R} (hS :
 IsOpen S) : IsOpen (S.matrix : Set (Matrix m n R))
参数：hS : IsOpen S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `isOpen_set_pi`：isOpen_set_pi {i : Set ι} {s : forall a, Set (A a)} (hi :
 i.Finite) (hs : forall a in i, IsOpen (s a)) : IsOpen (pi i s)
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.matrix_eq_pi`：matrix_eq_pi {S : Set α} : S.matrix = of.symm ⁻¹' Set.
univ.pi fun (_ : m) => Set.univ.pi fun (_ : n) => S
-/
theorem IsOpen.matrix [Finite m] [Finite n]
    [TopologicalSpace R] {S : Set R} (hS : IsOpen S) :
    IsOpen (S.matrix : Set (Matrix m n R)) :=
  Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id
/-
**IsCompact.matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.matrix [TopologicalSpace R] {S : Set R} (hS : IsCompact S) : IsC
ompact (S.matrix : Set (Matrix m n R))
参数：hS : IsCompact S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_pi_infinite`：isCompact_pi_infinite {s : forall i, Set (X i)} :
 (forall i, IsCompact (s i)) -> IsCompact { x : forall i, X i | forall i, x i in
 s i }
-/
theorem IsCompact.matrix [TopologicalSpace R] {S : Set R} (hS : IsCompact S) :
    IsCompact (S.matrix : Set (Matrix m n R)) :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

end Set

/-! ### Lemmas about continuity of operations -/

section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousConstSMul α (m → n → R))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousSMul α (m → n → R))
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R) :=
  Pi.continuousAdd
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R) :=
  Pi.continuousNeg
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] [IsTopologicalAddGroup R] : IsTopologicalAddGroup (Matrix m n R) :=
  Pi.topologicalAddGroup

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
/-
**continuous_matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_matrix [TopologicalSpace α] {f : α -> Matrix m n R} (h : forall
 i j, Continuous fun a => f a i j) : Continuous f
参数：h : forall i j, Continuous fun a => f a i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)

--- 原说明 ---
To show a function into matrices is continuous it suffices to show the coefficie
nts of the
resulting matrix are continuous
-/
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R}
    (h : ∀ i j, Continuous fun a => f a i j) : Continuous f :=
  continuous_pi fun _ => continuous_pi fun _ => h _ _
/-
**Continuous.matrix_elem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_elem {A : X -> Matrix m n R} (hA : Continuous A) (i : m)
 (j : n) : Continuous fun x => A x i j
参数：hA : Continuous A；i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply_apply`：continuous_apply_apply {ρ : κ -> ι -> Type*} [fo
rall j i, TopologicalSpace (ρ j i)] (j : κ) (i : ι) : Continuous fun p : forall 
j, forall i,…
-/
theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA
/-
**continuous_matrixOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_matrixOf [TopologicalSpace α] {f : α -> m -> n -> R} : Continuo
us (fun x => Matrix.of (f x)) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma continuous_matrixOf [TopologicalSpace α] {f : α → m → n → R} :
    Continuous (fun x ↦ Matrix.of (f x)) ↔ Continuous f := by
  rfl

@[fun_prop]
alias ⟨_, Continuous.matrixOf⟩ := continuous_matrixOf

@[continuity, fun_prop]
/-
**Continuous.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_map [TopologicalSpace S] {A : X -> Matrix m n S} {f : S 
-> R} (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f
参数：hA : Continuous A；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R}
    (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun _ _ => hf.comp <| hA.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_transpose {A : X -> Matrix m n R} (hA : Continuous A) : 
Continuous fun x => (A x)ᵀ
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i

@[continuity, fun_prop]
/-
**Continuous.matrix_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X -> Matr
ix m n R} (hA : Continuous A) : Continuous fun x => (A x)ᴴ
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.matrix_map`：Continuous.matrix_map [TopologicalSpace S] {A : X
 -> Matrix m n S} {f : S -> R} (hA : Continuous A) (hf : Continuous f) : Continu
ous fun x =…
· 使用定理 `Continuous.matrix_transpose`：Continuous.matrix_transpose {A : X -> Matri
x m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
theorem Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [ContinuousStar R] : ContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conjTranspose⟩

@[continuity, fun_prop]
/-
**Continuous.matrix_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_replicateCol {ι : Type*} {A : X -> n -> R} (hA : Continu
ous A) : Continuous fun x => replicateCol ι (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Continuous.matrix_replicateCol {ι : Type*} {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => replicateCol ι (A x) :=
  continuous_matrix fun i _ => (continuous_apply i).comp hA

@[continuity, fun_prop]
/-
**Continuous.matrix_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_replicateRow {ι : Type*} {A : X -> n -> R} (hA : Continu
ous A) : Continuous fun x => replicateRow ι (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Continuous.matrix_replicateRow {ι : Type*} {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => replicateRow ι (A x) :=
  continuous_matrix fun _ _ => (continuous_apply _).comp hA

@[continuity, fun_prop]
/-
**Continuous.matrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X -> n -> R} (hA 
: Continuous A) : Continuous fun x => diagonal (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.if_const`：Continuous.if_const (p : Prop) [Decidable p] (hf : 
Continuous f) (hg : Continuous g) : Continuous fun a => if p then f a else g a
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
-/
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonal (A x) :=
  continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity, fun_prop]
/-
**Continuous.dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {n : Type u_5} {R : Type u_8} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace R]   [inst_2 : Fintype n] [inst_3 : Mul R] [inst_4 :
 AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R]   {A B : X → n → R}, Conti
nuous A → Continuous B → Continuous fun x => A x ⬝ᵥ B x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
protected theorem Continuous.dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ⬝ᵥ B x := by
  dsimp only [dotProduct]
  fun_prop

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity, fun_prop]
/-
**Continuous.matrix_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd
 R] [ContinuousMul R] {A : X -> Matrix m n R} {B : X -> Matrix n p R} (hA : Cont
inuous A) (hB : Continuous B) : Continuous fun x => A x * B x
参数：hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j

--- 原说明 ---
For square matrices the usual `continuous_mul` can be used.
-/
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => A x * B x :=
  continuous_matrix fun _ _ =>
    continuous_finsetSum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
    ContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype n] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (Matrix n n R) where
/-
**Matrix.topologicalRing** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_5} {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : Fint
ype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopologicalRing R], IsTopological
Ring (Matrix n n R)
参数：Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalSemiringMatrix`：∀ {n : Type u_5} {R : Type u_8} [inst :
 TopologicalSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocSemiring R]
   [IsTopologicalSemi…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instContinuousNegMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} 
[inst : TopologicalSpace R] [inst_1 : Neg R] [ContinuousNeg R],   ContinuousNeg 
(Matrix m n R…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
-/
instance Matrix.topologicalRing [Fintype n] [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsTopologicalRing (Matrix n n R) where

@[continuity, fun_prop]
/-
**Continuous.matrix_vecMulVec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X -> m -> R} {B
 : X -> n -> R} (hA : Continuous A) (hB : Continuous B) : Continuous fun x => ve
cMulVec (A x) (B x)
参数：hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X → m → R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => vecMulVec (A x) (B x) :=
  continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity, fun_prop]
/-
**Continuous.matrix_mulVec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [
ContinuousMul R] [Fintype n] {A : X -> Matrix m n R} {B : X -> n -> R} (hA : Con
tinuous A) (hB : Continuous B) : Continuous fun x => A x *ᵥ B x
参数：hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.dotProduct`：∀ {X : Type u_1} {n : Type u_5} {R : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace R]   [inst_2 : Fintype n] [
inst_3 : Mu…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype n] {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x *ᵥ B x :=
  continuous_pi fun i => ((continuous_apply i).comp hA).dotProduct hB

@[continuity, fun_prop]
/-
**Continuous.matrix_vecMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [
ContinuousMul R] [Fintype m] {A : X -> m -> R} {B : X -> Matrix m n R} (hA : Con
tinuous A) (hB : Continuous B) : Continuous fun x => A x ᵥ* B x
参数：hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.dotProduct`：∀ {X : Type u_1} {n : Type u_5} {R : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace R]   [inst_2 : Fintype n] [
inst_3 : Mu…
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype m] {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ᵥ* B x :=
  continuous_pi fun _i => hA.dotProduct <| continuous_pi fun _j => hB.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_submatrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_submatrix {A : X -> Matrix l n R} (hA : Continuous A) (e
₁ : m -> l) (e₂ : p -> n) : Continuous fun x => (A x).submatrix e₁ e₂
参数：hA : Continuous A；e₁ : m -> l；e₂ : p -> n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_submatrix {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l)
    (e₂ : p → n) : Continuous fun x => (A x).submatrix e₁ e₂ :=
  continuous_matrix fun _i _j => hA.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_reindex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_reindex {A : X -> Matrix l n R} (hA : Continuous A) (e₁ 
: l ≃ m) (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x)
参数：hA : Continuous A；e₁ : l ≃ m；e₂ : n ≃ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.matrix_submatrix`：Continuous.matrix_submatrix {A : X -> Matri
x l n R} (hA : Continuous A) (e₁ : m -> l) (e₂ : p -> n) : Continuous fun x => (
A x).submatrix e₁…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_submatrix _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_diag {A : X -> Matrix n n R} (hA : Continuous A) : Conti
nuous fun x => Matrix.diag (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) :
    Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _

-- note this doesn't elaborate well from the above
/-
**continuous_matrix_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R -> n -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.matrix_diag`：Continuous.matrix_diag {A : X -> Matrix n n R} (
hA : Continuous A) : Continuous fun x => Matrix.diag (A x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R → n → R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity, fun_prop]
/-
**Continuous.matrix_trace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R] {A
 : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x) :=
  continuous_finsetSum _ fun _ _ => hA.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [IsTopologi
calRing R] {A : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x => (A 
x).det
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `continuous_finsetProd`：continuous_finsetProd {f : ι -> X -> M} (s : Fins
et ι) : (forall i in s, Continuous (f i)) -> Continuous fun a => ∏ i in s, f i a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine continuous_finsetSum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finsetProd _ fun l _ => hA.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_updateCol** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_updateCol [DecidableEq n] (i : n) {A : X -> Matrix m n R
} {B : X -> m -> R} (hA : Continuous A) (hB : Continuous B) : Continuous fun x =
> (A x).updateCol i (B x)
参数：i : n；hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
-/
theorem Continuous.matrix_updateCol [DecidableEq n] (i : n) {A : X → Matrix m n R}
    {B : X → m → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).updateCol i (B x) :=
  continuous_matrix fun _j k =>
    (continuous_apply k).comp <|
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity, fun_prop]
/-
**Continuous.matrix_updateRow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X -> Matrix m n R
} {B : X -> n -> R} (hA : Continuous A) (hB : Continuous B) : Continuous fun x =
> (A x).updateRow i (B x)
参数：i : m；hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.update`：Continuous.update [DecidableEq ι] (hf : Continuous f)
 (i : ι) {g : X -> A i} (hg : Continuous g) : Continuous fun a => update (f a) i
 (g a)
-/
theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB

@[continuity, fun_prop]
/-
**Continuous.matrix_cramer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [IsTopol
ogicalRing R] {A : X -> Matrix n n R} {B : X -> n -> R} (hA : Continuous A) (hB 
: Continuous B) : Continuous fun x => cramer (A x) (B x)
参数：hA : Continuous A；hB : Continuous B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `Continuous.matrix_updateCol`：Continuous.matrix_updateCol [DecidableEq n]
 (i : n) {A : X -> Matrix m n R} {B : X -> m -> R} (hA : Continuous A) (hB : Con
tinuous B) : Cont…
-/
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => cramer (A x) (B x) :=
  continuous_pi fun _ => (hA.matrix_updateCol _ hB).matrix_det

@[continuity, fun_prop]
/-
**Continuous.matrix_adjugate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [IsTop
ologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x =
> (A x).adjugate
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `Continuous.matrix_updateCol`：Continuous.matrix_updateCol [DecidableEq n]
 (i : n) {A : X -> Matrix m n R} {B : X -> m -> R} (hA : Continuous A) (hB : Con
tinuous B) : Cont…
· 使用定理 `Continuous.matrix_transpose`：Continuous.matrix_transpose {A : X -> Matri
x m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateCol k continuous_const).matrix_det

/-- When `Ring.inverse` is continuous at the determinant (such as in a `NormedRing`, or a
topological field), so is `Matrix.inv`. -/
/-
**continuousAt_matrix_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [IsTopolo
gicalRing R] (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : Continuo
usAt Inv.inv A
参数：A : Matrix n n R；h : ContinuousAt Ring.inverse A.det。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.smul`：ContinuousAt.smul (hf : ContinuousAt f b) (hg : Conti
nuousAt g b) : ContinuousAt (f • g) b
· 使用定理 `instContinuousSMulMatrix`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5}
 {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   [ins
t_2 : SMul α R…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.matrix_det`：Continuous.matrix_det [Fintype n] [DecidableEq n]
 [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Continuous A) 
: Continuou…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.matrix_adjugate`：Continuous.matrix_adjugate [Fintype n] [Deci
dableEq n] [CommRing R] [IsTopologicalRing R] {A : X -> Matrix n n R} (hA : Cont
inuous A) : Cont…

--- 原说明 ---
When `Ring.inverse` is continuous at the determinant (such as in a `NormedRing`,
 or a
topological field), so is `Matrix.inv`.
-/
theorem continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt

namespace Topology

variable {m n R S : Type*} [TopologicalSpace R] [TopologicalSpace S] {f : R → S}

/-
**Topology.IsInducing.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsInducing`
。
形式化陈述：∀ {m : Type u_11} {n : Type u_12} {R : Type u_13} {S : Type u_14} [inst : 
TopologicalSpace R]   [inst_1 : TopologicalSpace S] {f : R → S}, Topology.IsIndu
cing f → Topology.IsInducing fun x => x.map f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι → 
Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topological
Space (B i)] {f…
-/
lemma IsInducing.matrix_map (hf : IsInducing f) :
    IsInducing (map · f : Matrix m n R → Matrix m n S) :=
  IsInducing.piMap fun _ : m ↦ (IsInducing.piMap fun _ : n ↦ hf)
/-
**Topology.IsEmbedding.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsEmbeddin
g`。
形式化陈述：∀ {m : Type u_11} {n : Type u_12} {R : Type u_13} {S : Type u_14} [inst : 
TopologicalSpace R]   [inst_1 : TopologicalSpace S] {f : R → S}, Topology.IsEmbe
dding f → Topology.IsEmbedding fun x => x.map f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B : ι →
 Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topologica
lSpace (B i)] {f…
-/
lemma IsEmbedding.matrix_map (hf : IsEmbedding f) :
    IsEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsEmbedding.piMap fun _ : m ↦ (IsEmbedding.piMap fun _ : n ↦ hf)
/-
**Topology.IsClosedEmbedding.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsCl
osedEmbedding`。
形式化陈述：∀ {m : Type u_11} {n : Type u_12} {R : Type u_13} {S : Type u_14} [inst : 
TopologicalSpace R]   [inst_1 : TopologicalSpace S] {f : R → S}, Topology.IsClos
edEmbedding f → Topology.IsClosedEmbedding fun x => x.map f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B
 : ι → Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topo
logicalSpace (B i)] {f…
-/
lemma IsClosedEmbedding.matrix_map (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsClosedEmbedding.piMap fun _ : m ↦ (IsClosedEmbedding.piMap fun _ : n ↦ hf)
/-
**Topology.IsOpenEmbedding.matrix_map** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsOpen
Embedding`。
形式化陈述：∀ {m : Type u_11} {n : Type u_12} {R : Type u_13} {S : Type u_14} [inst : 
TopologicalSpace R]   [inst_1 : TopologicalSpace S] {f : R → S} [Finite m] [Fini
te n],   Topology.IsOpenEmbedding f → Topology.IsOpenEmbedding fun x => x.map f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.piMap`：∀ {ι : Type u_5} {A : ι → Type u_6} {B :
 ι → Type u_7} [T : (i : ι) → TopologicalSpace (A i)]   [inst : (i : ι) → Topolo
gicalSpace (B i)] [F…
-/
lemma IsOpenEmbedding.matrix_map [Finite m] [Finite n] (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (map · f : Matrix m n R → Matrix m n S) :=
  IsOpenEmbedding.piMap fun _ : m ↦ (IsOpenEmbedding.piMap fun _ : n ↦ hf)

end Topology

-- lemmas about functions in `Mathlib/Data/Matrix/Block.lean`
section BlockMatrices

@[continuity, fun_prop]
/-
**Continuous.matrix_fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_fromBlocks {A : X -> Matrix n l R} {B : X -> Matrix n m 
R} {C : X -> Matrix p l R} {D : X -> Matrix p m R} (hA : Continuous A) (hB : Con
tinuous B) (hC : Continuous C) (hD : Continuous D) : Continuous fun x => Matrix.
fromBlocks (A x) (B x) (C x) (D x)
参数：hA : Continuous A；hB : Continuous B；hC : Continuous C；hD : Continuous D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_fromBlocks {A : X → Matrix n l R} {B : X → Matrix n m R}
    {C : X → Matrix p l R} {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix <| by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption

@[continuity, fun_prop]
/-
**Continuous.matrix_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X -> p -> Ma
trix m n R} (hA : Continuous A) : Continuous fun x => blockDiagonal (A x)
参数：hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.if_const`：Continuous.if_const (p : Prop) [Decidable p] (hf : 
Continuous f) (hg : Continuous g) : Continuous fun a => if p then f a else g a
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
-/
theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity, fun_prop]
/-
**Continuous.matrix_blockDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_blockDiag {A : X -> Matrix (m × p) (n × p) R} (hA : Cont
inuous A) : Continuous fun x => blockDiag (A x)
参数：m × p；n × p；hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_blockDiag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiag (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

@[continuity, fun_prop]
/-
**Continuous.matrix_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l] {A : X -> forall
 i, Matrix (m' i) (n' i) R} (hA : Continuous A) : Continuous fun x => blockDiago
nal' (A x)
参数：m' i；n' i；hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    {A : X → ∀ i, Matrix (m' i) (n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiagonal' (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const

@[continuity, fun_prop]
/-
**Continuous.matrix_blockDiag'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.matrix_blockDiag' {A : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (
hA : Continuous A) : Continuous fun x => blockDiag' (A x)
参数：Σ i, m' i；Σ i, n' i；hA : Continuous A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `continuous_matrix`：continuous_matrix [TopologicalSpace α] {f : α -> Matr
ix m n R} (h : forall i j, Continuous fun a => f a i j) : Continuous f
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
-/
theorem Continuous.matrix_blockDiag'
    {A : X → Matrix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag' (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _
/-
**isClosed_setOfPred_blockTriangular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_blockTriangular {α : Type*} {b : m -> α} [LinearOrder α
] [Zero R] [T2Space R] : IsClosed {M : Matrix m m R | M.BlockTriangular b}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.matrix_elem`：Continuous.matrix_elem {A : X -> Matrix m n R} (
hA : Continuous A) (i : m) (j : n) : Continuous fun x => A x i j
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem isClosed_setOfPred_blockTriangular {α : Type*} {b : m → α} [LinearOrder α] [Zero R]
    [T2Space R] : IsClosed {M : Matrix m m R | M.BlockTriangular b} := by
  simp only [BlockTriangular, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_blockTriangular := isClosed_setOfPred_blockTriangular

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [AddCommMonoid R] [TopologicalSpace R] {L : SummationFilter X}

/-
**HasSum.matrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_transpose {f : X -> Matrix m n R} {a : Matrix m n R} (hf : H
asSum f a L) : HasSum (fun x => (f x)ᵀ) aᵀ L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_transpose`：Continuous.matrix_transpose {A : X -> Matri
x m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_transpose {f : X → Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => (f x)ᵀ) aᵀ L :=
  (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose :)
/-
**Summable.matrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_transpose {f : X -> Matrix m n R} (hf : Summable f L) : Su
mmable (fun x => (f x)ᵀ) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_transpose`：HasSum.matrix_transpose {f : X -> Matrix m n R}
 {a : Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => (f x)ᵀ) aᵀ L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_transpose {f : X → Matrix m n R} (hf : Summable f L) :
    Summable (fun x => (f x)ᵀ) L :=
  hf.hasSum.matrix_transpose.summable

@[simp]
/-
**summable_matrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_matrix_transpose {f : X -> Matrix m n R} : (Summable (fun x => (f
 x)ᵀ) L) ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_equiv`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : Summ
ationFilter β} …
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_transpose`：Continuous.matrix_transpose {A : X -> Matri
x m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem summable_matrix_transpose {f : X → Matrix m n R} :
    (Summable (fun x => (f x)ᵀ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose
/-
**Matrix.transpose_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.transpose_tsum [T2Space R] {f : X -> Matrix m n R} : (∑'[L] x, f x)
ᵀ = ∑'[L] x, (f x)ᵀ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_transpose`：Continuous.matrix_transpose {A : X -> Matri
x m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
-/
theorem Matrix.transpose_tsum [T2Space R] {f : X → Matrix m n R} :
    (∑'[L] x, f x)ᵀ = ∑'[L] x, (f x)ᵀ :=
  Function.LeftInverse.map_tsum f (g := transposeAddEquiv m n R) continuous_id.matrix_transpose
    continuous_id.matrix_transpose transpose_transpose
/-
**HasSum.matrix_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X ->
 Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => (f x)ᴴ)
 aᴴ L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_conjTranspose`：Continuous.matrix_conjTranspose [Star R
] [ContinuousStar R] {A : X -> Matrix m n R} (hA : Continuous A) : Continuous fu
n x => (A x)ᴴ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    {a : Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => (f x)ᴴ) aᴴ L :=
  (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose :)
/-
**Summable.matrix_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X 
-> Matrix m n R} (hf : Summable f L) : Summable (fun x => (f x)ᴴ) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_conjTranspose`：HasSum.matrix_conjTranspose [StarAddMonoid 
R] [ContinuousStar R] {f : X -> Matrix m n R} {a : Matrix m n R} (hf : HasSum f 
a L) : HasSum (fu…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    (hf : Summable f L) : Summable (fun x => (f x)ᴴ) L :=
  hf.hasSum.matrix_conjTranspose.summable

@[simp]
/-
**summable_matrix_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X 
-> Matrix m n R} : (Summable (fun x => (f x)ᴴ) L) ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_equiv`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : Summ
ationFilter β} …
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_conjTranspose`：Continuous.matrix_conjTranspose [Star R
] [ContinuousStar R] {A : X -> Matrix m n R} (hA : Continuous A) : Continuous fu
n x => (A x)ᴴ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R} :
    (Summable (fun x => (f x)ᴴ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
/-
**Matrix.conjTranspose_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
 {f : X -> Matrix m n R} : (∑'[L] x, f x)ᴴ = ∑'[L] x, (f x)ᴴ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Continuous.matrix_conjTranspose`：Continuous.matrix_conjTranspose [Star R
] [ContinuousStar R] {A : X -> Matrix m n R} (hA : Continuous A) : Continuous fu
n x => (A x)ᴴ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
-/
theorem Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {f : X → Matrix m n R} : (∑'[L] x, f x)ᴴ = ∑'[L] x, (f x)ᴴ :=
  Function.LeftInverse.map_tsum f (g := conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
    conjTranspose_conjTranspose
/-
**HasSum.matrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_diagonal [DecidableEq n] {f : X -> n -> R} {a : n -> R} (hf 
: HasSum f a L) : HasSum (fun x => diagonal (f x)) (diagonal a) L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_diagonal`：Continuous.matrix_diagonal [Zero R] [Decidab
leEq n] {A : X -> n -> R} (hA : Continuous A) : Continuous fun x => diagonal (A 
x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_diagonal [DecidableEq n] {f : X → n → R} {a : n → R} (hf : HasSum f a L) :
    HasSum (fun x => diagonal (f x)) (diagonal a) L :=
  hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal
/-
**Summable.matrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_diagonal [DecidableEq n] {f : X -> n -> R} (hf : Summable 
f L) : Summable (fun x => diagonal (f x)) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_diagonal`：HasSum.matrix_diagonal [DecidableEq n] {f : X ->
 n -> R} {a : n -> R} (hf : HasSum f a L) : HasSum (fun x => diagonal (f x)) (di
agonal a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_diagonal [DecidableEq n] {f : X → n → R} (hf : Summable f L) :
    Summable (fun x => diagonal (f x)) L :=
  hf.hasSum.matrix_diagonal.summable

@[simp]
/-
**summable_matrix_diagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_matrix_diagonal [DecidableEq n] {f : X -> n -> R} : (Summable (fu
n x => diagonal (f x)) L) ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_leftInverse`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L 
: SummationFilter β} …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_diagonal`：Continuous.matrix_diagonal [Zero R] [Decidab
leEq n] {A : X -> n -> R} (hA : Continuous A) : Continuous fun x => diagonal (A 
x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_matrix_diag`：continuous_matrix_diag : Continuous (Matrix.diag
 : Matrix n n R -> n -> R)
· 使用定理 `Matrix.diag_diagonal`：diag_diagonal [DecidableEq n] [Zero α] (a : n -> α
) : diag (diagonal a) = a
-/
theorem summable_matrix_diagonal [DecidableEq n] {f : X → n → R} :
    (Summable (fun x => diagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A
/-
**Matrix.diagonal_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X -> n -> R} : diago
nal (∑'[L] x, f x) = ∑'[L] x, diagonal (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_diagonal`：Continuous.matrix_diagonal [Zero R] [Decidab
leEq n] {A : X -> n -> R} (hA : Continuous A) : Continuous fun x => diagonal (A 
x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_matrix_diag`：continuous_matrix_diag : Continuous (Matrix.diag
 : Matrix n n R -> n -> R)
· 使用定理 `Matrix.diag_diagonal`：diag_diagonal [DecidableEq n] [Zero α] (a : n -> α
) : diag (diagonal a) = a
-/
theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X → n → R} :
    diagonal (∑'[L] x, f x) = ∑'[L] x, diagonal (f x) :=
  Function.LeftInverse.map_tsum f (g := diagonalAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag diag_diagonal
/-
**HasSum.matrix_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_diag {f : X -> Matrix n n R} {a : Matrix n n R} (hf : HasSum
 f a L) : HasSum (fun x => diag (f x)) (diag a) L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `continuous_matrix_diag`：continuous_matrix_diag : Continuous (Matrix.diag
 : Matrix n n R -> n -> R)
-/
theorem HasSum.matrix_diag {f : X → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a L) :
    HasSum (fun x => diag (f x)) (diag a) L :=
  hf.map (diagAddMonoidHom n R) continuous_matrix_diag
/-
**Summable.matrix_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_diag {f : X -> Matrix n n R} (hf : Summable f L) : Summabl
e (fun x => diag (f x)) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_diag`：HasSum.matrix_diag {f : X -> Matrix n n R} {a : Matr
ix n n R} (hf : HasSum f a L) : HasSum (fun x => diag (f x)) (diag a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_diag {f : X → Matrix n n R} (hf : Summable f L) :
    Summable (fun x => diag (f x)) L :=
  hf.hasSum.matrix_diag.summable

section BlockMatrices

/-
**HasSum.matrix_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R} {
a : p -> Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => blockDiagonal (f x
)) (blockDiagonal a) L
参数：hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal`：Continuous.matrix_blockDiagonal [Zero R
] [DecidableEq p] {A : X -> p -> Matrix m n R} (hA : Continuous A) : Continuous 
fun x => blockDiagona…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    {a : p → Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal (f x)) (blockDiagonal a) L :=
  hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
/-
**Summable.matrix_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R}
 (hf : Summable f L) : Summable (fun x => blockDiagonal (f x)) L
参数：hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_blockDiagonal`：HasSum.matrix_blockDiagonal [DecidableEq p]
 {f : X -> p -> Matrix m n R} {a : p -> Matrix m n R} (hf : HasSum f a L) : HasS
um (fun x => bloc…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal (f x)) L :=
  hf.hasSum.matrix_blockDiagonal.summable
/-
**summable_matrix_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R}
 : (Summable (fun x => blockDiagonal (f x)) L) ↔ Summable f L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_leftInverse`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L 
: SummationFilter β} …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal`：Continuous.matrix_blockDiagonal [Zero R
] [DecidableEq p] {A : X -> p -> Matrix m n R} (hA : Continuous A) : Continuous 
fun x => blockDiagona…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.matrix_blockDiag`：Continuous.matrix_blockDiag {A : X -> Matri
x (m × p) (n × p) R} (hA : Continuous A) : Continuous fun x => blockDiag (A x)
· 使用定理 `Matrix.blockDiag_blockDiagonal`：blockDiag_blockDiagonal [DecidableEq o] 
(M : o -> Matrix m n α) : blockDiag (blockDiagonal M) = M
-/
theorem summable_matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} :
    (Summable (fun x => blockDiagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A
/-
**Matrix.blockDiagonal_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X -> p -> Matri
x m n R} : blockDiagonal (∑'[L] x, f x) = ∑'[L] x, blockDiagonal (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal`：Continuous.matrix_blockDiagonal [Zero R
] [DecidableEq p] {A : X -> p -> Matrix m n R} (hA : Continuous A) : Continuous 
fun x => blockDiagona…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.matrix_blockDiag`：Continuous.matrix_blockDiag {A : X -> Matri
x (m × p) (n × p) R} (hA : Continuous A) : Continuous fun x => blockDiag (A x)
· 使用定理 `Matrix.blockDiag_blockDiagonal`：blockDiag_blockDiagonal [DecidableEq o] 
(M : o -> Matrix m n α) : blockDiag (blockDiagonal M) = M
-/
theorem Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X → p → Matrix m n R} :
    blockDiagonal (∑'[L] x, f x) = ∑'[L] x, blockDiagonal (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonalAddMonoidHom m n p R) f
    continuous_id.matrix_blockDiagonal continuous_id.matrix_blockDiag blockDiag_blockDiagonal
/-
**HasSum.matrix_blockDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_blockDiag {f : X -> Matrix (m × p) (n × p) R} {a : Matrix (m
 × p) (n × p) R} (hf : HasSum f a L) : HasSum (fun x => blockDiag (f x)) (blockD
iag a) L
参数：m × p；n × p；m × p；n × p；hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiag`：Continuous.matrix_blockDiag {A : X -> Matri
x (m × p) (n × p) R} (hA : Continuous A) : Continuous fun x => blockDiag (A x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
    (hf : HasSum f a L) : HasSum (fun x => blockDiag (f x)) (blockDiag a) L :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id :)
/-
**Summable.matrix_blockDiag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_blockDiag {f : X -> Matrix (m × p) (n × p) R} (hf : Summab
le f L) : Summable (fun x => blockDiag (f x)) L
参数：m × p；n × p；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_blockDiag`：HasSum.matrix_blockDiag {f : X -> Matrix (m × p
) (n × p) R} {a : Matrix (m × p) (n × p) R} (hf : HasSum f a L) : HasSum (fun x 
=> blockDiag …
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} (hf : Summable f L) :
    Summable (fun x => blockDiag (f x)) L :=
  hf.hasSum.matrix_blockDiag.summable
/-
**HasSum.matrix_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix (m
' i) (n' i) R} {a : forall i, Matrix (m' i) (n' i) R} (hf : HasSum f a L) : HasS
um (fun x => blockDiagonal' (f x)) (blockDiagonal' a) L
参数：m' i；n' i；m' i；n' i；hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal'`：Continuous.matrix_blockDiagonal' [Zero
 R] [DecidableEq l] {A : X -> forall i, Matrix (m' i) (n' i) R} (hA : Continuous
 A) : Continuous fun x…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    {a : ∀ i, Matrix (m' i) (n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal' (f x)) (blockDiagonal' a) L :=
  hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
/-
**Summable.matrix_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix 
(m' i) (n' i) R} (hf : Summable f L) : Summable (fun x => blockDiagonal' (f x)) 
L
参数：m' i；n' i；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_blockDiagonal'`：HasSum.matrix_blockDiagonal' [DecidableEq 
l] {f : X -> forall i, Matrix (m' i) (n' i) R} {a : forall i, Matrix (m' i) (n' 
i) R} (hf : HasSum…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal' (f x)) L :=
  hf.hasSum.matrix_blockDiagonal'.summable
/-
**summable_matrix_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix 
(m' i) (n' i) R} : (Summable (fun x => blockDiagonal' (f x)) L) ↔ Summable f L
参数：m' i；n' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.map_iff_of_leftInverse`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L 
: SummationFilter β} …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal'`：Continuous.matrix_blockDiagonal' [Zero
 R] [DecidableEq l] {A : X -> forall i, Matrix (m' i) (n' i) R} (hA : Continuous
 A) : Continuous fun x…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.matrix_blockDiag'`：Continuous.matrix_blockDiag' {A : X -> Mat
rix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) : Continuous fun x => blockDi
ag' (A x)
· 使用定理 `Matrix.blockDiag'_blockDiagonal'`：∀ {o : Type u_4} {m' : o → Type u_7} {
n' : o → Type u_8} {α : Type u_12} [inst : Zero α] [inst_1 : DecidableEq o]   (M
 : (i : o) → Matrix (m…
-/
theorem summable_matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    (Summable (fun x => blockDiagonal' (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A
/-
**Matrix.blockDiagonal'_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {X : Type u_1} {l : Type u_3} {R : Type u_8} {m' : l → Type u_9} {n' : l
 → Type u_10} [inst : AddCommMonoid R]   [inst_1 : TopologicalSpace R] {L : Summ
ationFilter X} [inst_2 : DecidableEq l] [T2Space R]   {f : X → (i : l) → Matrix 
(m' i) (n' i) R},   Matrix.blockDiagonal' (∑'[L] (x : X), f x) = ∑'[L] (x : X), 
Matrix.blockDiagonal' (f x)
参数：i : l；m' i；n' i；∑'[L] (x : X), f x；x : X；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type
 u_3} [inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFil
ter β} {G : Type u_…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiagonal'`：Continuous.matrix_blockDiagonal' [Zero
 R] [DecidableEq l] {A : X -> forall i, Matrix (m' i) (n' i) R} (hA : Continuous
 A) : Continuous fun x…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.matrix_blockDiag'`：Continuous.matrix_blockDiag' {A : X -> Mat
rix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) : Continuous fun x => blockDi
ag' (A x)
· 使用定理 `Matrix.blockDiag'_blockDiagonal'`：∀ {o : Type u_4} {m' : o → Type u_7} {
n' : o → Type u_8} {α : Type u_12} [inst : Zero α] [inst_1 : DecidableEq o]   (M
 : (i : o) → Matrix (m…
-/
theorem Matrix.blockDiagonal'_tsum [DecidableEq l] [T2Space R]
    {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    blockDiagonal' (∑'[L] x, f x) = ∑'[L] x, blockDiagonal' (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonal'AddMonoidHom m' n' R) f
    continuous_id.matrix_blockDiagonal' continuous_id.matrix_blockDiag' blockDiag'_blockDiagonal'
/-
**HasSum.matrix_blockDiag'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.matrix_blockDiag' {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} {a : 
Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : HasSum f a L) : HasSum (fun x => blockDi
ag' (f x)) (blockDiag' a) L
参数：Σ i, m' i；Σ i, n' i；Σ i, m' i；Σ i, n' i；hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.matrix_blockDiag'`：Continuous.matrix_blockDiag' {A : X -> Mat
rix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) : Continuous fun x => blockDi
ag' (A x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasSum.matrix_blockDiag' {f : X → Matrix (Σ i, m' i) (Σ i, n' i) R}
    {a : Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiag' (f x)) (blockDiag' a) L :=
  hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'
/-
**Summable.matrix_blockDiag'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.matrix_blockDiag' {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (hf
 : Summable f L) : Summable (fun x => blockDiag' (f x)) L
参数：Σ i, m' i；Σ i, n' i；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.matrix_blockDiag'`：HasSum.matrix_blockDiag' {f : X -> Matrix (Σ i
, m' i) (Σ i, n' i) R} {a : Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : HasSum f a L
) : HasSum (fu…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.matrix_blockDiag' {f : X → Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : Summable f L) :
    Summable (fun x => blockDiag' (f x)) L :=
  hf.hasSum.matrix_blockDiag'.summable

end BlockMatrices

end tsum

