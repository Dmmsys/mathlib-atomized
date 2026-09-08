/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Recursive computation rules for the Clifford algebra

This file provides API for a special case `CliffordAlgebra.foldr` of the universal property
`CliffordAlgebra.lift` with `A = Module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `CliffordAlgebra.foldl`, implemented via
`CliffordAlgebra.reverse`

## Main definitions

* `CliffordAlgebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `CliffordAlgebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `CliffordAlgebra.right_induction`: an induction rule that adds generators from the right.
* `CliffordAlgebra.left_induction`: an induction rule that adds generators from the left.
-/

@[expose] public section


universe u1 u2 u3

variable {R M N : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section Foldr

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
/-
**CliffordAlgebra.foldr** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x) :
 N ->ₗ[R] CliffordAlgebra Q ->ₗ[R] N
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf : forall m x, f m (f m x) = Q m • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fold a bilinear map along the generators of a term of the clifford algebra, with
 the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)
`.
-/
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip

@[simp]
/-
**CliffordAlgebra.foldr_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldr Q f hf n (ι Q m) = f m n :=
  LinearMap.congr_fun (lift_ι_apply _ _ _) n

@[simp]
/-
**CliffordAlgebra.foldr_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R) : foldr Q 
f hf n (algebraMap R _ r) = r • n
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
-/
theorem foldr_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldr Q f hf n (algebraMap R _ r) = r • n :=
  LinearMap.congr_fun (AlgHom.commutes _ r) n

@[simp]
/-
**CliffordAlgebra.foldr_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) : foldr Q f hf n 1 = n
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem foldr_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldr Q f hf n 1 = n :=
  LinearMap.congr_fun (map_one (lift Q _)) n

@[simp]
/-
**CliffordAlgebra.foldr_mul** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
 : foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；a b : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem foldr_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
  LinearMap.congr_fun (map_mul (lift Q _) _ _) n

/-- This lemma demonstrates the origin of the `foldr` name. -/
/-
**CliffordAlgebra.foldr_prod_map_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma demonstrates the origin of the `foldr` name.
-/
theorem foldr_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldr Q f hf n (l.map <| ι Q).prod = List.foldr (fun m n => f m n) n l := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
  | cons hd tl ih => rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]

end Foldr

section Foldl

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldl Q f hf n (ι Q m * x) = f m (foldl Q f hf n x)`.

For example, `foldl f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
/-
**CliffordAlgebra.foldl** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldl (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x) :
 N ->ₗ[R] CliffordAlgebra Q ->ₗ[R] N
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf : forall m x, f m (f m x) = Q m • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fold a bilinear map along the generators of a term of the clifford algebra, with
 the rule
given by `foldl Q f hf n (ι Q m * x) = f m (foldl Q f hf n x)`.

For example, `foldl f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)
`.
-/
def foldl (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) :
    N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.compl₂ (foldr Q f hf) reverse

@[simp]
/-
**CliffordAlgebra.foldl_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldl_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra 
Q) : foldl Q f hf n (reverse x) = foldr Q f hf n x
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `CliffordAlgebra.reverse_reverse`：reverse_reverse : forall a : CliffordAl
gebra Q, reverse (reverse a) = a
-/
theorem foldl_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldl Q f hf n (reverse x) = foldr Q f hf n x :=
  DFunLike.congr_arg (foldr Q f hf n) <| reverse_reverse _

@[simp]
/-
**CliffordAlgebra.foldr_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra 
Q) : foldr Q f hf n (reverse x) = foldl Q f hf n x
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_reverse (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldr Q f hf n (reverse x) = foldl Q f hf n x :=
  rfl

@[simp]
/-
**CliffordAlgebra.foldl_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl_ι (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (m : M) : foldl Q f hf n (ι Q m) = f m n := by
  rw [← foldr_reverse, reverse_ι, foldr_ι]

@[simp]
/-
**CliffordAlgebra.foldl_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldl_algebraMap (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R) : foldl Q 
f hf n (algebraMap R _ r) = r • n
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.foldr_reverse`：foldr_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (
hf) (n : N) (x : CliffordAlgebra Q) : foldr Q f hf n (reverse x) = foldl Q f hf 
n x
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `CliffordAlgebra.foldr_algebraMap`：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R
] N) (hf) (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n
-/
theorem foldl_algebraMap (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (r : R) :
    foldl Q f hf n (algebraMap R _ r) = r • n := by
  rw [← foldr_reverse, reverse.commutes, foldr_algebraMap]

@[simp]
/-
**CliffordAlgebra.foldl_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldl_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) : foldl Q f hf n 1 = n
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.foldr_reverse`：foldr_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (
hf) (n : N) (x : CliffordAlgebra Q) : foldr Q f hf n (reverse x) = foldl Q f hf 
n x
· 使用定理 `CliffordAlgebra.reverse.map_one`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M}, Cliffo…
· 使用定理 `CliffordAlgebra.foldr_one`：foldr_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n :
 N) : foldr Q f hf n 1 = n
-/
theorem foldl_one (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) : foldl Q f hf n 1 = n := by
  rw [← foldr_reverse, reverse.map_one, foldr_one]

@[simp]
/-
**CliffordAlgebra.foldl_mul** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldl_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
 : foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b
参数：f : M ->ₗ[R] N ->ₗ[R] N；hf；n : N；a b : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.foldr_reverse`：foldr_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (
hf) (n : N) (x : CliffordAlgebra Q) : foldr Q f hf n (reverse x) = foldl Q f hf 
n x
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `CliffordAlgebra.foldr_mul`：foldr_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n :
 N) (a b : CliffordAlgebra Q) : foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f
 hf n b) a
-/
theorem foldl_mul (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b := by
  rw [← foldr_reverse, ← foldr_reverse, ← foldr_reverse, reverse.map_mul, foldr_mul]

/-- This lemma demonstrates the origin of the `foldl` name. -/
/-
**CliffordAlgebra.foldl_prod_map_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma demonstrates the origin of the `foldl` name.
-/
theorem foldl_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) (hf) (n : N) :
    foldl Q f hf n (l.map <| ι Q).prod = List.foldl (fun m n => f n m) n l := by
  rw [← foldr_reverse, reverse_prod_map_ι, ← List.map_reverse, foldr_prod_map_ι, List.foldr_reverse]

end Foldl

@[elab_as_elim]
/-
**CliffordAlgebra.right_induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：right_induction {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R
, P (algebraMap _ _ r)) (add : forall x y, P x -> P y -> P (x + y)) (mul_ι : for
all m x, P x -> P (x * ι Q m)) : forall x, P x
参数：algebraMap : forall r : R, P (algebraMap _ _ r)；add : forall x y, P x -> P y 
-> P (x + y)；mul_ι : forall m x, P x -> P (x * ι Q m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Submodule.iSup_induction'`：iSup_induction' {ι : Sort*} (p : ι -> Submodu
le R M) {motive : forall x, (x in ⨆ i, p i) -> Prop} (mem : forall (i) (x) (hx :
 x in p i), mot…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.pow_induction_on_right'`：∀ {R : Type u} [inst : CommSemiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A) 
  {C : (n : ℕ) → (x : A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CliffordAlgebra.iSup_ι_range_eq_top`：iSup_ι_range_eq_top : ⨆ i : Nat, Li
nearMap.range (ι Q) ^ i = ⊤
-/
theorem right_induction {P : CliffordAlgebra Q → Prop} (algebraMap : ∀ r : R, P (algebraMap _ _ r))
    (add : ∀ x y, P x → P y → P (x + y)) (mul_ι : ∀ m x, P x → P (x * ι Q m)) : ∀ x, P x := by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `CliffordAlgebra.induction`, but going via the grading seems easier. -/
  intro x
  have : x ∈ ⊤ := Submodule.mem_top (R := R)
  rw [← iSup_ι_range_eq_top] at this
  induction this using Submodule.iSup_induction' with
  | mem i x hx =>
    induction hx using Submodule.pow_induction_on_right' with
    | algebraMap r => exact algebraMap r
    | add _x _y _i _ _ ihx ihy => exact add _ _ ihx ihy
    | mul_mem _i x _hx px m hm =>
      obtain ⟨m, rfl⟩ := hm
      exact mul_ι _ _ px
  | zero => simpa only [map_zero] using algebraMap 0
  | add _x _y _ _ ihx ihy =>
    exact add _ _ ihx ihy

@[elab_as_elim]
/-
**CliffordAlgebra.left_induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：left_induction {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R,
 P (algebraMap _ _ r)) (add : forall x y, P x -> P y -> P (x + y)) (ι_mul : fora
ll x m, P x -> P (ι Q m * x)) : forall x, P x
参数：algebraMap : forall r : R, P (algebraMap _ _ r)；add : forall x y, P x -> P y 
-> P (x + y)；ι_mul : forall x m, P x -> P (ι Q m * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用定理 `CliffordAlgebra.reverse_involutive`：reverse_involutive : Function.Involu
tive (reverse (Q
· 使用定理 `CliffordAlgebra.right_induction`：right_induction {P : CliffordAlgebra Q 
-> Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P 
x -> P y -> P (x + y)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CliffordAlgebra.reverse.map_mul`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadr
aticForm R M} (a b : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
-/
theorem left_induction {P : CliffordAlgebra Q → Prop} (algebraMap : ∀ r : R, P (algebraMap _ _ r))
    (add : ∀ x y, P x → P y → P (x + y)) (ι_mul : ∀ x m, P x → P (ι Q m * x)) : ∀ x, P x := by
  refine reverse_involutive.surjective.forall.2 ?_
  intro x
  induction x using CliffordAlgebra.right_induction with
  | algebraMap r => simpa only [reverse.commutes] using algebraMap r
  | add _ _ hx hy => simpa only [map_add] using add _ _ hx hy
  | mul_ι _ _ hx => simpa only [reverse.map_mul, reverse_ι] using ι_mul _ _ hx

/-! ### Versions with extra state -/


/-- Auxiliary definition for `CliffordAlgebra.foldr'` -/
/-
**CliffordAlgebra.foldr'Aux** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {N : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : AddCommGroup M] →           [inst_2 : AddCommGroup 
N] →             [inst_3 : _root_.Module R M] →               [inst_4 : _root_.M
odule R N] →                 (Q : QuadraticForm R M) →                   (M →ₗ[R
] CliffordAlgebra Q × N →ₗ[R] N) → M →ₗ[R] Module.End R (CliffordAlgebra Q × N)
参数：Q : QuadraticForm R M；M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N；CliffordAlgebra Q
 × N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CliffordAlgebra.foldr'`
-/
def foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) :
    M →ₗ[R] Module.End R (CliffordAlgebra Q × N) := by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearMap.congr_fun (f.map_add _ _) x)
      map_smul' := fun c v =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_smul _ _) x)
            (LinearMap.congr_fun (f.map_smul _ _) x) }
/-
**CliffordAlgebra.foldr'Aux_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (Q : QuadraticForm R M)   (f : M →ₗ[R] CliffordAlgebra 
Q × N →ₗ[R] N) (m : M) (x_fx : CliffordAlgebra Q × N),   ((CliffordAlgebra.foldr
'Aux Q f) m) x_fx = ((CliffordAlgebra.ι Q) m * x_fx.1, (f m) x_fx)
参数：Q : QuadraticForm R M；f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N；m : M；x_fx : 
CliffordAlgebra Q × N；(CliffordAlgebra.foldr'Aux Q f) m；(CliffordAlgebra.ι Q) m 
* x_fx.1, (f m) x_fx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
-/
theorem foldr'Aux_apply_apply (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N) (m : M) (x_fx) :
    foldr'Aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) :=
  rfl
/-
**CliffordAlgebra.foldr'Aux_foldr'Aux** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (Q : QuadraticForm R M)   (f : M →ₗ[R] CliffordAlgebra 
Q × N →ₗ[R] N),   (∀ (m : M) (x : CliffordAlgebra Q) (fx : N), (f m) ((CliffordA
lgebra.ι Q) m * x, (f m) (x, fx)) = Q m • fx) →     ∀ (v : M) (x_fx : CliffordAl
gebra Q × N),       ((CliffordAlgebra.foldr'Aux Q f) v) (((CliffordAlgebra.foldr
'Aux Q f) v) x_fx) = Q v • x_fx
参数：Q : QuadraticForm R M；f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N；∀ (m : M) (x 
: CliffordAlgebra Q) (fx : N), (f m) ((CliffordAlgebra.ι Q) m * x, (f m) (x, fx)
) = Q m • fx；v : M；x_fx : CliffordAlgebra Q × N；(CliffordAlgebra.foldr'Aux Q f) 
v；((CliffordAlgebra.foldr'Aux Q f) v) x_fx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
-/
theorem foldr'Aux_foldr'Aux (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (v : M) (x_fx) :
    foldr'Aux Q f v (foldr'Aux Q f v x_fx) = Q v • x_fx := by
  simp only [foldr'Aux_apply_apply]
  rw [← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, hf, Prod.smul_mk]

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `CliffordAlgebra.foldr`, but with an extra `x` argument.
Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`. -/
/-
**CliffordAlgebra.foldr'** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：foldr'Aux (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N) : M ->ₗ[R] Module.
End R (CliffordAlgebra Q × N)
参数：f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.foldr'Aux_foldr'Aux`：∀ {R : Type u_1} {M : Type u_2} {N 
: Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…

--- 原说明 ---
Fold a bilinear map along the generators of a term of the clifford algebra, with
 the rule
given by `foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)`.
Note this is like `CliffordAlgebra.foldr`, but with an extra `x` argument.
Implement the recursion scheme `F[n0](m * x) = f(m, (x, F[n0](x)))`.
-/
def foldr' (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n : N) : CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)
/-
**CliffordAlgebra.foldr'_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (Q : QuadraticForm R M)   (f : M →ₗ[R] CliffordAlgebra 
Q × N →ₗ[R] N)   (hf : ∀ (m : M) (x : CliffordAlgebra Q) (fx : N), (f m) ((Cliff
ordAlgebra.ι Q) m * x, (f m) (x, fx)) = Q m • fx)   (n : N) (r : R), (CliffordAl
gebra.foldr' Q f hf n) ((algebraMap R (CliffordAlgebra Q)) r) = r • n
参数：Q : QuadraticForm R M；f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N；hf : ∀ (m : M
) (x : CliffordAlgebra Q) (fx : N), (f m) ((CliffordAlgebra.ι Q) m * x, (f m) (x
, fx)) = Q m • fx；n : N；r : R；CliffordAlgebra.foldr' Q f hf n；(algebraMap R (Cli
ffordAlgebra Q)) r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CliffordAlgebra.foldr'Aux_foldr'Aux`：∀ {R : Type u_1} {M : Type u_2} {N 
: Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `CliffordAlgebra.foldr_algebraMap`：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R
] N) (hf) (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n
-/
theorem foldr'_algebraMap (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
    foldr' Q f hf n (algebraMap R _ r) = r • n :=
  congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)
/-
**CliffordAlgebra.foldr'_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr'_ι (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
    foldr' Q f hf n (ι Q m) = f m (1, n) :=
  congr_arg Prod.snd (foldr_ι _ _ _ _ _)
/-
**CliffordAlgebra.foldr'_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr'_ι_mul (f : M →ₗ[R] CliffordAlgebra Q × N →ₗ[R] N)
    (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
    foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) := by
  dsimp [foldr']
  rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply]
  refine congr_arg (f m) (Prod.mk.eta.symm.trans ?_)
  congr 1
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [map_add, Prod.fst_add, hx, hy]
  | ι_mul m x hx => rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply, hx]

end CliffordAlgebra

