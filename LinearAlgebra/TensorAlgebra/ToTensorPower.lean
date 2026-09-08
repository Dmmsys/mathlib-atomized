/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `TensorAlgebra R M` is isomorphic to a direct sum of tensor powers, as
`TensorAlgebra.equivDirectSum`.
-/

@[expose] public section

open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

/-- The canonical embedding from a tensor power to the tensor algebra -/
/-
**TensorPower.toTensorAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
形式化陈述：toTensorAlgebra {n} : ⨂[R]^n M ->ₗ[R] TensorAlgebra R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding from a tensor power to the tensor algebra
-/
def toTensorAlgebra {n} : ⨂[R]^n M →ₗ[R] TensorAlgebra R M :=
  PiTensorProduct.lift (TensorAlgebra.tprod R M n)

@[simp]
/-
**TensorPower.toTensorAlgebra_tprod** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：toTensorAlgebra_tprod {n} (x : Fin n -> M) : TensorPower.toTensorAlgebra (
PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x
参数：x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
-/
theorem toTensorAlgebra_tprod {n} (x : Fin n → M) :
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x :=
  PiTensorProduct.lift.tprod _

@[simp]
/-
**TensorPower.toTensorAlgebra_gOne** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：toTensorAlgebra_gOne : TensorPower.toTensorAlgebra (@GradedMonoid.GOne.one
 _ (fun n => ⨂[R]^n M) _ _) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.toTensorAlgebra_tprod`：toTensorAlgebra_tprod {n} (x : Fin n 
-> M) : TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.
tprod R M n x
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toTensorAlgebra_gOne :
    TensorPower.toTensorAlgebra (@GradedMonoid.GOne.one _ (fun n => ⨂[R]^n M) _ _) = 1 := by
  simp [GradedMonoid.GOne.one, TensorPower.toTensorAlgebra_tprod]

@[simp]
/-
**TensorPower.toTensorAlgebra_gMul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPower`。
形式化陈述：toTensorAlgebra_gMul {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) : TensorPower
.toTensorAlgebra (@GradedMonoid.GMul.mul _ (fun n => ⨂[R]^n M) _ _ _ _ a b) = Te
nsorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b
参数：a : (⨂[R]^i) M；b : (⨂[R]^j) M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiTensorProduct.instSMulCommClass`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.instIsScalarTower`：∀ {ι : Type u_1} {R : Type u_4} [inst
 : CommSemiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]  
 [inst_2 : (i : ι) → _r…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.gMul_eq_coe_linearMap`：gMul_eq_coe_linearMap {i j} (a : ⨂[R]
^i M) (b : (⨂[R]^j) M) : a ₜ* b = ((TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : 
_ ≃ₗ[R] (⨂[R]^(i + j)) …
· 使用定理 `TensorAlgebra.instSMulCommClass`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst
_2 : AddCommMonoid M]…
· 使用定理 `TensorAlgebra.instIsScalarTower`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst
_2 : AddCommMonoid M]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.compr₂_apply`：compr₂_apply [Module R A] [Module A M] [Module A
 Qₗ] [SMulCommClass R A Qₗ] [IsScalarTower R A Qₗ] [IsScalarTower R A Pₗ] (f : M
 ->ₗ[A] Nₗ -…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.mul_apply'`：mul_apply' (a b : A) : mul R A a b = a * b
· 使用定理 `LinearMap.compl₂_apply`：compl₂_apply (h : M ->ₛₗ[σ₁₅] N ->ₛₗ[σ₂₃] P) (g 
: Q ->ₛₗ[σ₄₂] N) (m : M) (q : Q) : h.compl₂ g m q = h m (g q)
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorPower.tprod_mul_tprod`：tprod_mul_tprod {na nb} (a : Fin na -> M) (
b : Fin nb -> M) : tprod R a ₜ* tprod R b = tprod R (Fin.append a b)
· 使用定理 `TensorPower.toTensorAlgebra_tprod`：toTensorAlgebra_tprod {n} (x : Fin n 
-> M) : TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.
tprod R M n x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.ofFn_comp'`：ofFn_comp' {β : Type*} {n : Nat} (f : Fin n -> α) (g : 
α -> β) : ofFn (fun i => g (f i)) = map g (ofFn f)
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.ofFn_fin_append`：ofFn_fin_append {m n} (a : Fin m -> α) (b : Fin n 
-> α) : List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
-/
theorem toTensorAlgebra_gMul {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    TensorPower.toTensorAlgebra (@GradedMonoid.GMul.mul _ (fun n => ⨂[R]^n M) _ _ _ _ a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b := by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap, ← LinearMap.compr₂_apply, ← @LinearMap.mul_apply' R, ←
    LinearMap.compl₂_apply, ← LinearMap.comp_apply]
  refine LinearMap.congr_fun (LinearMap.congr_fun ?_ a) b
  clear! a b
  ext (a b)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, ← gMul_def,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, tprod_mul_tprod, toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  refine Eq.trans ?_ List.prod_append
  congr
  rw [List.ofFn_comp' _ (TensorAlgebra.ι R), List.ofFn_comp' _ (TensorAlgebra.ι R),
    List.ofFn_comp' _ (TensorAlgebra.ι R), ← List.map_append, List.ofFn_fin_append]

@[simp]
/-
**TensorPower.toTensorAlgebra_galgebra_toFun** 是 Mathlib 中的一个定理，位于命名空间 `TensorPo
wer`。
形式化陈述：toTensorAlgebra_galgebra_toFun (r : R) : TensorPower.toTensorAlgebra (Dire
ctSum.GAlgebra.toFun (R
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorPower.galgebra_toFun_def`：galgebra_toFun_def (r : R) : DirectSum.G
Algebra.toFun (A
· 使用定理 `TensorPower.algebraMap₀_eq_smul_one`：algebraMap₀_eq_smul_one (r : R) : (
algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `TensorPower.toTensorAlgebra_gOne`：toTensorAlgebra_gOne : TensorPower.toT
ensorAlgebra (@GradedMonoid.GOne.one _ (fun n => ⨂[R]^n M) _ _) = 1
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem toTensorAlgebra_galgebra_toFun (r : R) :
    TensorPower.toTensorAlgebra (DirectSum.GAlgebra.toFun (R := R) (A := fun n => ⨂[R]^n M) r) =
      algebraMap _ _ r := by
  rw [TensorPower.galgebra_toFun_def, TensorPower.algebraMap₀_eq_smul_one, map_smul,
    TensorPower.toTensorAlgebra_gOne, Algebra.algebraMap_eq_smul_one]

end TensorPower

namespace TensorAlgebra

/-- The canonical map from a direct sum of tensor powers to the tensor algebra. -/
/-
**TensorAlgebra.ofDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：ofDirectSum : (⨁ n, ⨂[R]^n M) ->ₐ[R] TensorAlgebra R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorPower.toTensorAlgebra_gOne`：toTensorAlgebra_gOne : TensorPower.toT
ensorAlgebra (@GradedMonoid.GOne.one _ (fun n => ⨂[R]^n M) _ _) = 1
· 使用定理 `TensorPower.toTensorAlgebra_gMul`：toTensorAlgebra_gMul {i j} (a : (⨂[R]^
i) M) (b : (⨂[R]^j) M) : TensorPower.toTensorAlgebra (@GradedMonoid.GMul.mul _ (
fun n => ⨂[R]^n M) _ _…

--- 原说明 ---
The canonical map from a direct sum of tensor powers to the tensor algebra.
-/
def ofDirectSum : (⨁ n, ⨂[R]^n M) →ₐ[R] TensorAlgebra R M :=
  DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

@[simp]
/-
**TensorAlgebra.ofDirectSum_of_tprod** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
形式化陈述：ofDirectSum_of_tprod {n} (x : Fin n -> M) : ofDirectSum (DirectSum.of _ n 
(PiTensorProduct.tprod R x)) = tprod R M n x
参数：x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
· 使用定理 `TensorPower.toTensorAlgebra_tprod`：toTensorAlgebra_tprod {n} (x : Fin n 
-> M) : TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.
tprod R M n x
-/
theorem ofDirectSum_of_tprod {n} (x : Fin n → M) :
    ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n x :=
  (DirectSum.toAddMonoid_of
    (fun _ ↦ LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)

/-- The canonical map from the tensor algebra to a direct sum of tensor powers. -/
/-
**TensorAlgebra.toDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：toDirectSum : TensorAlgebra R M ->ₐ[R] ⨁ n, ⨂[R]^n M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)

--- 原说明 ---
The canonical map from the tensor algebra to a direct sum of tensor powers.
-/
def toDirectSum : TensorAlgebra R M →ₐ[R] ⨁ n, ⨂[R]^n M :=
  TensorAlgebra.lift R <|
    DirectSum.lof R ℕ (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]
/-
**TensorAlgebra.toDirectSum_** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDirectSum_ι (x : M) :
    toDirectSum (ι R x) =
      DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => x) := by
  simp [toDirectSum, TensorAlgebra.lift_ι_apply, DirectSum.lof_eq_of]
/-
**TensorAlgebra.ofDirectSum_comp_toDirectSum** 是 Mathlib 中的一个定理，位于命名空间 `TensorAl
gebra`。
形式化陈述：ofDirectSum_comp_toDirectSum : ofDirectSum.comp toDirectSum = AlgHom.id R 
(TensorAlgebra R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] {f
 g : TensorAlgebra R M ->ₐ[R] A} (w : f.toLinearMap.comp (ι R) = g.toLinearMap.c
omp (ι R)) …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorAlgebra.toDirectSum_ι`：toDirectSum_ι (x : M) : toDirectSum (ι R x)
 = DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => 
x)
· 使用定理 `TensorAlgebra.ofDirectSum_of_tprod`：ofDirectSum_of_tprod {n} (x : Fin n 
-> M) : ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n
 x
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDirectSum_comp_toDirectSum :
    ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M) := by
  ext
  simp [tprod_apply]

@[simp]
/-
**TensorAlgebra.ofDirectSum_toDirectSum** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra
`。
形式化陈述：ofDirectSum_toDirectSum (x : TensorAlgebra R M) : ofDirectSum (TensorAlgeb
ra.toDirectSum x) = x
参数：x : TensorAlgebra R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `TensorAlgebra.ofDirectSum_comp_toDirectSum`：ofDirectSum_comp_toDirectSum
 : ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M)
-/
theorem ofDirectSum_toDirectSum (x : TensorAlgebra R M) :
    ofDirectSum (TensorAlgebra.toDirectSum x) = x :=
  AlgHom.congr_fun ofDirectSum_comp_toDirectSum x

@[simp]
/-
**TensorAlgebra.mk_reindex_cast** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
形式化陈述：mk_reindex_cast {n m : Nat} (h : n = m) (x : ⨂[R]^n M) : GradedMonoid.mk (
A
参数：h : n = m；x : ⨂[R]^n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PiTensorProduct.gradedMonoid_eq_of_reindex_cast`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   {ιι : Type u_3} {ι : ιι → …
-/
theorem mk_reindex_cast {n m : ℕ} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ ↦ M) (Equiv.cast <| congr_arg Fin h) x) =
    GradedMonoid.mk n x :=
  Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)

@[simp]
/-
**TensorAlgebra.mk_reindex_fin_cast** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
形式化陈述：mk_reindex_fin_cast {n m : Nat} (h : n = m) (x : ⨂[R]^n M) : GradedMonoid.
mk (A
参数：h : n = m；x : ⨂[R]^n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finCongr_eq_equivCast`：∀ {n m : ℕ} (h : n = m), finCongr h = Equiv.cast 
⋯
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `TensorAlgebra.mk_reindex_cast`：mk_reindex_cast {n m : Nat} (h : n = m) (
x : ⨂[R]^n M) : GradedMonoid.mk (A
-/
theorem mk_reindex_fin_cast {n m : ℕ} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ ↦ M) (finCongr h) x) = GradedMonoid.mk n x := by
  rw [finCongr_eq_equivCast, mk_reindex_cast h]

set_option backward.isDefEq.respectTransparency false in
/-- The product of tensor products made of a single vector is the same as a single product of
all the vectors. -/
/-
**TensorAlgebra._root_.TensorPower.list_prod_gradedMonoid_mk_single** 是 Mathlib 
中的一个定理，位于命名空间 `TensorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of tensor products made of a single vector is the same as a single p
roduct of
all the vectors.
-/
theorem _root_.TensorPower.list_prod_gradedMonoid_mk_single (n : ℕ) (x : Fin n → M) :
    ((List.finRange n).map fun a =>
          (GradedMonoid.mk _ (PiTensorProduct.tprod R fun _ : Fin 1 => x a) :
            GradedMonoid fun n => ⨂[R]^n M)).prod =
      GradedMonoid.mk n (PiTensorProduct.tprod R x) := by
  refine Fin.consInduction ?_ ?_ x <;> clear x
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    rfl
  · intro n x₀ x ih
    rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
    simp_rw [Function.comp_def, Fin.cons_zero, Fin.cons_succ]
    rw [ih, GradedMonoid.mk_mul_mk, TensorPower.tprod_mul_tprod]
    refine TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) ?_
    dsimp only [GradedMonoid.mk]
    rw [TensorPower.cast_tprod]
    simp_rw [Fin.append_left_eq_cons, Function.comp_def]
    congr 1 with i
/-
**TensorAlgebra.toDirectSum_tensorPower_tprod** 是 Mathlib 中的一个定理，位于命名空间 `TensorA
lgebra`。
形式化陈述：toDirectSum_tensorPower_tprod {n} (x : Fin n -> M) : toDirectSum (tprod R 
M n x) = DirectSum.of _ n (PiTensorProduct.tprod R x)
参数：x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorAlgebra.tprod_apply`：tprod_apply {n : Nat} (x : Fin n -> M) : tpro
d R M n x = (List.ofFn fun i => ι R (x i)).prod
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorAlgebra.toDirectSum_ι`：toDirectSum_ι (x : M) : toDirectSum (ι R x)
 = DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => 
x)
· 使用定理 `DirectSum.list_prod_ofFn_of_eq_dProd`：list_prod_ofFn_of_eq_dProd (n : Na
t) (fι : Fin n -> ι) (fA : forall a, A (fι a)) : (List.ofFn fun a => of A (fι a)
 (fA a)).prod = of A _ ((L…
· 使用定理 `DirectSum.of_eq_of_gradedMonoid_eq`：of_eq_of_gradedMonoid_eq {A : ι -> T
ype*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i} {b : A j} (h : Gra
dedMonoid.mk i a = Grade…
· 使用定理 `GradedMonoid.mk_list_dProd`：GradedMonoid.mk_list_dProd (l : List α) (fι 
: α -> ι) (fA : forall a, A (fι a)) : GradedMonoid.mk _ (l.dProd fι fA) = (l.map
 fun a => Graded…
· 使用定理 `TensorPower.list_prod_gradedMonoid_mk_single`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M] (n : ℕ)   (x : Fin n → M),  …
-/
theorem toDirectSum_tensorPower_tprod {n} (x : Fin n → M) :
    toDirectSum (tprod R M n x) = DirectSum.of _ n (PiTensorProduct.tprod R x) := by
  rw [tprod_apply, map_list_prod, List.map_ofFn]
  simp_rw [Function.comp_def, toDirectSum_ι]
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  rw [GradedMonoid.mk_list_dProd]
  rw [TensorPower.list_prod_gradedMonoid_mk_single]
/-
**TensorAlgebra.toDirectSum_comp_ofDirectSum** 是 Mathlib 中的一个定理，位于命名空间 `TensorAl
gebra`。
形式化陈述：toDirectSum_comp_ofDirectSum : toDirectSum.comp ofDirectSum = AlgHom.id R 
(⨁ n, ⨂[R]^n M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.algHom_ext'`：algHom_ext' ⦃f g : (⨁ i, A i) ->ₐ[R] B⦄ (h : fora
ll i, f.toLinearMap.comp (lof _ _ A i) = g.toLinearMap.comp (lof _ _ A i)) : f =
 g
· 使用定理 `PiTensorProduct.ext`：ext {φ₁ φ₂ : (⨂[R] i, s i) ->ₗ[R] E} (H : φ₁.compMu
ltilinearMap (tprod R) = φ₂.compMultilinearMap (tprod R)) : φ₁ = φ₂
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TensorAlgebra.ofDirectSum_of_tprod`：ofDirectSum_of_tprod {n} (x : Fin n 
-> M) : ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n
 x
· 使用定理 `TensorAlgebra.toDirectSum_tensorPower_tprod`：toDirectSum_tensorPower_tpr
od {n} (x : Fin n -> M) : toDirectSum (tprod R M n x) = DirectSum.of _ n (PiTens
orProduct.tprod R x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDirectSum_comp_ofDirectSum :
    toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, ⨂[R]^n M) := by
  ext
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]

@[simp]
/-
**TensorAlgebra.toDirectSum_ofDirectSum** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra
`。
形式化陈述：toDirectSum_ofDirectSum (x : ⨁ n, ⨂[R]^n M) : TensorAlgebra.toDirectSum (o
fDirectSum x) = x
参数：x : ⨁ n, ⨂[R]^n M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `TensorAlgebra.toDirectSum_comp_ofDirectSum`：toDirectSum_comp_ofDirectSum
 : toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, ⨂[R]^n M)
-/
theorem toDirectSum_ofDirectSum (x : ⨁ n, ⨂[R]^n M) :
    TensorAlgebra.toDirectSum (ofDirectSum x) = x :=
  AlgHom.congr_fun toDirectSum_comp_ofDirectSum x

/-- The tensor algebra is isomorphic to a direct sum of tensor powers. -/
@[simps!]
/-
**TensorAlgebra.equivDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：equivDirectSum : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorAlgebra.toDirectSum_comp_ofDirectSum`：toDirectSum_comp_ofDirectSum
 : toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, ⨂[R]^n M)
· 使用定理 `TensorAlgebra.ofDirectSum_comp_toDirectSum`：ofDirectSum_comp_toDirectSum
 : ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M)

--- 原说明 ---
The tensor algebra is isomorphic to a direct sum of tensor powers.
-/
def equivDirectSum : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M :=
  AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum

end TensorAlgebra

