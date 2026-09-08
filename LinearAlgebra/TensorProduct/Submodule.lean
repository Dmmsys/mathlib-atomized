/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!

# Some results on tensor product of submodules

## Linear maps induced by multiplication for submodules

Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`). We define some linear maps
induced by the multiplication in `S` (see also `LinearMap.mul'`), which are
mainly used in the definition of linearly disjointness (`Submodule.LinearDisjoint`).

- `Submodule.mulMap`: the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  induced by the multiplication in `S`, whose image is `M * N` (`Submodule.mulMap_range`).

- `Submodule.mulMap'`: the natural map `M ⊗[R] N →ₗ[R] M * N`
  induced by multiplication in `S`, which is surjective (`Submodule.mulMap'_surjective`).

- `Submodule.lTensorOne`, `Submodule.rTensorOne`: the natural isomorphism of `R`-modules between
  `i(R) ⊗[R] N` and `N`, resp. `M ⊗[R] i(R)` and `M`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `TensorProduct.lid`
  and `TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  Note that we use `⊥ : Subalgebra R S` instead of `1 : Submodule R S`, since the map
  `R →ₗ[R] (1 : Submodule R S)` is not defined directly in mathlib yet.

There are also `Submodule.mulLeftMap` and `Submodule.mulRightMap`, defined in earlier files.

-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

-- can't use `LinearMap.mul' R S ∘ₗ TensorProduct.mapIncl M N` since it is not defeq to
-- `Subalgebra.mulMap` which is `(Algebra.TensorProduct.productMap A.val B.val).toLinearMap`

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural `R`-linear map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`. -/
/-
**Submodule.mulMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mulMap : M otimes[R] N ->ₗ[R] S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural `
R`-linear map
`M ⊗[R] N →ₗ[R] S` induced by multiplication in `S`.
-/
def mulMap : M ⊗[R] N →ₗ[R] S := TensorProduct.lift ((LinearMap.mul R S).domRestrict₁₂ M N)

@[simp]
/-
**Submodule.mulMap_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_tmul (m : M) (n : N) : mulMap M N (m otimesₜ[R] n) = m.1 * n.1
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulMap_tmul (m : M) (n : N) : mulMap M N (m ⊗ₜ[R] n) = m.1 * n.1 := rfl
/-
**Submodule.mulMap_map_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_map_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T
) : mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : S ->ₗ[R] T)) ∘ₗ TensorProduct.ma
p ((f : S ->ₗ[R] T).submoduleMap M) ((f : S ->ₗ[R] T).submoduleMap N) = (f : S -
>ₗ[R] T) ∘ₗ mulMap M N
参数：f : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
-/
theorem mulMap_map_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S →ₐ[R] T) :
    mulMap (M.map (f : S →ₗ[R] T)) (N.map (f : S →ₗ[R] T)) ∘ₗ
      TensorProduct.map ((f : S →ₗ[R] T).submoduleMap M) ((f : S →ₗ[R] T).submoduleMap N)
        = (f : S →ₗ[R] T) ∘ₗ mulMap M N := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, mulMap_tmul, LinearMap.coe_coe, map_mul]
  rfl
/-
**Submodule.coe_mulMap_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_mulMap_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T
) : mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : S ->ₗ[R] T)) ∘ TensorProduct.map
 ((f : S ->ₗ[R] T).submoduleMap M) ((f : S ->ₗ[R] T).submoduleMap N) = f ∘ mulMa
p M N
参数：f : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulMap_map_comp_eq`：mulMap_map_comp_eq {T : Type w} [Semiring 
T] [Algebra R T] (f : S ->ₐ[R] T) : mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : 
S ->ₗ[R] T)) ∘ₗ Te…
-/
theorem coe_mulMap_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S →ₐ[R] T) :
    mulMap (M.map (f : S →ₗ[R] T)) (N.map (f : S →ₗ[R] T)) ∘
      TensorProduct.map ((f : S →ₗ[R] T).submoduleMap M) ((f : S →ₗ[R] T).submoduleMap N)
        = f ∘ mulMap M N :=
  congr(⇑($(mulMap_map_comp_eq M N f)))
/-
**Submodule.mulMap_op** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_op : mulMap (equivOpposite.symm (MulOpposite.op M)) (equivOpposite.
symm (MulOpposite.op N)) = (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ mulMap N
 M ∘ₗ (TensorProduct.congr (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv 
R).symm M) (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm N) ≪≫ₗ T
ensorProduct.comm R M N).toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem mulMap_op :
    mulMap (equivOpposite.symm (MulOpposite.op M)) (equivOpposite.symm (MulOpposite.op N)) =
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ mulMap N M ∘ₗ
    (TensorProduct.congr
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm M)
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm N) ≪≫ₗ
    TensorProduct.comm R M N).toLinearMap :=
  TensorProduct.ext' fun _ _ ↦ rfl
/-
**Submodule.mulMap_comm_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_comm_of_commute (hc : forall (m : M) (n : N), Commute m.1 n.1) : mu
lMap N M = mulMap M N ∘ₗ TensorProduct.comm R N M
参数：hc : forall (m : M) (n : N), Commute m.1 n.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
-/
theorem mulMap_comm_of_commute (hc : ∀ (m : M) (n : N), Commute m.1 n.1) :
    mulMap N M = mulMap M N ∘ₗ TensorProduct.comm R N M := by
  refine TensorProduct.ext' fun n m ↦ ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

variable {M} in
/-
**Submodule.mulMap_comp_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_comp_rTensor {M' : Submodule R S} (hM : M' <= M) : mulMap M N ∘ₗ (i
nclusion hM).rTensor N = mulMap M' N
参数：hM : M' <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem mulMap_comp_rTensor {M' : Submodule R S} (hM : M' ≤ M) :
    mulMap M N ∘ₗ (inclusion hM).rTensor N = mulMap M' N :=
  TensorProduct.ext' fun _ _ ↦ rfl

variable {N} in
/-
**Submodule.mulMap_comp_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_comp_lTensor {N' : Submodule R S} (hN : N' <= N) : mulMap M N ∘ₗ (i
nclusion hN).lTensor M = mulMap M N'
参数：hN : N' <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem mulMap_comp_lTensor {N' : Submodule R S} (hN : N' ≤ N) :
    mulMap M N ∘ₗ (inclusion hN).lTensor M = mulMap M N' :=
  TensorProduct.ext' fun _ _ ↦ rfl

variable {M N} in
/-
**Submodule.mulMap_comp_map_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_comp_map_inclusion {M' N' : Submodule R S} (hM : M' <= M) (hN : N' 
<= N) : mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M
' N'
参数：hM : M' <= M；hN : N' <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem mulMap_comp_map_inclusion {M' N' : Submodule R S} (hM : M' ≤ M) (hN : N' ≤ N) :
    mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M' N' :=
  TensorProduct.ext' fun _ _ ↦ rfl
/-
**Submodule.mulMap_eq_mul'_comp_mapIncl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] (M N : Submodule R S),   M.mulMap N = LinearMap.mul' R S 
∘ₗ TensorProduct.mapIncl M N
参数：M N : Submodule R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem mulMap_eq_mul'_comp_mapIncl : mulMap M N = .mul' R S ∘ₗ TensorProduct.mapIncl M N :=
  TensorProduct.ext' fun _ _ ↦ rfl
/-
**Submodule.mulMap_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_range : LinearMap.range (mulMap M N) = M * N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
-/
theorem mulMap_range : LinearMap.range (mulMap M N) = M * N := by
  refine le_antisymm ?_ (mul_le.2 fun m hm n hn ↦ ⟨⟨m, hm⟩ ⊗ₜ[R] ⟨n, hn⟩, rfl⟩)
  rintro _ ⟨x, rfl⟩
  induction x with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b => exact mul_mem_mul a.2 b.2
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/-- If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural `R`-linear map
`M ⊗[R] N →ₗ[R] M * N` induced by multiplication in `S`,
which is surjective (`Submodule.mulMap'_surjective`). -/
/-
**Submodule.mulMap'** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mulMap' : M otimes[R] N ->ₗ[R] ↥(M * N)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mulMap_range`：mulMap_range : LinearMap.range (mulMap M N) = M 
* N

--- 原说明 ---
If `M` and `N` are submodules in an algebra `S` over `R`, there is the natural `
R`-linear map
`M ⊗[R] N →ₗ[R] M * N` induced by multiplication in `S`,
which is surjective (`Submodule.mulMap'_surjective`).
-/
def mulMap' : M ⊗[R] N →ₗ[R] ↥(M * N) :=
  (LinearEquiv.ofEq _ _ (mulMap_range M N)).toLinearMap ∘ₗ (mulMap M N).rangeRestrict

variable {M N} in
@[simp]
/-
**Submodule.val_mulMap'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M N : Submodule R S}   (m : ↥M) (n : ↥N), ↑((M.mulMap' N
) (m ⊗ₜ[R] n)) = ↑m * ↑n
参数：m : ↥M；n : ↥N；(M.mulMap' N) (m ⊗ₜ[R] n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem val_mulMap'_tmul (m : M) (n : N) : (mulMap' M N (m ⊗ₜ[R] n) : S) = m.1 * n.1 := rfl
/-
**Submodule.mulMap'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] (M N : Submodule R S),   Function.Surjective ⇑(M.mulMap' 
N)
参数：M N : Submodule R S；M.mulMap' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mulMap_range`：mulMap_range : LinearMap.range (mulMap M N) = M 
* N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mulMap'_surjective : Function.Surjective (mulMap' M N) := by
  simp_rw [mulMap', LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    LinearMap.surjective_rangeRestrict]

/-- If `N` is a submodule in an algebra `S` over `R`, there is the natural `R`-linear map
`i(R) ⊗[R] N →ₗ[R] N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This is promoted to an isomorphism of `R`-modules as `Submodule.lTensorOne`. Use that instead. -/
/-
**Submodule.lTensorOne'** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：lTensorOne' : (⊥ : Subalgebra R S) otimes[R] N ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a submodule in an algebra `S` over `R`, there is the natural `R`-linea
r map
`i(R) ⊗[R] N →ₗ[R] N` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This is promoted to an isomorphism of `R`-modules as `Submodule.lTensorOne`. Use
 that instead.
-/
def lTensorOne' : (⊥ : Subalgebra R S) ⊗[R] N →ₗ[R] N :=
  show Subalgebra.toSubmodule ⊥ ⊗[R] N →ₗ[R] N from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, one_mul])).toLinearMap ∘ₗ
      (mulMap _ N).rangeRestrict

variable {N} in
@[simp]
/-
**Submodule.lTensorOne'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {N : Submodule R S}   (y : R) (n : ↥N), N.lTensorOne' ((a
lgebraMap R ↥⊥) y ⊗ₜ[R] n) = y • n
参数：y : R；n : ↥N；(algebraMap R ↥⊥) y ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submodule.mulMap_tmul`：mulMap_tmul (m : M) (n : N) : mulMap M N (m otime
sₜ[R] n) = m.1 * n.1
-/
theorem lTensorOne'_tmul (y : R) (n : N) :
    N.lTensorOne' (algebraMap R _ y ⊗ₜ[R] n) = y • n := Subtype.val_injective <| by
  simp_rw [lTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul, Algebra.smul_def]
  exact mulMap_tmul _ N _ _

variable {N} in
@[simp]
/-
**Submodule.lTensorOne'_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {N : Submodule R S}   (n : ↥N), N.lTensorOne' (1 ⊗ₜ[R] n)
 = n
参数：n : ↥N；1 ⊗ₜ[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.lTensorOne'_tmul`：∀ {R : Type u} {S : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {N : Submodule R S}   (y : 
R) (n : ↥N), N.l…
-/
theorem lTensorOne'_one_tmul (n : N) : N.lTensorOne' (1 ⊗ₜ[R] n) = n := by
  simpa using lTensorOne'_tmul 1 n

/-- If `N` is a submodule in an algebra `S` over `R`,
there is the natural isomorphism of `R`-modules between
`i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to `R`. -/
/-
**Submodule.lTensorOne** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：lTensorOne : (⊥ : Subalgebra R S) otimes[R] N ≃ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a submodule in an algebra `S` over `R`,
there is the natural isomorphism of `R`-modules between
`i(R) ⊗[R] N` and `N` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This generalizes `TensorProduct.lid` as `i(R)` is not necessarily isomorphic to 
`R`.
-/
def lTensorOne : (⊥ : Subalgebra R S) ⊗[R] N ≃ₗ[R] N :=
  LinearEquiv.ofLinearMap N.lTensorOne' (TensorProduct.mk R (⊥ : Subalgebra R S) N 1)
    (by ext; simp) <| TensorProduct.ext' fun r n ↦ by
  change 1 ⊗ₜ[R] lTensorOne' N _ = r ⊗ₜ[R] n
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h, lTensorOne'_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

variable {N} in
@[simp]
/-
**Submodule.lTensorOne_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：lTensorOne_tmul (y : R) (n : N) : N.lTensorOne (algebraMap R _ y otimesₜ[R
] n) = y • n
参数：y : R；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lTensorOne'_tmul`：∀ {R : Type u} {S : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {N : Submodule R S}   (y : 
R) (n : ↥N), N.l…
-/
theorem lTensorOne_tmul (y : R) (n : N) : N.lTensorOne (algebraMap R _ y ⊗ₜ[R] n) = y • n :=
  N.lTensorOne'_tmul y n

variable {N} in
@[simp]
/-
**Submodule.lTensorOne_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：lTensorOne_one_tmul (n : N) : N.lTensorOne (1 otimesₜ[R] n) = n
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lTensorOne'_one_tmul`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {N : Submodule R S}   (
n : ↥N), N.lTensorOn…
-/
theorem lTensorOne_one_tmul (n : N) : N.lTensorOne (1 ⊗ₜ[R] n) = n :=
  N.lTensorOne'_one_tmul n

variable {N} in
@[simp]
/-
**Submodule.lTensorOne_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：lTensorOne_symm_apply (n : N) : N.lTensorOne.symm n = 1 otimesₜ[R] n
参数：n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensorOne_symm_apply (n : N) : N.lTensorOne.symm n = 1 ⊗ₜ[R] n := rfl
/-
**Submodule.mulMap_one_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_one_left_eq : mulMap (Subalgebra.toSubmodule ⊥) N = N.subtype ∘ₗ N.
lTensorOne.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem mulMap_one_left_eq :
    mulMap (Subalgebra.toSubmodule ⊥) N = N.subtype ∘ₗ N.lTensorOne.toLinearMap :=
  TensorProduct.ext' fun _ _ ↦ rfl

/-- If `M` is a submodule in an algebra `S` over `R`, there is the natural `R`-linear map
`M ⊗[R] i(R) →ₗ[R] M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This is promoted to an isomorphism of `R`-modules as `Submodule.rTensorOne`. Use that instead. -/
/-
**Submodule.rTensorOne'** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：rTensorOne' : M otimes[R] (⊥ : Subalgebra R S) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a submodule in an algebra `S` over `R`, there is the natural `R`-linea
r map
`M ⊗[R] i(R) →ₗ[R] M` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This is promoted to an isomorphism of `R`-modules as `Submodule.rTensorOne`. Use
 that instead.
-/
def rTensorOne' : M ⊗[R] (⊥ : Subalgebra R S) →ₗ[R] M :=
  show M ⊗[R] Subalgebra.toSubmodule ⊥ →ₗ[R] M from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, mul_one])).toLinearMap ∘ₗ
      (mulMap M _).rangeRestrict

variable {M} in
@[simp]
/-
**Submodule.rTensorOne'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M : Submodule R S}   (y : R) (m : ↥M), M.rTensorOne' (m 
⊗ₜ[R] (algebraMap R ↥⊥) y) = y • m
参数：y : R；m : ↥M；m ⊗ₜ[R] (algebraMap R ↥⊥) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Submodule.mulMap_tmul`：mulMap_tmul (m : M) (n : N) : mulMap M N (m otime
sₜ[R] n) = m.1 * n.1
-/
theorem rTensorOne'_tmul (y : R) (m : M) :
    M.rTensorOne' (m ⊗ₜ[R] algebraMap R _ y) = y • m := Subtype.val_injective <| by
  simp_rw [rTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul]
  rw [Algebra.smul_def, Algebra.commutes]
  exact mulMap_tmul M _ _ _

variable {M} in
@[simp]
/-
**Submodule.rTensorOne'_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommSemiring R] [inst_1 : Semiring S] 
[inst_2 : Algebra R S] {M : Submodule R S}   (m : ↥M), M.rTensorOne' (m ⊗ₜ[R] 1)
 = m
参数：m : ↥M；m ⊗ₜ[R] 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Submodule.rTensorOne'_tmul`：∀ {R : Type u} {S : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M : Submodule R S}   (y : 
R) (m : ↥M), M.r…
-/
theorem rTensorOne'_tmul_one (m : M) : M.rTensorOne' (m ⊗ₜ[R] 1) = m := by
  simpa using rTensorOne'_tmul 1 m

/-- If `M` is a submodule in an algebra `S` over `R`,
there is the natural isomorphism of `R`-modules between
`M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the structure map.
This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to `R`. -/
/-
**Submodule.rTensorOne** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：rTensorOne : M otimes[R] (⊥ : Subalgebra R S) ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a submodule in an algebra `S` over `R`,
there is the natural isomorphism of `R`-modules between
`M ⊗[R] i(R)` and `M` induced by multiplication in `S`, here `i : R → S` is the 
structure map.
This generalizes `TensorProduct.rid` as `i(R)` is not necessarily isomorphic to 
`R`.
-/
def rTensorOne : M ⊗[R] (⊥ : Subalgebra R S) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap M.rTensorOne' ((TensorProduct.comm R _ _).toLinearMap ∘ₗ
    TensorProduct.mk R (⊥ : Subalgebra R S) M 1) (by ext; simp) <| TensorProduct.ext' fun n r ↦ by
  change rTensorOne' M _ ⊗ₜ[R] 1 = n ⊗ₜ[R] r
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h, rTensorOne'_tmul, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

variable {M} in
@[simp]
/-
**Submodule.rTensorOne_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：rTensorOne_tmul (y : R) (m : M) : M.rTensorOne (m otimesₜ[R] algebraMap R 
_ y) = y • m
参数：y : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rTensorOne'_tmul`：∀ {R : Type u} {S : Type v} [inst : CommSemi
ring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M : Submodule R S}   (y : 
R) (m : ↥M), M.r…
-/
theorem rTensorOne_tmul (y : R) (m : M) : M.rTensorOne (m ⊗ₜ[R] algebraMap R _ y) = y • m :=
  M.rTensorOne'_tmul y m

variable {M} in
@[simp]
/-
**Submodule.rTensorOne_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：rTensorOne_tmul_one (m : M) : M.rTensorOne (m otimesₜ[R] 1) = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rTensorOne'_tmul_one`：∀ {R : Type u} {S : Type v} [inst : Comm
Semiring R] [inst_1 : Semiring S] [inst_2 : Algebra R S] {M : Submodule R S}   (
m : ↥M), M.rTensorOn…
-/
theorem rTensorOne_tmul_one (m : M) : M.rTensorOne (m ⊗ₜ[R] 1) = m :=
  M.rTensorOne'_tmul_one m

variable {M} in
@[simp]
/-
**Submodule.rTensorOne_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：rTensorOne_symm_apply (m : M) : M.rTensorOne.symm m = m otimesₜ[R] 1
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensorOne_symm_apply (m : M) : M.rTensorOne.symm m = m ⊗ₜ[R] 1 := rfl
/-
**Submodule.mulMap_one_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_one_right_eq : mulMap M (Subalgebra.toSubmodule ⊥) = M.subtype ∘ₗ M
.rTensorOne.toLinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem mulMap_one_right_eq :
    mulMap M (Subalgebra.toSubmodule ⊥) = M.subtype ∘ₗ M.rTensorOne.toLinearMap :=
  TensorProduct.ext' fun _ _ ↦ rfl

@[simp]
/-
**Submodule.comm_trans_lTensorOne** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comm_trans_lTensorOne : (TensorProduct.comm R _ _).trans M.lTensorOne = M.
rTensorOne
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.lTensorOne_tmul`：lTensorOne_tmul (y : R) (n : N) : N.lTensorOn
e (algebraMap R _ y otimesₜ[R] n) = y • n
· 使用定理 `Submodule.rTensorOne_tmul`：rTensorOne_tmul (y : R) (m : M) : M.rTensorOn
e (m otimesₜ[R] algebraMap R _ y) = y • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comm_trans_lTensorOne :
    (TensorProduct.comm R _ _).trans M.lTensorOne = M.rTensorOne := by
  refine LinearEquiv.toLinearMap_injective <| TensorProduct.ext' fun m r ↦ ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

@[simp]
/-
**Submodule.comm_trans_rTensorOne** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comm_trans_rTensorOne : (TensorProduct.comm R _ _).trans M.rTensorOne = M.
lTensorOne
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.rTensorOne_tmul`：rTensorOne_tmul (y : R) (m : M) : M.rTensorOn
e (m otimesₜ[R] algebraMap R _ y) = y • m
· 使用定理 `Submodule.lTensorOne_tmul`：lTensorOne_tmul (y : R) (n : N) : N.lTensorOn
e (algebraMap R _ y otimesₜ[R] n) = y • n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comm_trans_rTensorOne :
    (TensorProduct.comm R _ _).trans M.rTensorOne = M.lTensorOne := by
  refine LinearEquiv.toLinearMap_injective <| TensorProduct.ext' fun r m ↦ ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

variable {M} in
/-
**Submodule.mulLeftMap_eq_mulMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulLeftMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (m : ι -> M) : mulLe
ftMap N m = mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.linearCombination R m) ∘ₗ
 (TensorProduct.finsuppScalarLeft R N ι).symm.toLinearMap
参数：m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulLeftMap_apply_single`：mulLeftMap_apply_single {M N : Submod
ule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N) : mulLeftMap N m (Finsupp.sing
le i n) = (m i).1 * n.1
· 使用引理 `TensorProduct.finsuppScalarLeft_symm_apply_single`：finsuppScalarLeft_sym
m_apply_single (i : ι) (n : N) : (finsuppScalarLeft R N ι).symm (Finsupp.single 
i n) = (Finsupp.single i 1) otimesₜ[R] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulLeftMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (m : ι → M) :
    mulLeftMap N m = mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.linearCombination R m) ∘ₗ
      (TensorProduct.finsuppScalarLeft R N ι).symm.toLinearMap := by
  ext; simp

variable {N} in
/-
**Submodule.mulRightMap_eq_mulMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulRightMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (n : ι -> N) : mulR
ightMap M n = mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.linearCombination R n) 
∘ₗ (TensorProduct.finsuppScalarRight R R M ι).symm.toLinearMap
参数：n : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulRightMap_apply_single`：mulRightMap_apply_single {M N : Subm
odule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M) : mulRightMap M n (Finsupp.s
ingle i m) = m.1 * (n i)…
· 使用引理 `TensorProduct.finsuppScalarRight_symm_apply_single`：finsuppScalarRight_s
ymm_apply_single (i : ι) (m : M) : (finsuppScalarRight R S M ι).symm (Finsupp.si
ngle i m) = m otimesₜ[R] (Finsupp.single…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulRightMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (n : ι → N) :
    mulRightMap M n = mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.linearCombination R n) ∘ₗ
      (TensorProduct.finsuppScalarRight R R M ι).symm.toLinearMap := by
  ext; simp

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

/-
**Submodule.mulMap_comm** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).to
LinearMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mulMap_comm_of_commute`：mulMap_comm_of_commute (hc : forall (m
 : M) (n : N), Commute m.1 n.1) : mulMap N M = mulMap M N ∘ₗ TensorProduct.comm 
R N M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ ↦ mul_comm _ _

end CommSemiring

end Submodule

