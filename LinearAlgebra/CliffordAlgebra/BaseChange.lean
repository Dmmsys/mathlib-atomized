/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The base change of a clifford algebra

In this file we show the isomorphism

* `CliffordAlgebra.equivBaseChange A Q` :
  `CliffordAlgebra (Q.baseChange A) ≃ₐ[A] (A ⊗[R] CliffordAlgebra Q)`
  with forward direction `CliffordAlgebra.toBaseChange A Q` and reverse direction
  `CliffordAlgebra.ofBaseChange A Q`.

This covers a more general case of the complexification of clifford algebras (as described in §2.2
of https://empg.maths.ed.ac.uk/Activities/Spin/Lecture2.pdf), where ℂ and ℝ are replaced by an
`R`-algebra `A` (where `2 : R` is invertible).

We show the additional results:

* `CliffordAlgebra.toBaseChange_ι`: the effect of base-changing pure vectors.
* `CliffordAlgebra.ofBaseChange_tmul_ι`: the effect of un-base-changing a tensor of a pure vectors.
* `CliffordAlgebra.toBaseChange_involute`: the effect of base-changing an involution.
* `CliffordAlgebra.toBaseChange_reverse`: the effect of base-changing a reversal.
-/

@[expose] public section

variable {R A V : Type*}
variable [CommRing R] [CommRing A] [AddCommGroup V]
variable [Algebra R A] [Module R V]
variable [Invertible (2 : R)]

open scoped TensorProduct

namespace CliffordAlgebra

variable (A)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary construction: note this is really just a heterobasic `CliffordAlgebra.map`. -/
/-
**CliffordAlgebra.ofBaseChangeAux** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：ofBaseChangeAux (Q : QuadraticForm R V) : CliffordAlgebra Q ->ₐ[R] Cliffor
dAlgebra (Q.baseChange A)
参数：Q : QuadraticForm R V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction: note this is really just a heterobasic `CliffordAlgebra.
map`.
-/
def ofBaseChangeAux (Q : QuadraticForm R V) :
    CliffordAlgebra Q →ₐ[R] CliffordAlgebra (Q.baseChange A) :=
  CliffordAlgebra.lift Q <| by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 ⊗ₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul, one_mul, ← Algebra.algebraMap_eq_smul_one,
      ← IsScalarTower.algebraMap_apply]
/-
**CliffordAlgebra.ofBaseChangeAux_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofBaseChangeAux_ι (Q : QuadraticForm R V) (v : V) :
    ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (1 ⊗ₜ v) :=
  CliffordAlgebra.lift_ι_apply _ _ v

set_option backward.isDefEq.respectTransparency false in
/-- Convert from the base-changed clifford algebra to the clifford algebra over a base-changed
module. -/
/-
**CliffordAlgebra.ofBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：ofBaseChange (Q : QuadraticForm R V) : A otimes[R] CliffordAlgebra Q ->ₐ[A
] CliffordAlgebra (Q.baseChange A)
参数：Q : QuadraticForm R V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert from the base-changed clifford algebra to the clifford algebra over a ba
se-changed
module.
-/
def ofBaseChange (Q : QuadraticForm R V) :
    A ⊗[R] CliffordAlgebra Q →ₐ[A] CliffordAlgebra (Q.baseChange A) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A Q)
    fun _a _x => Algebra.commutes _ _
/-
**CliffordAlgebra.ofBaseChange_tmul_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofBaseChange_tmul_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    ofBaseChange A Q (z ⊗ₜ ι Q v) = ι (Q.baseChange A) (z ⊗ₜ v) := by
  change algebraMap _ _ z * ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z ⊗ₜ[R] v)
  rw [ofBaseChangeAux_ι, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
    mul_one]
/-
**CliffordAlgebra.ofBaseChange_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {V : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : AddCommGroup V]   [inst_3 : Algebra R A] [inst_4 : _roo
t_.Module R V] [inst_5 : Invertible 2] (Q : QuadraticForm R V) (z : A),   (Cliff
ordAlgebra.ofBaseChange A Q) (z ⊗ₜ[R] 1) = (algebraMap A (CliffordAlgebra (Quadr
aticForm.baseChange A Q))) z
参数：A : Type u_2；Q : QuadraticForm R V；z : A；CliffordAlgebra.ofBaseChange A Q；z ⊗
ₜ[R] 1；algebraMap A (CliffordAlgebra (QuadraticForm.baseChange A Q))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] theorem ofBaseChange_tmul_one (Q : QuadraticForm R V) (z : A) :
    ofBaseChange A Q (z ⊗ₜ 1) = algebraMap _ _ z := by
  change algebraMap _ _ z * ofBaseChangeAux A Q 1 = _
  rw [map_one, mul_one]

set_option backward.defeqAttrib.useBackward true in
/-- Convert from the clifford algebra over a base-changed module to the base-changed clifford
algebra. -/
/-
**CliffordAlgebra.toBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：toBaseChange (Q : QuadraticForm R V) : CliffordAlgebra (Q.baseChange A) ->
ₐ[A] A otimes[R] CliffordAlgebra Q
参数：Q : QuadraticForm R V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert from the clifford algebra over a base-changed module to the base-changed
 clifford
algebra.
-/
def toBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift _ <| by
    refine ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (ι Q), ?_⟩
    let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    let : Invertible (2 : A ⊗[R] CliffordAlgebra Q) :=
      (Invertible.map (algebraMap R _) 2).copy 2 (map_ofNat _ _).symm
    suffices hpure_tensor : ∀ v w, (1 * 1) ⊗ₜ[R] (ι Q v * ι Q w) + (1 * 1) ⊗ₜ[R] (ι Q w * ι Q v) =
        QuadraticMap.polarBilin (Q.baseChange A) (1 ⊗ₜ[R] v) (1 ⊗ₜ[R] w) ⊗ₜ[R] 1 by
      -- the crux is that by converting to a statement about linear maps instead of quadratic forms,
      -- we then have access to all the partially-applied `ext` lemmas.
      rw [CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible _)]
      refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      ext v w
      dsimp
      exact hpure_tensor v w
    intro v w
    rw [← TensorProduct.tmul_add, CliffordAlgebra.ι_mul_ι_add_swap,
      QuadraticForm.polarBilin_baseChange, LinearMap.BilinForm.baseChange_tmul, one_mul,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, QuadraticMap.polarBilin_apply_apply]
/-
**CliffordAlgebra.toBaseChange_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toBaseChange_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    toBaseChange A Q (ι (Q.baseChange A) (z ⊗ₜ v)) = z ⊗ₜ ι Q v :=
  CliffordAlgebra.lift_ι_apply _ _ _
/-
**CliffordAlgebra.toBaseChange_comp_involute** 是 Mathlib 中的一个定理，位于命名空间 `Clifford
Algebra`。
形式化陈述：toBaseChange_comp_involute (Q : QuadraticForm R V) : (toBaseChange A Q).co
mp (involute : CliffordAlgebra (Q.baseChange A) ->ₐ[A] _) = (Algebra.TensorProdu
ct.map (AlgHom.id _ _) involute).comp (toBaseChange A Q)
参数：Q : QuadraticForm R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.toBaseChange_ι`：∀ {R : Type u_1} (A : Type u_2) {V : Typ
e u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V]   [in
st_3 : Algebra R A] …
· 使用定理 `CliffordAlgebra.involute_ι`：involute_ι (m : M) : involute (ι Q m) = -ι Q
 m
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Algebra.TensorProduct.map_tmul`：map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] 
D) (a : A) (b : B) : map f g (a otimesₜ b) = f a otimesₜ g b
· 使用定理 `AlgHom.id_apply`：id_apply (p : A) : AlgHom.id R A p = p
· 使用定理 `TensorProduct.tmul_neg`：tmul_neg (m : M) (p : P) : m otimesₜ (-p) = -m o
timesₜ[R] p
-/
theorem toBaseChange_comp_involute (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (involute : CliffordAlgebra (Q.baseChange A) →ₐ[A] _) =
      (Algebra.TensorProduct.map (AlgHom.id _ _) involute).comp (toBaseChange A Q) := by
  ext v
  change toBaseChange A Q (involute (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A ⊗[R] CliffordAlgebra Q →ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))
  rw [toBaseChange_ι, involute_ι, map_neg (toBaseChange A Q), toBaseChange_ι,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, involute_ι, TensorProduct.tmul_neg]

/-- The involution acts only on the right of the tensor product. -/
/-
**CliffordAlgebra.toBaseChange_involute** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：toBaseChange_involute (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.base
Change A)) : toBaseChange A Q (involute x) = TensorProduct.map LinearMap.id (inv
olute.toLinearMap) (toBaseChange A Q x)
参数：Q : QuadraticForm R V；x : CliffordAlgebra (Q.baseChange A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CliffordAlgebra.toBaseChange_comp_involute`：toBaseChange_comp_involute (
Q : QuadraticForm R V) : (toBaseChange A Q).comp (involute : CliffordAlgebra (Q.
baseChange A) ->ₐ[A] _) = (Algeb…

--- 原说明 ---
The involution acts only on the right of the tensor product.
-/
theorem toBaseChange_involute (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (involute x) =
      TensorProduct.map LinearMap.id (involute.toLinearMap) (toBaseChange A Q x) :=
  DFunLike.congr_fun (toBaseChange_comp_involute A Q) x

open MulOpposite

/-- Auxiliary theorem used to prove `toBaseChange_reverse` without needing induction. -/
/-
**CliffordAlgebra.toBaseChange_comp_reverseOp** 是 Mathlib 中的一个定理，位于命名空间 `Cliffor
dAlgebra`。
形式化陈述：toBaseChange_comp_reverseOp (Q : QuadraticForm R V) : (toBaseChange A Q).o
p.comp reverseOp = ((Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q))
.toAlgHom.comp <| (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom 
(reverseOp (Q
参数：Q : QuadraticForm R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.toBaseChange_ι`：∀ {R : Type u_1} (A : Type u_2) {V : Typ
e u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V]   [in
st_3 : Algebra R A] …
· 使用定理 `CliffordAlgebra.reverse_ι`：reverse_ι (m : M) : reverse (ι Q m) = ι Q m
· 使用定理 `Algebra.TensorProduct.map_tmul`：map_tmul (f : A ->ₐ[S] C) (g : B ->ₐ[R] 
D) (a : A) (b : B) : map f g (a otimesₜ b) = f a otimesₜ g b
· 使用定理 `Algebra.TensorProduct.opAlgEquiv_tmul`：opAlgEquiv_tmul (a : Aᵐᵒᵖ) (b : B
ᵐᵒᵖ) : opAlgEquiv R S A B (a otimesₜ[R] b) = op (a.unop otimesₜ b.unop)
· 使用定理 `CliffordAlgebra.reverseOp_ι`：reverseOp_ι (m : M) : reverseOp (ι Q m) = o
p (ι Q m)

--- 原说明 ---
Auxiliary theorem used to prove `toBaseChange_reverse` without needing induction
.
-/
theorem toBaseChange_comp_reverseOp (Q : QuadraticForm R V) :
    (toBaseChange A Q).op.comp reverseOp =
      ((Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)).toAlgHom.comp <|
        (Algebra.TensorProduct.map
          (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))).comp
        (toBaseChange A Q)) := by
  ext v
  change op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 ⊗ₜ[R] v)))) =
    Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
      (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))
        (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] v))))
  rw [toBaseChange_ι, reverse_ι, toBaseChange_ι, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.opAlgEquiv_tmul, reverseOp_ι]
  rfl

/-- `reverse` acts only on the right of the tensor product. -/
/-
**CliffordAlgebra.toBaseChange_reverse** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：toBaseChange_reverse (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseC
hange A)) : toBaseChange A Q (reverse x) = TensorProduct.map LinearMap.id revers
e (toBaseChange A Q x)
参数：Q : QuadraticForm R V；x : CliffordAlgebra (Q.baseChange A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `CliffordAlgebra.toBaseChange_comp_reverseOp`：toBaseChange_comp_reverseOp
 (Q : QuadraticForm R V) : (toBaseChange A Q).op.comp reverseOp = ((Algebra.Tens
orProduct.opAlgEquiv R A A (Cliff…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.AlgebraTensorModule.map_comp`：map_comp (f₂ : P ->ₗ[A] P') 
(f₁ : M ->ₗ[A] P) (g₂ : Q ->ₗ[R] Q') (g₁ : N ->ₗ[R] Q) : map (f₂.comp f₁) (g₂.co
mp g₁) = (map f₂ g₂).comp (map f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.reverse.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {M : 
Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quadrati
cForm R M},   Clif…
· 使用引理 `AlgEquiv.toAlgHom_toLinearMap`：toAlgHom_toLinearMap : e.toAlgHom.toLinea
rMap = e.toLinearEquiv.toLinearMap
· 使用定理 `AlgEquiv.toLinearEquiv_toOpposite`：∀ (R : Type u_1) (A : Type u_3) [inst
 : CommSemiring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A],   ↑(AlgEqui
v.toOpposite R A) = Mul…
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁

--- 原说明 ---
`reverse` acts only on the right of the tensor product.
-/
theorem toBaseChange_reverse (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (reverse x) =
      TensorProduct.map LinearMap.id reverse (toBaseChange A Q x) := by
  have := DFunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.map_comp _ _ _ _).symm _).trans ?_
  rw [reverse, AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearEquiv_toOpposite]
  dsimp
  -- `simp` fails here due to a timeout looking for a `Subsingleton` instance!?
  rw [LinearEquiv.self_trans_symm]
  rfl

attribute [ext] TensorProduct.ext
/-
**CliffordAlgebra.toBaseChange_comp_ofBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `Clif
fordAlgebra`。
形式化陈述：toBaseChange_comp_ofBaseChange (Q : QuadraticForm R V) : (toBaseChange A Q
).comp (ofBaseChange A Q) = AlgHom.id _ _
参数：Q : QuadraticForm R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `CliffordAlgebra.instIsScalarTower`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.AlgebraTensorModule.mk_apply`：∀ (R : Type uR) [inst : Comm
Semiring R] (A : Type u_1) (M : Type u_2) (N : Type u_3) [inst_1 : Semiring A]  
 [inst_2 : AddCommMonoid M] [ins…
· 使用定理 `CliffordAlgebra.ofBaseChange_tmul_ι`：∀ {R : Type u_1} (A : Type u_2) {V 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V] 
  [inst_3 : Algebra R A] …
· 使用定理 `CliffordAlgebra.toBaseChange_ι`：∀ {R : Type u_1} (A : Type u_2) {V : Typ
e u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V]   [in
st_3 : Algebra R A] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toBaseChange_comp_ofBaseChange (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (ofBaseChange A Q) = AlgHom.id _ _ := by
  ext v
  simp
/-
**CliffordAlgebra.toBaseChange_ofBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {V : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : AddCommGroup V]   [inst_3 : Algebra R A] [inst_4 : _roo
t_.Module R V] [inst_5 : Invertible 2] (Q : QuadraticForm R V)   (x : TensorProd
uct R A (CliffordAlgebra Q)),   (CliffordAlgebra.toBaseChange A Q) ((CliffordAlg
ebra.ofBaseChange A Q) x) = x
参数：A : Type u_2；Q : QuadraticForm R V；x : TensorProduct R A (CliffordAlgebra Q)；
CliffordAlgebra.toBaseChange A Q；(CliffordAlgebra.ofBaseChange A Q) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `CliffordAlgebra.toBaseChange_comp_ofBaseChange`：toBaseChange_comp_ofBase
Change (Q : QuadraticForm R V) : (toBaseChange A Q).comp (ofBaseChange A Q) = Al
gHom.id _ _
-/
@[simp] theorem toBaseChange_ofBaseChange (Q : QuadraticForm R V) (x : A ⊗[R] CliffordAlgebra Q) :
    toBaseChange A Q (ofBaseChange A Q x) = x :=
  AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q :) x

set_option backward.isDefEq.respectTransparency false in
/-
**CliffordAlgebra.ofBaseChange_comp_toBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `Clif
fordAlgebra`。
形式化陈述：ofBaseChange_comp_toBaseChange (Q : QuadraticForm R V) : (ofBaseChange A Q
).comp (toBaseChange A Q) = AlgHom.id _ _
参数：Q : QuadraticForm R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `CliffordAlgebra.instIsScalarTower`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [in
st_2 : AddCommGroup M] …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.toBaseChange_ι`：∀ {R : Type u_1} (A : Type u_2) {V : Typ
e u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V]   [in
st_3 : Algebra R A] …
· 使用定理 `CliffordAlgebra.ofBaseChange_tmul_ι`：∀ {R : Type u_1} (A : Type u_2) {V 
: Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : AddCommGroup V] 
  [inst_3 : Algebra R A] …
-/
theorem ofBaseChange_comp_toBaseChange (Q : QuadraticForm R V) :
    (ofBaseChange A Q).comp (toBaseChange A Q) = AlgHom.id _ _ := by
  ext x
  change ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 ⊗ₜ[R] x)))
    = ι (Q.baseChange A) (1 ⊗ₜ[R] x)
  rw [toBaseChange_ι, ofBaseChange_tmul_ι]
/-
**CliffordAlgebra.ofBaseChange_toBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {V : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : AddCommGroup V]   [inst_3 : Algebra R A] [inst_4 : _roo
t_.Module R V] [inst_5 : Invertible 2] (Q : QuadraticForm R V)   (x : CliffordAl
gebra (QuadraticForm.baseChange A Q)),   (CliffordAlgebra.ofBaseChange A Q) ((Cl
iffordAlgebra.toBaseChange A Q) x) = x
参数：A : Type u_2；Q : QuadraticForm R V；x : CliffordAlgebra (QuadraticForm.baseCha
nge A Q)；CliffordAlgebra.ofBaseChange A Q；(CliffordAlgebra.toBaseChange A Q) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebra.ofBaseChange_comp_toBaseChange`：ofBaseChange_comp_toBase
Change (Q : QuadraticForm R V) : (ofBaseChange A Q).comp (toBaseChange A Q) = Al
gHom.id _ _
-/
@[simp] theorem ofBaseChange_toBaseChange
    (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    ofBaseChange A Q (toBaseChange A Q x) = x :=
  AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q :) x

/-- Base-changing the vector space of a clifford algebra is isomorphic as an A-algebra to
base-changing the clifford algebra itself; $<|Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)<|$.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an equivalence. -/
@[simps!]
/-
**CliffordAlgebra.equivBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：equivBaseChange (Q : QuadraticForm R V) : CliffordAlgebra (Q.baseChange A)
 ≃ₐ[A] A otimes[R] CliffordAlgebra Q
参数：Q : QuadraticForm R V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.toBaseChange_comp_ofBaseChange`：toBaseChange_comp_ofBase
Change (Q : QuadraticForm R V) : (toBaseChange A Q).comp (ofBaseChange A Q) = Al
gHom.id _ _
· 使用定理 `CliffordAlgebra.ofBaseChange_comp_toBaseChange`：ofBaseChange_comp_toBase
Change (Q : QuadraticForm R V) : (ofBaseChange A Q).comp (toBaseChange A Q) = Al
gHom.id _ _

--- 原说明 ---
Base-changing the vector space of a clifford algebra is isomorphic as an A-algeb
ra to
base-changing the clifford algebra itself; $<|Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)<
|$.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an 
equivalence.
-/
def equivBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A] A ⊗[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

end CliffordAlgebra

