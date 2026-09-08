/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a commutative ring `R` and an `R`-algebra `A`, we say that `A` is geometrically reduced
(`IsGeometricallyReduced`) if for every prime ideal `p` of `R`, the base change of `A`
to an algebraic closure of `κ(p)` is reduced.
In the case of `R = k` a field, this is equivalent to `AlgebraicClosure k ⊗[k] A` being reduced.

## Main results

- `Algebra.isGeometricallyReduced_field_iff` : for a field `k` and a commutative `k`-algebra `A`,
  `A` is geometrically reduced iff `AlgebraicClosure k ⊗[k] A` is reduced.

- `IsGeometricallyReduced.of_forall_fg`: for a field `k` and a commutative `k`-algebra `A`, if all
  finitely generated subalgebras `B` of `A` are geometrically reduced, then `A` is geometrically
  reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent (see TODO).

## TODO
- Prove that if `A` is a geometrically reduced `R`-algebra, then for every `R`-algebra `K` that is
  a field, the tensor product `K ⊗[R] A` is reduced. (@Thmoas-Guan)

-/

public section

open TensorProduct

noncomputable section

namespace Algebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- An `R`-algebra `A` is geometrically reduced iff for every prime ideal `p` of R`
  the base change to `AlgebraicClosure p.ResidueField` is reduced. -/
@[mk_iff]
/-
**Algebra.IsGeometricallyReduced** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_3) → (A : Type u_4) → [inst : CommRing R] → [inst_1 : Ring A] 
→ [Algebra R A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-algebra `A` is geometrically reduced iff for every prime ideal `p` of R`
  the base change to `AlgebraicClosure p.ResidueField` is reduced.
-/
class IsGeometricallyReduced (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : Prop where
  isReduced_algebraicClosure_tensorProduct (p : Ideal R) [p.IsPrime] :
    IsReduced (AlgebraicClosure p.ResidueField ⊗[R] A)

attribute [instance] IsGeometricallyReduced.isReduced_algebraicClosure_tensorProduct

section Field

/-
**Algebra.isGeometricallyReduced_field_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：isGeometricallyReduced_field_iff (k A : Type*) [Field k] [Ring A] [Algebra
 k A] : IsGeometricallyReduced k A ↔ IsReduced (AlgebraicClosure k otimes[k] A)
参数：k A : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `AlgebraicClosure.instIsAlgClosureOfIsAlgebraic`：∀ (k : Type u) [inst : F
ield k] {L : Type u_1} [inst_1 : Field L] [inst_2 : Algebra k L] [Algebra.IsAlge
braic k L],   IsAlgClosure k (Algebr…
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma isGeometricallyReduced_field_iff (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    IsGeometricallyReduced k A ↔ IsReduced (AlgebraicClosure k ⊗[k] A) := by
  let e (p : Ideal k) [p.IsPrime] : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure p.ResidueField :=
    have := p.algEquivResidueFieldOfField.isAlgebraic
    IsAlgClosure.equiv k _ _
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨fun p hp ↦ ?_⟩⟩
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e ⊥) AlgEquiv.refl).injective
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e p).symm AlgEquiv.refl).injective
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (k A K : Type*) [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGeometricallyReduced k A] : IsReduced (K ⊗[k] A) := by
  have := (isGeometricallyReduced_field_iff k A).mp ‹_›
  exact isReduced_of_injective
    (Algebra.TensorProduct.map ((IsAlgClosed.lift : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))
/-
**Algebra.IsGeometricallyReduced.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsGeometricallyReduced`。
形式化陈述：∀ {k : Type u_1} {A : Type u_2} [inst : Field k] [inst_1 : Ring A] [inst_2
 : Algebra k A] {B : Type u_3}   [inst_3 : Ring B] [inst_4 : Algebra k B] (f : A
 →ₐ[k] B),   Function.Injective ⇑f → ∀ [Algebra.IsGeometricallyReduced k B], Alg
ebra.IsGeometricallyReduced k A
参数：f : A →ₐ[k] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isGeometricallyReduced_field_iff`：isGeometricallyReduced_field_i
ff (k A : Type*) [Field k] [Ring A] [Algebra k A] : IsGeometricallyReduced k A ↔
 IsReduced (AlgebraicClosure k…
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`
：∀ (k : Type u_3) (A : Type u_4) (K : Type u_5) [inst : Field k] [inst_1 : Ring 
A] [inst_2 : Algebra k A]   [inst_3 : Field K] [inst_4 : Alge…
-/
lemma IsGeometricallyReduced.of_injective {B : Type*} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A := by
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

variable (k) in
/-
**Algebra.isReduced_of_isGeometricallyReduced** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
形式化陈述：isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduc
ed A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isReduced_of_injective`：isReduced_of_injective [MonoidWithZero R] [Monoi
dWithZero S] {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] (f : F) 
(hf : Functi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.TensorProduct.includeRight_injective`：includeRight_injective [Mo
dule.Flat R B] (ha : Function.Injective (algebraMap R A)) : Function.Injective (
includeRight : B ->ₐ[R] A otimes[R…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.instIsReducedTensorProductOfIsAlgebraicOfIsGeometricallyReduced`
：∀ (k : Type u_3) (A : Type u_4) (K : Type u_5) [inst : Field k] [inst_1 : Ring 
A] [inst_2 : Algebra k A]   [inst_3 : Field K] [inst_4 : Alge…
-/
theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

/-- If all finitely generated subalgebras of `A` are geometrically reduced, then `A` is
  geometrically reduced. -/
@[stacks 030T]
/-
**Algebra.IsGeometricallyReduced.of_forall_fg** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsGeometricallyReduced`。
形式化陈述：∀ {k : Type u_1} {A : Type u_2} [inst : Field k] [inst_1 : Ring A] [inst_2
 : Algebra k A],   (∀ (B : Subalgebra k A), B.FG → Algebra.IsGeometricallyReduce
d k ↥B) → Algebra.IsGeometricallyReduced k A
参数：∀ (B : Subalgebra k A), B.FG → Algebra.IsGeometricallyReduced k ↥B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsReduced.tensorProduct_of_flat_of_forall_fg`：IsReduced.tensorProduct_of
_flat_of_forall_fg {R C A : Type*} [CommSemiring R] [CommSemiring C] [Semiring A
] [Algebra R A] [Algebra R C] [Mod…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If all finitely generated subalgebras of `A` are geometrically reduced, then `A`
 is
  geometrically reduced.
-/
theorem IsGeometricallyReduced.of_forall_fg
    (h : ∀ B : Subalgebra k A, B.FG → IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  simp_rw [isGeometricallyReduced_field_iff] at h ⊢
  exact IsReduced.tensorProduct_of_flat_of_forall_fg h

end Field

end Algebra

