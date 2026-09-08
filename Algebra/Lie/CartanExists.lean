/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Rank

/-!
# Existence of Cartan subalgebras

In this file we prove existence of Cartan subalgebras in finite-dimensional Lie algebras,
following [barnes1967].

## Main results

* `exists_isCartanSubalgebra_of_finrank_le_card`:
  A Lie algebra `L` over a field `K` has a Cartan subalgebra,
  provided that the dimension of `L` over `K` is less than or equal to the cardinality of `K`.
* `exists_isCartanSubalgebra`:
  A finite-dimensional Lie algebra `L` over an infinite field `K` has a Cartan subalgebra.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

namespace LieAlgebra

section CommRing

variable {K R L M : Type*}
variable [Field K] [CommRing R]
variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite K L]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]

open Module LieSubalgebra Module.Free Polynomial

variable (K)

namespace engel_isBot_of_isMin

/-!
## Implementation details for the proof of `LieAlgebra.engel_isBot_of_isMin`

In this section we provide some auxiliary definitions and lemmas
that are used in the proof of `LieAlgebra.engel_isBot_of_isMin`,
which is the following statement:

Let `L` be a Lie algebra of dimension `n` over a field `K` with at least `n` elements.
Given a Lie subalgebra `U` of `L`, and an element `x ∈ U` such that `U ≤ engel K x`.
Suppose that `engel K x` is minimal amongst the Engel subalgebras `engel K y` for `y ∈ U`.
Then `engel K x ≤ engel K y` for all `y ∈ U`.

We follow the proof strategy of Lemma 2 in [barnes1967].
-/

variable (R M)

variable (x y : L)

open LieModule LinearMap
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "φ" => LieModule.toEnd R L M

set_option backward.privateInPublic true in
/-- Let `x` and `y` be elements of a Lie `R`-algebra `L`, and `M` a Lie module over `L`.
Then the characteristic polynomials of the family of endomorphisms `⁅r • y + x, _⁆` of `M`
have coefficients that are polynomial in `r : R`.
In other words, we obtain a polynomial over `R[X]`
that specializes to the characteristic polynomial of `⁅r • y + x, _⁆` under the map `X ↦ r`.
This polynomial is captured in `lieCharpoly R M x y`. -/
private noncomputable
/-
**LieAlgebra.engel_isBot_of_isMin.lieCharpoly** 是 Mathlib 中的一个定义，位于命名空间 `LieAlge
bra.engel_isBot_of_isMin`。
形式化陈述：lieCharpoly : Polynomial R[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lieCharpoly : Polynomial R[X] :=
  letI bL := chooseBasis R L
  (polyCharpoly (LieHom.toLinearMap φ) bL).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.engel_isBot_of_isMin.lieCharpoly_monic** 是 Mathlib 中的一个引理，位于命名空间 `L
ieAlgebra.engel_isBot_of_isMin`。
形式化陈述：lieCharpoly_monic : (lieCharpoly R M x y).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用引理 `LinearMap.polyCharpoly_monic`：polyCharpoly_monic : (polyCharpoly φ b).Mo
nic
-/
lemma lieCharpoly_monic : (lieCharpoly R M x y).Monic :=
  (polyCharpoly_monic _ _).map _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.engel_isBot_of_isMin.lieCharpoly_natDegree** 是 Mathlib 中的一个引理，位于命名空
间 `LieAlgebra.engel_isBot_of_isMin`。
形式化陈述：lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly R M x y).natDegree = f
inrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Lie.CartanExists.0.LieAlgebra.engel_isBot_of_is
Min.lieCharpoly.eq_1`：∀ (R : Type u_2) {L : Type u_3} (M : Type u_4) [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup
 M…
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用引理 `LinearMap.polyCharpoly_monic`：polyCharpoly_monic : (polyCharpoly φ b).Mo
nic
· 使用引理 `LinearMap.polyCharpoly_natDegree`：polyCharpoly_natDegree [Nontrivial R] 
: (polyCharpoly φ b).natDegree = finrank R M
-/
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly R M x y).natDegree = finrank R M := by
  rw [lieCharpoly, (polyCharpoly_monic _ _).natDegree_map, polyCharpoly_natDegree]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable {R} in
/-
**LieAlgebra.engel_isBot_of_isMin.lieCharpoly_map_eval** 是 Mathlib 中的一个引理，位于命名空间
 `LieAlgebra.engel_isBot_of_isMin`。
形式化陈述：lieCharpoly_map_eval (r : R) : (lieCharpoly R M x y).map (evalRingHom r) =
 (φ (r • y + x)).charpoly
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.Lie.CartanExists.0.LieAlgebra.engel_isBot_of_is
Min.lieCharpoly.eq_1`：∀ (R : Type u_2) {L : Type u_3} (M : Type u_4) [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup
 M…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHomClass.toRingHom.congr_simp`：∀ {F : Type u_1} {α : Type u_2} {β : 
Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSemir
ing β} [inst_1 : RingHo…
· 使用定理 `MvPolynomial.comp_aeval`：comp_aeval {B : Type*} [CommSemiring B] [Algebr
a R B] (φ : S₁ ->ₐ[R] B) : φ.comp (aeval f) = aeval fun i => φ (f i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.charpoly.congr_simp`：∀ {R : Type u} {M : Type v} [inst : CommR
ing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_3 : Module
.Free R M] [inst_4 …
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用引理 `LinearMap.polyCharpoly_map_eq_charpoly`：polyCharpoly_map_eq_charpoly (x 
: L) : (polyCharpoly φ b).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly
-/
lemma lieCharpoly_map_eval (r : R) :
    (lieCharpoly R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly, map_map]
  set b := chooseBasis R L
  have aux : (fun i ↦ (b.repr y) i * r + (b.repr x) i) = b.repr (r • y + x) := by
    ext i; simp [mul_comm r]
  simp_rw [← coe_aeval_eq_evalRingHom, ← AlgHom.comp_toRingHom, MvPolynomial.comp_aeval,
    map_add, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X, aux,
    MvPolynomial.coe_aeval_eq_eval, polyCharpoly_map_eq_charpoly, LieHom.coe_toLinearMap, map_add]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.engel_isBot_of_isMin.lieCharpoly_coeff_natDegree** 是 Mathlib 中的一个引理
，位于命名空间 `LieAlgebra.engel_isBot_of_isMin`。
形式化陈述：lieCharpoly_coeff_natDegree [Nontrivial R] (i j : Nat) (hij : i + j = finr
ank R M) : ((lieCharpoly R M x y).coeff i).natDegree <= j
参数：i j : Nat；hij : i + j = finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `_private.Mathlib.Algebra.Lie.CartanExists.0.LieAlgebra.engel_isBot_of_is
Min.lieCharpoly.eq_1`：∀ (R : Type u_2) {L : Type u_3} (M : Type u_4) [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup
 M…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `MvPolynomial.aeval_natDegree_le`：aeval_natDegree_le {R : Type*} [CommSem
iring R] {m n : Nat} (F : MvPolynomial σ R) (hF : F.totalDegree <= m) (f : σ -> 
Polynomial R) (hf : f…
· 使用引理 `MvPolynomial.IsHomogeneous.totalDegree_le`：totalDegree_le (hφ : IsHomoge
neous φ n) : φ.totalDegree <= n
· 使用引理 `LinearMap.polyCharpoly_coeff_isHomogeneous`：polyCharpoly_coeff_isHomogen
eous (i j : Nat) (hij : i + j = finrank R M) [Nontrivial R] : ((polyCharpoly φ b
).coeff i).IsHomogeneous j
· 使用定理 `Polynomial.natDegree_linear_le`：natDegree_linear_le : natDegree (C a * X
 + C b) <= 1
-/
lemma lieCharpoly_coeff_natDegree [Nontrivial R] (i j : ℕ) (hij : i + j = finrank R M) :
    ((lieCharpoly R M x y).coeff i).natDegree ≤ j := by
  rw [← mul_one j, lieCharpoly, coeff_map]
  apply MvPolynomial.aeval_natDegree_le
  · apply (polyCharpoly_coeff_isHomogeneous φ (chooseBasis R L) _ _ hij).totalDegree_le
  intro k
  exact natDegree_linear_le

end engel_isBot_of_isMin

end CommRing

section Field

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra LieSubmodule Polynomial Cardinal LieModule engel_isBot_of_isMin

set_option backward.isDefEq.respectTransparency false in
/-- Let `L` be a Lie algebra of dimension `n` over a field `K` with at least `n` elements.
Given a Lie subalgebra `U` of `L`, and an element `x ∈ U` such that `U ≤ engel K x`.
Suppose that `engel K x` is minimal amongst the Engel subalgebras `engel K y` for `y ∈ U`.
Then `engel K x ≤ engel K y` for all `y ∈ U`.

Lemma 2 in [barnes1967]. -/
/-
**LieAlgebra.engel_isBot_of_isMin** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：engel_isBot_of_isMin (hLK : finrank K L <= #K) (U : LieSubalgebra K L) (E 
: {engel K x | x in U}) (hUle : U <= E) (hmin : IsMin E) : IsBot E
参数：hLK : finrank K L <= #K；U : LieSubalgebra K L；E : {engel K x | x in U}；hUle :
 U <= E；hmin : IsMin E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LieSubalgebra.engel_zero`：engel_zero : engel R (0 : L) = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LieSubalgebra.toSubmodule_injective`：toSubmodule_injective : Function.In
jective ((↑) : LieSubalgebra R L -> Submodule R L)
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LieSubmodule.instIsNoetherianSubtypeMem`：∀ {R : Type u} {L : Type v} {M 
: Type w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [
inst_3 : _root_.Module R M] […
· 使用引理 `Polynomial.eq_zero_of_forall_eval_zero_of_natDegree_lt_card`：eq_zero_of_
forall_eval_zero_of_natDegree_lt_card (f : R[X]) (hf : forall r, f.eval r = 0) (
hfR : f.natDegree < #R) : f = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.coe_evalRingHom`：coe_evalRingHom (r : R) : (evalRingHom r : R
[X] -> R) = eval r
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
Let `L` be a Lie algebra of dimension `n` over a field `K` with at least `n` ele
ments.
Given a Lie subalgebra `U` of `L`, and an element `x ∈ U` such that `U ≤ engel K
 x`.
Suppose that `engel K x` is minimal amongst the Engel subalgebras `engel K y` fo
r `y ∈ U`.
Then `engel K x ≤ engel K y` for all `y ∈ U`.

Lemma 2 in [barnes1967].
-/
lemma engel_isBot_of_isMin (hLK : finrank K L ≤ #K) (U : LieSubalgebra K L)
    (E : {engel K x | x ∈ U}) (hUle : U ≤ E) (hmin : IsMin E) :
    IsBot E := by
  rcases E with ⟨_, x, hxU, rfl⟩
  rintro ⟨_, y, hyU, rfl⟩
  -- It will be useful to repackage the Engel subalgebras
  set Ex : {engel K x | x ∈ U} := ⟨engel K x, x, hxU, rfl⟩
  set Ey : {engel K y | y ∈ U} := ⟨engel K y, y, hyU, rfl⟩
  replace hUle : U ≤ Ex := hUle
  replace hmin : ∀ E, E ≤ Ex → Ex ≤ E := @hmin
  -- We also repackage the Engel subalgebra `engel K x`
  -- as Lie submodule `E` of `L` over the Lie algebra `U`.
  let E : LieSubmodule K U L :=
  { engel K x with
    lie_mem := by rintro ⟨u, hu⟩ y hy; exact (engel K x).lie_mem (hUle hu) hy }
  -- We may and do assume that `x ≠ 0`, since otherwise the statement is trivial.
  obtain rfl | hx₀ := eq_or_ne x 0
  · simpa [Ex, Ey] using hmin Ey
  -- We denote by `Q` the quotient `L / E`, and by `r` the dimension of `E`.
  let Q := L ⧸ E
  let r := finrank K E
  -- If `r = finrank K L`, then `E = L`, and the statement is trivial.
  obtain hr | hr : r = finrank K L ∨ r < finrank K L := (Submodule.finrank_le _).eq_or_lt
  · suffices engel K y ≤ engel K x from hmin Ey this
    suffices engel K x = ⊤ by simp_rw [this, le_top]
    apply LieSubalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq hr
  -- So from now on, we assume that `r < finrank K L`.
  -- We denote by `x'` and `y'` the elements `x` and `y` viewed as terms of `U`.
  set x' : U := ⟨x, hxU⟩
  set y' : U := ⟨y, hyU⟩
  -- Let `u : U` denote `y - x`.
  let u : U := y' - x'
  -- We denote by `χ r` the characteristic polynomial of `⁅r • u + x, _⁆`
  --   viewed as endomorphism of `E`. Note that `χ` is polynomial in its argument `r`.
  -- Similarly: `ψ r` is the characteristic polynomial of `⁅r • u + x, _⁆`
  --   viewed as endomorphism of `Q`. Note that `ψ` is polynomial in its argument `r`.
  let χ : Polynomial (K[X]) := lieCharpoly K E x' u
  let ψ : Polynomial (K[X]) := lieCharpoly K Q x' u
  -- It suffices to show that `χ` is the monomial `X ^ r`.
  suffices χ = X ^ r by
    -- Indeed, by evaluating the coefficients at `1`
    apply_fun (fun p ↦ p.map (evalRingHom 1)) at this
    -- we find that the characteristic polynomial `χ 1` of `⁅y, _⁆` is equal to `X ^ r`
    simp_rw [Polynomial.map_pow, map_X, χ, lieCharpoly_map_eval, one_smul, u, sub_add_cancel,
      -- and therefore the endomorphism `⁅y, _⁆` acts nilpotently on `E`.
      r, LinearMap.charpoly_eq_X_pow_iff,
      Subtype.ext_iff, coe_toEnd_pow _ _ _ E, ZeroMemClass.coe_zero] at this
    -- We ultimately want to show `engel K x ≤ engel K y`
    intro z hz
    -- which holds by definition of Engel subalgebra and the nilpotency that we just established.
    rw [mem_engel_iff]
    exact this ⟨z, hz⟩
  -- To show that `χ = X ^ r`, it suffices to show that all coefficients in degrees `< r` are `0`.
  suffices ∀ i < r, χ.coeff i = 0 by
    simp_rw [r, ← lieCharpoly_natDegree K E x' u] at this ⊢
    rw [(lieCharpoly_monic K E x' u).eq_X_pow_iff_natDegree_le_natTrailingDegree]
    exact le_natTrailingDegree (lieCharpoly_monic K E x' u).ne_zero this
  -- Let us consider the `i`-th coefficient of `χ`, for `i < r`.
  intro i hi
  -- We separately consider the case `i = 0`.
  obtain rfl | hi0 := eq_or_ne i 0
  · -- `The polynomial `coeff χ 0` is zero if it evaluates to zero on all elements of `K`,
    -- provided that its degree is strictly less than `#K`.
    apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card _ _ ?deg
    case deg =>
      -- We need to show `(natDegree (coeff χ 0)) < #K` and know that `finrank K L ≤ #K`
      apply lt_of_lt_of_le _ hLK
      rw [Nat.cast_lt]
      -- So we are left with showing `natDegree (coeff χ 0) < finrank K L`
      apply lt_of_le_of_lt _ hr
      apply lieCharpoly_coeff_natDegree _ _ _ _ 0 r (zero_add r)
    -- Fix an element of `K`.
    intro α
    -- We want to show that `α` is a root of `coeff χ 0`.
    -- So we need to show that there is a `z ≠ 0` in `E` satisfying `⁅α • u + x, z⁆ = 0`.
    rw [← coe_evalRingHom, ← coeff_map, lieCharpoly_map_eval,
      ← constantCoeff_apply, LinearMap.charpoly_constantCoeff_eq_zero_iff]
    -- We consider `z = α • u + x`, and split into the cases `z = 0` and `z ≠ 0`.
    let z := α • u + x'
    obtain hz₀ | hz₀ := eq_or_ne z 0
    · -- If `z = 0`, then `⁅α • u + x, x⁆` vanishes and we use our assumption `x ≠ 0`.
      refine ⟨⟨x, self_mem_engel K x⟩, ?_, ?_⟩
      · exact Subtype.coe_ne_coe.mp hx₀
      · dsimp only [z] at hz₀
        simp only [hz₀, map_zero, LinearMap.zero_apply]
    -- If `z ≠ 0`, then `⁅α • u + x, z⁆` vanishes per axiom of Lie algebras
    refine ⟨⟨z, hUle z.2⟩, ?_, ?_⟩
    · simpa only [coe_bracket_of_module, ne_eq, Submodule.mk_eq_zero, Subtype.ext_iff] using! hz₀
    · change ⁅z, _⁆ = (0 : E)
      ext
      exact lie_self z.1
  -- We are left with the case `i ≠ 0`, and want to show `coeff χ i = 0`.
  -- We will do this once again by showing that `coeff χ i` vanishes
  -- on a sufficiently large subset `s` of `K`.
  -- But we first need to get our hands on that subset `s`.
  -- We start by observing that `ψ` has non-trivial constant coefficient.
  have hψ : constantCoeff ψ ≠ 0 := by
    -- Suppose that `ψ` in fact has trivial constant coefficient.
    intro H
    -- Then there exists a `z ≠ 0` in `Q` such that `⁅x, z⁆ = 0`.
    obtain ⟨z, hz0, hxz⟩ : ∃ z : Q, z ≠ 0 ∧ ⁅x', z⁆ = 0 := by
      -- Indeed, if the constant coefficient of `ψ` is trivial,
      -- then `0` is a root of the characteristic polynomial of `⁅0 • u + x, _⁆` acting on `Q`,
      -- and hence we find an eigenvector `z` as desired.
      apply_fun (evalRingHom 0) at H
      rw [constantCoeff_apply, ← coeff_map, lieCharpoly_map_eval,
        ← constantCoeff_apply, map_zero, LinearMap.charpoly_constantCoeff_eq_zero_iff] at H
      simpa only [coe_bracket_of_module, ne_eq, zero_smul, zero_add, toEnd_apply_apply]
        using H
    -- It suffices to show `z = 0` (in `Q`) to obtain a contradiction.
    apply hz0
    -- We replace `z : Q` by a representative in `L`.
    obtain ⟨z, rfl⟩ := LieSubmodule.Quotient.surjective_mk' E z
    -- The assumption `⁅x, z⁆ = 0` is equivalent to `⁅x, z⁆ ∈ E`.
    have : ⁅x, z⁆ ∈ E := by rwa [← LieSubmodule.Quotient.mk_eq_zero']
    -- From this we deduce that there exists an `n` such that `⁅x, _⁆ ^ n` vanishes on `⁅x, z⁆`.
    -- On the other hand, our goal is to show `z = 0` in `Q`,
    -- which is equivalent to showing that `⁅x, _⁆ ^ n` vanishes on `z`, for some `n`.
    simp only [LieSubmodule.mem_mk_iff', LieSubalgebra.mem_toSubmodule, mem_engel_iff,
      LieSubmodule.Quotient.mk'_apply, LieSubmodule.Quotient.mk_eq_zero', E, Q] at this ⊢
    -- Hence we win.
    obtain ⟨n, hn⟩ := this
    use n + 1
    rwa [pow_succ]
  -- Now we find a subset `s` of `K` of size `≥ r`
  -- such that `constantCoeff ψ` takes non-zero values on all of `s`.
  -- This turns out to be the subset that we alluded to earlier.
  obtain ⟨s, hs, hsψ⟩ : ∃ s : Finset K, r ≤ s.card ∧ ∀ α ∈ s, (constantCoeff ψ).eval α ≠ 0 := by
    classical
    -- Let `t` denote the set of roots of `constantCoeff ψ`.
    let t := (constantCoeff ψ).roots.toFinset
    -- We show that `t` has cardinality at most `finrank K L - r`.
    have ht : t.card ≤ finrank K L - r := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (card_roots' _).trans ?_
      rw [constantCoeff_apply]
      -- Indeed, `constantCoeff ψ` has degree at most `finrank K Q = finrank K L - r`.
      apply lieCharpoly_coeff_natDegree
      suffices finrank K Q + r = finrank K L by rw [← this, zero_add, Nat.add_sub_cancel]
      apply Submodule.finrank_quotient_add_finrank
    -- Hence there exists a subset of size `≥ r` in the complement of `t`,
    -- and `constantCoeff ψ` takes non-zero values on all of this subset.
    obtain ⟨s, hs⟩ := exists_finset_le_card K _ hLK
    use s \ t
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (Finset.le_card_sdiff _ _)
      omega
    · intro α hα
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset, mem_roots', IsRoot.def, not_and, t] at hα
      exact hα.2 hψ
  -- So finally we can continue our proof strategy by showing that `coeff χ i` vanishes on `s`.
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s _ ?hcard
  case hcard =>
    -- We need to show that `natDegree (coeff χ i) < s.card`
    -- Which follows from our assumptions `i < r` and `r ≤ s.card`
    -- and the fact that the degree of `coeff χ i` is less than or equal to `r - i`.
    apply lt_of_le_of_lt (lieCharpoly_coeff_natDegree _ _ _ _ i (r - i) _)
    · omega
    · dsimp only [r] at hi ⊢
      rw [Nat.add_sub_cancel' hi.le]
  -- We need to show that for all `α ∈ s`, the polynomial `coeff χ i` evaluates to zero at `α`.
  intro α hα
  -- Once again, we are left with showing that `⁅y, _⁆` acts nilpotently on `E`.
  rw [← coe_evalRingHom, ← coeff_map, lieCharpoly_map_eval,
    (LinearMap.charpoly_eq_X_pow_iff _).mpr, coeff_X_pow, if_neg hi.ne]
  -- To do so, it suffices to show that the Engel subalgebra of `v = a • u + x` is contained in `E`.
  let v := α • u + x'
  suffices engel K (v : L) ≤ engel K x by
    -- Indeed, in that case the minimality assumption on `E` implies
    -- that `E` is contained in the Engel subalgebra of `v`.
    replace this : engel K x ≤ engel K (v : L) := (hmin ⟨_, v, v.2, rfl⟩ this).ge
    intro z
    -- And so we are done, by the definition of Engel subalgebra.
    simpa only [mem_engel_iff, Subtype.ext_iff, coe_toEnd_pow _ _ _ E] using! this z.2
  -- Now we are in good shape.
  -- Fix an element `z` in the Engel subalgebra of `y`.
  intro z hz
  -- We need to show that `z` is in `E`, or alternatively that `z = 0` in `Q`.
  change z ∈ E
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  -- We denote the image of `z` in `Q` by `z'`.
  set z' : Q := LieSubmodule.Quotient.mk' E z
  -- First we observe that `z'` is killed by a power of `⁅v, _⁆`.
  have hz' : ∃ n : ℕ, (toEnd K U Q v ^ n) z' = 0 := by
    rw [mem_engel_iff] at hz
    obtain ⟨n, hn⟩ := hz
    use n
    apply_fun LieSubmodule.Quotient.mk' E at hn
    rw [map_zero] at hn
    rw [← hn]
    clear hn
    induction n with
    | zero => simp only [z', pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; rfl
  classical
  -- Now let `n` be the smallest power such that `⁅v, _⁆ ^ n` kills `z'`.
  set n := Nat.find hz' with _hn
  have hn : (toEnd K U Q v ^ n) z' = 0 := Nat.find_spec hz'
  -- If `n = 0`, then we are done.
  obtain hn₀ | ⟨k, hk⟩ : n = 0 ∨ ∃ k, n = k + 1 := by cases n <;> simp
  · simpa only [hn₀, pow_zero, Module.End.one_apply] using hn
  -- If `n = k + 1`, then we can write `⁅v, _⁆ ^ n = ⁅v, _⁆ ∘ ⁅v, _⁆ ^ k`.
  -- Recall that `constantCoeff ψ` is non-zero on `α`, and `v = α • u + x`.
  specialize hsψ α hα
  -- Hence `⁅v, _⁆` acts injectively on `Q`.
  rw [← coe_evalRingHom, constantCoeff_apply, ← coeff_map, lieCharpoly_map_eval,
    ← constantCoeff_apply, ne_eq, LinearMap.charpoly_constantCoeff_eq_zero_iff] at hsψ
  -- We deduce from this that `z' = 0`, arguing by contraposition.
  contrapose! hsψ
  -- Indeed `⁅v, _⁆` kills `⁅v, _⁆ ^ k` applied to `z'`.
  use (toEnd K U Q v ^ k) z'
  refine ⟨?_, ?_⟩
  · -- And `⁅v, _⁆ ^ k` applied to `z'` is non-zero by definition of `n`.
    apply Nat.find_min hz'; lia
  · rw [← hn, hk, pow_succ', Module.End.mul_apply]

variable (K L)
/-
**LieAlgebra.exists_isCartanSubalgebra_engel_of_finrank_le_card** 是 Mathlib 中的一个
引理，位于命名空间 `LieAlgebra`。
形式化陈述：exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L <= #K)
 : exists x : L, IsCartanSubalgebra (engel K x)
参数：h : finrank K L <= #K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `LieAlgebra.exists_isRegular_of_finrank_le_card`：exists_isRegular_of_finr
ank_le_card (h : finrank R L <= #R) : exists x : L, IsRegular R x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `LieSubalgebra.isNilpotent_of_forall_le_engel`：isNilpotent_of_forall_le_e
ngel [IsNoetherian R L] (H : LieSubalgebra R L) (h : forall x in H, H <= engel R
 x) : LieRing.IsNilpotent H
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用引理 `LieSubalgebra.self_mem_engel`：self_mem_engel (x : L) : x in engel R x
· 使用引理 `LieAlgebra.engel_isBot_of_isMin`：engel_isBot_of_isMin (hLK : finrank K L
 <= #K) (U : LieSubalgebra K L) (E : {engel K x | x in U}) (hUle : U <= E) (hmin
 : IsMin E) : IsBot E
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieAlgebra.isRegular_iff_finrank_engel_eq_rank`：isRegular_iff_finrank_en
gel_eq_rank (x : L) : IsRegular K x ↔ finrank K (engel K x) = rank K L
· 使用引理 `LieAlgebra.rank_le_finrank_engel`：rank_le_finrank_engel (x : L) : rank K
 L <= finrank K (engel K x)
· 使用定理 `LieSubalgebra.toSubmodule_injective`：toSubmodule_injective : Function.In
jective ((↑) : LieSubalgebra R L -> Submodule R L)
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `LieSubalgebra.normalizer_engel`：normalizer_engel (x : L) : normalizer (e
ngel R x) = engel R x
-/
lemma exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L ≤ #K) :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  obtain ⟨x, hx⟩ := exists_isRegular_of_finrank_le_card K L h
  use x
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {engel K z | z ∈ engel K x} := ⟨engel K x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨engel K y, y, hy, rfl⟩
  apply engel_isBot_of_isMin h (engel K x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices finrank K (engel K x) ≤ finrank K (engel K y) by
    suffices engel K y = engel K x from this.ge
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply rank_le_finrank_engel
/-
**LieAlgebra.exists_isCartanSubalgebra_engel** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：exists_isCartanSubalgebra_engel [Infinite K] : exists x : L, IsCartanSubal
gebra (engel K x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieAlgebra.exists_isCartanSubalgebra_engel_of_finrank_le_card`：exists_is
CartanSubalgebra_engel_of_finrank_le_card (h : finrank K L <= #K) : exists x : L
, IsCartanSubalgebra (engel K x)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.infinite_iff`：infinite_iff {α : Type u} : Infinite α ↔ ℵ₀ <= #α
-/
lemma exists_isCartanSubalgebra_engel [Infinite K] :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  apply exists_isCartanSubalgebra_engel_of_finrank_le_card
  exact natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite K›

end Field

end LieAlgebra

