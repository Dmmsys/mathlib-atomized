/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# The group homology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group homology of
`A : Rep k G` to be the homology of the complex
$$\dots \to \bigoplus_{G^2} A \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A$$
with differential $d_n$ sending $a\cdot (g_0, \dots, g_n)$ to
$$\rho(g_0^{-1})(a)\cdot (g_1, \dots, g_n)$$
$$+ \sum_{i = 0}^{n - 1}(-1)^{i + 1}a\cdot (g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}a\cdot (g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\bigoplus_{G^n} A \cong (A \otimes_k \left(\bigoplus_{G^n} k[G]\right))_G$ given by
`Rep.coinvariantsTensorFreeLEquiv`. If we conjugate the $n$th differential in $(A \otimes_k P)_G$
by this isomorphism, where `P` is the bar resolution of `k` as a trivial `k`-linear
`G`-representation, then the resulting map agrees with the differential $d_n$ defined
above, a fact we prove.

Hence our $d_n$ squares to zero, and we get
$\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k),$ where $\mathrm{Tor}$ is defined by deriving the
second argument of the functor $(A, B) \mapsto (A \otimes_k B)_G.$

To talk about homology in low degree, the file
`Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean` provides API specialized to
`H₀`, `H₁`, `H₂`.

## Main definitions

* `Rep.Tor k G n`: the left-derived functors given by deriving the second argument of
  $(A, B) \mapsto (A \otimes_k B)_G$.
* `groupHomology.inhomogeneousChains A`: a complex whose objects are
  $\bigoplus_{G^n} A$ and whose homology is the group homology $\mathrm{H}_n(G, A).$
* `groupHomology.inhomogeneousChainsIso A`: an isomorphism between the above two complexes.
* `groupHomology A n`: this is $\mathrm{H}_n(G, A),$ defined as the $n$th homology of the
  second complex, `inhomogeneousChains A`.
* `groupHomologyIsoTor A n`: an isomorphism $\mathrm{H}_n(G, A) \cong \mathrm{Tor}_n(A, k)$
  induced by `inhomogeneousChainsIso A`.

## Implementation notes

Group homology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep` definition.
We avoid using instances `Module k[G] A` so that we do not run into possible scalar action diamonds.

Note that the existing definition of `Tor` in `Mathlib.CategoryTheory.Monoidal.Tor` is for monoidal
categories, and the bifunctor we need to derive here maps to `ModuleCat k`. Hence we define
`Rep.Tor k G n` by instead left-deriving the second argument of `Rep.coinvariantsTensor k G`:
$(A, B) \mapsto (A \otimes_k B)_G$. The functor `Rep.coinvariantsTensor k G` is naturally
isomorphic to the functor sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module
structure defined by `g • a := A.ρ g⁻¹ a`, but currently mathlib's `TensorProduct` is only defined
for commutative rings.

## TODO

* Upgrading `groupHomologyIsoTor` to an isomorphism of derived functors.

-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

variable (k G : Type u) [CommRing k] [Group G]

open MonoidalCategory Representation Finsupp

section Tor

variable {k G} in
/-- Given `A : Rep k G` and a chain complex `P` in `Rep k G`, this is the chain complex whose
`n`th object is `(A ⊗ Pₙ)_G`. -/
/-
**HomologicalComplex.coinvariantsTensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomologicalComplex.coinvariantsTensorObj {α : Type*} [AddRightCancelSemigr
oup α] [One α] (A : Rep k G) (P : ChainComplex (Rep k G) α) : ChainComplex (Modu
leCat k) α
参数：A : Rep k G；P : ChainComplex (Rep k G) α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
Given `A : Rep k G` and a chain complex `P` in `Rep k G`, this is the chain comp
lex whose
`n`th object is `(A ⊗ Pₙ)_G`.
-/
abbrev HomologicalComplex.coinvariantsTensorObj {α : Type*} [AddRightCancelSemigroup α] [One α]
    (A : Rep k G) (P : ChainComplex (Rep k G) α) :
    ChainComplex (ModuleCat k) α :=
  (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj P

namespace Rep

/-- The left-derived functors given by deriving the second argument of `A, B ↦ (A ⊗[k] B)_G`. -/
@[simps]
/-
**Rep.Tor** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：Tor (n : Nat) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where obj X
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-derived functors given by deriving the second argument of `A, B ↦ (A ⊗[
k] B)_G`.
-/
def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((coinvariantsTensor k G).obj X) n
  map f := NatTrans.leftDerived ((coinvariantsTensor k G).map f) n

variable {k G} (A : Rep.{w} k G)

/-- `Tor` can be computed using a projective resolution. -/
/-
**Rep.torIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：torIso (A : Rep k G) {B : Rep k G} (P : ProjectiveResolution B) (n : Nat) 
: ((Rep.Tor k G n).obj A).obj B ≅ (P.complex.coinvariantsTensorObj A).homology n
参数：A : Rep k G；P : ProjectiveResolution B；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Tor` can be computed using a projective resolution.
-/
abbrev torIso (A : Rep k G) {B : Rep k G} (P : ProjectiveResolution B) (n : ℕ) :
    ((Rep.Tor k G n).obj A).obj B ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  P.isoLeftDerivedObj _ n

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
/-
**Rep.isZero_Tor_succ_of_projective** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：isZero_Tor_succ_of_projective (X Y : Rep k G) [Projective Y] (n : Nat) : I
sZero (((Tor k G (n + 1)).obj X).obj Y)
参数：X Y : Rep k G；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : Categor
yTheory.Category.{v_1, u_1} D]   [inst_2 : Category…

--- 原说明 ---
The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective.
-/
lemma isZero_Tor_succ_of_projective (X Y : Rep k G) [Projective Y] (n : ℕ) :
    IsZero (((Tor k G (n + 1)).obj X).obj Y) :=
  Functor.isZero_leftDerived_obj_projective_succ ..

end Rep
end Tor

namespace groupHomology

open Rep Finsupp

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (n : ℕ)

namespace inhomogeneousChains

/-- The differential in the complex of inhomogeneous chains used to calculate group homology. -/
/-
**groupHomology.inhomogeneousChains.d** 是 Mathlib 中的一个定义，位于命名空间 `groupHomology.i
nhomogeneousChains`。
形式化陈述：d : ModuleCat.of k ((Fin (n + 1) -> G) ->₀ A) ⟶ ModuleCat.of k ((Fin n -> 
G) ->₀ A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential in the complex of inhomogeneous chains used to calculate group 
homology.
-/
def d : ModuleCat.of k ((Fin (n + 1) → G) →₀ A) ⟶ ModuleCat.of k ((Fin n → G) →₀ A) :=
  ModuleCat.ofHom <| lsum (R := k) k fun g => lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹ +
    Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • lsingle (Fin.contractNth j (· * ·) g)

variable {A n} in
@[simp]
/-
**groupHomology.inhomogeneousChains.d_single** 是 Mathlib 中的一个定理，位于命名空间 `groupHom
ology.inhomogeneousChains`。
形式化陈述：d_single (n : Nat) (g : Fin (n + 1) -> G) (a : A) : d A n (single g a) = s
ingle (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) + Finset.univ.sum fun j : Fin (n + 1) 
=> (-1 : k) ^ ((j : Nat) + 1) • single (Fin.contractNth j (· * ·) g) a
参数：n : Nat；g : Fin (n + 1) -> G；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
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
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
-/
theorem d_single (n : ℕ) (g : Fin (n + 1) → G) (a : A) :
    d A n (single g a) = single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • single (Fin.contractNth j (· * ·) g) a := by
  simp [d]

open ModuleCat.MonoidalCategory

set_option backward.defeqAttrib.useBackward true in
/-
**groupHomology.inhomogeneousChains.d_eq** 是 Mathlib 中的一个定理，位于命名空间 `groupHomolog
y.inhomogeneousChains`。
形式化陈述：d_eq [DecidableEq G] : d A n = (coinvariantsTensorFreeLEquiv A (Fin (n + 1
) -> G)).toModuleIso.inv ≫ ((barComplex k G).coinvariantsTensorObj A).d (n + 1) 
n ≫ (coinvariantsTensorFreeLEquiv A (Fin n -> G)).toModuleIso.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `groupHomology.inhomogeneousChains.d_single`：d_single (n : Nat) (g : Fin 
(n + 1) -> G) (a : A) : d A n (single g a) = single (fun i => g i.succ) (A.ρ (g 
0)⁻¹ a) + Finset.univ.sum fun j …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用引理 `Rep.finsuppToCoinvariantsTensorFree_single`：finsuppToCoinvariantsTensorF
ree_single (i : α) (x : A) : DFunLike.coe (F
· 使用定理 `Rep.barComplex.d_single`：∀ {k G : Type u} [inst : CommRing k] (n : ℕ) [i
nst_1 : Group G] (x : Fin (n + 1) → G),   ((Rep.Hom.hom (Rep.barComplex.d k G n)
) fun₀ | x =>…
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single`：coinvariantsTensorFr
eeToFinsupp_mk_tmul_single (x : A) (i : α) (g : G) (r : k) : DFunLike.coe (F
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
（共 32 条，此处仅展示前 30 条）
-/
theorem d_eq [DecidableEq G] :
    d A n = (coinvariantsTensorFreeLEquiv A (Fin (n + 1) → G)).toModuleIso.inv ≫
      ((barComplex k G).coinvariantsTensorObj A).d (n + 1) n ≫
      (coinvariantsTensorFreeLEquiv A (Fin n → G)).toModuleIso.hom := by
  ext : 3
  simp [d_single (k := k), TensorProduct.tmul_add, TensorProduct.tmul_sum,
    barComplex.d_single (k := k)]

end inhomogeneousChains

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous chains
$$\dots \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A \to 0$$
which calculates the group homology of `A`. -/
/-
**groupHomology.inhomogeneousChains** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：inhomogeneousChains : ChainComplex (ModuleCat k) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous 
chains
$$\dots \to \bigoplus_{G^1} A \to \bigoplus_{G^0} A \to 0$$
which calculates the group homology of `A`.
-/
noncomputable abbrev inhomogeneousChains :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n → G) →₀ A))
    (fun n => inhomogeneousChains.d A n) fun n => by
    classical
    rw [inhomogeneousChains.d_eq, inhomogeneousChains.d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).coinvariantsTensorObj A).d_comp_d]
    simp

open inhomogeneousChains

variable {A n} in
@[ext]
/-
**groupHomology.inhomogeneousChains.ext** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology
.inhomogeneousChains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] {A : Rep.{u, u, u}
 k G} {n : ℕ} {M : ModuleCat k}   {x y : (groupHomology.inhomogeneousChains A).X
 n ⟶ M},   (∀ (g : Fin n → G),       CategoryTheory.CategoryStruct.comp (ModuleC
at.ofHom (Finsupp.lsingle g)) x =         CategoryTheory.CategoryStruct.comp (Mo
duleCat.ofHom (Finsupp.lsingle g)) y) →     x = y
参数：groupHomology.inhomogeneousChains A；∀ (g : Fin n → G),       CategoryTheory.C
ategoryStruct.comp (ModuleCat.ofHom (Finsupp.lsingle g)) x =         CategoryThe
ory.CategoryStruct.comp (ModuleCat.ofHom (Finsupp.lsingle g)) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.hom_ext_iff`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R
} {f g : M ⟶ N}, f = g ↔ ModuleCat.Hom.hom f = ModuleCat.Hom.hom g
-/
theorem inhomogeneousChains.ext {M : ModuleCat k} {x y : (inhomogeneousChains A).X n ⟶ M}
    (h : ∀ g, ModuleCat.ofHom (lsingle g) ≫ x = ModuleCat.ofHom (lsingle g) ≫ y) :
    x = y := ModuleCat.hom_ext <| lhom_ext' fun g => ModuleCat.hom_ext_iff.1 (h g)
/-
**groupHomology.inhomogeneousChains.d_def** 是 Mathlib 中的一个定理，位于命名空间 `groupHomolo
gy.inhomogeneousChains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] (A : Rep.{u, u, u}
 k G) (n : ℕ),   (groupHomology.inhomogeneousChains A).d (n + 1) n = groupHomolo
gy.inhomogeneousChains.d A n
参数：A : Rep.{u, u, u} k G；n : ℕ；groupHomology.inhomogeneousChains A；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inhomogeneousChains.d_def (n : ℕ) :
    (inhomogeneousChains A).d (n + 1) n = d A n := by
  simp [inhomogeneousChains]

set_option backward.defeqAttrib.useBackward true in
/-
**groupHomology.inhomogeneousChains.d_comp_d** 是 Mathlib 中的一个定理，位于命名空间 `groupHom
ology.inhomogeneousChains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] (A : Rep.{u, u, u}
 k G) (n : ℕ),   CategoryTheory.CategoryStruct.comp (groupHomology.inhomogeneous
Chains.d A (n + 1))       (groupHomology.inhomogeneousChains.d A n) =     0
参数：A : Rep.{u, u, u} k G；n : ℕ；groupHomology.inhomogeneousChains.d A (n + 1)；gro
upHomology.inhomogeneousChains.d A n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Simproc.add_eq_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → (a + b = c + d
) = (a = c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem inhomogeneousChains.d_comp_d :
    d A (n + 1) ≫ d A n = 0 := by
  simpa [ChainComplex.of.d] using ((inhomogeneousChains A).d_comp_d (n + 2) (n + 1) n)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous chains is isomorphic
to `(A ⊗[k] P)_G`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
/-
**groupHomology.inhomogeneousChainsIso** 是 Mathlib 中的一个定义，位于命名空间 `groupHomology`
。
形式化陈述：inhomogeneousChainsIso [DecidableEq G] : inhomogeneousChains A ≅ (barCompl
ex k G).coinvariantsTensorObj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous chains i
s isomorphic
to `(A ⊗[k] P)_G`, where `P` is the bar resolution of `k` as a trivial `G`-repre
sentation.
-/
def inhomogeneousChainsIso [DecidableEq G] :
    inhomogeneousChains A ≅ (barComplex k G).coinvariantsTensorObj A := by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeLEquiv A (Fin i → G)).toModuleIso.symm
  rintro i j rfl
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

/-- The `n`-cycles `Zₙ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
differential `Cₙ(G, A) ⟶ Cₙ₋₁(G, A)` in the complex of inhomogeneous chains. -/
/-
**groupHomology.cycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：cycles (n : Nat) : ModuleCat k
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-cycles `Zₙ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kerne
l of the
differential `Cₙ(G, A) ⟶ Cₙ₋₁(G, A)` in the complex of inhomogeneous chains.
-/
abbrev cycles (n : ℕ) : ModuleCat k := (inhomogeneousChains A).cycles n

open HomologicalComplex

variable {A} in
/-- When `m = 0` this makes a term of `cycles A 0` from any element of `A` (or more precisely
any element in the kernel of `d₀,₀ = 0`). When `m` is positive, this makes a term of `cycles A m`
from any element of the kernel of `dₘ,ₘ₋₁`. -/
/-
**groupHomology.cyclesMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：cyclesMk (m n : Nat) (h : (ComplexShape.down Nat).next m = n) (f : (Fin m 
-> G) ->₀ A) (hf : (inhomogeneousChains A).d m n f = 0) : cycles A m
参数：m n : Nat；h : (ComplexShape.down Nat).next m = n；f : (Fin m -> G) ->₀ A；hf : 
(inhomogeneousChains A).d m n f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `m = 0` this makes a term of `cycles A 0` from any element of `A` (or more 
precisely
any element in the kernel of `d₀,₀ = 0`). When `m` is positive, this makes a ter
m of `cycles A m`
from any element of the kernel of `dₘ,ₘ₋₁`.
-/
abbrev cyclesMk (m n : ℕ) (h : (ComplexShape.down ℕ).next m = n) (f : (Fin m → G) →₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) : cycles A m :=
  (inhomogeneousChains A).cyclesMk f n h hf

/-- The natural inclusion of the `n`-cycles `Zₙ(G, A)` into the `n`-chains `Cₙ(G, A).` -/
/-
**groupHomology.iCycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：iCycles (n : Nat) : cycles A n ⟶ (inhomogeneousChains A).X n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion of the `n`-cycles `Zₙ(G, A)` into the `n`-chains `Cₙ(G, A)
.`
-/
abbrev iCycles (n : ℕ) : cycles A n ⟶ (inhomogeneousChains A).X n :=
  (inhomogeneousChains A).iCycles n

variable {A} in
/-
**groupHomology.iCycles_mk** 是 Mathlib 中的一个定理，位于命名空间 `groupHomology`。
形式化陈述：iCycles_mk {m n : Nat} (h : (ComplexShape.down Nat).next m = n) (f : (Fin 
m -> G) ->₀ A) (hf : (inhomogeneousChains A).d m n f = 0) : iCycles A m (cyclesM
k m n h f hf) = f
参数：h : (ComplexShape.down Nat).next m = n；f : (Fin m -> G) ->₀ A；hf : (inhomogen
eousChains A).d m n f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `HomologicalComplex.i_cyclesMk`：i_cyclesMk {i : ι} (x : (forget₂ C Ab).ob
j (K.X i)) (j : ι) (hj : c.next i = j) (hx : ((forget₂ C Ab).map (K.d i j)) x = 
0) : ((forget₂ C Ab…
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
· 使用定理 `CategoryTheory.ShortComplex.instPreservesHomologyModuleCatAbForget₂Linea
rMapIdCarrierAddMonoidHomCarrier`：∀ {R : Type u} [inst : Ring R], (CategoryTheor
y.forget₂ (ModuleCat R) Ab).PreservesHomology
-/
theorem iCycles_mk {m n : ℕ} (h : (ComplexShape.down ℕ).next m = n) (f : (Fin m → G) →₀ A)
    (hf : (inhomogeneousChains A).d m n f = 0) :
    iCycles A m (cyclesMk m n h f hf) = f := by
  exact (inhomogeneousChains A).i_cyclesMk f n h hf

/-- This is the map from `i`-chains to `j`-cycles induced by the differential in the complex of
inhomogeneous chains. -/
/-
**groupHomology.toCycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupHomology`。
形式化陈述：toCycles (i j : Nat) : (inhomogeneousChains A).X i ⟶ cycles A j
参数：i j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the map from `i`-chains to `j`-cycles induced by the differential in the
 complex of
inhomogeneous chains.
-/
abbrev toCycles (i j : ℕ) : (inhomogeneousChains A).X i ⟶ cycles A j :=
  (inhomogeneousChains A).toCycles i j

end groupHomology

open groupHomology Rep

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

/-- The group homology of a `k`-linear `G`-representation `A`, as the homology of its complex
of inhomogeneous chains. -/
/-
**groupHomology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupHomology (n : Nat) : ModuleCat k
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homology of a `k`-linear `G`-representation `A`, as the homology of it
s complex
of inhomogeneous chains.
-/
def groupHomology (n : ℕ) : ModuleCat k :=
  (inhomogeneousChains A).homology n

/-- The natural map from `n`-cycles to `n`th group homology for a `k`-linear
`G`-representation `A`. -/
/-
**groupHomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from `n`-cycles to `n`th group homology for a `k`-linear
`G`-representation `A`.
-/
abbrev groupHomology.π (n : ℕ) :
    cycles A n ⟶ groupHomology A n :=
  (inhomogeneousChains A).homologyπ n

set_option backward.isDefEq.respectTransparency false in
variable {A} in
@[elab_as_elim]
/-
**groupHomology_induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：groupHomology_induction_on {n : Nat} {C : groupHomology A n -> Prop} (x : 
groupHomology A n) (h : forall x : cycles A n, C (π A n x)) : C x
参数：x : groupHomology A n；h : forall x : cycles A n, C (π A n x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `HomologicalComplex.instEpiHomologyπ`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
-/
theorem groupHomology_induction_on {n : ℕ}
    {C : groupHomology A n → Prop} (x : groupHomology A n)
    (h : ∀ x : cycles A n, C (π A n x)) : C x := by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

/-- The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Torₙ(A, k)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
/-
**groupHomologyIsoTor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupHomologyIsoTor [DecidableEq G] (n : Nat) : groupHomology A n ≅ ((Tor 
k G n).obj A).obj (Rep.trivial k G k)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Torₙ(A, k)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-represe
ntation.
-/
def groupHomologyIsoTor [DecidableEq G] (n : ℕ) :
    groupHomology A n ≅ ((Tor k G n).obj A).obj (Rep.trivial k G k) :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIso A)).hom n ≪≫
    (torIso A (barResolution k G) n).symm

/-- The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Hₙ((A ⊗ P)_G)`, where `P` is any projective resolution of `k` as a trivial `k`-linear
`G`-representation. -/
/-
**groupHomologyIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupHomologyIso [DecidableEq G] (A : Rep k G) (n : Nat) (P : ProjectiveRe
solution (Rep.trivial k G k)) : groupHomology A n ≅ (P.complex.coinvariantsTenso
rObj A).homology n
参数：A : Rep k G；n : Nat；P : ProjectiveResolution (Rep.trivial k G k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th group homology of a `k`-linear `G`-representation `A` is isomorphic to
`Hₙ((A ⊗ P)_G)`, where `P` is any projective resolution of `k` as a trivial `k`-
linear
`G`-representation.
-/
def groupHomologyIso [DecidableEq G] (A : Rep k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupHomology A n ≅ (P.complex.coinvariantsTensorObj A).homology n :=
  groupHomologyIsoTor A n ≪≫ torIso A P n
/-
**isZero_groupHomology_succ_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isZero_groupHomology_succ_of_subsingleton [Subsingleton G] (n : Nat) : Lim
its.IsZero (groupHomology A (n + 1))
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用引理 `Rep.isZero_Tor_succ_of_projective`：isZero_Tor_succ_of_projective (X Y : 
Rep k G) [Projective Y] (n : Nat) : IsZero (((Tor k G (n + 1)).obj X).obj Y)
-/
lemma isZero_groupHomology_succ_of_subsingleton [Subsingleton G] (n : ℕ) :
    Limits.IsZero (groupHomology A (n + 1)) :=
  (isZero_Tor_succ_of_projective A (Rep.trivial k G k) n).of_iso <| groupHomologyIsoTor _ _

end

