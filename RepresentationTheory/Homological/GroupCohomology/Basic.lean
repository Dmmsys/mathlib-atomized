/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Homological.Resolution
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism
$\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(\bigoplus_{G^n} k[G], A)$, where
the right-hand side is morphisms in `Rep k G`, and $k[G]$ is equipped with the left regular
representation. If we conjugate the $n$th differential in $\mathrm{Hom}(P, A)$ by this isomorphism,
where `P` is the bar resolution of `k` as a trivial `k`-linear `G`-representation, then the
resulting map agrees with the differential $d^n$ defined above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`, which provides API
specialized to `H⁰`, `H¹`, `H²`.

## Main definitions

* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
  $\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above complex and the
  complex $\mathrm{Hom}(P, A),$ where `P` is the bar resolution of `k` as a trivial resolution.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of
  `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
  (where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module k[G] A` so that we do not run into
possible scalar action diamonds.

## TODO

* Upgrading `groupCohomologyIsoExt` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
  spectral sequences in general).
-/

@[expose] public section


noncomputable section

universe u

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory

namespace inhomogeneousCochains

open Rep

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps! -isSimp]
/-
**inhomogeneousCochains.d** 是 Mathlib 中的一个定义，位于命名空间 `inhomogeneousCochains`。
形式化陈述：d [Monoid G] (A : Rep k G) (n : Nat) : ModuleCat.of k ((Fin n -> G) -> A) 
⟶ ModuleCat.of k ((Fin (n + 1) -> G) -> A)
参数：A : Rep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The differential in the complex of inhomogeneous cochains used to
calculate group cohomology.
-/
def d [Monoid G] (A : Rep k G) (n : ℕ) :
    ModuleCat.of k ((Fin n → G) → A) ⟶ ModuleCat.of k ((Fin (n + 1) → G) → A) :=
  ModuleCat.ofHom
  { toFun f g :=
      A.ρ (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
    map_add' f g := by
      ext
      simp [Finset.sum_add_distrib, add_add_add_comm]
    map_smul' r f := by
      ext
      simp [Finset.smul_sum, ← smul_assoc, mul_comm r] }

variable [Group G] (A : Rep k G) (n : ℕ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**inhomogeneousCochains.d_eq** 是 Mathlib 中的一个定理，位于命名空间 `inhomogeneousCochains`。
形式化陈述：d_eq : d A n = (freeLiftLEquiv k G (Fin n -> G) A).toModuleIso.inv ≫ ((bar
Complex k G).linearYonedaObj k A).d n (n + 1) ≫ (freeLiftLEquiv k G (Fin (n + 1)
 -> G) A).toModuleIso.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ChainComplex.of_d`：of_d (j : α) : of.d X d (j + 1) j = d j
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `Rep.barComplex.d_single`：∀ {k G : Type u} [inst : CommRing k] (n : ℕ) [i
nst_1 : Group G] (x : Fin (n + 1) → G),   ((Rep.Hom.hom (Rep.barComplex.d k G n)
) fun₀ | x =>…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Representation.IntertwiningMap.instLinearMapClass`：∀ {A : Type u_1} {G :
 Type u_2} {V : Type u_3} {W : Type u_4} [inst : Semiring A] [inst_1 : Monoid G]
   [inst_2 : AddCommMonoid V] [inst_3 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Representation.freeLift_single_single`：freeLift_single_single {α : Type 
w'} (i : α) (g : G) (r : k) (f : α -> V) : freeLift σ f (Finsupp.single i (.sing
le g r)) = r • σ g (f i)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 31 条，此处仅展示前 30 条）
-/
theorem d_eq :
    d A n =
      (freeLiftLEquiv k G (Fin n → G) A).toModuleIso.inv ≫
        ((barComplex k G).linearYonedaObj k A).d n (n + 1) ≫
          (freeLiftLEquiv k G (Fin (n + 1) → G) A).toModuleIso.hom := by
  ext
  simp [d_hom_apply, map_add, barComplex.d_single (k := k), homEquiv]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep.{u} k G)

open inhomogeneousCochains Rep

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
/-
**groupCohomology.inhomogeneousCochains** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomo
logy`。
形式化陈述：inhomogeneousCochains : CochainComplex (ModuleCat k) Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous 
cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \
to \dots$$
which calculates the group cohomology of `A`.
-/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d A n) fun n => by
    rw [d_eq, d_eq]
    slice_lhs 3 4 => rw [Iso.hom_inv_id]
    slice_lhs 2 4 => rw [Category.id_comp, ((barComplex k G).linearYonedaObj k A).d_comp_d]
    simp

variable {A n} in
@[ext]
/-
**groupCohomology.inhomogeneousCochains.ext** 是 Mathlib 中的一个定理，位于命名空间 `groupCoho
mology.inhomogeneousCochains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] {n : ℕ} [inst_1 : Group G] {A : Rep.{
u, u, u} k G}   {x y : ↑((groupCohomology.inhomogeneousCochains A).X n)}, (∀ (g 
: Fin n → G), x g = y g) → x = y
参数：(groupCohomology.inhomogeneousCochains A).X n；∀ (g : Fin n → G), x g = y g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem inhomogeneousCochains.ext {x y : (inhomogeneousCochains A).X n} (h : ∀ g, x g = y g) :
    x = y := funext h
/-
**groupCohomology.inhomogeneousCochains.d_def** 是 Mathlib 中的一个定理，位于命名空间 `groupCo
homology.inhomogeneousCochains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] [inst_1 : Group G] (A : Rep.{u, u, u}
 k G) (n : ℕ),   (groupCohomology.inhomogeneousCochains A).d n (n + 1) = inhomog
eneousCochains.d A n
参数：A : Rep.{u, u, u} k G；n : ℕ；groupCohomology.inhomogeneousCochains A；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.of_d`：of_d (j : α) : of.d X d j (j + 1) = d j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = d A n := by
  simp

set_option backward.defeqAttrib.useBackward true in
/-
**groupCohomology.inhomogeneousCochains.d_comp_d** 是 Mathlib 中的一个定理，位于命名空间 `grou
pCohomology.inhomogeneousCochains`。
形式化陈述：∀ {k G : Type u} [inst : CommRing k] (n : ℕ) [inst_1 : Group G] (A : Rep.{
u, u, u} k G),   CategoryTheory.CategoryStruct.comp (inhomogeneousCochains.d A n
) (inhomogeneousCochains.d A (n + 1)) = 0
参数：n : ℕ；A : Rep.{u, u, u} k G；inhomogeneousCochains.d A n；inhomogeneousCochains
.d A (n + 1)。
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Nat.Simproc.add_eq_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → (a + b = c + d
) = (a = c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `HomologicalComplex.d_comp_d`：d_comp_d (C : HomologicalComplex V c) (i j 
k : ι) : C.d i j ≫ C.d j k = 0
-/
theorem inhomogeneousCochains.d_comp_d :
    d A n ≫ d A (n + 1) = 0 := by
  simpa [CochainComplex.of.d] using (inhomogeneousCochains A).d_comp_d n (n + 1) (n + 2)

set_option backward.isDefEq.respectTransparency false in
/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the bar resolution of `k` as a trivial `G`-representation. -/
/-
**groupCohomology.inhomogeneousCochainsIso** 是 Mathlib 中的一个定义，位于命名空间 `groupCohom
ology`。
形式化陈述：inhomogeneousCochainsIso : inhomogeneousCochains A ≅ (barComplex k G).line
arYonedaObj k A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains
 is isomorphic
to `Hom(P, A)`, where `P` is the bar resolution of `k` as a trivial `G`-represen
tation.
-/
def inhomogeneousCochainsIso :
    inhomogeneousCochains A ≅ (barComplex k G).linearYonedaObj k A := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (Rep.freeLiftLEquiv k G (Fin i → G) A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  simp [d_eq, -LinearEquiv.toModuleIso_hom, -LinearEquiv.toModuleIso_inv]

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of inhomogeneous cochains. -/
/-
**groupCohomology.cocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：cocycles (n : Nat) : ModuleCat k
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the ker
nel of the
`n`th differential in the complex of inhomogeneous cochains.
-/
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n

variable {A} in
/-- Make an `n`-cocycle out of an element of the kernel of the `n`th differential. -/
/-
**groupCohomology.cocyclesMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：cocyclesMk {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.d 
A n f = 0) : cocycles A n
参数：f : (Fin n -> G) -> A；h : inhomogeneousCochains.d A n f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an `n`-cocycle out of an element of the kernel of the `n`th differential.
-/
abbrev cocyclesMk {n : ℕ} (f : (Fin n → G) → A) (h : inhomogeneousCochains.d A n f = 0) :
    cocycles A n :=
  (inhomogeneousCochains A).cyclesMk f (n + 1) (by simp) (by simp [h])

/-- The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G, A).` -/
/-
**groupCohomology.iCocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：iCocycles (n : Nat) : cocycles A n ⟶ (inhomogeneousCochains A).X n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G
, A).`
-/
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ (inhomogeneousCochains A).X n :=
  (inhomogeneousCochains A).iCycles n

/-- This is the map from `i`-cochains to `j`-cocycles induced by the differential in the complex of
inhomogeneous cochains. -/
/-
**groupCohomology.toCocycles** 是 Mathlib 中的一个缩写定义，位于命名空间 `groupCohomology`。
形式化陈述：toCocycles (i j : Nat) : (inhomogeneousCochains A).X i ⟶ cocycles A j
参数：i j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the map from `i`-cochains to `j`-cocycles induced by the differential in
 the complex of
inhomogeneous cochains.
-/
abbrev toCocycles (i j : ℕ) : (inhomogeneousCochains A).X i ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

variable {A} in
/-
**groupCohomology.iCocycles_mk** 是 Mathlib 中的一个定理，位于命名空间 `groupCohomology`。
形式化陈述：iCocycles_mk {n : Nat} (f : (Fin n -> G) -> A) (h : inhomogeneousCochains.
d A n f = 0) : iCocycles A n (cocyclesMk f h) = f
参数：f : (Fin n -> G) -> A；h : inhomogeneousCochains.d A n f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.i_cyclesMk`：i_cyclesMk {i : ι} (x : (forget₂ C Ab).ob
j (K.X i)) (j : ι) (hj : c.next i = j) (hx : ((forget₂ C Ab).map (K.d i j)) x = 
0) : ((forget₂ C Ab…
· 使用定理 `ModuleCat.forget₂_addCommGrp_additive`：∀ {R : Type u} [inst : Ring R], (
CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat).Additive
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `ModuleCat.instPreservesColimitsOfSizeAddCommGrpCatForget₂LinearMapIdCarr
ierAddMonoidHomCarrierOfHasColimitsOfSizeAddCommGrpMax`：∀ (R : Type w) [inst : R
ing R]   [CategoryTheory.Limits.HasColimitsOfSize.{u, v, max w w', max (w + 1) (
w' + 1)} AddCommGrpMax],   CategoryT…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.next`：next (α : Type*) [AddRightCancelSemigroup α] [One α
] (i : α) : (ComplexShape.up α).next i = i + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `CochainComplex.of_d`：of_d (j : α) : of.d X d j (j + 1) = d j
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
theorem iCocycles_mk {n : ℕ} (f : (Fin n → G) → A) (h : inhomogeneousCochains.d A n f = 0) :
    iCocycles A n (cocyclesMk f h) = f := by
  exact (inhomogeneousCochains A).i_cyclesMk (i := n) f (n + 1) (by simp) (by simp [h])

end groupCohomology

open groupCohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
/-
**groupCohomology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupCohomology [Group G] (A : Rep k G) (n : Nat) : ModuleCat k
参数：A : Rep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology o
f its complex
of inhomogeneous cochains.
-/
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
/-
**groupCohomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`.
-/
abbrev groupCohomology.π [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
/-
**groupCohomology_induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：groupCohomology_induction_on [Group G] {A : Rep k G} {n : Nat} {C : groupC
ohomology A n -> Prop} (x : groupCohomology A n) (h : forall x : cocycles A n, C
 (π A n x)) : C x
参数：x : groupCohomology A n；h : forall x : cocycles A n, C (π A n x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `HomologicalComplex.instEpiHomologyπ`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
-/
theorem groupCohomology_induction_on [Group G] {A : Rep k G} {n : ℕ}
    {C : groupCohomology A n → Prop} (x : groupCohomology A n)
    (h : ∀ x : cocycles A n, C (π A n x)) : C x := by
  rcases (ModuleCat.epi_iff_surjective (π A n)).1 inferInstance x with ⟨y, rfl⟩
  exact h y

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
/-
**groupCohomologyIsoExt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupCohomologyIsoExt [Group G] (A : Rep k G) (n : Nat) : groupCohomology 
A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A
参数：A : Rep k G；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic 
to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-represe
ntation.
-/
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.barResolution.extIso k G A n).symm

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Hⁿ(Hom(P, A))`, where `P` is any projective resolution of `k` as a trivial `k`-linear
`G`-representation. -/
/-
**groupCohomologyIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：groupCohomologyIso [Group G] (A : Rep k G) (n : Nat) (P : ProjectiveResolu
tion (Rep.trivial k G k)) : groupCohomology A n ≅ (P.complex.linearYonedaObj k A
).homology n
参数：A : Rep k G；n : Nat；P : ProjectiveResolution (Rep.trivial k G k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic 
to
`Hⁿ(Hom(P, A))`, where `P` is any projective resolution of `k` as a trivial `k`-
linear
`G`-representation.
-/
def groupCohomologyIso [Group G] (A : Rep k G) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  groupCohomologyIsoExt A n ≪≫ P.isoExt _ _
/-
**isZero_groupCohomology_succ_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isZero_groupCohomology_succ_of_subsingleton [Group G] [Subsingleton G] (A 
: Rep k G) (n : Nat) : Limits.IsZero (groupCohomology A (n + 1))
参数：A : Rep k G；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `Rep.instEnoughProjectives`：∀ {k G : Type u} [inst : CommRing k] [inst_1 
: Monoid G], CategoryTheory.EnoughProjectives (Rep.{max w u, u, u} k G)
· 使用引理 `isZero_Ext_succ_of_projective`：isZero_Ext_succ_of_projective (X Y : C) [
Projective X] (n : Nat) : IsZero (((Ext R C (n + 1)).obj (Opposite.op X)).obj Y)
-/
lemma isZero_groupCohomology_succ_of_subsingleton
    [Group G] [Subsingleton G] (A : Rep k G) (n : ℕ) :
    Limits.IsZero (groupCohomology A (n + 1)) :=
  (isZero_Ext_succ_of_projective (Rep.trivial k G k) A n).of_iso <| groupCohomologyIsoExt _ _
