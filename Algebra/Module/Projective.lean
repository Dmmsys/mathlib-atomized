/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Antoine Labelle
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Logic.UnivLE

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `Module.Projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `Module.projective_lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `Module.Projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `Module.Projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## Tags

projective module

-/

@[expose] public section

universe w v u

open LinearMap hiding id
open DirectSum hiding id_apply
open Finsupp

/- The actual implementation we choose: `P` is projective if the natural surjection
from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
if maps from the module lift along surjections. There are several other equivalent
definitions. -/
@[wikidata Q942423]
/-
**Module.Projective** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → (P : Type u_2) → [inst_1 : AddCommM
onoid P] → [_root_.Module R P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An R-module is projective if it is a direct summand of a free module, or equival
ently
if maps from the module lift along surjections. There are several other equivale
nt
definitions.
-/
class Module.Projective (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P] :
    Prop where
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.linearCombination R id) s

namespace Module

section Semiring

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

/-
**Module.projective_def** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：projective_def : Projective R P ↔ exists s : P ->ₗ[R] P ->₀ R, Function.Le
ftInverse (linearCombination R id) s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.out`：∀ {R : Type u_1} {inst : Semiring R} {P : Type u_
2} {inst_1 : AddCommMonoid P} {inst_2 : _root_.Module R P}   [self : Module.Proj
ective R P]…
-/
theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**Module.projective_def'** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：projective_def' : Projective R P ↔ exists s : P ->ₗ[R] P ->₀ R, Finsupp.li
nearCombination R id ∘ₗ s = .id
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem projective_def' :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.linearCombination R id ∘ₗ s = .id := by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

/-- A projective R-module has the property that maps from it lift along surjections. -/
/-
**Module.projective_lifting_property** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：projective_lifting_property [h : Projective R P] (f : M ->ₗ[R] N) (g : P -
>ₗ[R] N) (hf : Function.Surjective f) : exists h : P ->ₗ[R] M, f ∘ₗ h = g
参数：f : M ->ₗ[R] N；g : P ->ₗ[R] N；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.out`：∀ {R : Type u_1} {inst : Semiring R} {P : Type u_
2} {inst_1 : AddCommMonoid P} {inst_2 : _root_.Module R P}   [self : Module.Proj
ective R P]…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A projective R-module has the property that maps from it lift along surjections.
-/
theorem projective_lifting_property [h : Projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
    (hf : Function.Surjective f) : ∃ h : P →ₗ[R] M, f ∘ₗ h = g := by
  /-
    Here's the first step of the proof.
    Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
    on a type `X`. The universal property `Finsupp.linearCombination` says that to a map
    `X → N` from a type to an `R`-module, we get an associated R-module map
    `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
    `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
    a map `φ : (P →₀ R) →ₗ M`.
    -/
  let φ : (P →₀ R) →ₗ[R] M := Finsupp.linearCombination _ fun p => Function.surjInv hf (g p)
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  obtain ⟨s, hs⟩ := h.out
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s
  ext p
  conv_rhs => rw [← hs p]
  simp [φ, Finsupp.linearCombination_apply, Function.surjInv_eq hf, map_finsuppSum]
/-
**Module._root_.LinearMap.exists_rightInverse_of_surjective** 是 Mathlib 中的一个定理，位
于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.exists_rightInverse_of_surjective [Projective R P]
    (f : M →ₗ[R] P) (hf_surj : range f = ⊤) : ∃ g : P →ₗ[R] M, f ∘ₗ g = LinearMap.id :=
  projective_lifting_property f (.id : P →ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

open Function in
/-
**Module._root_.Function.Surjective.surjective_linearMapComp_left** 是 Mathlib 中的
一个定理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Surjective.surjective_linearMapComp_left [Projective R P]
    {f : M →ₗ[R] P} (hf_surj : Surjective f) : Surjective (fun g : N →ₗ[R] M ↦ f.comp g) :=
  surjective_comp_left_of_exists_rightInverse <|
    f.exists_rightInverse_of_surjective <| range_eq_top_of_surjective f hf_surj

/-- A module which satisfies the universal property is projective: If all surjections of
`R`-modules `(P →₀ R) →ₗ[R] P` have `R`-linear left inverse maps, then `P` is
projective. -/
/-
**Module.Projective.of_lifting_property''** 是 Mathlib 中的一个定理，位于命名空间 `Module.Proj
ective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Type v} [inst_1 : AddCommMonoid P]
 [inst_2 : _root_.Module R P],   (∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective 
⇑f → ∃ h, f ∘ₗ h = LinearMap.id) → Module.Projective R P
参数：∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective ⇑f → ∃ h, f ∘ₗ h = LinearMap.id
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.projective_def'`：projective_def' : Projective R P ↔ exists s : P 
->ₗ[R] P ->₀ R, Finsupp.linearCombination R id ∘ₗ s = .id
· 使用定理 `Finsupp.linearCombination_surjective`：linearCombination_surjective (h : 
Function.Surjective v) : Function.Surjective (linearCombination R v)
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id

--- 原说明 ---
A module which satisfies the universal property is projective: If all surjection
s of
`R`-modules `(P →₀ R) →ₗ[R] P` have `R`-linear left inverse maps, then `P` is
projective.
-/
theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : ∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective f →
      ∃ h : P →ₗ[R] (P →₀ R), f.comp h = .id) :
    Projective R P :=
  projective_def'.2 <| huniv (Finsupp.linearCombination R (id : P → P))
    (linearCombination_surjective _ Function.surjective_id)

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Projective R P] [Projective R Q] : Projective R (P × Q) := by
  refine .of_lifting_property'' fun f hf ↦ ?_
  rcases projective_lifting_property f (.inl _ _ _) hf with ⟨g₁, hg₁⟩
  rcases projective_lifting_property f (.inr _ _ _) hf with ⟨g₂, hg₂⟩
  refine ⟨coprod g₁ g₂, ?_⟩
  rw [LinearMap.comp_coprod, hg₁, hg₂, LinearMap.coprod_inl_inr]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : ∀ i : ι, Projective R (A i)] : Projective R (Π₀ i, A i) :=
  .of_lifting_property'' fun f hf ↦ by
    classical
      choose g hg using fun i ↦ projective_lifting_property f (DFinsupp.lsingle i) hf
      replace hg : ∀ i x, f (g i x) = DFinsupp.single i x := fun i ↦ DFunLike.congr_fun (hg i)
      refine ⟨DFinsupp.coprodMap g, ?_⟩
      ext i x j
      simp only [comp_apply, id_apply, DFinsupp.lsingle_apply, DFinsupp.coprodMap_apply_single, hg]

/-- Free modules are projective. -/
/-
**Module.Projective.of_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Type u_2} [inst_1 : AddCommMonoi
d P] [inst_2 : _root_.Module R P]   {ι : Type u_8} (b : Module.Basis ι R P), Mod
ule.Projective R P
参数：b : Module.Basis ι R P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.constr_apply`：constr_apply (f : ι -> M') (x : M) : constr (
M'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.smul_single'`：smul_single' {_ : Semiring R} (c : R) (a : α) (b :
 R) : c • Finsupp.single a b = Finsupp.single a (c * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x

--- 原说明 ---
Free modules are projective.
-/
theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Projective.of_free [Module.Free R P] : Module.Projective R P :=
  .of_basis <| Module.Free.chooseBasis R P

/-- A direct summand of a projective module is projective. -/
/-
**Module.Projective.of_split** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Type u_2} [inst_1 : AddCommMonoi
d P] [inst_2 : _root_.Module R P]   {M : Type u_3} [inst_3 : AddCommMonoid M] [i
nst_4 : _root_.Module R M] [Module.Projective R M] (i : P →ₗ[R] M)   (s : M →ₗ[R
] P), s ∘ₗ i = LinearMap.id → Module.Projective R P
参数：i : P →ₗ[R] M；s : M →ₗ[R] P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x

--- 原说明 ---
A direct summand of a projective module is projective.
-/
theorem Projective.of_split [Module.Projective R M]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x ↦ ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply, hg,
    ← LinearMap.comp_apply, H, LinearMap.id_apply]
/-
**Module.Projective.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_8} {S : Type u_9} [inst : Semiring R] [inst_1 : Semiring S] 
{M : Type u_10} {N : Type u_11}   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMo
noid N] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module S N]   {σ : R →+* S
} {σ' : S →+* R} [inst_6 : RingHomInvPair σ σ'] [inst_7 : RingHomInvPair σ' σ] (
e₂ : M ≃ₛₗ[σ] N)   [Module.Projective R M], Module.Projective S N
参数：e₂ : M ≃ₛₗ[σ] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.map_zero`：∀ {R : Type u_4} {S : Type u_5} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S), f 0 = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapRange.congr_simp`：∀ {α : Type u_1} {M : Type u_4} {N : Type u
_5} [inst : Zero M] [inst_1 : Zero N] (f f_1 : M → N) (e_f : f = f_1)   (hf : f 
0 = 0) (g g_1 : α…
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
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `RingHomInvPair.toRingEquiv_apply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [ins
t : Semiring R₁] [inst_1 : Semiring R₂] (σ : R₁ →+* R₂) (σ' : R₂ →+* R₁)   [inst
_2 : RingHomInvPair σ …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 36 条，此处仅展示前 30 条）
-/
theorem Projective.of_equiv {R S} [Semiring R] [Semiring S] {M N}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] N)
    [Projective R M] : Projective S N := by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N →ₗ[S] N →₀ S :=
  { toFun := fun x ↦ (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y ↦ by ext; simp
    map_smul' := fun r v ↦ by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x ↦ ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using! hf
/-
**Module.Projective.of_equiv'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Type u_2} [inst_1 : AddCommMonoi
d P] [inst_2 : _root_.Module R P]   {M : Type u_3} [inst_3 : AddCommMonoid M] [i
nst_4 : _root_.Module R M] [Module.Projective R M] (e : M ≃ₗ[R] P),   Module.Pro
jective R P
参数：e : M ≃ₗ[R] P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
-/
theorem Projective.of_equiv' [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P :=
  .of_equiv e

@[deprecated (since := "2026-02-14")] alias Projective.of_ringEquiv := Projective.of_equiv
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Projective R M] : Projective R (ULift.{w} M) :=
  Projective.of_equiv' ULift.moduleEquiv.symm
/-
**Module.Projective.of_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_3} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Module.Projective R (ULift.{w, u_3} M)], Mo
dule.Projective R M
参数：ULift.{w, u_3} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_equiv'`：∀ {R : Type u_1} [inst : Semiring R] {P : T
ype u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3
} [inst_3 : AddCo…
-/
theorem Projective.of_ulift [Projective R (ULift.{w} M)] : Projective R M :=
  Projective.of_equiv' ULift.moduleEquiv
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{w} M] [Projective R M] : Projective R (Shrink.{w} M) :=
  Projective.of_equiv' (Shrink.linearEquiv R M).symm
/-
**Module.Projective.of_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {M : Type u_3} [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [inst_3 : Small.{w, u_3} M] [Module.Projecti
ve R (Shrink.{w, u_3} M)], Module.Projective R M
参数：Shrink.{w, u_3} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_equiv'`：∀ {R : Type u_1} [inst : Semiring R] {P : T
ype u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3
} [inst_3 : AddCo…
-/
theorem Projective.of_shrink [Small.{w} M] [Projective R (Shrink.{w} M)] : Projective R M :=
  Projective.of_equiv' (Shrink.linearEquiv R M)

/-- A quotient of a projective module is projective iff it is a direct summand. -/
/-
**Module.Projective.iff_split_of_projective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Pr
ojective`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {P : Type u_2} [inst_1 : AddCommMonoi
d P] [inst_2 : _root_.Module R P]   {M : Type u_3} [inst_3 : AddCommMonoid M] [i
nst_4 : _root_.Module R M] [Module.Projective R M] (s : M →ₗ[R] P),   Function.S
urjective ⇑s → (Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id)
参数：s : M →ₗ[R] P；Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…

--- 原说明 ---
A quotient of a projective module is projective iff it is a direct summand.
-/
theorem Projective.iff_split_of_projective [Module.Projective R M] (s : M →ₗ[R] P)
    (hs : Function.Surjective s) :
    Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id :=
  ⟨fun _ ↦ projective_lifting_property _ _ hs, fun ⟨i, H⟩ ↦ Projective.of_split i s H⟩

end Semiring

section Ring

variable {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P]
variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]
variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]

/-- A variant of `Projective.iff_split` allowing for a more flexible selection of the universe
  for the free module `M`. -/
/-
**Module.Projective.iff_split'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Type v} [inst_1 : AddCommMonoid P]
 [inst_2 : _root_.Module R P] [Small.{w, u} R]   [Small.{w, v} P], Module.Projec
tive R P ↔ ∃ M x x_1, ∃ (_ : Module.Free R M), ∃ i s, s ∘ₗ i = LinearMap.id
参数：_ : Module.Free R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…

--- 原说明 ---
A variant of `Projective.iff_split` allowing for a more flexible selection of th
e universe
  for the free module `M`.
-/
theorem Projective.iff_split' [Small.{w} R] [Small.{w} P] : Module.Projective R P ↔
    ∃ (M : Type w) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id := by
  let e : (Shrink.{w, v} P →₀ Shrink.{w, u} R) ≃ₗ[R] P →₀ R :=
    Finsupp.mapDomain.linearEquiv _ R (equivShrink P).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨(Shrink.{w} P) →₀ (Shrink.{w} R), _, _, Free.of_basis ⟨e⟩,
    e.symm.toLinearMap ∘ₗ i, (linearCombination R id) ∘ₗ e.toLinearMap, ?_⟩,
      fun ⟨_, _, _, _, i, s, H⟩ ↦ Projective.of_split i s H⟩
  apply LinearMap.ext
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.apply_symm_apply]
  exact hi

/-- A module is projective iff it is the direct summand of a free module. -/
/-
**Module.Projective.iff_split** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Type v} [inst_1 : AddCommMonoid P]
 [inst_2 : _root_.Module R P],   Module.Projective R P ↔ ∃ M x x_1, ∃ (_ : Modul
e.Free R M), ∃ i s, s ∘ₗ i = LinearMap.id
参数：_ : Module.Free R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.iff_split'`：∀ {R : Type u} [inst : Semiring R] {P : Ty
pe v} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P] [Small.{w, u} R]  
 [Small.{w, v} P],…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
A module is projective iff it is the direct summand of a free module.
-/
theorem Projective.iff_split : Module.Projective R P ↔
    ∃ (M : Type max u v) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id :=
  Projective.iff_split'.{max u v}

open TensorProduct in
/-
**Module.Projective.tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {R₀ : Type u_2} {M : Type u_1} {N : Typ
e u_3} [inst_1 : CommSemiring R₀]   [inst_2 : Algebra R₀ R] [inst_3 : AddCommMon
oid M] [inst_4 : _root_.Module R₀ M] [inst_5 : _root_.Module R M]   [inst_6 : Is
ScalarTower R₀ R M] [inst_7 : AddCommMonoid N] [inst_8 : _root_.Module R₀ N] [hM
 : Module.Projective R M]   [hN : Module.Projective R₀ N], Module.Projective R (
TensorProduct R₀ M N)
参数：TensorProduct R₀ M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Projective.tensorProduct [hM : Module.Projective R M] [hN : Module.Projective R₀ N] :
    Module.Projective R (M ⊗[R₀] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  have : Module.Projective R (M ⊗[R₀] (N →₀ R₀)) := by
    fapply Projective.of_split (R := R) (M := ((M →₀ R) ⊗[R₀] (N →₀ R₀)))
    · exact (AlgebraTensorModule.map sM (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · exact (AlgebraTensorModule.map
        (Finsupp.linearCombination R id) (LinearMap.id (R := R₀) (M := N →₀ R₀)))
    · ext; simp [hsM _]
  fapply Projective.of_split (R := R) (M := (M ⊗[R₀] (N →₀ R₀)))
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) sN)
  · exact (AlgebraTensorModule.map (LinearMap.id (R := R) (M := M)) (linearCombination R₀ id))
  · ext; simp [hsN _]

end Ring

section OfLiftingProperty

/-- A module which satisfies the universal property is projective. -/
/-
**Module.Projective.of_lifting_property'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Proje
ctive`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Type v} [inst_1 : AddCommMonoid P]
 [inst_2 : _root_.Module R P]   [Small.{v, u} R],   (∀ {M N : Type v} [inst_4 : 
AddCommMonoid M] [inst_5 : AddCommMonoid N] [inst_6 : _root_.Module R M]       [
inst_7 : _root_.Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N), Function.Surjective
 ⇑f → ∃ h, f ∘ₗ h = g) →     Module.Projective R P
参数：∀ {M N : Type v} [inst_4 : AddCommMonoid M] [inst_5 : AddCommMonoid N] [inst_
6 : _root_.Module R M]       [inst_7 : _root_.Module R N] (f : M →ₗ[R] N) (g : P
 →ₗ[R] N), Function.Surjective ⇑f → ∃ h, f ∘ₗ h = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_lifting_property''`：∀ {R : Type u} [inst : Semiring
 R] {P : Type v} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P],   (∀ (
f : (P →₀ R) →ₗ[R] P), Functi…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…

--- 原说明 ---
A module which satisfies the universal property is projective.
-/
theorem Projective.of_lifting_property' {R : Type u} [Semiring R] {P : Type v}
    [AddCommMonoid P] [Module R P] [Small.{v} R]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (h : ∀ {M : Type v} {N : Type v} [AddCommMonoid M] [AddCommMonoid N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P := by
  refine of_lifting_property'' (fun p hp ↦ ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

/-- A variant of `of_lifting_property'` when we're working over a `[Ring R]`,
  which only requires quantifying over modules with an `AddCommGroup` instance. -/
/-
**Module.Projective.of_lifting_property** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projec
tive`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {P : Type v} [inst_1 : AddCommGroup P] [ins
t_2 : _root_.Module R P] [Small.{v, u} R],   (∀ {M N : Type v} [inst_4 : AddComm
Group M] [inst_5 : AddCommGroup N] [inst_6 : _root_.Module R M]       [inst_7 : 
_root_.Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N), Function.Surjective ⇑f → ∃ h
, f ∘ₗ h = g) →     Module.Projective R P
参数：∀ {M N : Type v} [inst_4 : AddCommGroup M] [inst_5 : AddCommGroup N] [inst_6 
: _root_.Module R M]       [inst_7 : _root_.Module R N] (f : M →ₗ[R] N) (g : P →
ₗ[R] N), Function.Surjective ⇑f → ∃ h, f ∘ₗ h = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_lifting_property''`：∀ {R : Type u} [inst : Semiring
 R] {P : Type v} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P],   (∀ (
f : (P →₀ R) →ₗ[R] P), Functi…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…

--- 原说明 ---
A variant of `of_lifting_property'` when we're working over a `[Ring R]`,
  which only requires quantifying over modules with an `AddCommGroup` instance.
-/
theorem Projective.of_lifting_property {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module R P] [Small.{v} R]
    -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
    (h : ∀ {M : Type v} {N : Type v} [AddCommGroup M] [AddCommGroup N]
      [Module R M] [Module R N] (f : M →ₗ[R] N) (g : P →ₗ[R] N),
        Function.Surjective f → ∃ h : P →ₗ[R] M, f.comp h = g) :
    -- then `P` is projective.
    Projective R P := by
  refine of_lifting_property'' (fun p hp ↦ ?_)
  let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
  rcases h (p ∘ₗ e.toLinearMap) LinearMap.id (hp.comp e.surjective) with ⟨g, hg⟩
  exact ⟨e.toLinearMap ∘ₗ g, hg⟩

end OfLiftingProperty

section DirectSum

variable {R : Type u} [Semiring R]
variable {ι : Type v} {M : ι → Type w} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]

/-
**Module.Projective.directSum_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)],   
Module.Projective R (DirectSum ι fun i => M i) ↔ ∀ (i : ι), Module.Projective R 
(M i)
参数：i : ι；M i；i : ι；M i；DirectSum ι fun i => M i；i : ι；M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirectSum.component_comp_lof_same`：component_comp_lof_same [DecidableEq 
ι] (i : ι) : component R ι M i ∘ₗ lof R ι M i = .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Projective.of_equiv'`：∀ {R : Type u_1} [inst : Semiring R] {P : T
ype u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3
} [inst_3 : AddCo…
· 使用定理 `Module.instProjectiveDFinsupp`：∀ {R : Type u_1} [inst : Semiring R] {ι :
 Type u_6} (A : ι → Type u_7) [inst_1 : (i : ι) → AddCommMonoid (A i)]   [inst_2
 : (i : ι) → _root_…
-/
theorem Projective.directSum_iff : Projective R (⨁ i, M i) ↔ ∀ (i : ι), Projective R (M i) := by
  classical
  refine ⟨fun H i ↦ ?_, fun H ↦ ?_⟩
  · exact .of_split (DirectSum.lof ..) (DirectSum.component ..) (by simp)
  · let e : (⨁ i, M i) ≃ₗ[R] Π₀ i, M i := .refl ..
    exact Projective.of_equiv' e.symm
/-
**Module.Projective.directSum** 是 Mathlib 中的一个定理，位于命名空间 `Module.Projective`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] [∀ 
(i : ι), Module.Projective R (M i)],   Module.Projective R (DirectSum ι fun i =>
 M i)
参数：i : ι；M i；i : ι；M i；i : ι；M i；DirectSum ι fun i => M i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Projective.directSum_iff`：∀ {R : Type u} [inst : Semiring R] {ι :
 Type v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (
i : ι) → _root_.Modul…
-/
instance Projective.directSum [∀ (i : ι), Projective R (M i)] : Projective R (⨁ i, M i) :=
  directSum_iff.mpr ‹_›

end DirectSum

end Module

