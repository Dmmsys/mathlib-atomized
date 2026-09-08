/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Topology on `Hom(R, S)`

In this file, we define topology on `Hom(A, R)` for a topological ring `R`,
given by the coarsest topology that makes `f ↦ f x` continuous for all `x : A`.
Alternatively, given a presentation `A = ℤ[xᵢ]/I`,
this is the subspace topology `Hom(A, R) ↪ Hom(ℤ[xᵢ], R) = Rᶥ`.

## Main results
- `CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective`:
  `Hom(A/I, R)` is a closed subspace of `Hom(A, R)` if `R` is Hausdorff.
- `CommRingCat.HomTopology.mvPolynomialHomeomorph`:
  `Hom(A[Xᵢ], R)` is homeomorphic to `Hom(A, R) × Rᶥ`.
- `CommRingCat.HomTopology.isEmbedding_pushout`:
  `Hom(B ⊗[A] C, R)` has the subspace topology from `Hom(B, R) × Hom(C, R)`.

-/

@[expose] public section

universe u v

open CategoryTheory Topology

namespace CommRingCat.HomTopology

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

/--
The topology on `Hom(A, R)` for a topological ring `R`, given by the coarsest topology that
makes `f ↦ f x` continuous for all `x : A` (see `continuous_apply`).
Alternatively, given a presentation `A = ℤ[xᵢ]/I`,
this is the subspace topology `Hom(A, R) ↪ Hom(ℤ[xᵢ], R) = Rᶥ` (see `mvPolynomialHomeomorph`).

This is a scoped instance in `CommRingCat.HomTopology`.
-/
/-
**CommRingCat.HomTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.HomTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on `Hom(A, R)` for a topological ring `R`, given by the coarsest to
pology that
makes `f ↦ f x` continuous for all `x : A` (see `continuous_apply`).
Alternatively, given a presentation `A = ℤ[xᵢ]/I`,
this is the subspace topology `Hom(A, R) ↪ Hom(ℤ[xᵢ], R) = Rᶥ` (see `mvPolynomia
lHomeomorph`).

This is a scoped instance in `CommRingCat.HomTopology`.
-/
scoped instance : TopologicalSpace (A ⟶ R) :=
  .induced (fun f ↦ f.hom : _ → A → R) inferInstance

@[fun_prop]
nonrec lemma continuous_apply (x : A) :
    Continuous (fun f : A ⟶ R ↦ f.hom x) :=
  (continuous_apply x).comp continuous_induced_dom

variable (R A) in
/-
**CommRingCat.HomTopology.isEmbedding_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat
.HomTopology`。
形式化陈述：isEmbedding_hom : IsEmbedding (fun f : A ⟶ R => (f.hom : A -> R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isEmbedding_hom :
    IsEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) :=
  ⟨.induced _, fun _ _ e ↦ by ext; rw [e]⟩

@[fun_prop]
/-
**CommRingCat.HomTopology.continuous_precomp** 是 Mathlib 中的一个引理，位于命名空间 `CommRing
Cat.HomTopology`。
形式化陈述：continuous_precomp (f : A ⟶ B) : Continuous ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Pi.continuous_precomp`：Pi.continuous_precomp {ι' : Type*} (φ : ι' -> ι) 
: Continuous (· ∘ φ : (ι -> X) -> (ι' -> X))
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
lemma continuous_precomp (f : A ⟶ B) :
    Continuous ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) :=
  continuous_induced_rng.mpr ((Pi.continuous_precomp f.hom).comp continuous_induced_dom)

/-- If `A ≅ B`, then `Hom(A, R)` is homeomorphic to `Hom(B, R)`. -/
@[simps]
/-
**CommRingCat.HomTopology.precompHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `CommRingC
at.HomTopology`。
形式化陈述：precompHomeomorph (f : A ≅ B) : (B ⟶ R) ≃ₜ (A ⟶ R) where toFun φ
参数：f : A ≅ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A ≅ B`, then `Hom(A, R)` is homeomorphic to `Hom(B, R)`.
-/
def precompHomeomorph (f : A ≅ B) :
    (B ⟶ R) ≃ₜ (A ⟶ R) where
  toFun φ := _
  invFun φ := _
  continuous_toFun := continuous_precomp f.hom
  continuous_invFun := continuous_precomp f.inv
  left_inv _ := by simp
  right_inv _ := by simp
/-
**CommRingCat.HomTopology.isHomeomorph_precomp** 是 Mathlib 中的一个引理，位于命名空间 `CommRi
ngCat.HomTopology`。
形式化陈述：isHomeomorph_precomp (f : A ⟶ B) [IsIso f] : IsHomeomorph ((f ≫ ·) : (B ⟶ 
R) -> (A ⟶ R))
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
-/
lemma isHomeomorph_precomp (f : A ⟶ B) [IsIso f] :
    IsHomeomorph ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) :=
  (precompHomeomorph (asIso f)).isHomeomorph

/-- `Hom(A/I, R)` has the subspace topology of `Hom(A, R)`.
More generally, a surjection `A ⟶ B` gives rise to an embedding `Hom(B, R) ⟶ Hom(A, R)` -/
/-
**CommRingCat.HomTopology.isEmbedding_precomp_of_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `CommRingCat.HomTopology`。
形式化陈述：isEmbedding_precomp_of_surjective (f : A ⟶ B) (hf : Function.Surjective f)
 : Topology.IsEmbedding ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
参数：f : A ⟶ B；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.of_comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type 
u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topological
Space Y] [inst_2 :…
· 使用引理 `CommRingCat.HomTopology.continuous_precomp`：continuous_precomp (f : A ⟶ 
B) : Continuous ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Topology.IsInducing.induced`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace Y] (f : X → Y), Topology.IsInducing f
· 使用引理 `Function.Surjective.isEmbedding_comp`：Function.Surjective.isEmbedding_co
mp {n m : Type*} (f : m -> n) (hf : Function.Surjective f) : IsEmbedding ((· ∘ f
) : (n -> X) -> (m -> X))
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Topology.IsEmbedding.induced`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y
} [t : TopologicalSpace Y], Function.Injective f → Topology.IsEmbedding f
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
`Hom(A/I, R)` has the subspace topology of `Hom(A, R)`.
More generally, a surjection `A ⟶ B` gives rise to an embedding `Hom(B, R) ⟶ Hom
(A, R)`
-/
lemma isEmbedding_precomp_of_surjective
    (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine IsEmbedding.of_comp (continuous_precomp _) (IsInducing.induced _).continuous ?_
  suffices IsEmbedding ((· ∘ f.hom) : (B → R) → (A → R)) from
    this.comp (.induced (fun f g e ↦ by ext a; exact congr($e a)))
  exact Function.Surjective.isEmbedding_comp _ hf

/-- `Hom(A/I, R)` is a closed subspace of `Hom(A, R)` if `R` is T1. -/
/-
**CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective** 是 Mathlib 中的
一个引理，位于命名空间 `CommRingCat.HomTopology`。
形式化陈述：isClosedEmbedding_precomp_of_surjective [T1Space R] (f : A ⟶ B) (hf : Func
tion.Surjective f) : Topology.IsClosedEmbedding ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
参数：f : A ⟶ B；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.HomTopology.isEmbedding_precomp_of_surjective`：isEmbedding_p
recomp_of_surjective (f : A ⟶ B) (hf : Function.Surjective f) : Topology.IsEmbed
ding ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `CommRingCat.HomTopology.continuous_apply`：∀ {R A : CommRingCat} [inst : 
TopologicalSpace ↑R] (x : ↑A), Continuous fun f => (CommRingCat.Hom.hom f) x
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `RingHom.liftOfRightInverse_comp_apply`：liftOfRightInverse_comp_apply (hf
 : Function.RightInverse f_inv f) (g : { g : A ->+* C // RingHom.ker f <= RingHo
m.ker g }) (x : A) : (f.lif…

--- 原说明 ---
`Hom(A/I, R)` is a closed subspace of `Hom(A, R)` if `R` is T1.
-/
lemma isClosedEmbedding_precomp_of_surjective
    [T1Space R] (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine ⟨isEmbedding_precomp_of_surjective f hf, ?_⟩
  have : IsClosed (⋂ i : RingHom.ker f.hom, { f : A ⟶ R | f i = 0 }) :=
    isClosed_iInter fun x ↦ (isClosed_singleton (x := 0)).preimage (continuous_apply (R := R) x.1)
  convert! this
  ext x
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq, Subtype.forall, RingHom.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩ a ha; simp [ha]
  · exact fun H ↦ ⟨CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨x.hom, H⟩),
      by ext; simp [RingHom.liftOfRightInverse_comp_apply]⟩

/-- `Hom(A[Xᵢ], R)` is homeomorphic to `Hom(A, R) × Rⁱ`. -/
@[simps! apply_fst apply_snd symm_apply_hom]
noncomputable
/-
**CommRingCat.HomTopology.mvPolynomialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Comm
RingCat.HomTopology`。
形式化陈述：mvPolynomialHomeomorph (σ : Type v) (R A : CommRingCat.{max u v}) [Topolog
icalSpace R] [IsTopologicalRing R] : (CommRingCat.of (MvPolynomial σ A) ⟶ R) ≃ₜ 
((A ⟶ R) × (σ -> R)) where toFun f
参数：σ : Type v；R A : CommRingCat.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mvPolynomialHomeomorph (σ : Type v) (R A : CommRingCat.{max u v})
    [TopologicalSpace R] [IsTopologicalRing R] :
    (CommRingCat.of (MvPolynomial σ A) ⟶ R) ≃ₜ ((A ⟶ R) × (σ → R)) where
  toFun f := ⟨CommRingCat.ofHom MvPolynomial.C ≫ f, fun i ↦ f (.X i)⟩
  invFun fx := CommRingCat.ofHom (MvPolynomial.eval₂Hom fx.1.hom fx.2)
  left_inv f := by ext <;> simp
  right_inv fx := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine continuous_induced_rng.mpr ?_
    refine continuous_pi fun p ↦ ?_
    simp only [Function.comp_apply, hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    fun_prop

open Limits

variable (R A) in
/-
**CommRingCat.HomTopology.isClosedEmbedding_hom** 是 Mathlib 中的一个引理，位于命名空间 `CommR
ingCat.HomTopology`。
形式化陈述：isClosedEmbedding_hom [IsTopologicalRing R] [T1Space R] : IsClosedEmbeddin
g (fun f : A ⟶ R => (f.hom : A -> R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CommRingCat.HomTopology.mvPolynomialHomeomorph_apply_snd`：∀ (σ : Type v)
 (R A : CommRingCat) [inst : TopologicalSpace ↑R] [inst_1 : IsTopologicalRing ↑R
]   (f : CommRingCat.of (MvPolynomial σ ↑A) ⟶ …
· 使用定理 `MvPolynomial.comp_eval₂Hom`：comp_eval₂Hom [CommSemiring S₂] (f : R ->+* 
S₁) (g : σ -> S₁) (φ : S₁ ->+* S₂) : φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f)
 fun i => φ (g i…
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
· 使用引理 `CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective`：isClose
dEmbedding_precomp_of_surjective [T1Space R] (f : A ⟶ B) (hf : Function.Surjecti
ve f) : Topology.IsClosedEmbedding ((f ≫ ·) : (B ⟶ R)…
-/
lemma isClosedEmbedding_hom [IsTopologicalRing R] [T1Space R] :
    IsClosedEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) := by
  let f : CommRingCat.of (MvPolynomial A (⊥_ CommRingCat)) ⟶ A :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (initial.to A).hom id)
  have : Function.Surjective f := Function.LeftInverse.surjective (g := .X) fun x ↦ by simp [f]
  convert!
    ((mvPolynomialHomeomorph A R (.of _)).trans
          (.uniqueProd (⊥_ CommRingCat ⟶ R) _)).isClosedEmbedding.comp
      (isClosedEmbedding_precomp_of_surjective f this) using
    2 with g
  ext x
  simp +instances [f]
/-
**CommRingCat.HomTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.HomTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T2Space R] : T2Space (A ⟶ R) :=
  (isEmbedding_hom R A).t2Space
/-
**CommRingCat.HomTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat.HomTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTopologicalRing R] [T1Space R] [CompactSpace R] :
    CompactSpace (A ⟶ R) :=
  (isClosedEmbedding_hom R A).compactSpace

open Limits

set_option backward.isDefEq.respectTransparency false in
/-- `Hom(B ⊗[A] C, R)` has the subspace topology from `Hom(B, R) × Hom(C, R)`. -/
/-
**CommRingCat.HomTopology.isEmbedding_pushout** 是 Mathlib 中的一个引理，位于命名空间 `CommRin
gCat.HomTopology`。
形式化陈述：isEmbedding_pushout [IsTopologicalRing R] (φ : A ⟶ B) (ψ : A ⟶ C) : IsEmbe
dding fun f : pushout φ ψ ⟶ R => (pushout.inl φ ψ ≫ f, pushout.inr φ ψ ≫ f)
参数：φ : A ⟶ B；ψ : A ⟶ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `MvPolynomial.eval₂Hom_X'`：eval₂Hom_X' (f : R ->+* S₁) (g : σ -> S₁) (i :
 σ) : eval₂Hom f g (X i) = g i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.prodMap`：Topology.IsEmbedding.prodMap {f : X -> Y} 
{g : Z -> W} (hf : IsEmbedding f) (hg : IsEmbedding g) : IsEmbedding (Prod.map f
 g) where toIsIndu…
· 使用引理 `CommRingCat.HomTopology.isEmbedding_precomp_of_surjective`：isEmbedding_p
recomp_of_surjective (f : A ⟶ B) (hf : Function.Surjective f) : Topology.IsEmbed
ding ((f ≫ ·) : (B ⟶ R) -> (A ⟶ R))
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z : T
ype u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topolog
icalSpace Y] [inst_2 :…
· 使用定理 `RingHom.range_eq_top`：range_eq_top {f : R ->+* S} : f.range = (⊤ : Subri
ng S) ↔ Function.Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `CommRingCat.closure_range_union_range_eq_top_of_isPushout`：closure_range
_union_range_eq_top_of_isPushout {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R 
⟶ B} {a : A ⟶ X} {b : B ⟶ X} (H : IsPushout f g…
· 使用定理 `CategoryTheory.IsPushout.of_hasPushout`：of_hasPushout (f : Z ⟶ X) (g : Z
 ⟶ Y) [HasPushout f g] : IsPushout f g (pushout.inl f g) (pushout.inr f g)
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h
· 使用引理 `isEmbedding_graph`：isEmbedding_graph {f : X -> Y} (hf : Continuous f) : 
IsEmbedding fun x => (x, f x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
`Hom(B ⊗[A] C, R)` has the subspace topology from `Hom(B, R) × Hom(C, R)`.
-/
lemma isEmbedding_pushout [IsTopologicalRing R] (φ : A ⟶ B) (ψ : A ⟶ C) :
    IsEmbedding fun f : pushout φ ψ ⟶ R ↦ (pushout.inl φ ψ ≫ f, pushout.inr φ ψ ≫ f) := by
  -- The key idea: Let `X = Spec B` and `Y = Spec C`.
  -- We want to show `(X × Y)(R)` has the subspace topology from `X(R) × Y(R)`.
  -- We already know that `X(R) × Y(R)` is a subspace of `𝔸ᴮ(R) × 𝔸ᶜ(R)` and by explicit calculation
  -- this is isomorphic to `𝔸ᴮ⁺ᶜ(R)` which `(X × Y)(R)` embeds into.
  let PB := CommRingCat.of (MvPolynomial B A)
  let PC := CommRingCat.of (MvPolynomial C A)
  let fB : PB ⟶ B := CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id)
  have hfB : Function.Surjective fB.hom := fun x ↦ ⟨.X x, by simp [PB, fB]⟩
  let fC : PC ⟶ C := CommRingCat.ofHom (MvPolynomial.eval₂Hom ψ.hom id)
  have hfC : Function.Surjective fC.hom := fun x ↦ ⟨.X x, by simp [PC, fC]⟩
  have := (isEmbedding_precomp_of_surjective (R := R) fB hfB).prodMap
    (isEmbedding_precomp_of_surjective (R := R) fC hfC)
  rw [← IsEmbedding.of_comp_iff this]
  let PBC := CommRingCat.of (MvPolynomial (B ⊕ C) A)
  let fBC : PBC ⟶ pushout φ ψ :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (φ ≫ pushout.inl φ ψ).hom
      (Sum.elim (pushout.inl φ ψ).hom (pushout.inr φ ψ).hom))
  have hfBC : Function.Surjective fBC := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← closure_range_union_range_eq_top_of_isPushout (.of_hasPushout _ _), Subring.closure_le]
    simp only [Set.union_subset_iff, RingHom.coe_range, Set.range_subset_iff, Set.mem_range]
    exact ⟨fun x ↦ ⟨.X (.inl x), by simp [fBC, PBC]⟩, fun x ↦ ⟨.X (.inr x), by simp [fBC, PBC]⟩⟩
  let F : ((A ⟶ R) × ((B ⊕ C) → R)) → ((A ⟶ R) × (B → R)) × ((A ⟶ R) × (C → R)) :=
    fun x ↦ ⟨⟨x.1, x.2 ∘ Sum.inl⟩, ⟨x.1, x.2 ∘ Sum.inr⟩⟩
  have hF : IsEmbedding F := (Homeomorph.prodProdProdComm _ _ _ _).isEmbedding.comp
    ((isEmbedding_graph continuous_id).prodMap Homeomorph.sumArrowHomeomorphProdArrow.isEmbedding)
  have H := (mvPolynomialHomeomorph B R A).symm.isEmbedding.prodMap
    (mvPolynomialHomeomorph C R A).symm.isEmbedding
  convert!
    ((H.comp hF).comp (mvPolynomialHomeomorph _ R A).isEmbedding).comp
      (isEmbedding_precomp_of_surjective (R := R) fBC hfBC)
  have (s : _) : (pushout.inr φ ψ).hom (ψ.hom s) = (pushout.inl φ ψ).hom (φ.hom s) :=
    congr($(pushout.condition (f := φ)).hom s).symm
  ext f s <;> simp [fB, fC, fBC, PB, PC, PBC, F, this]

end CommRingCat.HomTopology

