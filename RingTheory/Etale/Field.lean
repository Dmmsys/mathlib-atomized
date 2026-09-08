/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Unramified.Field

/-!
# Étale algebras over fields

## Main results

Let `K` be a field, `A` be a `K`-algebra and `L` be a field extension of `K`.

- `Algebra.FormallyEtale.of_isSeparable`:
    If `L` is separable over `K`, then `L` is formally étale over `K`.
- `Algebra.FormallyEtale.iff_isSeparable`:
    If `L` is (essentially) of finite type over `K`, then `L/K` is étale iff `L/K` is separable.
- `Algebra.FormallyEtale.iff_formallyUnramified_of_field`:
    If `A` is (essentially) of finite type over `K`,
    then `A/K` is formally étale iff `A/K` is formally unramified.
- `Algebra.FormallyEtale.iff_exists_algEquiv_prod`:
    If `A` is (essentially) of finite type over `K`,
    then `A/K` is étale iff `A` is a finite product of separable field extensions.
- `Algebra.Etale.iff_exists_algEquiv_prod`:
    `A/K` is étale iff `A` is a finite product of finite separable field extensions.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

public section


universe u

variable (K L : Type*) (A : Type u) [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A]

open Algebra Polynomial

open scoped TensorProduct

namespace Algebra.FormallyEtale

/--
This is a weaker version of `of_isSeparable` that additionally assumes `EssFiniteType K L`.
Use that instead.

This is Iversen Corollary II.5.3.
-/
/-
**Algebra.FormallyEtale.of_isSeparable_aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Fo
rmallyEtale`。
形式化陈述：of_isSeparable_aux [Algebra.IsSeparable K L] [EssFiniteType K L] : Formall
yEtale K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.of_isSeparable`：of_isSeparable [Algebra.IsSep
arable K L] : FormallyUnramified K L
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyEtale.iff_comp_bijective`：iff_comp_bijective : FormallyE
tale R A ↔ forall ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I
 ^ 2 = ⊥ -> Function.Bijective…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective_of_small`：iff_comp_injecti
ve_of_small [Small.{w} A] : FormallyUnramified R A ↔ forall ⦃B : Type w⦄ [CommRi
ng B], forall [Algebra R B] (I : Ideal B) (_…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Polynomial.Separable.aeval_derivative_ne_zero`：∀ {R : Type u} [inst : Co
mmSemiring R] {S : Type v} [inst_1 : CommSemiring S] [Nontrivial S] [inst_3 : Al
gebra R S]   {p : Polynomial R},   …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
This is a weaker version of `of_isSeparable` that additionally assumes `EssFinit
eType K L`.
Use that instead.

This is Iversen Corollary II.5.3.
-/
theorem of_isSeparable_aux [Algebra.IsSeparable K L] [EssFiniteType K L] :
    FormallyEtale K L := by
  -- We already know that for field extensions
  -- IsSeparable + EssFiniteType => FormallyUnramified + Finite
  have := FormallyUnramified.of_isSeparable K L
  have := FormallyUnramified.finite_of_free (R := K) (S := L)
  -- We shall show that any `f : L → B/I` can be lifted to `L → B` if `I^2 = ⊥`
  refine FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_
  refine ⟨FormallyUnramified.iff_comp_injective_of_small.mp
    (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  -- By separability and finiteness, we may assume `L = K(α)` with `p` the minpoly of `α`.
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  -- Let `x : B` such that `f(α) = x` in `B / I`.
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (f pb.gen)
  have helper : ∀ x, IsScalarTower.toAlgHom K B (B ⧸ I) x = Ideal.Quotient.mk I x := fun _ ↦ rfl
  -- Then `p(x) = 0 mod I`, and the goal is to find some `ε ∈ I` such that
  -- `p(x + ε) = p(x) + ε p'(x) = 0`, and we will get our lift into `B`.
  have hx' : Ideal.Quotient.mk I (aeval x (minpoly K pb.gen)) = 0 := by
    rw [← helper, ← aeval_algHom_apply, helper, hx, aeval_algHom_apply, minpoly.aeval, map_zero]
  -- Since `p` is separable, `-p'(x)` is invertible in `B ⧸ I`,
  obtain ⟨u, hu⟩ : ∃ u, (aeval x) (derivative (minpoly K pb.gen)) * u + 1 ∈ I := by
    have := (isUnit_iff_ne_zero.mpr ((Algebra.IsSeparable.isSeparable K
      pb.gen).aeval_derivative_ne_zero (minpoly.aeval K _))).map f
    rw [← aeval_algHom_apply, ← hx, ← helper, aeval_algHom_apply, helper] at this
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (-this.unit⁻¹ : B ⧸ I)
    use u
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, map_one, hu, mul_neg,
      IsUnit.mul_val_inv, neg_add_cancel]
  -- And `ε = p(x)/(-p'(x))` works.
  use pb.liftEquiv.symm ⟨x + u * aeval x (minpoly K pb.gen), ?_⟩
  · apply pb.algHom_ext
    simp [hx, hx']
  · rw [← eval_map_algebraMap, Polynomial.eval_add_of_sq_eq_zero, derivative_map,
      ← one_mul (eval x _), eval_map_algebraMap, eval_map_algebraMap, ← mul_assoc, ← add_mul,
      ← Ideal.mem_bot, ← h, pow_two, add_comm]
    · exact Ideal.mul_mem_mul hu (Ideal.Quotient.eq_zero_iff_mem.mp hx')
    rw [← Ideal.mem_bot, ← h]
    apply Ideal.pow_mem_pow
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hx', mul_zero]

open scoped IntermediateField in
/-
**Algebra.FormallyEtale.of_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Formal
lyEtale`。
形式化陈述：of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.FormallyEtale.iff_comp_bijective`：iff_comp_bijective : FormallyE
tale R A ↔ forall ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I
 ^ 2 = ⊥ -> Function.Bijective…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective_of_small`：iff_comp_injecti
ve_of_small [Small.{w} A] : FormallyUnramified R A ↔ forall ⦃B : Type w⦄ [CommRi
ng B], forall [Algebra R B] (I : Ideal B) (_…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Algebra.FormallyUnramified.of_isSeparable`：of_isSeparable [Algebra.IsSep
arable K L] : FormallyUnramified K L
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Algebra.IsSeparable.of_algHom`：Algebra.IsSeparable.of_algHom [Algebra.Is
Separable F E'] : Algebra.IsSeparable F E
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `Algebra.FormallyEtale.of_isSeparable_aux`：of_isSeparable_aux [Algebra.Is
Separable K L] [EssFiniteType K L] : FormallyEtale K L
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用引理 `Algebra.FormallyEtale.comp_bijective`：comp_bijective [FormallyEtale R A]
 (I : Ideal B) (hI : I ^ 2 = ⊥) : Function.Bijective ((Ideal.Quotient.mkₐ R I).c
omp : (A ->ₐ[R] B) -> A ->…
· 使用定理 `Function.Bijective.existsUnique`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Bijective f → ∀ (b : β), ∃! a, f a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.comp_assoc`：comp_assoc (φ₁ : C ->ₐ[R] D) (φ₂ : B ->ₐ[R] C) (φ₃ : 
A ->ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 66 条，此处仅展示前 30 条）
-/
lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L := by
  -- We shall show that any `f : L → B/I` can be lifted to `L → B` if `I^2 = ⊥`.
  refine FormallyEtale.iff_comp_bijective.mpr fun B _ _ I h ↦ ?_
  -- But we already know that there exists a unique lift for every finite subfield of `L`
  -- by `of_isSeparable_aux`, so we can glue them all together.
  refine ⟨FormallyUnramified.iff_comp_injective_of_small.mp
    (FormallyUnramified.of_isSeparable K L) I h, ?_⟩
  intro f
  have : ∀ k : L, ∃! g : K⟮k⟯ →ₐ[K] B,
      (Ideal.Quotient.mkₐ K I).comp g = f.comp (IsScalarTower.toAlgHom K _ L) := by
    intro k
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮k⟯) L)
    have := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsSeparable.isSeparable K k).isIntegral
    have := FormallyEtale.of_isSeparable_aux K (K⟮k⟯)
    have := FormallyEtale.comp_bijective (R := K) (A := K⟮k⟯) I h
    exact this.existsUnique _
  choose g hg₁ hg₂ using this
  have hg₃ : ∀ x y (h : x ∈ K⟮y⟯), g y ⟨x, h⟩ = g x (IntermediateField.AdjoinSimple.gen K x) := by
    intro x y h
    have e : K⟮x⟯ ≤ K⟮y⟯ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact h
    rw [← hg₂ _ ((g _).comp (IntermediateField.inclusion e))]
    · rfl
    apply AlgHom.ext
    rw [← AlgHom.comp_assoc, hg₁, AlgHom.comp_assoc]
    simp
  have H : ∀ x y : L, ∃ α : L, x ∈ K⟮α⟯ ∧ y ∈ K⟮α⟯ := by
    intro x y
    have : FiniteDimensional K K⟮x, y⟯ := by
      apply IntermediateField.finiteDimensional_adjoin
      intro x _; exact (Algebra.IsSeparable.isSeparable K x).isIntegral
    have := IsSeparable.of_algHom _ _ (IsScalarTower.toAlgHom K (K⟮x, y⟯) L)
    obtain ⟨⟨α, hα⟩, e⟩ := Field.exists_primitive_element K K⟮x, y⟯
    apply_fun (IntermediateField.map (IntermediateField.val _)) at e
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map] at e
    simp only [IntermediateField.coe_val, Set.image_singleton,
      IntermediateField.fieldRange_val] at e
    have hx : x ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    have hy : y ∈ K⟮α⟯ := e ▸ IntermediateField.subset_adjoin K {x, y} (by simp)
    exact ⟨α, hx, hy⟩
  refine ⟨⟨⟨⟨⟨fun x ↦ g x (IntermediateField.AdjoinSimple.gen K x), ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · change g 1 1 = 1; rw [map_one]
  · intro x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_mul, ← hg₃ _ _ (mul_mem hx hy)]
    rfl
  · change g 0 0 = 0; rw [map_zero]
  · intro x y
    obtain ⟨α, hx, hy⟩ := H x y
    simp only [← hg₃ _ _ hx, ← hg₃ _ _ hy, ← map_add, ← hg₃ _ _ (add_mem hx hy)]
    rfl
  · intro r
    change g _ (algebraMap K _ r) = _
    rw [AlgHom.commutes]
  · ext x
    simpa using AlgHom.congr_fun (hg₁ x) (IntermediateField.AdjoinSimple.gen K x)
/-
**Algebra.FormallyEtale.iff_isSeparable** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Forma
llyEtale`。
形式化陈述：iff_isSeparable [EssFiniteType K L] : FormallyEtale K L ↔ Algebra.IsSepara
ble K L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.isSeparable`：isSeparable : Algebra.IsSeparabl
e K L
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用引理 `Algebra.FormallyEtale.of_isSeparable`：of_isSeparable [Algebra.IsSeparabl
e K L] : FormallyEtale K L
-/
theorem iff_isSeparable [EssFiniteType K L] :
    FormallyEtale K L ↔ Algebra.IsSeparable K L :=
  ⟨fun _ ↦ FormallyUnramified.isSeparable K L, fun _ ↦ of_isSeparable K L⟩
/-
**Algebra.FormallyEtale.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [EssFiniteType K A] [FormallyEtale K A] (p : Ideal A) [p.IsPrime] :
    Algebra.IsSeparable K (A ⧸ p) := by
  have := Algebra.FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  have := Algebra.FormallyUnramified.isReduced_of_field K A
  let := Ideal.Quotient.field p
  rw [← Algebra.FormallyEtale.iff_isSeparable]
  have : Algebra.FormallyEtale K (Π (m : MaximalSpectrum A), (A ⧸ m.asIdeal)) :=
    .of_equiv ((IsArtinianRing.equivPi _).restrictScalars K)
  rw [Algebra.FormallyEtale.pi_iff] at this
  exact this ⟨p, inferInstance⟩

attribute [local instance] Ideal.Quotient.field FormallyUnramified.finite_of_free in
/-
**Algebra.FormallyEtale.of_formallyUnramified_of_field** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.FormallyEtale`。
形式化陈述：of_formallyUnramified_of_field [EssFiniteType K A] [FormallyUnramified K A
] : FormallyEtale K A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyEtale.iff_isSeparable`：iff_isSeparable [EssFiniteType K 
L] : FormallyEtale K L ↔ Algebra.IsSeparable K L
· 使用定理 `Algebra.instEssFiniteTypeQuotientIdeal`：∀ (R : Type u_1) (S : Type u_2) 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssF
initeType R S] (I : Ideal S)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.FormallyUnramified.iff_isSeparable`：iff_isSeparable (L : Type u)
 [Field L] [Algebra K L] [EssFiniteType K L] : FormallyUnramified K L ↔ Algebra.
IsSeparable K L
· 使用定理 `Algebra.FormallyEtale.of_equiv`：of_equiv [FormallyEtale R A] (e : A ≃ₐ[R
] B) : FormallyEtale R B
· 使用定理 `Algebra.FormallyEtale.instForallOfFinite`：∀ {R : Type u_1} {I : Type u_2
} (A : I → Type u_3) [inst : CommRing R] [inst_1 : (i : I) → CommRing (A i)]   [
inst_2 : (i : I) → Algebra R (…
· 使用定理 `IsArtinianRing.instFiniteMaximalSpectrum`：∀ (R : Type u_1) [inst : CommS
emiring R] [IsArtinianRing R], Finite (MaximalSpectrum R)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
-/
lemma of_formallyUnramified_of_field [EssFiniteType K A] [FormallyUnramified K A] :
    FormallyEtale K A := by
  have := FormallyUnramified.isReduced_of_field K A
  have : IsArtinianRing A := .of_finite K A
  have (I : MaximalSpectrum A) : FormallyEtale K (A ⧸ I.asIdeal) := by
    rw [FormallyEtale.iff_isSeparable, ← FormallyUnramified.iff_isSeparable]
    infer_instance
  exact .of_equiv ((IsArtinianRing.equivPi A).restrictScalars K).symm

variable {K A} in
/-
**Algebra.FormallyEtale.iff_formallyUnramified_of_field** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.FormallyEtale`。
形式化陈述：iff_formallyUnramified_of_field [EssFiniteType K A] : FormallyEtale K A ↔ 
FormallyUnramified K A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用引理 `Algebra.FormallyEtale.of_formallyUnramified_of_field`：of_formallyUnramif
ied_of_field [EssFiniteType K A] [FormallyUnramified K A] : FormallyEtale K A
-/
lemma iff_formallyUnramified_of_field [EssFiniteType K A] :
    FormallyEtale K A ↔ FormallyUnramified K A :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_formallyUnramified_of_field K A⟩

attribute [local instance] IsArtinianRing.fieldOfSubtypeIsMaximal in
/--
If `A` is an essentially of finite type algebra over a field `K`, then `A` is formally étale
over `K` if and only if `A` is a finite product of separable field extensions.
-/
/-
**Algebra.FormallyEtale.iff_exists_algEquiv_prod** 是 Mathlib 中的一个定理，位于命名空间 `Alge
bra.FormallyEtale`。
形式化陈述：iff_exists_algEquiv_prod [EssFiniteType K A] : FormallyEtale K A ↔ exists 
(I : Type u) (_ : Finite I) (Ai : I -> Type u) (_ : forall i, Field (Ai i)) (_ :
 forall i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i), forall i, Algebra.IsSepara
ble K (Ai i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Algebra.FormallyEtale.instFormallyUnramified`：∀ {R : Type u} {A : Type v
} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fo
rmallyEtale R A], Algebra.Formally…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.FormallyUnramified.isReduced_of_field`：isReduced_of_field : IsRe
duced A
· 使用定理 `isArtinian_of_tower`：isArtinian_of_tower (R) {S M} [Semiring R] [Semirin
g S] [AddCommMonoid M] [SMul R S] [Module S M] [Module R M] [IsScalarTower R S M
] (h : Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsArtinianRing.instFiniteMaximalSpectrum`：∀ (R : Type u_1) [inst : CommS
emiring R] [IsArtinianRing R], Finite (MaximalSpectrum R)
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyEtale.iff_isSeparable`：iff_isSeparable [EssFiniteType K 
L] : FormallyEtale K L ↔ Algebra.IsSeparable K L
· 使用定理 `Algebra.instEssFiniteTypeQuotientIdeal`：∀ (R : Type u_1) (S : Type u_2) 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssF
initeType R S] (I : Ideal S)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyEtale.pi_iff`：pi_iff [Finite I] : FormallyEtale R (Π i, 
A i) ↔ forall i, FormallyEtale R (A i)
· 使用定理 `Algebra.FormallyEtale.iff_of_equiv`：iff_of_equiv (e : A ≃ₐ[R] B) : Forma
llyEtale R A ↔ FormallyEtale R B
· 使用引理 `Algebra.FormallyEtale.of_isSeparable`：of_isSeparable [Algebra.IsSeparabl
e K L] : FormallyEtale K L

--- 原说明 ---
If `A` is an essentially of finite type algebra over a field `K`, then `A` is fo
rmally étale
over `K` if and only if `A` is a finite product of separable field extensions.
-/
theorem iff_exists_algEquiv_prod [EssFiniteType K A] :
    FormallyEtale K A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
        ∀ i, Algebra.IsSeparable K (Ai i) := by
  classical
  constructor
  · intro H
    have := FormallyUnramified.finite_of_free K A
    have := FormallyUnramified.isReduced_of_field K A
    have : IsArtinianRing A := isArtinian_of_tower K inferInstance
    let v (i : MaximalSpectrum A) : A := (IsArtinianRing.equivPi A).symm (Pi.single i 1)
    rw [FormallyEtale.iff_of_equiv ((IsArtinianRing.equivPi A).restrictScalars K),
      FormallyEtale.pi_iff] at H
    exact ⟨_, inferInstance, _, _, _, (IsArtinianRing.equivPi A).restrictScalars K,
      fun I ↦ (iff_isSeparable _ _).mp inferInstance⟩
  · intro ⟨I, _, Ai, _, _, e, _⟩
    rw [FormallyEtale.iff_of_equiv e, FormallyEtale.pi_iff]
    exact fun I ↦ of_isSeparable K (Ai I)

/-- If `R` is an étale `k`-algebra over a separably closed field `k`, it is
isomorphic to the (finite) product of copies of `k` indexed by the prime spectrum of `R`. -/
noncomputable
/-
**Algebra.FormallyEtale.equivPiOfIsSepClosed** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.
FormallyEtale`。
形式化陈述：equivPiOfIsSepClosed [EssFiniteType K A] [FormallyEtale K A] [IsSepClosed 
K] : A ≃ₐ[K] PrimeSpectrum A -> K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivPiOfIsSepClosed [EssFiniteType K A] [FormallyEtale K A] [IsSepClosed K] :
    A ≃ₐ[K] PrimeSpectrum A → K :=
  haveI := Algebra.FormallyUnramified.finite_of_free K A
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  haveI := FormallyUnramified.isReduced_of_field K A
  letI _ (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  ((IsArtinianRing.equivPi _).restrictScalars K).trans <|
    (AlgEquiv.piCongrRight fun _ ↦ (AlgEquiv.ofBijective (Algebra.ofId K _)
      (IsSepClosed.algebraMap_bijective _ _)).symm).trans <|
    (AlgEquiv.piCongrLeft _ (fun _ ↦ K) IsArtinianRing.primeSpectrumEquivMaximalSpectrum).symm

variable {K} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.FormallyEtale`。
形式化陈述：equivPiOfIsSepClosed_self_apply [IsSepClosed K] (x : K) (p : PrimeSpectrum
 K) : equivPiOfIsSepClosed K K x p = x
参数：x : K；p : PrimeSpectrum K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.piCongrLeft_symm_apply`：piCongrLeft_symm_apply (g : forall b, P b)
 (a : α) : (piCongrLeft P e).symm g a = g (e a)
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用引理 `IsSepClosed.algebraMap_bijective`：algebraMap_bijective [IsSepClosed k] [
Algebra k K] [Algebra.IsSeparable k K] : Function.Bijective (algebraMap k K)
· 使用定理 `Algebra.FormallyEtale.instIsSeparableQuotientIdealOfEssFiniteTypeOfIsPri
me`：∀ (K : Type u_1) (A : Type u) [inst : Field K] [inst_1 : CommRing A] [inst_2
 : Algebra K A] [Algebra.EssFiniteType K A]   [Algebra.FormallyE…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivPiOfIsSepClosed_self_apply [IsSepClosed K] (x : K) (p : PrimeSpectrum K) :
    equivPiOfIsSepClosed K K x p = x := by
  let := Ideal.Quotient.field p.asIdeal
  dsimp [equivPiOfIsSepClosed]
  simp only [Equiv.piCongrLeft_symm_apply, AlgEquiv.piCongrRight_apply,
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum_apply_asIdeal, IsArtinianRing.equivPi_apply]
  apply (AlgEquiv.ofBijective (ofId K (K ⧸ p.asIdeal))
    (IsSepClosed.algebraMap_bijective _ _)).injective
  simp

variable {K A} in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.FormallyEtale.equivPiOfIsSepClosed_comap** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.FormallyEtale`。
形式化陈述：equivPiOfIsSepClosed_comap {B : Type*} [CommRing B] [EssFiniteType K A] [F
ormallyEtale K A] [Algebra K B] [EssFiniteType K B] [FormallyEtale K B] [IsSepCl
osed K] (f : A ->ₐ[K] B) (x : A) (p : PrimeSpectrum B) : equivPiOfIsSepClosed K 
A x (p.comap f) = equivPiOfIsSepClosed K B (f x) p
参数：f : A ->ₐ[K] B；x : A；p : PrimeSpectrum B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.piCongrLeft_symm_apply`：piCongrLeft_symm_apply (g : forall b, P b)
 (a : α) : (piCongrLeft P e).symm g a = g (e a)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.comp_ofId`：comp_ofId (φ : A ->ₐ[R] B) : φ.comp (Algebra.ofId R A
) = Algebra.ofId R B
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.ofId_apply`：ofId_apply (r) : ofId R A r = algebraMap R A r
· 使用引理 `AlgEquiv.ofBijective_apply_symm_apply`：ofBijective_apply_symm_apply (f :
 A₁ ->ₐ[R] A₂) (hf : Function.Bijective f) (x : A₂) : f ((ofBijective f hf).symm
 x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma equivPiOfIsSepClosed_comap {B : Type*} [CommRing B] [EssFiniteType K A] [FormallyEtale K A]
    [Algebra K B] [EssFiniteType K B] [FormallyEtale K B] [IsSepClosed K]
    (f : A →ₐ[K] B) (x : A) (p : PrimeSpectrum B) :
    equivPiOfIsSepClosed K A x (p.comap f) = equivPiOfIsSepClosed K B (f x) p := by
  dsimp [equivPiOfIsSepClosed]
  simp only [Equiv.piCongrLeft_symm_apply, AlgEquiv.piCongrRight_apply,
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum_apply_asIdeal, PrimeSpectrum.comap_asIdeal,
    IsArtinianRing.equivPi_apply]
  have heq : ofId K (B ⧸ p.asIdeal) = (Ideal.quotientMapₐ p.asIdeal f le_rfl).comp (ofId _ _) := by
    simp
  suffices h : Ideal.quotientMapₐ p.asIdeal f le_rfl x = f x by
    apply FaithfulSMul.algebraMap_injective K (B ⧸ p.asIdeal)
    rw [← ofId_apply, ← ofId_apply]
    nth_rw 1 [heq]
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.ofBijective_apply_symm_apply]
    convert h
    apply AlgEquiv.ofBijective_apply_symm_apply
  simp

end Algebra.FormallyEtale

/--
`A` is étale over a field `K` if and only if
`A` is a finite product of finite separable field extensions.
-/
/-
**Algebra.Etale.iff_exists_algEquiv_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.Etale.iff_exists_algEquiv_prod : Etale K A ↔ exists (I : Type u) (
_ : Finite I) (Ai : I -> Type u) (_ : forall i, Field (Ai i)) (_ : forall i, Alg
ebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i), forall i, Module.Finite K (Ai i) ∧ Algeb
ra.IsSeparable K (Ai i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyEtale.iff_exists_algEquiv_prod`：iff_exists_algEquiv_prod
 [EssFiniteType K A] : FormallyEtale K A ↔ exists (I : Type u) (_ : Finite I) (A
i : I -> Type u) (_ : forall i, Fiel…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用引理 `Algebra.FormallyUnramified.finite_of_free`：finite_of_free [Module.Free R
 S] : Module.Finite R S
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.FinitePresentation.of_finiteType`：of_finiteType [IsNoetherianRin
g R] : FiniteType R A ↔ FinitePresentation R A
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R

--- 原说明 ---
`A` is étale over a field `K` if and only if
`A` is a finite product of finite separable field extensions.
-/
theorem Algebra.Etale.iff_exists_algEquiv_prod :
    Etale K A ↔
      ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
        (_ : ∀ i, Algebra K (Ai i)) (_ : A ≃ₐ[K] Π i, Ai i),
        ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  constructor
  · intro H
    obtain ⟨I, _, Ai, _, _, e, _⟩ := (FormallyEtale.iff_exists_algEquiv_prod K A).mp inferInstance
    have := FormallyUnramified.finite_of_free K A
    exact ⟨_, ‹_›, _, _, _, e, fun i ↦ ⟨.of_surjective ((LinearMap.proj i).comp e.toLinearMap)
      ((Function.surjective_eval i).comp e.surjective), inferInstance⟩⟩
  · intro ⟨I, _, Ai, _, _, e, H⟩
    choose h₁ h₂ using H
    have := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
    refine ⟨?_, FinitePresentation.of_finiteType.mp inferInstance⟩
    exact (FormallyEtale.iff_exists_algEquiv_prod K A).mpr ⟨_, inferInstance, _, _, _, e, h₂⟩
