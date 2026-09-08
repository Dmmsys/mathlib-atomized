/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, David Swinarski
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!

# Being projective is a local property

## Main results
- `LinearMap.split_surjective_of_localization_maximal`
  If `N` is finitely presented, then `f : M →ₗ[R] N`
  being split injective can be checked on stalks (of maximal ideals).
- `Module.projective_of_localization_maximal` If `M` is finitely presented,
  then `M` being projective can be checked on stalks (of maximal ideals).

## TODO
- Show that being projective is Zariski-local (very hard)

-/

public section

universe uM

variable {R N N' : Type*} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
variable [Module R N] [AddCommGroup N'] [Module R N'] (S : Submonoid R)

/-
**Module.free_of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ] [
CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S) (f : M ->
ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] : Modul
e.Free Rₛ Mₛ
参数：S；f : M ->ₗ[R] Mₛ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] :
    Module.Free Rₛ Mₛ :=
  Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

universe uR' uM' in
/--
Also see `IsLocalizedModule.lift_rank_eq` for a version for non-free modules,
but requires `S` to not contain any zero-divisors.
-/
/-
**Module.lift_rank_of_isLocalizedModule_of_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.lift_rank_of_isLocalizedModule_of_free (Rₛ : Type uR') {Mₛ : Type u
M'} [AddCommGroup Mₛ] [Module R Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] 
[IsScalarTower R Rₛ Mₛ] (S : Submonoid R) (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ
] [IsLocalizedModule S f] [Module.Free R M] [Nontrivial Rₛ] : Cardinal.lift.{uM}
 (Module.rank Rₛ Mₛ) = Cardinal.lift.{uM'} (Module.rank R M)
参数：Rₛ : Type uR'；S : Submonoid R；f : M ->ₗ[R] Mₛ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `rank_tensorProduct`：rank_tensorProduct : Module.rank R (M otimes[S] M') 
= Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M')
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Also see `IsLocalizedModule.lift_rank_eq` for a version for non-free modules,
but requires `S` to not contain any zero-divisors.
-/
theorem Module.lift_rank_of_isLocalizedModule_of_free
    (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Cardinal.lift.{uM} (Module.rank Rₛ Mₛ) = Cardinal.lift.{uM'} (Module.rank R M) := by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert! this
  exact Cardinal.lift_umax
/-
**Module.finrank_of_isLocalizedModule_of_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_of_isLocalizedModule_of_free (Rₛ : Type*) {Mₛ : Type*} [Add
CommGroup Mₛ] [Module R Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScala
rTower R Rₛ Mₛ] (S : Submonoid R) (f : M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLoc
alizedModule S f] [Module.Free R M] [Nontrivial Rₛ] : Module.finrank Rₛ Mₛ = Mod
ule.finrank R M
参数：Rₛ : Type*；S : Submonoid R；f : M ->ₗ[R] Mₛ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Module.lift_rank_of_isLocalizedModule_of_free`：Module.lift_rank_of_isLoc
alizedModule_of_free (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R
 Mₛ] [CommRing Rₛ] [Algebra R Rₛ] […
-/
theorem Module.finrank_of_isLocalizedModule_of_free
    (Rₛ : Type*) {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
    Module.finrank Rₛ Mₛ = Module.finrank R M := by
  simpa using! congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))
/-
**Module.projective_of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R
 Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S) (f 
: M ->ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective 
R M] : Module.Projective Rₛ Mₛ
参数：S；f : M ->ₗ[R] Mₛ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `Module.Projective.tensorProduct`：∀ {R : Type u} [inst : Semiring R] {R₀ 
: Type u_2} {M : Type u_1} {N : Type u_3} [inst_1 : CommSemiring R₀]   [inst_2 :
 Algebra R₀ R] [inst_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
-/
theorem Module.projective_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Projective R M] :
    Module.Projective Rₛ Mₛ :=
  Projective.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Projective R M] : Module.Projective (Localization S) (LocalizedModule S M) :=
  Module.projective_of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [CommRing A] [Algebra R A] [Module.Projective R A] :
    Module.Projective (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)) :=
  Module.projective_of_isLocalizedModule S (IsScalarTower.toAlgHom R A _).toLinearMap
/-
**LinearMap.split_surjective_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：LinearMap.split_surjective_of_localization_maximal (f : M ->ₗ[R] N) [Modul
e.FinitePresentation R N] (H : forall (I : Ideal R) (_ : I.IsMaximal), exists (g
 : _ ->ₗ[Localization.AtPrime I] _), (LocalizedModule.map I.primeCompl f).comp g
 = LinearMap.id) : exists (g : N ->ₗ[R] M), f.comp g = LinearMap.id
参数：f : M ->ₗ[R] N；H : forall (I : Ideal R) (_ : I.IsMaximal), exists (g : _ ->ₗ[
Localization.AtPrime I] _), (LocalizedModule.map I.primeCompl f).comp g = Linear
Map.id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Submodule.mem_of_localization_maximal`：Submodule.mem_of_localization_max
imal (m : M) (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], f P m 
in N.localized₀ P.primeComp…
· 使用定理 `instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePr
esentation`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [
inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCom…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.map_id`：LocalizedModule.map_id : LocalizedModule.map S (
.id (R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
· 使用定理 `IsLocalizedModule.ext`：ext (map_unit : forall x : S, IsUnit ((algebraMap
 R (Module.End R M'')) x)) ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j =
 k
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用引理 `LocalizedModule.map_mk`：LocalizedModule.map_mk (f : M ->ₗ[R] N) (x y) : 
map S f (.mk x y) = LocalizedModule.mk (f x) y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
theorem LinearMap.split_surjective_of_localization_maximal
    (f : M →ₗ[R] N) [Module.FinitePresentation R N]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
    ∃ (g : _ →ₗ[Localization.AtPrime I] _),
      (LocalizedModule.map I.primeCompl f).comp g = LinearMap.id) :
    ∃ (g : N →ₗ[R] M), f.comp g = LinearMap.id := by
  change LinearMap.id ∈ LinearMap.range (LinearMap.llcomp R N M N f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ ↦ LocalizedModule.map P.primeCompl) _ _
    fun I hI ↦ ?_
  rw [LocalizedModule.map_id]
  have : LinearMap.id ∈ LinearMap.range (LinearMap.llcomp _
    (LocalizedModule I.primeCompl N) _ _ (LocalizedModule.map I.primeCompl f)) := H I hI
  convert! this
  · ext f
    constructor
    · intro hf
      obtain ⟨a, ha, c, rfl⟩ := hf
      obtain ⟨g, rfl⟩ := ha
      use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) g c
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
        (LocalizedModule.map I.primeCompl) c).injective
      dsimp
      conv_rhs => rw [← Submonoid.smul_def]
      conv_lhs => rw [← LinearMap.map_smul_of_tower]
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', IsLocalizedModule.mk'_cancel']
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [LocalizedModule.map_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearMap.llcomp_apply,
        LocalizedModule.map_mk]
    · rintro ⟨g, rfl⟩
      obtain ⟨⟨g, s⟩, rfl⟩ :=
        IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.map I.primeCompl) g
      simp only [Function.uncurry_apply_pair]
      refine ⟨f.comp g, ⟨g, rfl⟩, s, ?_⟩
      apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
         (LocalizedModule.map I.primeCompl) s).injective
      simp only [Module.algebraMap_end_apply, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
        ← LinearMap.map_smul_of_tower]
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl N)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl N)
      ext
      simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
        LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, llcomp_apply]
/-
**Module.projective_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.projective_of_localization_maximal (H : forall (I : Ideal R) (_ : I
.IsMaximal), Module.Projective (Localization.AtPrime I) (LocalizedModule I.prime
Compl M)) [Module.FinitePresentation R M] : Module.Projective R M
参数：H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Localization.A
tPrime I) (LocalizedModule I.primeCompl M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用引理 `LocalizedModule.map_surjective`：LocalizedModule.map_surjective (l : M ->
ₗ[R] N) (hl : Function.Surjective l) : Function.Surjective (map S l)
· 使用定理 `LinearMap.split_surjective_of_localization_maximal`：LinearMap.split_surj
ective_of_localization_maximal (f : M ->ₗ[R] N) [Module.FinitePresentation R N] 
(H : forall (I : Ideal R) (_ : I.IsMaxim…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
-/
theorem Module.projective_of_localization_maximal (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
    Module.Projective (Localization.AtPrime I) (LocalizedModule I.primeCompl M))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  have : Module.Finite R M := by infer_instance
  obtain ⟨s, hs⟩ := this
  let N := s →₀ R
  let f : N →ₗ[R] M := Finsupp.linearCombination R (Subtype.val : s → M)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, Subtype.range_val]
    convert! hs
  have (I : Ideal R) (hI : I.IsMaximal) :=
    letI := H I hI
    Module.projective_lifting_property (LocalizedModule.map I.primeCompl f) LinearMap.id
    (LocalizedModule.map_surjective _ _ hf)
  obtain ⟨g, hg⟩ := LinearMap.split_surjective_of_localization_maximal _ this
  exact Module.Projective.of_split _ _ hg

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
include f in
/--
A variant of `Module.projective_of_localization_maximal` that accepts `IsLocalizedModule`.
-/
/-
**Module.projective_of_localization_maximal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.projective_of_localization_maximal' (H : forall (I : Ideal R) (_ : 
I.IsMaximal), Module.Projective (Rₚ I) (Mₚ I)) [Module.FinitePresentation R M] :
 Module.Projective R M
参数：H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Rₚ I) (Mₚ I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.projective_of_localization_maximal`：Module.projective_of_localiza
tion_maximal (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Loc
alization.AtPrime I) (Localized…
· 使用定理 `Module.Projective.of_equiv`：∀ {R : Type u_8} {S : Type u_9} [inst : Semi
ring R] [inst_1 : Semiring S] {M : Type u_10} {N : Type u_11}   [inst_2 : AddCom
mMonoid M] [inst…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用定理 `RingHomInvPair.of_ringEquiv_symm`：of_ringEquiv_symm (e : R₁ ≃+* R₂) : Ri
ngHomInvPair (↑e.symm : R₂ ->+* R₁) ↑e
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalization.map_id_mk'`：map_id_mk' {Q : Type*} [CommSemiring Q] [Alge
bra R Q] [IsLocalization M Q] (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk
' S x y) = mk' …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…

--- 原说明 ---
A variant of `Module.projective_of_localization_maximal` that accepts `IsLocaliz
edModule`.
-/
theorem Module.projective_of_localization_maximal'
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal), Module.Projective (Rₚ I) (Mₚ I))
    [Module.FinitePresentation R M] : Module.Projective R M := by
  apply Module.projective_of_localization_maximal
  intro P hP
  set e := (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
  refine Module.Projective.of_equiv (M := Mₚ P) (R := Rₚ P)
    (σ := e)
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
        (LocalizedModule.mkLinearMap P.primeCompl M)
      map_smul' := ?_ }
  · intro r m
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
    dsimp [e]
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
      IsLocalization.map_id_mk']
