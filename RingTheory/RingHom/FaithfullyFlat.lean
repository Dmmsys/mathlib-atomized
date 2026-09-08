/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.RingTheory.RingHom.Flat

/-!
# Faithfully flat ring maps

A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. This is
the same as being flat and a surjection on prime spectra.
-/

@[expose] public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}

/-- A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. -/
@[stacks 00HB "Part (4)", algebraize Module.FaithfullyFlat]
/-
**RingHom.FaithfullyFlat** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Pr
op
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-
algebra.
-/
def FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S
/-
**RingHom.faithfullyFlat_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：faithfullyFlat_algebraMap_iff [Algebra R S] : (algebraMap R S).FaithfullyF
lat ↔ Module.FaithfullyFlat R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
-/
lemma faithfullyFlat_algebraMap_iff [Algebra R S] :
    (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S := by
  simp only [FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FaithfullyFlat

/-
**RingHom.FaithfullyFlat.flat** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.FaithfullyFlat`
。
形式化陈述：flat (hf : f.FaithfullyFlat) : f.Flat
参数：hf : f.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
-/
lemma flat (hf : f.FaithfullyFlat) : f.Flat := by
  algebraize [f]
  exact inferInstanceAs <| Module.Flat R S
/-
**RingHom.FaithfullyFlat.iff_flat_and_comap_surjective** 是 Mathlib 中的一个引理，位于命名空间
 `RingHom.FaithfullyFlat`。
形式化陈述：iff_flat_and_comap_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surje
ctive (PrimeSpectrum.comap f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
· 使用引理 `RingHom.flat_algebraMap_iff`：RingHom.flat_algebraMap_iff {R S : Type*} [
CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).Flat ↔ Module.Flat R S
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用引理 `PrimeSpectrum.comap_surjective_of_faithfullyFlat`：PrimeSpectrum.comap_su
rjective_of_faithfullyFlat : Function.Surjective (comap (algebraMap A B))
· 使用引理 `Module.FaithfullyFlat.of_comap_surjective`：Module.FaithfullyFlat.of_coma
p_surjective [Flat A B] (h : Function.Surjective (PrimeSpectrum.comap (algebraMa
p A B))) : Module.FaithfullyFla…
-/
lemma iff_flat_and_comap_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.comap f) := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f, faithfullyFlat_algebraMap_iff, flat_algebraMap_iff]
  exact ⟨fun h ↦ ⟨inferInstance, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ ↦ .of_comap_surjective hf⟩
/-
**RingHom.FaithfullyFlat.eq_and** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.FaithfullyFla
t`。
形式化陈述：eq_and : FaithfullyFlat = fun (f : R ->+* S) => f.Flat ∧ Function.Surjecti
ve (PrimeSpectrum.comap f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`：iff_flat_and_comap
_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.com
ap f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_and : FaithfullyFlat =
      fun (f : R →+* S) ↦ f.Flat ∧ Function.Surjective (PrimeSpectrum.comap f) := by
  ext
  rw [iff_flat_and_comap_surjective]
/-
**RingHom.FaithfullyFlat.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingH
om.FaithfullyFlat`。
形式化陈述：stableUnderComposition : StableUnderComposition FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
· 使用定理 `Module.FaithfullyFlat.trans`：trans : FaithfullyFlat R M
-/
lemma stableUnderComposition : StableUnderComposition FaithfullyFlat := by
  introv R hf hg
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f), faithfullyFlat_algebraMap_iff]
  exact .trans R S T
/-
**RingHom.FaithfullyFlat.of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Faithfu
llyFlat`。
形式化陈述：of_bijective (hf : Function.Bijective f) : f.FaithfullyFlat
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`：iff_flat_and_comap
_surjective : f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective (PrimeSpectrum.com
ap f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PrimeSpectrum.comap_comp_apply`：comap_comp_apply (f : R ->+* S) (g : S -
>+* S') (x : PrimeSpectrum S') : comap (g.comp f) x = comap f (comap g x)
· 使用定理 `PrimeSpectrum.comap_id`：comap_id : comap (RingHom.id R) = fun x => x
-/
lemma of_bijective (hf : Function.Bijective f) : f.FaithfullyFlat := by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p ↦ ?_⟩
  use p.comap ((RingEquiv.ofBijective f hf).symm : _ →+* _)
  have : ((RingEquiv.ofBijective f hf).symm : _ →+* _).comp f = id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSpectrum.comap_comp_apply, this, PrimeSpectrum.comap_id]
/-
**RingHom.FaithfullyFlat.injective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Faithfully
Flat`。
形式化陈述：injective (hf : f.FaithfullyFlat) : Function.Injective ⇑f
参数：hf : f.FaithfullyFlat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
lemma injective (hf : f.FaithfullyFlat) : Function.Injective ⇑f := by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S
/-
**RingHom.FaithfullyFlat.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Faithful
lyFlat`。
形式化陈述：respectsIso : RespectsIso FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.FaithfullyFlat.stableUnderComposition`：stableUnderComposition : 
StableUnderComposition FaithfullyFlat
· 使用引理 `RingHom.FaithfullyFlat.of_bijective`：of_bijective (hf : Function.Bijecti
ve f) : f.FaithfullyFlat
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma respectsIso : RespectsIso FaithfullyFlat :=
  stableUnderComposition.respectsIso (fun e ↦ .of_bijective e.bijective)
/-
**RingHom.FaithfullyFlat.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `Ring
Hom.FaithfullyFlat`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange FaithfullyFlat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.FaithfullyFlat.respectsIso`：respectsIso : RespectsIso Faithfully
Flat
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
· 使用定理 `Module.FaithfullyFlat.instTensorProduct`：∀ (R : Type u) (M : Type v) [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (S : Typ
e u_1)   [inst_3 : CommRing S…
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange FaithfullyFlat := by
  refine .mk respectsIso (fun R S T _ _ _ _ _ _ ↦ show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

end RingHom.FaithfullyFlat

