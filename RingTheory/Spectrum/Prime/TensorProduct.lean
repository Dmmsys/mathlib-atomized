/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!

# Lemmas regarding the prime spectrum of tensor products

## Main result
- `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks`:
  If `R →+* T` is surjective on stalks (see `Mathlib/RingTheory/SurjectiveOnStalks.lean`),
  then `Spec(S ⊗[R] T) → Spec S × Spec T` is a topological embedding
  (where `Spec S × Spec T` is the Cartesian product with the product topology).
-/

@[expose] public section

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing T] [Algebra R T]

open TensorProduct Topology

/-- The canonical map from `Spec(S ⊗[R] T)` to the Cartesian product `Spec S × Spec T`. -/
noncomputable
/-
**PrimeSpectrum.tensorProductTo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimeSpectrum.tensorProductTo (x : PrimeSpectrum (S otimes[R] T)) : PrimeS
pectrum S × PrimeSpectrum T
参数：x : PrimeSpectrum (S otimes[R] T)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def PrimeSpectrum.tensorProductTo (x : PrimeSpectrum (S ⊗[R] T)) :
    PrimeSpectrum S × PrimeSpectrum T :=
  ⟨comap (algebraMap _ _) x, comap Algebra.TensorProduct.includeRight.toRingHom x⟩

@[fun_prop]
/-
**PrimeSpectrum.continuous_tensorProductTo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.continuous_tensorProductTo : Continuous (tensorProductTo R S
 T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
-/
lemma PrimeSpectrum.continuous_tensorProductTo : Continuous (tensorProductTo R S T) :=
  (continuous_comap _).prodMk (continuous_comap _)

variable (hRT : (algebraMap R T).SurjectiveOnStalks)
include hRT
/-
**PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux** 是 Mathli
b 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux (p₁ p₂
 : PrimeSpectrum (S otimes[R] T)) (h : tensorProductTo R S T p₁ = tensorProductT
o R S T p₂) : p₁ <= p₂
参数：p₁ p₂ : PrimeSpectrum (S otimes[R] T)；h : tensorProductTo R S T p₁ = tensorPr
oductTo R S T p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `RingHom.SurjectiveOnStalks.exists_mul_eq_tmul`：∀ {R : Type u_1} [inst : 
CommRing R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRi
ng T]   [inst_3 : Algebra R T] [ins…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux
    (p₁ p₂ : PrimeSpectrum (S ⊗[R] T))
    (h : tensorProductTo R S T p₁ = tensorProductTo R S T p₂) :
    p₁ ≤ p₂ := by
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  intro x hxp₁
  by_contra hxp₂
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul x
    (p₂.asIdeal.comap g) inferInstance
  have h₁ : a ⊗ₜ[R] t ∈ p₁.asIdeal := e ▸ p₁.asIdeal.mul_mem_left (1 ⊗ₜ[R] (r • t)) hxp₁
  have h₂ : a ⊗ₜ[R] t ∉ p₂.asIdeal := e ▸ p₂.asIdeal.primeCompl.mul_mem ht hxp₂
  rw [← mul_one a, ← one_mul t, ← Algebra.TensorProduct.tmul_mul_tmul] at h₁ h₂
  have h₃ : t ∉ p₂.asIdeal.comap g := fun h ↦ h₂ (Ideal.mul_mem_left _ _ h)
  have h₄ : a ∉ p₂.asIdeal.comap (algebraMap S (S ⊗[R] T)) :=
    fun h ↦ h₂ (Ideal.mul_mem_right _ _ h)
  replace h₃ : t ∉ p₁.asIdeal.comap g := by
    rwa [show p₁.asIdeal.comap g = p₂.asIdeal.comap g from congr($h.2.1)]
  replace h₄ : a ∉ p₁.asIdeal.comap (algebraMap S (S ⊗[R] T)) := by
    rwa [show p₁.asIdeal.comap (algebraMap S (S ⊗[R] T)) = p₂.asIdeal.comap _ from congr($h.1.1)]
  exact p₁.asIdeal.primeCompl.mul_mem h₄ h₃ h₁
/-
**PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks** 是 Mathlib 中的
一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks : IsEmbedd
ing (tensorProductTo R S T)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Continuous.le_induced`：Continuous.le_induced (h : Continuous[t, t'] f) :
 t <= t'.induced f
· 使用引理 `PrimeSpectrum.continuous_tensorProductTo`：PrimeSpectrum.continuous_tenso
rProductTo : Continuous (tensorProductTo R S T)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.IsBasis.le_iff`：∀ {α : Type u_5} {t₁ t₂ : Topolog
icalSpace α} {Us : Set (TopologicalSpace.Opens α)},   TopologicalSpace.Opens.IsB
asis Us → (t₁ ≤ t₂ ↔ ∀ U ∈ …
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `RingHom.SurjectiveOnStalks.exists_mul_eq_tmul`：∀ {R : Type u_1} [inst : 
CommRing R] {S : Type u_2} [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRi
ng T]   [inst_3 : Algebra R T] [ins…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.IsPrime.mul_mem_iff_mem_or_mem`：∀ {α : Type u} [inst : Semiring α]
 {I : Ideal α} [I.IsTwoSided], I.IsPrime → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ 
I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux`：Pri
meSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux (p₁ p₂ : PrimeS
pectrum (S otimes[R] T)) (h : tensorProductTo R S T p₁ = …
-/
lemma PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks :
    IsEmbedding (tensorProductTo R S T) := by
  refine ⟨?_, fun p₁ p₂ e ↦
    (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₁ p₂ e).antisymm
      (isEmbedding_tensorProductTo_of_surjectiveOnStalks_aux R S T hRT p₂ p₁ e.symm)⟩
  let g : T →+* S ⊗[R] T := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨(continuous_tensorProductTo ..).le_induced.antisymm (isBasis_basic_opens.le_iff.mpr ?_)⟩
  rintro _ ⟨f, rfl⟩
  rw [@isOpen_iff_forall_mem_open]
  rintro J (hJ : f ∉ J.asIdeal)
  obtain ⟨t, r, a, ht, e⟩ := hRT.exists_mul_eq_tmul f
    (J.asIdeal.comap g) inferInstance
  refine ⟨_, ?_, ⟨_, (basicOpen a).2.prod (basicOpen t).2, rfl⟩, ?_⟩
  · rintro x ⟨hx₁ : a ⊗ₜ[R] (1 : T) ∉ x.asIdeal, hx₂ : (1 : S) ⊗ₜ[R] t ∉ x.asIdeal⟩
      (hx₃ : f ∈ x.asIdeal)
    apply x.asIdeal.primeCompl.mul_mem hx₁ hx₂
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← e]
    exact x.asIdeal.mul_mem_left _ hx₃
  · have : a ⊗ₜ[R] (1 : T) * (1 : S) ⊗ₜ[R] t ∉ J.asIdeal := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← e]
      exact J.asIdeal.primeCompl.mul_mem ht hJ
    rwa [J.isPrime.mul_mem_iff_mem_or_mem.not, not_or] at this
