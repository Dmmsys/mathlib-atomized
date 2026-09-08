/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Junyan Xu
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Purely inseparable extensions are universal homeomorphisms

If `K` is a purely inseparable extension of `k`, the induced map `Spec K ⟶ Spec k` is a universal
homeomorphism, i.e. it stays a homeomorphism after arbitrary base change.

## Main results

- `PrimeSpectrum.isHomeomorph_comap`: if `f : R →+* S` is a ring map with locally nilpotent kernel
  such that for every `x : S`, there exists `n > 0` such that `x ^ n` is in the image of `f`,
  `Spec f` is a homeomorphism.
- `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`: `Spec K ⟶ Spec k` is a universal
  homeomorphism for a purely inseparable field extension `K` over `k`.
-/

public section

open TensorProduct

variable (k K R S : Type*) [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] [CommRing S]

variable {R S} in
/-- If the kernel of `f : R →+* S` consists of nilpotent elements and for every `x : S`,
there exists `n > 0` such that `x ^ n` is in the range of `f`, then `Spec f` is a homeomorphism.
Note: This does not hold for semirings, because `ℕ →+* ℤ` satisfies these conditions, but
`Spec ℕ` has one more point than `Spec ℤ`. -/
@[stacks 0BR8 "Homeomorphism part"]
/-
**PrimeSpectrum.isHomeomorph_comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.isHomeomorph_comap (f : R ->+* S) (H : forall (x : S), exist
s n > 0, x ^ n in f.range) (hker : RingHom.ker f <= nilradical R) : IsHomeomorph
 (comap f)
参数：f : R ->+* S；H : forall (x : S), exists n > 0, x ^ n in f.range；hker : RingHo
m.ker f <= nilradical R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `PrimeSpectrum.ext_iff`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : P
rimeSpectrum R}, x = y ↔ x.asIdeal = y.asIdeal
· 使用定理 `IsIntegral.of_pow`：IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn
 : 0 < n) (hx : IsIntegral R <| x ^ n) : IsIntegral R x
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical`：comap_quotien
tMk_bijective_of_le_nilradical {I : Ideal R} (hle : I <= nilradical R) : Functio
n.Bijective (comap <| Ideal.Quotient.mk I)
· 使用定理 `RingHom.IsIntegral.comap_surjective`：∀ {R : Type u_1} {S : Type u_2} [in
st : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.IsIntegral → Function.
Injective ⇑f → Function.S…
· 使用定理 `RingHom.kerLift_injective`：kerLift_injective : Function.Injective (kerLi
ft f)
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpenMap_iff`：∀ {α : Type u} {β : T
ype u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {B : Set (Set α)},
   TopologicalSpace.IsTopologicalBasis …
· 使用定理 `PrimeSpectrum.isTopologicalBasis_basic_opens`：isTopologicalBasis_basic_o
pens : TopologicalSpace.IsTopologicalBasis (Set.range fun r : R => (basicOpen r 
: Set (PrimeSpectrum R)))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {f : α -> β} (hf 
: Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t
· 使用定理 `PrimeSpectrum.basicOpen_pow`：basicOpen_pow (f : R) (n : Nat) (hn : 0 < n
) : basicOpen (f ^ n) = basicOpen f
· 使用定理 `PrimeSpectrum.isOpen_basicOpen`：isOpen_basicOpen {a : R} : IsOpen (basic
Open a : Set (PrimeSpectrum R))

--- 原说明 ---
If the kernel of `f : R →+* S` consists of nilpotent elements and for every `x :
 S`,
there exists `n > 0` such that `x ^ n` is in the range of `f`, then `Spec f` is 
a homeomorphism.
Note: This does not hold for semirings, because `ℕ →+* ℤ` satisfies these condit
ions, but
`Spec ℕ` has one more point than `Spec ℤ`.
-/
lemma PrimeSpectrum.isHomeomorph_comap (f : R →+* S) (H : ∀ (x : S), ∃ n > 0, x ^ n ∈ f.range)
    (hker : RingHom.ker f ≤ nilradical R) : IsHomeomorph (comap f) := by
  have h1 : Function.Injective (comap f) := by
    intro q q' hqq'
    ext x
    obtain ⟨n, hn, y, hy⟩ := H x
    rw [← q.2.pow_mem_iff_mem _ hn, ← q'.2.pow_mem_iff_mem _ hn, ← hy]
    rw [PrimeSpectrum.ext_iff, SetLike.ext_iff] at hqq'
    apply hqq'
  have hint : f.kerLift.IsIntegral := fun x ↦
    have ⟨n, hn, y, hy⟩ := H x
    let _ := f.kerLift.toAlgebra
    IsIntegral.of_pow hn (hy ▸ f.kerLift.isIntegralElem_map (x := ⟦y⟧))
  have hbij : Function.Bijective (comap f) :=
    ⟨h1, (comap_quotientMk_bijective_of_le_nilradical hker).2.comp <|
      hint.comap_surjective f.kerLift_injective⟩
  refine ⟨continuous_comap f, ?_, h1, hbij.2⟩
  rw [isTopologicalBasis_basic_opens.isOpenMap_iff]
  rintro - ⟨s, rfl⟩
  obtain ⟨n, hn, r, hr⟩ := H s
  have : (comap f) '' (basicOpen s) = basicOpen r :=
    (Set.eq_preimage_iff_image_eq hbij).mp <| by rw [← basicOpen_pow _ n hn, ← hr]; rfl
  exact this ▸ isOpen_basicOpen

/-- Purely inseparable field extensions are universal homeomorphisms. -/
@[stacks 0BRA "Special case for purely inseparable field extensions"]
/-
**PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable [IsPurelyInseparab
le k K] : IsHomeomorph (comap <| algebraMap R (R otimes[k] K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PrimeSpectrum.isHomeomorph_comap`：PrimeSpectrum.isHomeomorph_comap (f : 
R ->+* S) (H : forall (x : S), exists n > 0, x ^ n in f.range) (hker : RingHom.k
er f <= nilradical R) …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `IsPurelyInseparable.exists_pow_mem_range_tensorProduct`：IsPurelyInsepara
ble.exists_pow_mem_range_tensorProduct [IsPurelyInseparable k K] (x : R otimes[k
] K) : exists n > 0, x ^ n in (algebraMap R …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Algebra.TensorProduct.includeLeft_injective`：includeLeft_injective [Modu
le.Flat R A] (hb : Function.Injective (algebraMap R B)) : Function.Injective (in
cludeLeft : A ->ₐ[S] A otimes[R] …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
Purely inseparable field extensions are universal homeomorphisms.
-/
lemma PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable [IsPurelyInseparable k K] :
    IsHomeomorph (comap <| algebraMap R (R ⊗[k] K)) := by
  let q := ringExpChar k
  refine isHomeomorph_comap _ (IsPurelyInseparable.exists_pow_mem_range_tensorProduct) ?_
  convert! bot_le
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap k K).injective

/-- If `L` is a purely inseparable extension of `K` over `R` and `S` is an `R`-algebra,
the induced map `Spec (L ⊗[R] S) ⟶ Spec (K ⊗[R] S)` is a homeomorphism. -/
/-
**PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable** 是 M
athlib 中的一个引理，位于命名空间 ``。
形式化陈述：PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable [
Algebra R K] [Algebra R S] (L : Type*) [Field L] [Algebra R L] [Algebra K L] [Is
ScalarTower R K L] [IsPurelyInseparable K L] : IsHomeomorph (comap (Algebra.Tens
orProduct.map (Algebra.ofId K L) (.id R S)).toRingHom)
参数：L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_restrictScalars_comp_includeRight`：map_restric
tScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : ((map f g).restri
ctScalars R).comp includeRight = includeRight.com…
· 使用引理 `Algebra.TensorProduct.cancelBaseChange_tmul`：cancelBaseChange_tmul (a : 
A) (s : S) (b : B) : Algebra.TensorProduct.cancelBaseChange R S T A B (a otimesₜ
 (s otimesₜ b)) = (s • a) otimesₜ…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用引理 `IsHomeomorph.comp`：comp {g : Y -> Z} (hg : IsHomeomorph g) (hf : IsHomeo
morph f) : IsHomeomorph (g ∘ f)
· 使用引理 `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`：PrimeSpectrum.i
sHomeomorph_comap_of_isPurelyInseparable [IsPurelyInseparable k K] : IsHomeomorp
h (comap <| algebraMap R (R otimes[k] K))
· 使用引理 `PrimeSpectrum.isHomeomorph_comap_of_bijective`：isHomeomorph_comap_of_bij
ective {f : R ->+* S} (hf : Function.Bijective f) : IsHomeomorph (comap f)
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
If `L` is a purely inseparable extension of `K` over `R` and `S` is an `R`-algeb
ra,
the induced map `Spec (L ⊗[R] S) ⟶ Spec (K ⊗[R] S)` is a homeomorphism.
-/
lemma PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable [Algebra R K]
    [Algebra R S] (L : Type*) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [IsPurelyInseparable K L] :
    IsHomeomorph (comap (Algebra.TensorProduct.map (Algebra.ofId K L) (.id R S)).toRingHom) := by
  let e : (L ⊗[R] S) ≃ₐ[K] L ⊗[K] (K ⊗[R] S) :=
    (Algebra.TensorProduct.cancelBaseChange R K K L S).symm
  let e2 : L ⊗[K] (K ⊗[R] S) ≃ₐ[K] (K ⊗[R] S) ⊗[K] L := Algebra.TensorProduct.comm ..
  have heq : Algebra.TensorProduct.map (Algebra.ofId K L) (AlgHom.id R S) =
      (e.symm.toAlgHom.comp e2.symm.toAlgHom).comp
        (IsScalarTower.toAlgHom K (K ⊗[R] S) ((K ⊗[R] S) ⊗[K] L)) := by
    ext; simp [e, e2]
  rw [heq]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    AlgEquiv.toAlgHom_toRingHom, IsScalarTower.coe_toAlgHom, comap_comp]
  exact (isHomeomorph_comap_of_isPurelyInseparable K L (K ⊗[R] S)).comp <|
    (isHomeomorph_comap_of_bijective e2.symm.bijective).comp <|
    isHomeomorph_comap_of_bijective e.symm.bijective
