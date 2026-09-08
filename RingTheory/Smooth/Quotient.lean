/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!

# Some lemmas about formally smooth under quotient

In this file, we formalize the result [Stacks 031L] : For flat ring homomorphism `f : R →+* S`,
`I` an ideal of `R` which is square zero, if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`.

-/

public section

open IsLocalRing

variable {R : Type*} [CommRing R]

/-- For any surjection `f : M →ₗ[R] N`, with `N` a flat `R`-module,
we have `K ⊓ IM = IK` for any `I : Ideal R`. -/
/-
**LinearMap.ker_inf_smul_top_eq_smul_of_flat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.ker_inf_smul_top_eq_smul_of_flat {M N : Type*} [AddCommGroup M] 
[AddCommGroup N] [Module R M] [Module R N] (I : Ideal R) (f : M ->ₗ[R] N) (surj 
: Function.Surjective f) [Module.Flat R N] : f.ker ⊓ (I • (⊤ : Submodule R M)) =
 I • f.ker
参数：I : Ideal R；f : M ->ₗ[R] N；surj : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ext_iff`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p q : Submodule R M}, p = 
q ↔ ∀ (…
· 使用引理 `Ideal.subtype_rTensor_range`：Ideal.subtype_rTensor_range {R : Type*} [Co
mmRing R] (M : Type*) [AddCommGroup M] [Module R M] (I : Ideal R) : ((TensorProd
uct.lid R M).comp…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.iff_rTensor_injective'`：iff_rTensor_injective' : Flat R M ↔ 
forall I : Ideal R, Function.Injective (rTensor M I.subtype)
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
For any surjection `f : M →ₗ[R] N`, with `N` a flat `R`-module,
we have `K ⊓ IM = IK` for any `I : Ideal R`.
-/
lemma LinearMap.ker_inf_smul_top_eq_smul_of_flat {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) (surj : Function.Surjective f)
    [Module.Flat R N] : f.ker ⊓ (I • (⊤ : Submodule R M)) = I • f.ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero, ← LinearMap.comp_apply, comm1, LinearMap.comp_apply, hy, f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply, ← comm2, LinearMap.comp_apply, hz, hy, Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

variable {S : Type*} [CommRing S] {R' S' : Type*} [CommRing R'] [CommRing S']

section

variable [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']

/-
**comap_ker_eq_sup_of_ker_eq_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma comap_ker_eq_sup_of_ker_eq_map (surjRS : Function.Surjective (algebraMap R S))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S)) :
    (RingHom.ker (algebraMap R' S')).comap (algebraMap R R') =
      RingHom.ker (algebraMap R R') ⊔ RingHom.ker (algebraMap R S) := by
  rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ S,
      ← RingHom.comap_ker]
  simp [eqmap, Ideal.comap_map_of_surjective' _ surjRS]
/-
**mul_le_ker_of_range_le_mul_of_sq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mul_le_ker_of_range_le_mul_of_sq_zero {J I : Ideal R} (sq : I ^ 2 = ⊥)
    (f : J.Cotangent →ₗ[R] J.Cotangent)
    (le : f.range ≤ (Submodule.comap J.subtype (I * J)).map J.toCotangent) :
    (Submodule.comap J.subtype (I * J)).map J.toCotangent ≤ f.ker := by
  rw [pow_two] at sq
  have {x : R} (h : x ∈ I * J) : f (J.toCotangent ⟨x, Ideal.mul_le_right h⟩) = 0 := by
    induction h using Submodule.mul_induction_on' with
    | mem_mul_mem y hy z hz =>
      rcases Submodule.mem_map.mp (le (f.mem_range_self (J.toCotangent ⟨z, hz⟩))) with ⟨w, hw, eqz⟩
      have mem_bot := Ideal.mul_mem_mul hy (Submodule.mem_comap.mp hw)
      simp only [← mul_assoc, sq, Submodule.bot_mul, Submodule.mem_bot] at mem_bot
      have eq0 : y • w = 0 := SetCoe.ext mem_bot
      have : ⟨y * z, Ideal.mul_le_right (Submodule.mul_mem_mul hy hz)⟩ = y • (⟨z, hz⟩ : J) := rfl
      rw [this, map_smul, map_smul, ← eqz, ← map_smul, eq0, map_zero]
    | add y ymem z zmem hy hz =>
      have : (⟨y + z, Ideal.mul_le_right (add_mem ymem zmem)⟩ : J) =
        ⟨y, Ideal.mul_le_right ymem⟩ + ⟨z, Ideal.mul_le_right zmem⟩ := rfl
      rw [this, map_add, map_add, hy, hz, add_zero]
  intro x hx
  rcases Submodule.mem_map.mp hx with ⟨x', hx', eq⟩
  simpa [← eq] using this hx'

set_option backward.isDefEq.respectTransparency.types false in
/-- For flat ring homomorphism `f : R →+* S`, `I` an ideal of `R` which is square zero,
if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`. -/
@[stacks 031L]
/-
**Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat [Module.Flat R 
S] (surj : Function.Surjective (algebraMap R R')) (surjS : Function.Surjective (
algebraMap S S')) (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebra
Map R R')).map (algebraMap R S)) (sq0 : (RingHom.ker (algebraMap R R')) ^ 2 = ⊥)
 (smoothq : Algebra.FormallySmooth R' S') : Algebra.FormallySmooth R S
参数：surj : Function.Surjective (algebraMap R R')；surjS : Function.Surjective (alg
ebraMap S S')；eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R
 R')).map (algebraMap R S)；sq0 : (RingHom.ker (algebraMap R R')) ^ 2 = ⊥；smoothq
 : Algebra.FormallySmooth R' S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `MvPolynomial.aeval_algebraMap_apply`：aeval_algebraMap_apply (x : σ -> A)
 (p : MvPolynomial σ R) : aeval (algebraMap A B ∘ x) p = algebraMap A B (MvPolyn
omial.aeval x p)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `MvPolynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : σ -> B) (p 
: MvPolynomial σ R) : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `MvPolynomial.ker_map`：ker_map (f : R ->+* S) : RingHom.ker (map f : MvPo
lynomial σ R ->+* MvPolynomial σ S) = Ideal.map (C : R ->+* MvPolynomial σ R) (R
ingHom.ker…
· 使用定理 `MvPolynomial.map_surjective`：map_surjective (hf : Function.Surjective f)
 : Function.Surjective (map f : MvPolynomial σ R -> MvPolynomial σ S₁)
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Extension.algebraMap_σ`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Algebra.Extension
 R S) (x : S), (alge…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FormallySmooth.iff_split_injection`：∀ {R : Type u} {A : Type v} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {P : Type u_2} 
  [inst_3 : CommRing P] [inst_4 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用引理 `LinearMap.ker_inf_smul_top_eq_smul_of_flat`：LinearMap.ker_inf_smul_top_e
q_smul_of_flat {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Mod
ule R N] (I : Ideal R) (f : M ->…
· 使用定理 `Ideal.smul_top_eq_map`：smul_top_eq_map {R S : Type*} [CommSemiring R] [C
ommSemiring S] [Algebra R S] (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (a
lgebraMap R…
（共 84 条，此处仅展示前 30 条）

--- 原说明 ---
For flat ring homomorphism `f : R →+* S`, `I` an ideal of `R` which is square ze
ro,
if `R ⧸ I →+* S ⧸ IS` is formally smooth, so is `f`.
-/
lemma Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat [Module.Flat R S]
    (surj : Function.Surjective (algebraMap R R'))
    (surjS : Function.Surjective (algebraMap S S'))
    (eqmap : RingHom.ker (algebraMap S S') = (RingHom.ker (algebraMap R R')).map (algebraMap R S))
    (sq0 : (RingHom.ker (algebraMap R R')) ^ 2 = ⊥) (smoothq : Algebra.FormallySmooth R' S') :
    Algebra.FormallySmooth R S := by
  let P := (Algebra.Generators.self R S).toExtension
  let : Algebra.FormallySmooth R P.Ring := instFormallySmoothMvPolynomial S
  let IP := (RingHom.ker (algebraMap R R')).map (algebraMap R P.Ring)
  let Gen : Algebra.Generators R' S' S := {
    val := algebraMap S S'
    σ' := fun s' ↦ MvPolynomial.X (Classical.choose (surjS s'))
    aeval_val_σ' s' := by simp [Classical.choose_spec (surjS s')] }
  let P' := Gen.toExtension
  let : Algebra.FormallySmooth R' P'.Ring := instFormallySmoothMvPolynomial S
  let : Algebra P.Ring P'.Ring := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P.Ring P'.Ring :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (MvPolynomial.map_C _ x).symm)
  algebraize [(algebraMap S S').comp (algebraMap P.Ring S)]
  have : IsScalarTower P.Ring P'.Ring S' := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    change (algebraMap S S') (MvPolynomial.aeval _root_.id x) =
      MvPolynomial.aeval Gen.val (MvPolynomial.map (algebraMap R R') x)
    rw [← MvPolynomial.aeval_algebraMap_apply]
    simp [MvPolynomial.aeval_map_algebraMap, Gen]
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring S')
  let I := RingHom.ker (algebraMap R R')
  let IS := I.map (algebraMap R S)
  have kerS : RingHom.ker (algebraMap S S') = IS := eqmap
  let IP := I.map (algebraMap R P.Ring)
  have kerP : RingHom.ker (algebraMap P.Ring P'.Ring) = IP := MvPolynomial.ker_map _
  have surjPP' : Function.Surjective (algebraMap P.Ring P'.Ring) :=
    MvPolynomial.map_surjective _ surj
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  classical
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x ↦ ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring S') := fun x ↦ ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have infeq : IP ⊓ J = IP * J := by
    refine le_antisymm (fun x hx ↦ ?_) Ideal.mul_le_inf
    have : x ∈ I • (J.restrictScalars R) := by
      change x ∈ I • (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.ker
      rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ surjP]
      simpa using! ⟨hx.2, hx.1⟩
    simpa [← Ideal.smul_restrictScalars I J, Submodule.restrictScalars_mem] using! this
  have h : J'.comap (algebraMap P.Ring P'.Ring) = RingHom.ker (algebraMap P.Ring P'.Ring) ⊔ J :=
    comap_ker_eq_sup_of_ker_eq_map surjP (by simp [kerP, ← ISeq, eqmap, IS, I])
  have Jle : J ≤ J'.comap (algebraMap P.Ring P'.Ring) := le_of_le_of_eq le_sup_right h.symm
  let mapcot := Ideal.mapCotangent J J' (Algebra.ofId P.Ring P'.Ring) Jle
  have cotsurj : Function.Surjective mapcot := Ideal.mapCotangent_surjective_of_comap_eq surjPP' h
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (_ ⊓ J)).map J.toCotangent :=
    Ideal.mapCotangent_ker_of_surjective surjPP' h
  rw [kerP, infeq] at cotker
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor R' P'.Ring S'
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] →ₗ[P.Ring]
    TensorProduct P'.Ring S' Ω[P'.Ring⁄R'] :=
    _root_.TensorProduct.lift ((((TensorProduct.mk P'.Ring S' Ω[P'.Ring⁄R']).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R R' P.Ring P'.Ring)).comp
      (IsScalarTower.toAlgHom P.Ring S S').toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, rfl⟩
    have : (KaehlerDifferential.kerToTensor R' P'.Ring S')
      ⟨(algebraMap P.Ring P'.Ring) y.1, Jle y.2⟩ =
      mapTen ((KaehlerDifferential.kerToTensor R P.Ring S) y) := by
      simp [KaehlerDifferential.kerToTensor, mapTen]
    simpa [mapcot] using! this
  let ediff : Ω[P.Ring⁄R] ≃ₗ[P.Ring] S →₀ P.Ring := KaehlerDifferential.mvPolynomialEquiv R S
  let eTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ≃ₗ[P.Ring] (S →₀ S) :=
    ((ediff.lTensor S).trans (TensorProduct.finsuppRight P.Ring P.Ring _ _ S)).trans
    (Finsupp.mapRange.linearEquiv (_root_.TensorProduct.rid P.Ring _))
  let toJ'cot : (S →₀ S) →ₗ[P.Ring] J'.Cotangent :=
    ((σ.restrictScalars P.Ring).comp mapTen).comp eTen.symm.toLinearMap
  let eS : (P.Ring ⧸ J) ≃ₗ[P.Ring] S :=
    (Submodule.quotEquivOfEq _ _ rfl).trans
    ((Algebra.linearMap P.Ring S).quotKerEquivOfSurjective surjP)
  let toJcot : (S →₀ S) →ₗ[P.Ring] J.Cotangent :=
    Finsupp.lsum P.Ring (fun s ↦ ((LinearMap.toSpanSingleton (P.Ring ⧸ J) J.Cotangent
      (Classical.choose (cotsurj (toJ'cot (Finsupp.single s 1))))).restrictScalars P.Ring).comp
        eS.symm.toLinearMap)
  have toJcot_spec : mapcot.comp toJcot = toJ'cot := by
    ext i s
    simp only [LinearMap.comp_assoc, toJcot, Finsupp.lsum_comp_lsingle]
    rcases Ideal.Quotient.mk_surjective (eS.symm s) with ⟨p, hp⟩
    have (x : J.Cotangent) : mapcot (eS.symm s • x) = p • mapcot x := hp ▸ map_smul mapcot p x
    have psmul : p • 1 = s := by simpa [Algebra.smul_def, eS] using! eS.eq_symm_apply.mp hp
    simp [this, Classical.choose_spec (cotsurj (toJ'cot (Finsupp.single i 1))), ← map_smul, psmul]
  let σ' := toJcot.comp eTen.toLinearMap
  have σ'_spec' : mapcot.comp σ' = (σ.restrictScalars P.Ring).comp mapTen := by
    simp only [← LinearMap.comp_assoc, toJcot_spec, σ']
    apply LinearMap.ext (fun x ↦ ?_)
    exact ((σ.restrictScalars P.Ring).comp mapTen).congr_arg (eTen.symm_apply_apply x)
  have σ'_spec : mapcot.comp (σ'.comp cottoTen) = mapcot := by
    rw [← LinearMap.comp_assoc, σ'_spec', LinearMap.comp_assoc, ← comm, ← LinearMap.comp_assoc,
      ← LinearMap.restrictScalars_comp, hσ]
    rfl
  let Δ : J.Cotangent →ₗ[P.Ring] J.Cotangent := LinearMap.id - (σ'.comp cottoTen)
  have rΔle : Δ.range ≤ (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    rintro x ⟨y, hy⟩
    simp only [← cotker, ← hy, LinearMap.mem_ker, Δ]
    rw [LinearMap.sub_apply, map_sub, LinearMap.id_apply, ← LinearMap.comp_apply, σ'_spec, sub_self]
  have leΔk := mul_le_ker_of_range_le_mul_of_sq_zero (by simp [IP, ← Ideal.map_pow, I, sq0]) Δ rΔle
  let δ := (Submodule.liftQ _ Δ (le_of_eq_of_le cotker leΔk)).comp
    (mapcot.quotKerEquivOfSurjective cotsurj).symm.toLinearMap
  have δ_spec : δ.comp mapcot = Δ := by
    ext
    simp [δ]
  have : σ'.comp cottoTen + δ.comp ((σ.restrictScalars P.Ring).comp (mapTen.comp cottoTen)) =
    LinearMap.id := by
    rw [← comm, ← LinearMap.comp_assoc mapcot, ← LinearMap.restrictScalars_comp, hσ]
    exact add_eq_of_eq_sub' δ_spec
  exact ⟨σ' + (δ.comp (σ.restrictScalars P.Ring)).comp mapTen, this⟩

end

/-- A pure `RingHom` variant of `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat` -/
/-
**RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero (f : R ->+* S)
 (flat : f.Flat) (qR : R ->+* R') (qS : S ->+* S') (g : R' ->+* S') (surjR : Fun
ction.Surjective qR) (surjS : Function.Surjective qS) (comm : qS.comp f = g.comp
 qR) (sq0 : (RingHom.ker qR) ^ 2 = ⊥) (eqmap : RingHom.ker qS = (RingHom.ker qR)
.map f) (smoothq : g.FormallySmooth) : f.FormallySmooth
参数：f : R ->+* S；flat : f.Flat；qR : R ->+* R'；qS : S ->+* S'；g : R' ->+* S'；surjR
 : Function.Surjective qR；surjS : Function.Surjective qS；comm : qS.comp f = g.co
mp qR；sq0 : (RingHom.ker qR) ^ 2 = ⊥；eqmap : RingHom.ker qS = (RingHom.ker qR).m
ap f；smoothq : g.FormallySmooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat`：Algebra.Form
allySmooth.of_surjective_of_ker_eq_map_of_flat [Module.Flat R S] (surj : Functio
n.Surjective (algebraMap R R')) (surjS : Functio…
· 使用定理 `RingHom.FormallySmooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.FormallySmooth → Algebra.
FormallySmooth R S

--- 原说明 ---
A pure `RingHom` variant of `Algebra.FormallySmooth.of_surjective_of_ker_eq_map_
of_flat`
-/
lemma RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero (f : R →+* S) (flat : f.Flat)
    (qR : R →+* R') (qS : S →+* S') (g : R' →+* S') (surjR : Function.Surjective qR)
    (surjS : Function.Surjective qS) (comm : qS.comp f = g.comp qR)
    (sq0 : (RingHom.ker qR) ^ 2 = ⊥) (eqmap : RingHom.ker qS = (RingHom.ker qR).map f)
    (smoothq : g.FormallySmooth) : f.FormallySmooth := by
  algebraize [f, qR, qS, g, qS.comp f]
  let _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' comm
  exact Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat surjR surjS eqmap sq0 ‹_›
